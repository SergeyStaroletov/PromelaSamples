// (c) Sergey Staroletov
//spin -B -T gpu_pipeline_frame_s3virge.pml 

// S3 Virge pipeline variant with no hardware z-buffer (low vram memory)
#define VERTEX_SHADERS 0
#define PIXEL_SHADERS 1
#define TMUS 1
#define ROPS 1

#define FB
#define DEBUG
#define FRAME_TIME 100000
#define CLOCK_STAT 30000

#include "gpu_verticles.pml"
#include "gpu_triangles.pml"
#include "gpu_trigo.pml"
#include "gpu_adjacency.pml"

#define DRAW_VERTICES
#define DRAW_RASTER
#define DRAW_TEXTURES
#define TOTAL_FRAMES 1

#define MX 200
#define MY 60
#define MX2 MX/2
#define MY2 MY/2

#define MAX_FRAGMENTS MX*MY
#define MAX_PIXELS MX*MY

#define MEM_READ_DELAY 5
#define MEM_WRITE_DELAY 5

int vertex_x[MAX_VERTICES];
int vertex_y[MAX_VERTICES];
int vertex_z[MAX_VERTICES];

int vertex_u[MAX_VERTICES];
int vertex_v[MAX_VERTICES];

int vertex_nx[MAX_VERTICES];
int vertex_ny[MAX_VERTICES];
int vertex_nz[MAX_VERTICES];

byte vertex_ready[MAX_VERTICES];

int triangle_v0[MAX_TRIANGLES];
int triangle_v1[MAX_TRIANGLES];
int triangle_v2[MAX_TRIANGLES];
byte triangle_ready[MAX_TRIANGLES];

int vertex_adj_start[MAX_VERTICES];
int vertex_adj_count[MAX_VERTICES];
int adj_tri_ids[MAX_ADJ_DATA];
int tri_ready_count[MAX_TRIANGLES];

int fragment_x[MAX_FRAGMENTS];
int fragment_y[MAX_FRAGMENTS];
int fragment_z[MAX_FRAGMENTS];
int fragment_u[MAX_FRAGMENTS];
int fragment_v[MAX_FRAGMENTS];
int fragment_nx[MAX_FRAGMENTS];
int fragment_ny[MAX_FRAGMENTS];
int fragment_nz[MAX_FRAGMENTS];

int fragment_base_color[MAX_FRAGMENTS];
int fragment_tri_id[MAX_FRAGMENTS];
int fragment_tex_color[MAX_FRAGMENTS];

byte fragment_color_r[MAX_FRAGMENTS];
byte fragment_color_g[MAX_FRAGMENTS];
byte fragment_color_b[MAX_FRAGMENTS];
byte fragment_ready[MAX_FRAGMENTS];

//Z-buffer is now in SystemMemory

int frame_buffer[(MX + 1) * (MY + 1)];

int current_vertex_id = 0;
int current_triangle_id = 0;
int current_fragment_id = 0;
int current_pixel_id = 0;

int triangles_assembled = 0;
int fragments_generated = 0;
int total_pixels_written = 0;

byte current_frame = 0;
byte total_frames_completed = 0;
byte simulation_active = 1;
byte frame_in_progress = 0;
byte all_data_sent = 0;

byte pipe_raster_finised = 0;
byte pipe_texture_finised = 0;
byte pipe_pixel_finised = 0;
byte pipe_rop_finised = 0;

int pipe_texture_processed[TMUS];
int pipe_pixel_fragment_processed[PIXEL_SHADERS];
int pipe_rop_processed[ROPS];

int vertex_orig_x[MAX_VERTICES];
int vertex_orig_y[MAX_VERTICES];
int vertex_orig_z[MAX_VERTICES];

int norm_x[MAX_TRIANGLES];
int norm_y[MAX_TRIANGLES];
int norm_z[MAX_TRIANGLES];

byte tri_color[MAX_TRIANGLES];

#define TEX_SIZE 16
byte texture[TEX_SIZE*TEX_SIZE];

int angle = 0;

byte shades[8] = {' ', '.', ':', 'o', 'O', '8', '@', '#'};

typedef ZReq {
    int x;       
    int y;       
    int new_z;   
    byte op;     
};

chan z_req = [10] of { ZReq };
chan z_resp = [10] of { int }; 

inline display_frame_buffer(frame, pixels) {
    #ifdef FB
    printf("--- Frame %d (pixels: %d) ---\n", frame, pixels);
    #endif
    int yy = 0;
    do
    :: yy < MY -> {
        #ifdef FB
        printf("|");
        #endif
        int xx = 0;
        do
        :: xx < MX -> {
            int pixel_val = frame_buffer[yy * MX + xx];
            byte char_index;
            if
            :: pixel_val == ' ' -> char_index = 0
            :: pixel_val >= 0 && pixel_val < 255 ->
                char_index = (pixel_val * 7) / 255;
                #ifdef FB
                printf("%c", shades[char_index])
                #endif
            :: else ->
                #ifdef FB
                printf("%c", pixel_val)
                #endif
            fi;
            xx++;
        }
        :: else -> break
        od;
        yy++;
        #ifdef FB
        printf("\n");
        #endif
    }
    :: else -> break
    od;
}

inline clear_frame_buffer() {
    int f;
    for (f : 0 .. (MX-1) * (MY - 1)) {
        frame_buffer[f] = 0;
    }
}

inline init_texture() {
    int x, y;
    for (y : 0 .. TEX_SIZE-1) {
        for (x : 0 .. TEX_SIZE-1) {
            if :: ((x/4 + y/4) % 2 == 0) -> {
                texture[y * TEX_SIZE + x] = 200;
            } :: else -> {
                texture[y * TEX_SIZE + x] = 100;
            }
            fi;
        }
    }
    for (x : 0 .. MAX_VERTICES-1) {
        vertex_u[x] = 15;
        vertex_v[x] = 0;
    }
}

int global_clock = 0;
byte clock_updated = 0;
chan clock_sync = [0] of { bit };

chan vertex_to_fetch = [20] of { int };
chan vertex_processed = [20] of { int };
chan triangle_assembled = [20] of { int };
chan fragment_rasterized = [200] of { int };
chan fragment_textured = [200] of { int };
chan fragment_shaded = [200] of { int };
chan pixel_ready = [200] of { int };

chan sem_fetch_ready = [0] of { bit };
chan sem_assembler_ready = [0] of { bit };
chan sem_raster_ready = [0] of { bit };
chan sem_tex_ready[TMUS] = [0] of { bit };
chan sem_pixel_ready[PIXEL_SHADERS] = [0] of { bit };
chan sem_rop_ready[ROPS] = [0] of { bit };

chan frame_start = [0] of { byte };
chan frame_end = [0] of { byte };

byte fin = false;

inline wait_clock() {
    do
    :: clock_updated == 1 -> break
    :: else -> skip
    od;
    clock_updated = 0;
}

inline advance_clock() {
    global_clock = global_clock + 1;
    clock_updated = 1;
}


inline reset_frame_counters() {
    current_vertex_id = 0;
    current_triangle_id = 0;
    current_fragment_id = 0;
    current_pixel_id = 0;
    triangles_assembled = 0;
    fragments_generated = 0;
    total_pixels_written = 0;

    pipe_raster_finised = 0;
    pipe_texture_finised = 0;
    pipe_pixel_finised = 0;
    pipe_rop_finised = 0;

    int r;
    for (r: 0 .. PIXEL_SHADERS-1) {
        pipe_pixel_fragment_processed[r] = 0;
    }
    for (r: 0 .. TMUS-1) {
        pipe_texture_processed[r] = 0;
    }
    for (r: 0 .. ROPS-1) {
        pipe_rop_processed[r] = 0;
    }
}


inline transform_vertices(angle) {
    int sin_a = sin_table[angle % 360];
    int cos_a = cos_table[angle % 360];
    for (i: 0 .. MAX_VERTICES-1) {
        int ox = vertex_orig_x[i];
        int oy = vertex_orig_y[i];
        int oz = vertex_orig_z[i];

        int rx = (ox * cos_a - oz * sin_a) / 1000;
        int rz = (ox * sin_a + oz * cos_a) / 2000;
        int ry = oy;

        int onx = vertex_nx[i];
        int ony = vertex_ny[i];
        int onz = vertex_nz[i];
        int rnx = (onx * cos_a - onz * sin_a) / 1000;
        int rnz = (onx * sin_a + onz * cos_a) / 1000;
        int rny = ony;

        int focal = 2000;
        int screen_x, screen_y;
        if :: rz + focal != 0 ->
            screen_x = (rx * focal) / (rz + focal);
            screen_y = (ry * focal) / (rz + focal);
        :: else ->
            screen_x = rx;
            screen_y = ry;
        fi;
        screen_x = MX2 - screen_x / 100;
        screen_y = MY2 - screen_y / 100;

        vertex_x[i] = screen_x;
        vertex_y[i] = screen_y;
        vertex_z[i] = rz;
        vertex_nx[i] = rnx;
        vertex_ny[i] = rny;
        vertex_nz[i] = rnz;
        vertex_ready[i] = 2;
    }
}

proctype ClockGenerator() {
    #ifdef DEBUG
    printf("ClockGenerator: started\n");
    #endif
    do
    :: !fin ->
        advance_clock();
        if
        :: global_clock % FRAME_TIME == 0 && global_clock > 0 ->
            #ifdef DEBUG
            printf("ClockGenerator: WARNING! Deadline missed at tick %d\n", global_clock);
            #endif
        :: else -> skip
        fi;

        if
        :: global_clock % CLOCK_STAT == 0 ->
            #ifdef DEBUG
            printf("ClockGenerator: Tick %d, frame %d, triangles: %d, pixels: %d\n",
                   global_clock, current_frame, triangles_assembled, total_pixels_written);
            #endif
        :: else -> skip
        fi
    :: else -> break
    od;
#ifdef DEBUG
    printf("ClockGenerator: done for %d clocks\n", global_clock);
#endif
}


proctype CPU() {
#ifdef DEBUG
    printf("CPU: started\n");
#endif
    init_vertices();
    init_triangles();
    init_trig_tables();
    init_texture();
    init_adjacency();

    int i;
    for (i: 0 .. MAX_VERTICES-1) {
        vertex_orig_x[i] = vertex_x[i];
        vertex_orig_y[i] = vertex_y[i];
        vertex_orig_z[i] = vertex_z[i];
    }

    int frame;
    angle = 99;
    for (frame : 1 .. TOTAL_FRAMES) {
#ifdef DEBUG
        printf("\nCPU: Preparing frame %d\n", frame);
#endif
        transform_vertices(angle);

        for (i: 0 .. MAX_TRIANGLES-1) {
            tri_ready_count[i] = 3;
        }

        current_frame = frame;
        frame_in_progress = 1;
#ifdef DEBUG
        printf("CPU: Start of frame %d\n", frame);
#endif
        int vertices_to_send = MAX_VERTICES;
        i = 0;
        do
        :: i < vertices_to_send ->
            sem_fetch_ready?1;
            vertex_to_fetch!i;
#ifdef DEBUG
            printf("CPU[frame %d]: Vertex %d sent\n", frame, i);
#endif
            i = i + 1
        :: else -> break
        od;
        all_data_sent = 1;

        byte completed_frame;
        frame_end?completed_frame;
        if
        :: completed_frame == frame ->
#ifdef DEBUG
            printf("CPU: Frame %d successfully completed\n", frame);
#endif
            total_frames_completed = total_frames_completed + 1
        :: else ->
#ifdef DEBUG
            printf("CPU: ERROR! Received frame completion signal %d instead of %d\n",
                   completed_frame, frame);
#endif
        fi;

        frame_in_progress = 0;
        int pause = 0;
        do
        :: pause < 10 ->
            wait_clock();
            pause = pause + 1
        :: else -> break
        od;

        reset_frame_counters();
        angle = angle + 2;
    }
    fin = 1;
    simulation_active = 0;
#ifdef DEBUG
    printf("CPU: All %d frames completed\n", TOTAL_FRAMES);
#endif
}


proctype VertexFetcher(byte id) {
    #ifdef DEBUG
    printf("VertexFetcher %d: started\n", id);
    #endif
    int vid;
    int total_fetched = 0;
    byte current_working_frame = 0;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame && frame_in_progress == 1 ->
            current_working_frame = current_frame;
            #ifdef DEBUG
            printf("VF%d: Starting work on frame %d\n", id, current_working_frame);
            #endif
            total_fetched = 0;
            sem_fetch_ready!1
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: vertex_to_fetch?[vid] ->
                vertex_to_fetch?vid;
                #ifdef DEBUG
                printf("VF%d[frame %d]: Fetching vertex %d\n", id, current_frame, vid);
                #endif
                int delay = 0;
                do
                :: delay < 2 ->
                    wait_clock();
                    delay = delay + 1
                :: else -> break
                od;
                sem_assembler_ready?1;
                vertex_processed!vid;
                total_fetched = total_fetched + 1;
                #ifdef DEBUG
                printf("VF%d: Vertex %d sent to assembler\n", id, vid);
                #endif
                sem_fetch_ready!1
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("VertexFetcher %d: done\n", id);
    #endif
}

proctype PrimitiveAssembler() {
    #ifdef DEBUG
    printf("PrimitiveAssembler: started\n");
    #endif
    int buffer_count = 0;
    int total_triangles = 0;
    byte current_working_frame = 0;
    int vid;

    sem_assembler_ready!1;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
            buffer_count = 0;
            #ifdef DEBUG
            printf("PA: Switching to frame %d\n", current_working_frame);
            #endif
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: vertex_processed?[vid] ->
                vertex_processed?vid;
                if
                :: vertex_ready[vid] == 2 ->   
                    int start = vertex_adj_start[vid];
                    int count = vertex_adj_count[vid];
                    buffer_count = buffer_count + 1;
                    #ifdef DEBUG
                    printf("PA[frame %d]: Vertex %d ready, checking associated triangles\n", current_frame, vid);
                    #endif
                    int t = 0;
                    int tid;
                    for (t : 0 .. count - 1) {
                        tid = adj_tri_ids[start + t];
                        tri_ready_count[tid]--;
                        #ifdef DEBUG
                        printf("PA[frame %d]: vid = %d , tid = %d, tri_ready_count = %d\n", current_frame, vid, tid, tri_ready_count[tid]);
                        #endif
                        if
                        :: tri_ready_count[tid] == 0 ->
                            sem_raster_ready?1;
                            triangle_ready[tid] = 1;
                            triangle_assembled!tid;
                            total_triangles = total_triangles + 1;
                            triangles_assembled = triangles_assembled + 1;
                            #ifdef DEBUG
                            printf("PA[frame %d]: Triangle %d created\n", current_frame, tid);
                            #endif
                        :: else -> skip;
                        fi
                    }
                :: else ->
                    #ifdef DEBUG
                    printf("PA: ERROR! Vertex %d not processed\n", vid);
                    #endif
                fi;
                sem_assembler_ready!1
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("PrimitiveAssembler: done\n");
    #endif
}

proctype Rasterizer() {
    #ifdef DEBUG
    printf("Rasterizer: started\n");
    #endif
    int tid;
    int total_triangles = 0;
    byte current_working_frame = 0;

    sem_raster_ready!1;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
            #ifdef DEBUG
            printf("Rast: Switching to frame %d\n", current_working_frame);
            #endif
            current_fragment_id = 0;
            total_triangles = 0;
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: triangle_assembled?[tid] ->
                triangle_assembled?tid;
                if
                :: triangle_ready[tid] == 1 ->
                    #ifdef DEBUG
                    printf("Rast[frame %d]: Rasterizing triangle %d of %d\n", current_frame, tid, total_triangles+1);
                    #endif
                    int cycles = 0;
                    do
                    :: cycles < 5 ->
                        wait_clock();
                        cycles = cycles + 1
                    :: else -> break
                    od;

                    total_triangles = total_triangles + 1;
                    if ::(total_triangles == MAX_TRIANGLES) -> 
                        pipe_raster_finised = 1;
                        ::else -> skip 
                    fi;

                    int from = current_fragment_id;
                    int v0 = triangle_v0[tid];
                    int v1 = triangle_v1[tid];
                    int v2 = triangle_v2[tid];
                    int x0, y0, z0, x1, y1, z1, x2, y2, z2;
                    x1 = vertex_x[v0] - vertex_x[v2];
                    y1 = vertex_y[v0] - vertex_y[v2];
                    z1 = vertex_z[v0] - vertex_z[v2];
                    x2 = vertex_x[v1] - vertex_x[v2];
                    y2 = vertex_y[v1] - vertex_y[v2];
                    z2 = vertex_z[v1] - vertex_z[v2];
                    int nx = (y1 * z2) - (z1 * y2);
                    int ny = -((x1 * z2) - (z1 * x2));
                    int nz = (x1 * y2) - (y1 * x2);
                    x0 = vertex_x[v0]; y0 = vertex_y[v0]; z0 = vertex_z[v0];
                    x1 = vertex_x[v1]; y1 = vertex_y[v1]; z1 = vertex_z[v1];
                    x2 = vertex_x[v2]; y2 = vertex_y[v2]; z2 = vertex_z[v2];
                    int u0 = vertex_u[v0], v0_tex = vertex_v[v0];
                    int u1 = vertex_u[v1], v1_tex = vertex_v[v1];
                    int u2 = vertex_u[v2], v2_tex = vertex_v[v2];

                    int nx0 = vertex_nx[v0], ny0 = vertex_ny[v0], nz0 = vertex_nz[v0];
                    int nx1 = vertex_nx[v1], ny1 = vertex_ny[v1], nz1 = vertex_nz[v1];
                    int nx2 = vertex_nx[v2], ny2 = vertex_ny[v2], nz2 = vertex_nz[v2];
                    int min_x = x0, max_x = x0;
                    int min_y = y0, max_y = y0;
                    if :: x1 < min_x -> min_x = x1; :: else -> skip fi;
                    if :: x1 > max_x -> max_x = x1; :: else -> skip fi;
                    if :: x2 < min_x -> min_x = x2; :: else -> skip fi;
                    if :: x2 > max_x -> max_x = x2; :: else -> skip fi;
                    if :: y1 < min_y -> min_y = y1; :: else -> skip fi;
                    if :: y1 > max_y -> max_y = y1; :: else -> skip fi;
                    if :: y2 < min_y -> min_y = y2; :: else -> skip fi;
                    if :: y2 > max_y -> max_y = y2; :: else -> skip fi;
                    if :: min_x < 0 -> min_x = 0; :: else -> skip fi;
                    if :: max_x >= MX -> max_x = MX-1; :: else -> skip fi;
                    if :: min_y < 0 -> min_y = 0; :: else -> skip fi;
                    if :: max_y >= MY -> max_y = MY-1; :: else -> skip fi;
                    int y = min_y;
                    do
                    :: y <= max_y ->
                        int x = min_x;
                        do
                        :: x <= max_x ->
                            int w0 = (x1 - x2)*(y - y2) - (y1 - y2)*(x - x2);
                            int w1 = (x2 - x0)*(y - y0) - (y2 - y0)*(x - x0);
                            int w2 = (x0 - x1)*(y - y1) - (y0 - y1)*(x - x1);
                            if
                            :: (w0 >= 0 && w1 >= 0 && w2 >= 0) || (w0 <= 0 && w1 <= 0 && w2 <= 0) ->
                                int area = (x1 - x0)*(y2 - y0) - (x2 - x0)*(y1 - y0);
                                if :: area != 0 ->
                                    int alpha = w0 * 1000 / area;
                                    int beta = w1 * 1000 / area;
                                    int gamma = 1000 - alpha - beta;
                                    int frag_z = (z0 * alpha + z1 * beta + z2 * gamma) / 1000;
                                    int frag_u = (u0 * alpha + u1 * beta + u2 * gamma) / 1000;
                                    int frag_v = (v0_tex * alpha + v1_tex * beta + v2_tex * gamma) / 1000;
                                    int frag_nx = (nx0 * alpha + nx1 * beta + nx2 * gamma) / 1000;
                                    int frag_ny = (ny0 * alpha + ny1 * beta + ny2 * gamma) / 1000;
                                    int frag_nz = (nz0 * alpha + nz1 * beta + nz2 * gamma) / 1000;
                                    byte base_color = 100;
                                    int fid = current_fragment_id;
                                    fragment_x[fid] = x;
                                    fragment_y[fid] = y;
                                    fragment_z[fid] = frag_z;
                                    fragment_u[fid] = frag_u % 256;
                                    fragment_v[fid] = frag_v % 256;
                                    fragment_nx[fid] = frag_nx;
                                    fragment_ny[fid] = frag_ny;
                                    fragment_nz[fid] = frag_nz;
                                    fragment_base_color[fid] = base_color;
                                    fragment_tri_id[fid] = tid;
                                    #ifdef DRAW_RASTER
                                    frame_buffer[y * MX + x] = base_color * 100 - 50;
                                    #endif
                                    fragments_generated = fragments_generated + 1;
                                    current_fragment_id = current_fragment_id + 1;
                                    int tmu_id = fid % TMUS;
                                    do
                                        ::full(fragment_rasterized) -> wait_clock()
                                        ::true -> break
                                    od;
                                    sem_tex_ready[tmu_id]?1; 
                                    fragment_rasterized!fid; 
                                :: else -> skip
                                fi
                            :: else -> skip
                            fi;
                            x = x + 1
                        :: else -> break
                        od;
                        y = y + 1
                    :: else -> break
                    od;

                    #ifdef DEBUG
                    printf("Rast: Created fragments %d..%d for triangle %d\n", from, current_fragment_id, tid);
                    #endif

                    #ifdef DEBUG
                    if 
                    ::(pipe_raster_finised) ->
                        printf("Rast: Rastering pipeline part is finished with %d fragments (from %d triangles) ! \n", fragments_generated, total_triangles);
                    ::else -> skip
                    fi
                    #endif
                :: else ->
                    #ifdef DEBUG
                    printf("Rast: ERROR! Triangle %d not ready\n", tid);
                    #endif
                fi;
                sem_raster_ready!1
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("Rasterizer: done\n", total_triangles);
    #endif
}

proctype TextureUnit(byte id) {
    #ifdef DEBUG
    printf("TextureUnit %d: started\n", id);
    #endif
    int total_textured = 0;
    byte current_working_frame = 0;

    sem_tex_ready[id]!1;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
            #ifdef DEBUG
            printf("TMU%d: Switching to frame %d\n", id, current_working_frame);
            #endif
            total_textured = 0;
            pipe_texture_processed[id] = 0;
        :: else -> skip
        fi;

        int fid;
        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: fragment_rasterized?[fid] ->
                fragment_rasterized?fid;
                #ifdef DEBUG
                printf("TMU%d[frame %d]: Texturing fragment %d\n", id, current_frame, fid);
                #endif
                int cycles = 0;
                do
                :: cycles < 2 ->
                    wait_clock();
                    cycles = cycles + 1
                :: else -> break
                od;

                int u = fragment_u[fid];
                int v = fragment_v[fid];
                int tex_x = (u * TEX_SIZE) / 256;
                int tex_y = (v * TEX_SIZE) / 256;
                if :: tex_x < 0 -> tex_x = 0; :: else -> skip fi;
                if :: tex_x >= TEX_SIZE -> tex_x = TEX_SIZE - 1; :: else -> skip fi;
                if :: tex_y < 0 -> tex_y = 0; :: else -> skip fi;
                if :: tex_y >= TEX_SIZE -> tex_y = TEX_SIZE - 1; :: else -> skip fi;
                byte texel = texture[tex_y * TEX_SIZE + tex_x];
                fragment_tex_color[fid] = texel;

                total_textured = total_textured + 1;
                pipe_texture_processed[id] = total_textured;

                int t;
                int frag_textured = 0;
                for (t : 0 .. TMUS-1) {
                    frag_textured = frag_textured + pipe_texture_processed[t];
                }
                if ::(pipe_raster_finised && frag_textured == fragments_generated) -> 
                    pipe_texture_finised = 1; 
                    #ifdef DEBUG
                        printf("TMU0..%d[frame %d]: pipeline part is finished with %d textured fragments !\n", TMUS-1, current_frame, frag_textured);
                    #endif
                   ::else ->
                        // skip 
                        printf("TMU0..%d[frame %d]:  %d/%d...\n", TMUS-1, current_frame, frag_textured, fragments_generated);
                fi;

                int pp_id = fid % PIXEL_SHADERS;
                sem_pixel_ready[pp_id]?1;
                fragment_textured!fid;

                sem_tex_ready[id]!1
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("TextureUnit %d: done\n", id);
    #endif
}

proctype PixelProcessor(byte id) {
    #ifdef DEBUG
    printf("PixelProcessor %d: started\n", id);
    #endif
    int fid;
    int total_shaded = 0;
    byte current_working_frame = 0;

    int light_x = 1000;
    int light_y = 1000;
    int light_z = 1000;

    sem_pixel_ready[id]!1;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
            #ifdef DEBUG
            printf("PP%d: Switching to frame %d\n", id, current_working_frame);
            #endif
            pipe_pixel_fragment_processed[id] = 0;
            pipe_pixel_finised = 0;
            total_shaded = 0;
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: fragment_textured?[fid] ->
                fragment_textured?fid;
                #ifdef DEBUG
                printf("PP%d[frame %d]: Shading fragment %d\n", id, current_frame, fid);
                #endif
                int cycles = 0;
                do
                :: cycles < 3 ->
                    wait_clock();
                    cycles = cycles + 1
                :: else -> break
                od;

                byte texel = fragment_tex_color[fid];
                int nx = fragment_nx[fid];
                int ny = fragment_ny[fid];
                int nz = fragment_nz[fid];
                int base_color_idx = fragment_base_color[fid];
                int norm_len = 1000;
                int dot = (nx * light_x + ny * light_y + nz * light_z) / norm_len;
                if :: dot < 0 -> dot = 0; :: else -> skip fi;
                if :: dot > 1000 -> dot = 1000; :: else -> skip fi;
                int lit_texel = (texel * dot) / 1000;
                byte final_color;
                if
                :: base_color_idx == 1 ->
                    final_color = (lit_texel * 2) / 3;
                :: base_color_idx == 2 ->
                    final_color = (lit_texel * 3) / 4;
                :: base_color_idx == 3 ->
                    final_color = lit_texel;
                :: base_color_idx == 4 ->
                    final_color = lit_texel / 2;
                :: base_color_idx == 5 ->
                    final_color = lit_texel * 3;
                    if :: final_color > 255 -> final_color = 255; :: else -> skip fi;
                :: else ->
                    final_color = lit_texel
                fi;
                fragment_color_r[fid] = final_color;
                fragment_color_g[fid] = final_color;
                fragment_color_b[fid] = final_color;

                total_shaded = total_shaded + 1;

                pipe_pixel_fragment_processed[id] = total_shaded;
                int p;
                int f_count = 0;
                for (p: 0 .. PIXEL_SHADERS-1) {
                    f_count = f_count + pipe_pixel_fragment_processed[p];
                }
                if ::(pipe_texture_finised && f_count == fragments_generated) -> 
                    pipe_pixel_finised = 1;
                   ::else -> skip
                fi;   

                int rop_id = fid % ROPS;
                sem_rop_ready[rop_id]?1;
                fragment_shaded!fid;
                sem_pixel_ready[id]!1

            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("PixelProcessor %d: done\n", id);
    #endif
}

proctype SystemMemory() {
    int depth_buffer[(MX + 1) * (MY + 1)]; //its data  
    int i;
    for (i: 0 .. (MX * MY) - 1) {
        depth_buffer[i] = 32767;
    }

    #ifdef DEBUG
    printf("SystemMemory: initialized\n");
    #endif

    ZReq req;
    int idx;
    do
    :: true ->
        z_req?req;
        idx = req.y * MX + req.x;
        if
        :: req.op == 0 -> //read             
            int cycles = 0;
            do
            :: cycles < MEM_READ_DELAY ->
                wait_clock();
                cycles = cycles + 1
            :: else -> break
            od;
            z_resp!depth_buffer[idx];
#ifdef DEBUG
            printf("SystemMemory: read depth[%d,%d] = %d\n", req.x, req.y, depth_buffer[idx]);
#endif
        :: req.op == 1 ->  //write
            int mycycles = 0;
            do
            :: mycycles < MEM_WRITE_DELAY ->
                wait_clock();
                mycycles = mycycles + 1
            :: else -> break
            od;
            depth_buffer[idx] = req.new_z;
            z_resp!0; //ask                   
#ifdef DEBUG
            printf("SystemMemory: write depth[%d,%d] = %d\n", req.x, req.y, req.new_z);
#endif
        fi
    od;
}

proctype ROP(byte id) {
#ifdef DEBUG
    printf("ROP %d: started\n", id);
#endif
    int fid;
    int total_processed = 0;
    int pixels_written = 0;
    byte current_working_frame = 0;

    sem_rop_ready[id]!1;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
#ifdef DEBUG
            printf("ROP%d: Switching to frame %d\n", id, current_working_frame);
#endif
            total_processed = 0;
            pixels_written = 0;
            pipe_rop_processed[id] = 0;
            pipe_rop_finised = 0;
            // fix to clear z-buffer (use command)
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: fragment_shaded?[fid] ->
                fragment_shaded?fid;
#ifdef DEBUG
                printf("ROP%d[frame %d]: Processing fragment %d\n", id, current_frame, fid);
#endif
                total_processed = total_processed + 1;
                pipe_rop_processed[id] = total_processed;

                int x = fragment_x[fid];
                int y = fragment_y[fid];
                int z = fragment_z[fid];
                byte r = fragment_color_r[fid];
                byte g = fragment_color_g[fid];
                byte b = fragment_color_b[fid];

                if :: x >= 0 && x < MX && y >= 0 && y < MY ->
                    int buffer_idx = y * MX + x;

                    //!!!
                    ZReq read_req;
                    read_req.x = x;
                    read_req.y = y;
                    read_req.op = 0;
                    z_req!read_req;
                    int old_z;
                    z_resp?old_z;

                    if :: z < old_z ->
                        ZReq write_req;
                        write_req.x = x;
                        write_req.y = y;
                        write_req.new_z = z;
                        write_req.op = 1;
                        z_req!write_req;
                        int dummy;
                        z_resp?dummy; 

                        int base_color = fragment_base_color[fid];
                        #ifdef DRAW_TEXTURES
                            int bg_color = frame_buffer[buffer_idx];
                            frame_buffer[buffer_idx] = (r + bg_color) / 2;
                        #else
                            frame_buffer[buffer_idx] = r;
                        #endif
                        pixels_written = pixels_written + 1;
                        atomic {total_pixels_written++};
#ifdef DEBUG
                        printf("ROP%d: z-test passed for (%d,%d)\n", id, x, y);
#endif
                    :: else ->
#ifdef DEBUG
                        printf("ROP%d: z-test failed for (%d,%d) (z=%d, old=%d)\n", id, x, y, z, old_z);
#endif
                        skip;
                    fi;
                fi;

                int p;
                int rop_fid = 0;
                for (p : 0 .. ROPS-1) {
                    rop_fid = rop_fid + pipe_rop_processed[p];
                }
                if ::(pipe_pixel_finised && rop_fid == fragments_generated) -> 
                    pipe_rop_finised = 1;
#ifdef DEBUG
                    printf("ROP%d: pipeline part finishing\n", id);
#endif
                ::else -> skip;
                fi;

                pixel_ready!total_pixels_written;
                sem_rop_ready[id]!1
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
#ifdef DEBUG
    printf("ROP %d: done\n", id);
#endif
}

proctype FrameBuffer() {
    #ifdef DEBUG
    printf("FrameBuffer %dx%d: started\n", MX, MY);
    #endif
    int p_id;
    int pixels_this_frame = 0;
    byte current_working_frame = 0;
    int total_pixels = 0;

    do
    :: simulation_active == 1 ->
        if
        :: current_working_frame < current_frame ->
            current_working_frame = current_frame;
            pixels_this_frame = 0;
            #ifdef DEBUG
            printf("FB: Starting frame %d write\n", current_working_frame);
            #endif
        :: else -> skip
        fi;

        if
        :: frame_in_progress == 1 && current_working_frame == current_frame ->
            wait_clock();
            if
            :: pixel_ready?[p_id] ->
                pixel_ready?p_id;
                pixels_this_frame = pixels_this_frame + 1;
                total_pixels = total_pixels + 1;
                #ifdef DEBUG
                printf("FB[frame %d]: Received pixel %d (for now we have %d)\n",
                       current_frame, p_id, total_pixels_written);
                #endif
                if
                :: pipe_rop_finised ->
                    #ifdef DEBUG
                    printf("FB: Frame %d completed, pixels: %d\n",
                           current_frame, pixels_this_frame);
                    #endif
                    display_frame_buffer(current_frame, pixels_this_frame);
                    clear_frame_buffer();

                    frame_end!current_frame;
                    frame_in_progress = 0
                :: else -> skip
                fi
            :: else -> skip
            fi
        :: else -> skip
        fi
    :: else -> break
    od;
    #ifdef DEBUG
    printf("FrameBuffer: done\n");
    #endif
}


init {
#ifdef DEBUG
    printf("\n=== INITIALIZATION OF S3 ViRGE PIPELINE ===\n");
    printf("Configuration: %d VS (disabled), %d PS, %d TMU, %d ROP\n",
           VERTEX_SHADERS, PIXEL_SHADERS, TMUS, ROPS);
    printf("Z-buffer is in system memory with %d read delay, %d write delay\n",
           MEM_READ_DELAY, MEM_WRITE_DELAY);
    printf("Frames: %d, time per frame: %d ticks\n", TOTAL_FRAMES, FRAME_TIME);
#endif

    run ClockGenerator();
    run CPU();

    byte p;
    for (p : 0 .. 1) {
        run VertexFetcher(p);
    }
    run PrimitiveAssembler();
    run Rasterizer();
    for (p : 0 .. TMUS-1) {
        run TextureUnit(p);
    }
    for (p : 0 .. PIXEL_SHADERS-1) {
        run PixelProcessor(p);
    }
    for (p : 0 .. ROPS-1) {
        run ROP(p);
    }
    run SystemMemory(); 
    run FrameBuffer();

#ifdef DEBUG
    printf("\n=== SIMULATION STARTED ===\n");
#endif
}
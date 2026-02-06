// (c) Sergey Staroletov
#include "gpu_verticles.pml"
#include "gpu_triangles.pml"
#include "gpu_trigo.pml"

#define DRAW_VERTICES
#define DRAW_RASTER
//#define DRAW_FRAGMENTS
#define DRAW_TEXTURES

#define TOTAL_FRAMES 200

#define MX 200
#define MY 60
#define MX2 MX/2
#define MY2 MY/2

#define MAX_FRAGMENTS MX*MY
#define MAX_PIXELS MX*MY

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

int depth_buffer[(MX + 1) * (MY + 1)];
int frame_buffer[(MX + 1) * (MY + 1)];

int current_vertex_id = 0;
int current_triangle_id = 0;
int current_fragment_id = 0;
int current_pixel_id = 0;

int vertices_processed = 0;
int triangles_assembled = 0;
int fragments_generated = 0;
int pixels_written = 0;

byte current_frame = 0;
byte total_frames_completed = 0;
byte simulation_active = 1;
byte frame_in_progress = 0;

byte shades[8] = {' ', '.', ':', 'o', 'O', '8', '@', '#'};

inline display_frame_buffer(frame, pixels) {
    printf("\n--- Frame %d (pixels: %d) ---\n", frame, pixels);
    int yy = 0;
    do
    ::yy < MY -> {
        printf("|");
        int xx = 0;
        do
        ::xx < MX-> {
            byte pixel_val = frame_buffer[yy * MX + xx] % 256;
            byte char_index;
            if
            :: pixel_val == ' ' -> char_index = 0
            :: pixel_val >= 0 && pixel_val < 255 ->
                char_index = (pixel_val * 7) / 255;
                printf("%c", shades[char_index])
            :: else ->
                printf("%c", pixel_val)
            fi
            xx++;
        }
        ::else->break;
        od
        yy++;
        printf("\n");
    }
    ::else->break;
    od
}


int vertex_orig_x[MAX_VERTICES];
int vertex_orig_y[MAX_VERTICES];
int vertex_orig_z[MAX_VERTICES];

int norm_x[MAX_TRIANGLES];
int norm_y[MAX_TRIANGLES];
int norm_z[MAX_TRIANGLES];

byte tri_color[MAX_TRIANGLES];

#define TEX_SIZE 16
byte texture[TEX_SIZE*TEX_SIZE];

inline init_texture() {
    int x, y;
    for (y : 0 .. TEX_SIZE-1) {
        for (x : 0 .. TEX_SIZE-1) {
            if ::((x/4 + y/4) % 2 == 0) -> {
                texture[y * TEX_SIZE + x] = 200;
            } ::else -> {
                texture[y * TEX_SIZE + x] = 100;
            }
            fi
        }
    }
    for (x : 0 .. MAX_VERTICES-1) {
        vertex_u[x] = 15;
        vertex_v[x] = 0;
    }
}

active proctype main_draw() {
    init_vertices();
    init_triangles();
    init_trig_tables();
    init_texture();

    int i;
    for (i: 0 .. MAX_VERTICES-1) {
        vertex_orig_x[i] =  vertex_x[i];
        vertex_orig_y[i] =  vertex_y[i];
        vertex_orig_z[i] =  vertex_z[i];
    }

    int angle = 0;
    int frame = 0;
    for (frame: 0 .. TOTAL_FRAMES) {
        int f;
        for (f : 0 .. (MX-1) * (MY - 1)) {
            frame_buffer[f] = 0;
        }
        for (i:  0 .. MX * MY) {
            depth_buffer[i] = 32767;
        }
        int vid;
        for (vid: 0 .. MAX_VERTICES-1) {
            int orig_x = vertex_orig_x[vid];
            int orig_y = vertex_orig_y[vid];
            int orig_z = vertex_orig_z[vid];
            int rotated_x, rotated_y, rotated_z;
            int sin_a = sin_table[angle % 360];
            int cos_a = cos_table[angle % 360];
            rotated_x = (orig_x * cos_a - orig_z * sin_a) / 1000;
            rotated_z = (orig_x * sin_a + orig_z * cos_a) / 2000;
            rotated_y = orig_y;
            int screen_x, screen_y;
            int focal = 2000;
            if ::rotated_z + focal != 0 ->
                screen_x = (rotated_x * focal) / (rotated_z + focal);
                screen_y = (rotated_y * focal) / (rotated_z + focal);
            :: else ->
                screen_x = rotated_x;
                screen_y = rotated_y;
            fi;
            screen_x = MX2 - screen_x / 100;
            screen_y = MY2- screen_y / 100;
            vertex_x[vid] = screen_x;
            vertex_y[vid] = screen_y;
            vertex_z[vid] = rotated_z;
            vertex_ready[vid] = 2;
            int coord = screen_y * MX + screen_x;
            if
            :: coord >= 0 && coord <= (MX - 1) * (MY - 1)
                #ifdef DRAW_VERTICES
                frame_buffer[coord] = 200;
                #endif
            :: else -> skip;
            fi
        }

        fragments_generated = 0;
        current_fragment_id = 0;
        int tid;
        for (tid: 0 .. MAX_TRIANGLES-1) {
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
            int nx =  (y1 * z2) - (z1 * y2);
            int ny =  -((x1 * z2) - (z1 * x2));
            int nz =  (x1 * y2) - (y1 * x2);
            x0 = vertex_x[v0]; y0 = vertex_y[v0]; z0 = vertex_z[v0];
            x1 = vertex_x[v1]; y1 = vertex_y[v1]; z1 = vertex_z[v1];
            x2 = vertex_x[v2]; y2 = vertex_y[v2]; z2 = vertex_z[v2];
            int u0 = vertex_u[v0], v0_tex = vertex_v[v0];
            int u1 = vertex_u[v1], v1_tex = vertex_v[v1];
            int u2 = vertex_u[v2], v2_tex = vertex_v[v2];
            int nx0 = nx, ny0 = ny, nz0 = nz;
            int nx1 = nx, ny1 = ny, nz1 = nz;
            int nx2 = nx, ny2 = ny, nz2 = nz;
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
                            if
                            :: fid < MAX_FRAGMENTS ->
                                fragment_x[fid] = x;
                                fragment_y[fid] = y;
                                fragment_z[fid] = frag_z;
                                fragment_u[fid] = frag_u % 256;
                                fragment_v[fid] = frag_v % 256;
                                fragment_nx[fid] = frag_nx;
                                fragment_ny[fid] = frag_ny;
                                fragment_nz[fid] = frag_nz;
                                fragment_base_color[fid] = base_color ;
                                fragment_tri_id[fid] = tid;
                                #ifdef DRAW_RASTER
                                frame_buffer[y * MX + x] = base_color * 100 - 50; //100
                                #endif
                                fragments_generated = fragments_generated + 1;
                                current_fragment_id = current_fragment_id + 1;
                            :: else ->
                                //printf("Rast: tid=%d MAX_FRAGMENTS %d\n", tid, current_fragment_id);
                                skip
                            fi
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
        }

        int fid;
        for (fid: 0 .. fragments_generated-1) {
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
        }

        int light_x = 1000;
        int light_y = 1000;
        int light_z = 1000;

        for (fid: 0 .. fragments_generated-1) {
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
        }

        for (fid: 0 .. fragments_generated-1) {
            int x = fragment_x[fid];
            int y = fragment_y[fid];
            int z = fragment_z[fid];
            byte r = fragment_color_r[fid];
            byte g = fragment_color_g[fid];
            byte b = fragment_color_b[fid];
            if :: x >= 0 && x < MX && y >= 0 && y < MY ->
                int buffer_idx = y * MX + x;
                if :: z < depth_buffer[buffer_idx] ->
                    depth_buffer[buffer_idx] = z;
                    int base_color = fragment_base_color[fid];
                    #ifdef DRAW_TEXTURES
                    if
                    ::true->
                        int bg_color = frame_buffer[y * MX + x];
                        frame_buffer[y * MX + x] = (r + bg_color) / 2;
                    :: else ->
                        frame_buffer[y * MX + x] = r
                    fi;
                    #endif
                    pixels_written = pixels_written + 1
                :: else ->
                    skip
                fi
            :: else -> skip
            fi;
        }

        current_frame++;
        int pixels_this_frame = pixels_written;
        display_frame_buffer(current_frame, pixels_this_frame);
        angle = angle + 2;
    }
}

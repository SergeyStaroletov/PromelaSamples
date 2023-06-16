kernel void findMinValue(global int * glob, global int * mins, local int * loc, int TS, int IC) {
#define MIN(a, b) if (a > b) a = b;

    int mu = get_global_id(0) / get_local_size(0);
    int NP = get_global_size(0) / get_local_size(0);
    int me = get_local_id(0);

    loc[me] = INFINITY;

    for (int iter = 0; iter < IC; iter++) {
        for (int i = 0; i < TS; i++) {
            MIN(loc[me], glob[iter + i*IC + mu*IC*TS + me*IC*TS*NP])
        }
    }
    barrier (CLK_LOCAL_MEM_FENCE);
    if (me == 0) {
        mins[mu] = loc[0];
        for (int i = 1; i < get_local_size(0); i++){
            MIN(mins[mu], loc[i])
        }
    }
}

kernel void findMinValue2(global int *glob, global int *mins, local int *loc, int TS) {
#define MIN(a, b) if (a > b) a = b;
    int my_unit = get_global_id(0) / get_local_size(0);
    int my_elem = get_local_id(0);
    loc[my_elem] = INFINITY;
    // MAP
    for (int i = 0; i < TS; i++) {
        MIN(loc[my_elem], glob[i + get_global_id(0) * TS])
    }
    barrier (CLK_LOCAL_MEM_FENCE);
    // REDUCE local
    if (my_elem == 0) {
        mins[my_unit] = loc[0];
        for (int i = 1; i < get_local_size(0); i++) {
            MIN(mins[my_unit], loc[i])
  }
    }
}

#define MAXCPU 2
#define MAXTHREADS 3
#define MAXMEM 100

#define WZR 0
#define IP cpu[currentCPU].context.ip
#define SP cpu[currentCPU].context.sp
#define X29 cpu[currentCPU].context.x29
#define X30 cpu[currentCPU].context.x30
#define W0 cpu[currentCPU].context.w0
#define W1 cpu[currentCPU].context.w1
#define W8 cpu[currentCPU].context.w8
#define W9 cpu[currentCPU].context.w9
#define W10 cpu[currentCPU].context.w10

#define FLAGZ cpu[currentCPU].context.flag_z
#define FLAGN cpu[currentCPU].context.flag_n

#define FINISH cpu[currentCPU].finished

#define T cpu[currentCPU].currentThread
#define THREAD thread[T]
#define IDLE_THREAD MAXTHREADS * MAXCPU

typedef CONTEXT {
    int ip;
    int sp;
    int x29, x30;
    int w0, w1, w8, w9, w10;

    bit flag_z;
    bit flag_n;

    bit finished;
};

typedef CPU {
    int currentThread;
    CONTEXT context;
    bit finished;
};

CONTEXT thread[MAXTHREADS * MAXCPU + 1];

int idle_ticks[MAXCPU];
int total_ticks[MAXCPU];

CPU cpu[MAXCPU];
int memory[MAXMEM / 4 * 3];
int ready = 0;

//Разные типы аргументов a, b: 
//rm = register, memory
//rr = register, register
//mr = memory, register
//cm = const, memory (то же самое как register, memory тк берется просто значение)

inline sub_rrc(a, b, c) { 
    atomic { a = b - c; }
}

inline subs_rrr(a, b, d) { 
    atomic { 
        a = b - d; 
        FLAGZ = a == 0;
        FLAGN = a < 0;
    }
}

inline add_rrc(a, b, c) { 
    atomic { a = b + c; }
}

inline mul_rrr(a, b, d) { 
    atomic { a = b * d; }
}

inline sdiv_rrr(a, b, d) { 
    atomic { a = b / d; }
}

inline stur_rm(a, b) { 
    atomic { memory[(b) / 4] = a; }
}

inline str_rm(a, b) { 
    atomic { memory[(b) / 4] = a; }
}

inline ldur_rm(a, b) { 
    atomic { a = memory[(b) / 4]; }
}

inline ldr_rm(a, b) { 
    atomic { a = memory[(b) / 4]; }
}

inline mov_rc(a, b) { 
    atomic { a = b; }
}

inline nop() {
    skip;
}

inline NEXT_INSTRUCTION() {
    atomic {
        IP++;
        //printf("CPU %d THREAD %d go to instruction %d...\n", currentCPU, T, IP);
    }
}

proctype cpuProc(int currentCPU) {
    //IP = 1;

    do
        :: atomic {
            if 
                //::(IP == 1) -> { sub_rrc(SP, SP, 48); NEXT_INSTRUCTION(); }
                //::(IP == 2) -> { stp_rrm(X29, X30, SP + 32); NEXT_INSTRUCTION(); }
                ::(IP == 1) -> { add_rrc(X29, SP, 32); IP = 4; }
                ::(IP == 4) -> { stur_rm(W0, X29 - 4); NEXT_INSTRUCTION(); }
                ::(IP == 5) -> { stur_rm(W1, X29 - 8); NEXT_INSTRUCTION(); }
                ::(IP == 6) -> { ldur_rm(W8, X29 - 4); NEXT_INSTRUCTION(); }
                ::(IP == 7) -> { stur_rm(W8, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 8) -> { IP = 9; } //b LBB1_1
                //LBB1_1
                ::(IP == 9) -> { ldur_rm(W8, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 10) -> { ldur_rm(W9, X29 - 8); NEXT_INSTRUCTION(); }
                ::(IP == 11) -> { subs_rrr(W8, W8, W9); NEXT_INSTRUCTION(); }
                ::(IP == 12) -> { atomic {if ::(FLAGZ == 0 && FLAGN == 0) -> IP = 52; :: else -> NEXT_INSTRUCTION(); fi } }//b.gt LBB1_12
                ::(IP == 13) -> { IP = 14; } //b LBB1_2
                //LBB1_2
                ::(IP == 14) -> { ldur_rm(W9, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 15) -> { mov_rc(W8, 2); NEXT_INSTRUCTION(); }
                ::(IP == 16) -> { sdiv_rrr(W9, W9, W8); NEXT_INSTRUCTION(); }
                ::(IP == 17) -> { str_rm(W9, SP + 16); NEXT_INSTRUCTION(); }
                ::(IP == 18) -> { mov_rc(W9, 1); NEXT_INSTRUCTION(); }
                ::(IP == 19) -> { str_rm(W9, SP + 12); NEXT_INSTRUCTION(); }
                ::(IP == 20) -> { str_rm(W8, SP + 8); NEXT_INSTRUCTION(); }
                ::(IP == 21) -> { IP = 22; } //b LBB1_3
                //LBB1_3
                ::(IP == 22) -> { ldr_rm(W8, SP + 8); NEXT_INSTRUCTION(); }
                ::(IP == 23) -> { ldr_rm(W9, SP + 16); NEXT_INSTRUCTION(); }
                ::(IP == 24) -> { subs_rrr(W8, W8, W9); NEXT_INSTRUCTION(); }
                ::(IP == 25) -> { atomic {if ::(FLAGZ == 0 && FLAGN == 0) -> IP = 41; :: else -> NEXT_INSTRUCTION(); fi } } //b.gt LBB1_8
                ::(IP == 26) -> { IP = 27; } //b LBB1_4
                //LBB1_4
                ::(IP == 27) -> { ldur_rm(W8, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 28) -> { ldr_rm(W10, SP + 8); NEXT_INSTRUCTION(); }
                ::(IP == 29) -> { sdiv_rrr(W9, W8, W10); NEXT_INSTRUCTION(); }
                ::(IP == 30) -> { mul_rrr(W9, W9, W10); NEXT_INSTRUCTION(); }
                ::(IP == 31) -> { subs_rrr(W8, W8, W9); NEXT_INSTRUCTION(); }
                ::(IP == 32) -> { atomic {if ::(W8 != 0) -> IP = 36; :: else -> NEXT_INSTRUCTION(); fi } } //cbnz	w8, LBB1_6
                ::(IP == 33) -> { IP = 34; } //b LBB1_5
                //LBB1_5
                ::(IP == 34) -> { str_rm(WZR, SP + 12); NEXT_INSTRUCTION(); }
                ::(IP == 35) -> { IP = 41; } //b LBB1_8
                //LBB1_6
                ::(IP == 36) -> { IP = 37; } //b LBB1_7
                //LBB1_7
                ::(IP == 37) -> { ldr_rm(W8, SP + 8); NEXT_INSTRUCTION(); }
                ::(IP == 38) -> { add_rrc(W8, W8, 1); NEXT_INSTRUCTION(); }
                ::(IP == 39) -> { str_rm(W8, SP + 8); NEXT_INSTRUCTION(); }
                ::(IP == 40) -> { IP = 22; } //b LBB1_3
                //LBB1_8
                ::(IP == 41) -> { ldr_rm(W8, SP + 12); NEXT_INSTRUCTION(); }
                ::(IP == 42) -> { atomic {if ::(W8 == 0) -> IP = 47; :: else -> NEXT_INSTRUCTION(); fi } } //cbz	w8, LBB1_10
                ::(IP == 43) -> { IP = 44; } //b LBB1_9
                //LBB1_9
                ::(IP == 44) -> { ldur_rm(W0, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 45) -> { printf("CPU %d THREAD %d -------------------------------- Found prime: %d\n", currentCPU, T, W0); NEXT_INSTRUCTION(); } //bl process_prime
                ::(IP == 46) -> { IP = 47; } //b LBB1_10
                //LBB1_10
                ::(IP == 47) -> { IP = 48; } //b LBB1_11
                //LBB1_11
                ::(IP == 48) -> { ldur_rm(W8, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 49) -> { add_rrc(W8, W8, 1); NEXT_INSTRUCTION(); }
                ::(IP == 50) -> { stur_rm(W8, X29 - 12); NEXT_INSTRUCTION(); }
                ::(IP == 51) -> { IP = 9; } //b LBB1_1
                //LBB1_12
                ::(IP == 52) -> { if :: !THREAD.finished -> printf("Task %d for CPU %d done!\n", T, currentCPU); THREAD.finished = true; :: else -> ; fi }//break; }
                :: (FINISH) -> break;
                
                :: (IP == 1000) -> { nop(); };
                // ldp	x29, x30, [sp, #32]             ; 16-byte Folded Reload
                // add	sp, sp, #48
                // ret
                // .cfi_endproc ; -- End function
            fi;
        }
    od;
}

inline save_context() {
    atomic {
        THREAD.ip = IP;
        THREAD.sp = SP;
        THREAD.x29 = X29;
        THREAD.x30 = X30;
        THREAD.w0 = W0;
        THREAD.w1 = W1;
        THREAD.w8 = W8;
        THREAD.w9 = W9;
        THREAD.w10 = W10;
        THREAD.flag_z = FLAGZ;
        THREAD.flag_n = FLAGN;
    }
}

inline load_context(currentCPU) {
    atomic {
        IP = THREAD.ip;
        SP = THREAD.sp;
        X29 = THREAD.x29
        X30 = THREAD.x30;
        W0 = THREAD.w0;
        W1 = THREAD.w1;
        W8 = THREAD.w8;
        W9 = THREAD.w9;
        W10 = THREAD.w10;
        FLAGZ = THREAD.flag_z;
        FLAGN = THREAD.flag_n;
    }
}

proctype scheduler(int currentCPU, startThread) {
    do
        :: {
                int currentThread = T;

                if 
                    :: !thread[startThread].finished -> currentThread = startThread;
                    :: !thread[startThread + 1].finished -> currentThread = startThread + 1;
                    :: !thread[startThread + 2].finished -> currentThread = startThread + 2;
                    :: else -> { 
                        atomic {
                            if :: currentThread != IDLE_THREAD -> printf("\n\n!!! CPU %d DONE !!!\n\n", currentCPU); ready++; 
                            :: else -> ;
                            fi; 
                        }
                        idle_ticks[currentCPU]++;
                        currentThread = IDLE_THREAD;
                    } 
                fi; 

                total_ticks[currentCPU]++;

                atomic {
                    //if :: (currentThread != T) -> printf(" Scheduler: CPU %d SWITCHED to thread: %d!", currentCPU, T - startThread); 
                      // :: else -> 
                        //printf(" Scheduler: CPU %d thread: %d!", currentCPU, T);
                     //; fi;
                    save_context();
                    T = currentThread;
                    load_context(currentCPU);
                }

                FINISH = ready == MAXCPU;

                if :: (ready == MAXCPU) -> FINISH = true; printf("CPU %d: %d%%\n", currentCPU, 100 - idle_ticks[currentCPU] * 100 / total_ticks[currentCPU]); break;
                :: else -> ;
                fi;
            };
    od
}

active proctype main() {

    thread[IDLE_THREAD].ip = 1000;

    //изначальное распределение состояния, когда на двух процессорах работают две параллельные задачи
    thread[0].sp = 0
    thread[1].sp = MAXMEM / 2;
    thread[2].sp = MAXMEM;

    //1 ищет числа от 10 до 50
    thread[0].w0 = 10;
    thread[0].w1 = 50;

    //2 ищет числа от 51 до 100
    thread[1].w0 = 51;
    thread[1].w1 = 100;

    //3 ищет числа от 1 до 50
    thread[2].w0 = 1;
    thread[2].w1 = 50;

    thread[3].sp = MAXMEM / 2 + MAXMEM;
    thread[4].sp = MAXMEM * 2;
    thread[5].sp = MAXMEM * 2 + MAXMEM / 2;


    //1 ищет числа от 101 до 200
    thread[3].w0 = 101;
    thread[3].w1 = 200;

    //2 ищет числа от 51 до 100
    thread[4].w0 = 51;
    thread[4].w1 = 100;

    //3 ищет числа от 1 до 50
    thread[5].w0 = 1;
    thread[5].w1 = 50;

    thread[0].ip = 1;
    thread[1].ip = 1;
    thread[2].ip = 1;

    thread[3].ip = 1;
    thread[4].ip = 1;
    thread[5].ip = 1;

    cpu[0].currentThread = 0;
    load_context(0);

    cpu[1].currentThread = 3;
    load_context(1);


    run scheduler(0, 0);
    run scheduler(1, 3);

    run cpuProc(0);
    run cpuProc(1);

}

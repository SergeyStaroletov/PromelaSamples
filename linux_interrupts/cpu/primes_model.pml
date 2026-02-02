#define MAXCPU 2
#define MAXTHREADS 6
#define MAXMEM 100

#define IP cpu[currentCPU].context.ip
#define EDI cpu[currentCPU].context.edi
#define ESI cpu[currentCPU].context.esi
#define RBP cpu[currentCPU].context.rbp
#define RSP cpu[currentCPU].context.rsp
#define EAX cpu[currentCPU].context.eax
#define EBX cpu[currentCPU].context.ebx
#define ECX cpu[currentCPU].context.ecx
#define EDX cpu[currentCPU].context.edx
#define FLAGZ cpu[currentCPU].context.flag_z
#define FLAGS cpu[currentCPU].context.flag_s
#define FINISH cpu[currentCPU].finished

#define T cpu[currentCPU].currentThread
#define THREAD thread[T]
#define IDLE_THREAD MAXTHREADS * MAXCPU

typedef CONTEXT {
    int ip;
    int rsp;
    int rbp;
    int eax;
    int ebx;
    int edx;
    int ecx;
    int edi;
    int esi;
    bit flag_z;
    bit flag_s;
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

/*
если использовать память побайтово, то не эффективно: 
byte memory[MAXMEM];
inline movl_rm(a, b) { 
atomic {
memory[(b) & 0xff] = a & 0xff;
memory[(b >> 8) & 0xff] = (a >> 8) & 0xff;
memory[(b >> 16) & 0xff] = (a >> 16) & 0xff;
memory[(b >> 24) & 0xff] = (a >> 24) & 0xff; 
}
}
*/


//Разные типы аргументов a, b: 
//rm = register, memory
//rr = register, register
//mr = memory, register
//cm = const, memory (то же самое как register, memory тк берется просто значение)

inline movl_rm(a, b) { 
    atomic { memory[(b) / 4] = a; 
    //printf("CPU %d VALUE RM %d...\n", currentCPU, a);
    }
}

inline movl_rr(a, b) { 
    atomic { b = a; 
    //printf("CPU %d VALUE RR %d...\n", currentCPU, b);
    }
}

inline movl_mr(a, b) { 
    atomic { b = memory[(a) / 4]; 
    //printf("CPU %d VALUE MR %d...\n", currentCPU, b);
    }
}

inline movl_cm(a, b) { 
    atomic { memory[(b) / 4] = a; 
    //printf("CPU %d VALUE CM %d...\n", currentCPU, b);
    }
}

inline shrl(a, b) { 
    atomic { b = b >> a; 
    //printf("CPU %d SHRL VALUE %d...\n", currentCPU, b);
    }
}

inline addl(a, b) {
    atomic { b = a + b; 
    //printf("CPU %d ADDL VALUE %d...\n", currentCPU, b);
    }
}

inline addl_cm(a, b) {
    atomic { memory[(b) / 4] = a + memory[(b) / 4]; 
    //printf("CPU %d ADDL_CM VALUE %d...\n", currentCPU, memory[(b) / 4]);
    }
}

inline sarl(a) {
    atomic { a = a >> 1; 
    //printf("CPU %d SARL VALUE %d...\n", currentCPU, a);
    }
}

//Расширение eax в edx:eax (для деления)
inline cltd() {
    atomic { EDX = EAX; 
    //printf("CPU %d CLTD VALUE %d...\n", currentCPU, EDX);
    }
}

//Делим a (edx:eax) на b 
inline idivl(b) {
    atomic { 
        EAX = EAX / memory[(b) / 4]; 
        EDX = EDX % memory[(b) / 4]; 
        //printf("CPU %d IDIV VALUES -> div = %d, mod = %d...\n", currentCPU, EAX, EDX);
    }
}

inline testl(a, b) {
    atomic {
        FLAGZ = (((a) & (b)) == 0);
        FLAGS = (((a) & (b)) < 0);
        //printf("CPU %d TESTL VALUES %d & %d -> FZ = %d, FS = %d...\n", currentCPU, a, b, FLAGZ, FLAGS);
    }
}

inline cmpl_mr(a, b) {
    atomic {
        FLAGZ = (b == memory[(a) / 4]);
        FLAGS = (b < memory[(a) / 4]);
        //printf("CPU %d CMPL_MR VALUES MEM (2) %d  REG (1) %d, %d, %d...\n", currentCPU, memory[(a) / 4], b, FLAGZ, FLAGS);
    }
}

inline cmpl_rm(a, b) {
    atomic {
        FLAGZ = (memory[(b) / 4] == a);
        FLAGS = (memory[(b) / 4] < a);

        // printf("CPU %d CMPL_RM VALUES %d, %d, REG %d MEM %d...\n", currentCPU, FLAGZ, FLAGS, a, memory[(b) / 4]);
    }
}

inline nop() {
    skip;
}

inline NEXT_INSTRUCTION() {
    atomic {
        IP++;
        //printf("CPU %d THREAD %d go to instruction %d...\n", currentCPU, T, IP);

        //printf("STATE\n-------------\nIP %d | RSP %d | RBP %d | EAX %d | EDX %d | ESI %d | EDI %d | _MAX %d |i %d | d %d | isPrime %d | min %d | max %d \n\n", 
        //IP, RSP, RBP, EAX, EDX, ESI, EDI, memory[RBP / 4 - 4], memory[RBP / 4 - 1], memory[RBP / 4 - 3], memory[RBP / 4 - 2], memory[RBP / 4 - 5], memory[RBP / 4 - 6]);
    }
}

proctype cpuProc(int currentCPU) {
    //IP = 1;
    //printf("here\n\n");
    do
        :: atomic {
            if
                //::(IP == 1) -> { pushq(cpu[currentCPU].rbp); IP++; }
                ::(IP == 1) -> { movl_rr(RSP, RBP); /*movq(rsp, rbp)*/; IP = 4; }
                //::(IP == 3) -> { subq(32, rsp); IP++; }
                ::(IP == 4) -> { movl_rm(EDI, -20 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 5) -> { movl_rm(ESI, -24 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 6) -> { movl_mr(-20 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 7) -> { movl_rm(EAX, -4 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 8) -> { IP = 36; }//jmp .L3
                //.L9:
                ::(IP == 9) -> { movl_mr(-4 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 10) -> { movl_rr(EAX, EDX); NEXT_INSTRUCTION(); }
                ::(IP == 11) -> { shrl(31, EDX); NEXT_INSTRUCTION(); } 
                ::(IP == 12) -> { addl(EDX, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 13) -> { sarl(EAX); NEXT_INSTRUCTION(); }
                ::(IP == 14) -> { movl_rm(EAX, -16 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 15) -> { movl_cm(1, -8 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 16) -> { movl_cm(2, -12 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 17) -> { IP = 27; }//jmp .L4
                //.L7:
                ::(IP == 18) -> { movl_mr(-4 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 19) -> { cltd(); NEXT_INSTRUCTION(); }
                ::(IP == 20) -> { idivl(-12 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 21) -> { movl_rr(EDX, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 22) -> { testl(EAX, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 23) -> { atomic {if ::(FLAGZ == 0) -> IP = 26; :: else -> NEXT_INSTRUCTION(); fi } } //jne .L5
                ::(IP == 24) -> { movl_cm(0, -8 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 25) -> { IP = 30; } //jmp .L6
                //.L5:
                ::(IP == 26) -> { addl_cm(1, -12 + RBP); NEXT_INSTRUCTION(); }
                //.L4:
                ::(IP == 27) -> { movl_mr(-12 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 28) -> { cmpl_mr(-16 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 29) -> { atomic {if ::(FLAGZ == 1 || FLAGS == 1)  -> IP = 18; :: else -> NEXT_INSTRUCTION(); fi } } //jle .L7
                //.L6:
                ::(IP == 30) -> { cmpl_rm(0, -8 + RBP); NEXT_INSTRUCTION(); }
                ::(IP == 31) -> { atomic {if ::(FLAGZ == 1) -> IP = 35; :: else -> NEXT_INSTRUCTION(); fi } } //je .L8
                ::(IP == 32) -> { movl_mr(-4 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 33) -> { movl_rr(EAX, EDI); NEXT_INSTRUCTION(); }
                ::(IP == 34) -> { printf("\nCPU %d THREAD %d ---------------------- Found prime: %d\n", currentCPU, T, EDI); NEXT_INSTRUCTION(); } //call process_prime
                //.L8:
                ::(IP == 35) -> { addl_cm(1, -4 + RBP); NEXT_INSTRUCTION(); }
                //.L3:
                ::(IP == 36) -> { movl_mr(-4 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 37) -> { cmpl_mr(-24 + RBP, EAX); NEXT_INSTRUCTION(); }
                ::(IP == 38) -> { atomic {if ::(FLAGZ == 1 || FLAGS == 1) -> IP = 9; :: else -> NEXT_INSTRUCTION() fi } } //jle .L9
                ::(IP == 39) -> { if :: !THREAD.finished -> printf("Task %d for CPU %d done!\n", T, currentCPU); THREAD.finished = true; :: else -> ; fi }//break; }
                :: (FINISH) -> break;

                :: (IP == 1000) -> { nop(); };
                //nop
                //nop
                //leave
                //.cfi_def_cfa 7, 8
                //ret
                //.cfi_endproc
            fi;
        }
    od;
}

inline save_context() {
    atomic {
        THREAD.ip = IP;
        THREAD.rsp = RSP;
        THREAD.rbp = RBP;
        THREAD.eax = EAX;
        THREAD.ebx = EBX;
        THREAD.ecx = ECX;
        THREAD.edx = EDX;
        THREAD.edi = EDI;
        THREAD.esi = ESI;
        THREAD.flag_z = FLAGZ;
        THREAD.flag_s = FLAGS;
    }
}

inline load_context(currentCPU) {
    atomic {
        IP = THREAD.ip;
        RSP = THREAD.rsp;
        RBP = THREAD.rbp
        EAX = THREAD.eax;
        EBX = THREAD.ebx;
        ECX = THREAD.ecx;
        EDX = THREAD.edx;
        EDI = THREAD.edi;
        ESI = THREAD.esi;
        FLAGZ = THREAD.flag_z;
        FLAGS = THREAD.flag_s;
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
                    //if :: (currentThread != T) -> printf("Scheduler: CPU %d SWITCHED to thread: %d!", currentCPU, T - startThread); 
                     //  :: else -> 
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
    thread[0].rsp = MAXMEM / 2;
    thread[1].rsp = MAXMEM;
    thread[2].rsp = MAXMEM / 2 + MAXMEM;

    //1 ищет числа от 100 до 500
    thread[0].edi = 100;
    thread[0].esi = 500;

    //2 ищет числа от 51 до 100
    thread[1].edi = 51;
    thread[1].esi = 100;

    //3 ищет числа от 1 до 50
    thread[2].edi = 1;
    thread[2].esi = 50;


    thread[3].rsp = MAXMEM * 2;
    thread[4].rsp = MAXMEM * 2 + MAXMEM / 2;
    thread[5].rsp = MAXMEM * 3;

    //1 ищет числа от 101 до 200
    thread[3].edi = 101;
    thread[3].esi = 200;

    //2 ищет числа от 51 до 100
    thread[4].edi = 51;
    thread[4].esi = 100;

    //3 ищет числа от 1 до 50
    thread[5].edi = 1;
    thread[5].esi = 50;

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

// proctype interrupt_gen() {
//     do
//         ::true -> printf("selecting something") 
//     od
// }



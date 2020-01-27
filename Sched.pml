
//-----------------------------------------------------------------
//First OS in Promela:)
//(c) Sergey Staroletov
//-----------------------------------------------------------------

#define MAXPROC 2
#define MAXPART 2
#define MAXSTACK 10
#define TH1FIN 3
#define PARTITION1 0
#define PARTITION2 1
#define MAXTIMESIM 10000

//internal data declaration

typedef Context {
    int IP;
    int sp;
    int r0;
    int r1;
    int r2;
}
int currentThread = 0;
int currentPartition = 0;
Context currentContext;
Context stack[MAXPROC * MAXPART] = {0,0,0,0};
int sid = 0;
int realTime = 0; //time variable
bit osLive = 1;

chan Interrupt=[0] of {short};

Context stackInterrupt[MAXSTACK];
int stackInterruptTop = -1;

//syscalls
mtype = {sem_p, sem_v, delay, print}

inline do_syscall(N, param) {
    //prepare 
    currentContext.r0 = N;

    Interrupt ! 1;
}

//user library
//inline p(sem) {
//    do_syscall(0, sem)
//}

//inline v(sem) {
//    do_syscall(1, sem)
//}


inline pok_sem_signal(sid, ret) {
 printf("pok_sem_signal stub\n"); 
 ret = 0;
}


inline pok_sem_wait(sid, ret) {
 printf("pok_sem_wait stub\n"); 
 ret = 0;
}

inline pok_delay(time) {
 printf("pok_delay stub\n");
}

//scheduler model
active proctype sched() {
    do
    :: realTime < MAXTIMESIM -> {
        atomic {
            stack[currentPartition * MAXPART + currentThread].IP = currentContext.IP;
            //select partition
            if
                ::true -> currentPartition = 0;
                ::true -> currentPartition = 1;
            fi
            if ::(currentThread == 0) -> currentThread = 1;
               :: else -> currentThread = 0;
            fi
            currentContext.IP = stack[currentPartition * MAXPART + currentThread].IP;
            realTime++;
        }
     }
    :: else -> {printf("Pardon, time is over!\n"); osLive = 0; break;}
    od
}


//user's tread logic
//model: see examples/semaphores on pok repo
proctype threadP1T1(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> {
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { printf("P1T1: I will signal semaphores\n"); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_signal(sid, currentContext.r0); currentContext.IP++;}
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { printf("P1T1: pok_sem_signal ret %d\n", currentContext.r0); currentContext.IP++;}
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_delay(2000); currentContext.IP = 0; /* inf loop */}
                    ::else -> skip;
                    fi
                fi
            fi
        fi 
     }
 }
 :: else -> break;
od
}


proctype threadP1T2(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> {
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { printf("P1T2: I will wait for the semaphores\n"); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_wait(sid, currentContext.r0); currentContext.IP++;}
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { printf("P1T1: pok_sem_wait ret %d\n", currentContext.r0); currentContext.IP++;}
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_sem_wait(sid, currentContext.r0); currentContext.IP++;}
                    ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 4) -> 
                        { printf("P1T1: pok_sem_wait ret %d\n", currentContext.r0); currentContext.IP++;}
                        ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 5) -> 
                                { pok_delay(2000); currentContext.IP = 0;}
                                 ::else -> skip;
                            fi
                        fi
                    fi
                fi
            fi
        fi 
     }
 }
  :: else -> break;
  od
}

proctype threadP2T1(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> {
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { printf("P2T1: begin of task\n"); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_delay(5000); currentContext.IP = 0; }
            ::else ->  skip;   
            fi
        fi 
     }
 }
:: else -> break;
od
}

//entry point

active proctype main() {
    //setup the environment
    currentContext.IP = 0;
    stack[0].IP = 0;
    stack[1].IP = 0;
    stack[2].IP = 0;
    stack[3].IP = 0;


    currentThread = 0;
    currentPartition = PARTITION1;

    //run all the threads
    run threadP1T1(PARTITION1, 0);
    run threadP1T2(PARTITION1, 1);
    run threadP2T1(PARTITION2, 0);
    
}



//interrupts processing model
active proctype interrupt_handler() {
short buf;
do 
:: true ->  {
     Interrupt ? buf;
    run one_handler();
    }
od
}

//kernel api
inline sem_p(sem) {
    (sem != 0) -> sem = 0;
}

inline sem_v(sem) {
    sem = 1;
}


proctype one_handler() {
int myStackTop; 
int id;
 atomic {
        stackInterruptTop = stackInterruptTop + 1;
        myStackTop = stackInterruptTop;
        stackInterrupt[myStackTop].IP = currentContext.IP; //save ip
        stackInterrupt[myStackTop].r0 = currentContext.r0;
        id = stackInterrupt[myStackTop].r0; 
 }

    if 
        ::(id == 0) -> { atomic {printf("interrupt with function 0\n"); currentContext.IP++ }}
        ::(id == 1) -> { atomic {printf("interrupt with function 1\n"); currentContext.IP++ }}
        :: else -> skip;
    fi


 atomic{
        currentContext.IP = stackInterrupt[stackInterruptTop].IP; //restore ip
        stackInterruptTop-- ;
    }
}





ltl check_me { [] <> (stack[0].IP == 2 && stack[1].IP == 2) }

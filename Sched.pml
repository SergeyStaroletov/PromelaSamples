
//-----------------------------------------------------------------
//First OS in Promela:)
//(c) Sergey Staroletov
//-----------------------------------------------------------------

#define MAXPROC 2
#define MAXSTACK 10
#define TH1FIN 3


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
Context stack[MAXPROC] = {0,0};
int sem1 = 0;

chan Interrupt=[0] of {short};

Context stackInterrupt[MAXSTACK];
int stackInterruptTop=-1;


inline p(sem) {
    do_syscall(0, sem)
}

inline v(sem) {
    do_syscall(1, sem)
}

inline do_syscall(N, param) {
    //prepare 
    currentContext.r0 = N;
    Interrupt ! 1;
}


active proctype sched() {
    do
    :: true -> {
        atomic {
            stack[currentThread].IP = currentContext.IP;
            if ::(currentThread == 0) -> currentThread = 1;
               :: else -> currentThread = 0;
            fi
            currentContext.IP = stack[currentThread].IP;
        }
     }
    od
}



active proctype thread1() {
do
 :: (currentContext.IP != TH1FIN) -> {
     atomic {
     if ::(currentPartition == 0 && currentThread == 0 && currentContext.IP == 0) -> 
     { printf("th1: execute line 1\n"); p(0); currentContext.IP = currentContext.IP + 1;}
        :: else -> 
            if ::(currentPartition == 0 && currentThread == 0 && currentContext.IP == 1) -> 
            { printf("th1: execute line 2\n"); currentContext.IP = currentContext.IP + 1;}
            ::else -> if ::(currentPartition == 0 && currentThread == 0 && currentContext.IP == 2) -> 
                { printf("th1: execute line 3\n"); currentContext.IP = currentContext.IP + 1;}
                ::else -> skip;
                fi;
            fi
     fi 
     }
 }
 :: else -> {printf("th1 done! \n"); break; } 
od
}

active proctype th2() {
do
 :: (currentContext.IP != 2) -> {
     atomic {
     if ::(currentThread == 1 && currentContext.IP == 0) -> { printf("th2: execute line 1\n"); ; currentContext.IP = currentContext.IP + 1;}
        :: else -> 
            if ::(currentThread == 1 && currentContext.IP == 1) -> { v(0);  currentContext.IP = currentContext.IP + 1;}
            ::else -> skip;
            fi
     fi 
     }
 }
 :: else -> {printf("th2 done! \n"); break; } 
od
}


active proctype interrupt_handler() {
short buf;
do 
:: true ->  {
     Interrupt ? buf;
    run one_handler();
    }
od
}


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
        ::(id == 0) -> { atomic {printf("interrupt with function 0\n"); sem_p(sem1); currentContext.IP++ }}
        ::(id == 1) -> { atomic {printf("interrupt with function 1\n"); sem_v(sem1); currentContext.IP++ }}
        :: else -> skip;
    fi


 atomic{
        currentContext.IP = stackInterrupt[stackInterruptTop].IP; //restore ip
        stackInterruptTop-- ;
    }


}


ltl check_me { [] <> (stack[0].IP == 2 && stack[1].IP == 2) }
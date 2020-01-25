
//-----------------------------------------------------------------


#define MAXPROC 2
#define MAXSTACK 10
#define TH1FIN 2


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


int IP = 0;

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
            stack[currentThread].IP = IP;
            if ::(currentThread == 0) -> currentThread = 1;
               :: else -> currentThread = 0;
            fi
            IP = stack[currentThread].IP;
        }
     }
    od
}

//inline do_syscall() {
//
//}

active proctype thread1() {
do
 :: (currentContext.IP != TH1FIN) -> {
     atomic {
     if ::(currentPartition == 0 && currentThread == 0 && currentContext.IP == 0) -> 
     { printf("th1: execute line 1\n"); p(0); currentContext.IP = currentContext.IP + 1;}
        :: else -> 
            if ::(currentPartition == 0 && currentThread == 0 && currentContext.IP == 1) -> 
            { printf("th1: execute line 2\n"); v(0); currentContext.IP = currentContext.IP + 1;}
            ::else -> skip;
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
     if ::(currentThread == 1 && currentContext.IP == 0) -> { printf("th2: execute line 1\n");  currentContext.IP = currentContext.IP + 1;}
        :: else -> 
            if ::(currentThread == 1 && currentContext.IP == 1) -> { printf("th2: execute line 2\n");  currentContext.IP = currentContext.IP + 1;}
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


proctype one_handler() {

int myStackTop; 
 atomic {
        stackInterruptTop = stackInterruptTop + 1;
        myStackTop = stackInterruptTop;
        stackInterrupt[myStackTop].IP = currentContext.IP; //save ip
        stackInterrupt[myStackTop].r0 = currentContext.r0;
         }

    int id = stackInterrupt[myStackTop].r0; 

    if 
        ::(id == 0) -> { printf("interrupt with function 0\n"); currentContext.IP++ }
        ::(id == 1) -> { printf("interrupt with function 1\n"); currentContext.IP++ }
        :: else -> skip;
    fi


 atomic{
        currentContext.IP = stackInterrupt[stackInterruptTop].IP; //restore ip
        stackInterruptTop-- ;
    }


}


ltl check_me { [] <> (stack[0].IP == 2 && stack[1].IP == 2) }

//-----------------------------------------------------------------
//First OS in Promela:)
//moreover, it is a partitioned:)
//(c) Sergey Staroletov
//-----------------------------------------------------------------

#define MAXTHREADS 2
#define MAXPARTITIONS 2
#define MAXSTACK 10
#define MAXSEMAPHORES 1
#define PARTITION1 0
#define PARTITION2 1
#define INTERRUPT MAXPARTITIONS
#define MAXTIMESIM 10000

//internal data declaration

typedef Context {
    int IP;
    int sp;
    int r0;
    int r1;
    int r2;
}

typedef Thread {
    Context context;
    int timeSpacePerThread;
    bit isLocked;
    int wakeUpTime;
    short id;
    short partition;
}

typedef Partition {
    short timeSpacePerPartition;
    Thread threads[MAXTHREADS];
}

typedef Semaphore {
    short maxCount;
    short currentCount;
    short theadsAwaiting[MAXTHREADS];
    short threadAwaitingCount;
}

int currentThread = 0;
int currentPartition = 0;
Context currentContext;

Semaphore semaphores[MAXSEMAPHORES];

//our main composite data struct
Partition partitions[MAXPARTITIONS];


int realTime = 0; //time variable
short schedCurrentPartitionRunTime = 0;
short schedCurrentThreadRunTime = 0;

bit osLive = 1;
bit interruptsDisable = 0;

int sid = 0;


chan InterruptController = [0] of {short}; //for interrupt signals
chan InterruptRet = [0] of {short}; //for interrupt returns


//syscalls types
mtype = {syscall_sem_p, syscall_sem_v, syscall_delay, syscall_print}


//-------------------------------------------------------------------------------
// Scheduler model
//-------------------------------------------------------------------------------


//scheduler model entry
inline runSched() {
    //run schedNonDeterministicInstance();
    run schedDeterministicInstance();
}


inline saveCurrentContext() {
    partitions[currentPartition].threads[currentThread].context.IP = currentContext.IP;
    partitions[currentPartition].threads[currentThread].context.sp = currentContext.sp;
    partitions[currentPartition].threads[currentThread].context.r0 = currentContext.r0;
    partitions[currentPartition].threads[currentThread].context.r1 = currentContext.r1;
    partitions[currentPartition].threads[currentThread].context.r2 = currentContext.r2;
}

inline restoreCurrentContext() {
    currentContext.IP = partitions[currentPartition].threads[currentThread].context.IP;
    currentContext.sp = partitions[currentPartition].threads[currentThread].context.sp;
    currentContext.r0 = partitions[currentPartition].threads[currentThread].context.r0;
    currentContext.r1 = partitions[currentPartition].threads[currentThread].context.r1;
    currentContext.r2 = partitions[currentPartition].threads[currentThread].context.r2;
}


//scheduler logic - it was declared as inline to call it from sleep
inline schedDeterministicInstanceLogic() {
    //save current context
    saveCurrentContext(); 
    short currentPartitionC = currentPartition; //candidates to switch
    short currentThreadC = currentThread;

    //fix time for sleeping threads
    short partIter = 0;
    do
        ::(partIter < MAXPARTITIONS) -> {
            short threadIter = 0;
            do
                ::(threadIter < MAXTHREADS) -> {
                    if
                        ::(partitions[partIter].threads[threadIter].wakeUpTime <= realTime) -> { //wakeup time is over
                            partitions[partIter].threads[threadIter].wakeUpTime = 0; //that will stop its waiting
                        }
                        ::else -> skip; 
                    fi
                }
                ::else -> break;
            od
        }
        ::else -> break;
    od

    bit needPeakAThread = 0;
    //check run time and select a next partition
    if  
        :: (schedCurrentPartitionRunTime > partitions[currentPartition].timeSpacePerPartition) ->
        {
            currentPartitionC++;
            if 
                :: (currentPartitionC == MAXPARTITIONS) -> currentPartitionC = 0;
                :: else -> skip;
            fi
            schedCurrentPartitionRunTime = 0;
            schedCurrentThreadRunTime = 0; //we mean we change also the thread of the partition
            needPeakAThread = 1;
            currentThreadC = -1; //?
        }
        :: else -> skip;
    fi
    //calulate run time and select a next thread
    if
        ::(needPeakAThread == 1) || (schedCurrentThreadRunTime > partitions[currentPartition].threads[currentThread].timeSpacePerThread) -> {
            //find next non locked and sleeped thread  
            
            short nextThread = currentThreadC + 1;
            if
                :: (nextThread == MAXTHREADS) -> {
                        nextThread = 0;
                }
                :: else -> skip;
            fi
            
            bit isNextFound = 0;
            do ::(nextThread != currentThreadC) -> { //do while we interate all threads
                if 
                    ::(partitions[currentPartitionC].threads[nextThread].isLocked == 0) &&
                    (partitions[currentPartitionC].threads[nextThread].wakeUpTime == 0)  -> {
                        isNextFound = 1; //we found non-locked and non-sleeping thread
                        break;
                    }
                    ::else -> skip;
                fi
                nextThread++; 
                if
                    :: (nextThread == MAXTHREADS) -> {
                        nextThread = 0;
                    }
                    :: else -> skip;
                fi
                }
               ::else -> break;
            od
            //if we found a thread, change the variables values
            if 
                :: (isNextFound && nextThread != -1) -> {
                    //we found a next working thread to switch to
                    schedCurrentThreadRunTime = 0;
                    currentThread = nextThread;
                    currentPartition = currentPartitionC;
                }
                :: else -> skip; //we do not found a thread - rollback??
            fi
        }
        :: else -> skip; 
    fi

    //switch current context
    restoreCurrentContext();
}


proctype schedDeterministicInstance() {
    do
    ::(realTime < MAXTIMESIM) -> {
        realTime++;
        //increase time on tick
        schedCurrentPartitionRunTime++;
        schedCurrentThreadRunTime++;
        if 
            ::(interruptsDisable == 0) ->
            atomic {
                schedDeterministicInstanceLogic();
            }
        ::else ->skip;
        fi
     }
    ::else -> {printf("Pardon, time is over!\n"); osLive = 0; break;}
    od
}

//simple scheduler for education that peaks random partitions and threads (currently do not used)
proctype schedNonDeterministicInstance() {
    do
    :: realTime < MAXTIMESIM -> {
        atomic {
            //stack[currentPartition * MAXPARTITIONS + currentThread].IP = currentContext.IP;
            //select partition
            //non-deterministic scheduler - rewrite?
            if
                ::true -> currentPartition = 0;
                ::true -> currentPartition = 1;
            fi
            if 
                ::(currentThread == 0) -> currentThread = 1; //stub
                :: else -> currentThread = 0;
            fi
            //currentContext.IP = stack[currentPartition * MAXPARTITIONS + currentThread].IP;
            realTime++;
        }
     }
    :: else -> {printf("Pardon, time is over!\n"); osLive = 0; break;}
    od
}



//-------------------------------------------------------------------------------
// Syscalls model
//-------------------------------------------------------------------------------


//universal syscall executor - emulates interrupt caller
inline pok_do_syscall(N, param, ret) {
    atomic {
    //pass the params
    currentContext.r0 = N;
    currentContext.r1 = param;
    }
    //emit the interrupt
    InterruptController ! 42;
    //wait for iret
    InterruptRet ? ret;
}


//library available to user

inline pok_sem_signal(sid, ret) {
    pok_do_syscall(syscall_sem_v, sid, ret);
}

inline pok_sem_wait(sid, ret) {
    pok_do_syscall(syscall_sem_p, sid, ret);
}

inline pok_delay(time) {
    pok_do_syscall(syscall_delay, sid, currentContext.r0);
}

//kernel library for syscalls

inline sem_signal(sid) {
    semaphores[sid].currentCount++; //update the counter
    if  //check?
        ::(semaphores[sid].currentCount > semaphores[sid].maxCount) -> semaphores[sid].currentCount = semaphores[sid].maxCount;
        ::else -> skip;
    fi

    if
        ::(semaphores[sid].currentCount == 0) -> {
            //we need to unlock an awaiting thread -> just remove it from list of awaiters
            if
                ::(semaphores[sid].threadAwaitingCount > 0) -> {
                    //remove = decrement
                    semaphores[sid].threadAwaitingCount--;
                    //put islocked (not safe solution)
                    short idd = semaphores[sid].theadsAwaiting[semaphores[sid].threadAwaitingCount];
                    //find the thread by dfs using its id
                    short partIter = 0;
                    do
                        ::(partIter < MAXPARTITIONS) -> {
                            short threadIter = 0;
                            do
                                ::(threadIter < MAXTHREADS) -> {
                                    if
                                        ::(partitions[partIter].threads[threadIter].id == idd) -> {
                                            //unlock the thread
                                            partitions[partIter].threads[threadIter].isLocked = 0;
                                            break;
                                        }
                                        ::else -> skip; 
                                    fi
                                }
                                ::else -> break;
                            od
                        }
                        ::else -> break;
                    od

                }
                ::else -> skip;
            fi
        }
        ::else -> skip;    
    fi
}

inline sem_wait(sid) {
    semaphores[sid].currentCount--; //update the counter
    if 
        ::(semaphores[sid].currentCount < -1) -> semaphores[sid].currentCount = -1;
        ::else -> skip;
    fi

    if
        ::(semaphores[sid].currentCount < 0) -> {
            //we need to lock the current thread
            partitions[currentPartition].threads[currentThread].isLocked = 1;
            semaphores[sid].threadAwaitingCount++;
            //save current thread calculated id into the semaphore waiting list
            semaphores[sid].theadsAwaiting[semaphores[sid].threadAwaitingCount] = currentPartition * MAXPARTITIONS + currentThread;
        }
        ::else -> skip; 
    fi
}


inline sleep(sleepTime) {
    partitions[currentPartition].threads[currentThread].wakeUpTime = realTime + sleepTime;
    //schedDeterministicInstanceLogic(); //--buggy for now
}


//interrupts processing model
active proctype InterruptHandler() {
short intNum;

do 
:: true ->  {
    InterruptController ? intNum;

    int ret = 0; //stub
    int id = currentContext.r0;
    int param = currentContext.r1;
    interruptsDisable = 1; //stop the scheduler
    saveCurrentContext();
    if 
        :: (intNum == 42) -> { //we react on only one interrupt
            if
                :: (id == syscall_sem_v) -> sem_signal(param);
                :: (id == syscall_sem_p) -> sem_wait(param);
                :: (id == syscall_delay) -> sleep(param);
                :: else -> skip;
            fi
        }
        :: else -> skip;
    fi
    //restore current context
    restoreCurrentContext();
    interruptsDisable = 0;
    InterruptRet ! ret;
    }
od
}



//-------------------------------------------------------------------------------
// User code
//-------------------------------------------------------------------------------


//user's tread logic
//model: see examples/semaphores in pok repo
proctype threadP1T1(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> {
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { printf("P1T1: I will signal semaphores\n"); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_signal(sid, currentContext.r0); currentContext.IP++; }
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { printf("P1T1: pok_sem_signal ret %d\n", currentContext.r0); currentContext.IP++; }
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_delay(2000); currentContext.IP = 0; /* inf loop */ }
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
     { printf("P1T2: I will wait for the semaphores\n"); currentContext.IP++; }
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_wait(sid, currentContext.r0); currentContext.IP++; }
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { printf("P1T1: pok_sem_wait ret %d\n", currentContext.r0); currentContext.IP++;}
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_sem_wait(sid, currentContext.r0); currentContext.IP++; }
                    ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 4) -> 
                        { printf("P1T1: pok_sem_wait ret %d\n", currentContext.r0); currentContext.IP++;}
                        ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 5) -> 
                                { pok_delay(2000); currentContext.IP = 0; }
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



//-------------------------------------------------------------------------------
// Main 
//-------------------------------------------------------------------------------



inline createThread(partitionId, threadId) {
    partitions[partitionId].threads[threadId].id = partitionId * MAXPARTITIONS + threadId;
    partitions[partitionId].threads[threadId].partition = partitionId;
    partitions[partitionId].threads[threadId].context.IP = 0;
    partitions[partitionId].threads[threadId].wakeUpTime = 0;
    partitions[partitionId].threads[threadId].isLocked = 0;
}


//main entry point
active proctype main() {
    //setup the environment
    // timeSpacePerPartition[MAXPARTITIONS] = {100, 100};
    // timeSpacePerThread[MAXPARTITIONS * MAXTHREADS] = {50, 50, 100, 0};
    partitions[0].timeSpacePerPartition = 100;
    partitions[1].timeSpacePerPartition = 100;
    createThread(0, 0);
    partitions[0].threads[0].timeSpacePerThread = 50;
    createThread(0, 1);
    partitions[0].threads[1].timeSpacePerThread = 50;
    createThread(1, 0);
    partitions[1].threads[0].timeSpacePerThread = 100;
    createThread(1, 1);
    partitions[1].threads[1].timeSpacePerThread = 0;
    partitions[1].threads[1].isLocked = 1;

    semaphores[0].currentCount = 50;
    semaphores[0].maxCount = 50;
  
    currentThread = 0;
    currentPartition = PARTITION1;

    //run scheduler instance
    runSched();

    //run all the threads
    run threadP1T1(PARTITION1, 0);
    run threadP1T2(PARTITION1, 1);
    run threadP2T1(PARTITION2, 0);
    
}

//to be: 
// - memory checks
// - "pointer verify" model like in pok
// - semaphores

//ltl check_me { [] <> (stack[0].IP == 2 && stack[1].IP == 2) }

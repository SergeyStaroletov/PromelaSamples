
//-----------------------------------------------------------------
//First OS in Promela:)
//moreover, it is a partitioned OS:)
//(c) Sergey Staroletov
//-----------------------------------------------------------------

#define MAXTHREADS 2
#define MAXPARTITIONS 2
#define MAXSTACK 10
#define MAXSEMAPHORES 1
#define PARTITION1 0
#define PARTITION2 1
#define MAXTIMESIM 1000

#define NOPARAM -42
#define IDLE_THREAD 42
#define POK_INTERRUPT 42

//internal data declaration

//model for state of current process
typedef Context {
    int IP;         //instruction pointer
    int sp;         //stack pointer - for futher modeling
    int r0;         //arithmetic registers
    int r1;
    int r2;
}

//model for a thread (process) in system 
typedef Thread {
    Context context;  //thread context to save
    short timeSpacePerThread; //count of ticks to thread work 
    bit isLocked;     //1 if it has been locked on a semaphore
    int wakeUpTime;   //wake up time to schedule using sleep
    short id;         //unique thread id
    short partition;  //number of parent partition
    short prior;      //for futher model with priorities
    short rate;       //current execution time - for rms
}

//model for a partition, that has some threads and time piece for all threads inside
typedef Partition {
    short timeSpacePerPartition; //count of ticks to run this partition
    short threadCount;
    Thread threads[MAXTHREADS];  //threads of this partition
    short schedulingStrategy;    //type of sched for threads of this partition
    short mainThread;            //first thread to run
}

//model for a locking object
typedef Semaphore {
    short maxCount;
    short currentCount;
    short theadsAwaiting[MAXTHREADS * MAXPARTITIONS]; //list of threads waiting this object
    short threadAwaitingCount;  //count of waiters
}

short currentThread = 0;
short currentPartition = 0;
Context currentContext;

Semaphore semaphores[MAXSEMAPHORES];

//
//our main composite data struct
//
Partition partitions[MAXPARTITIONS];


int realTime = 0; //time variable
short schedCurrentPartitionRunTime = 0;
short schedCurrentThreadRunTime = 0;

bit osLive = 1;
bit interruptsDisabled = 0;

short sid = 0;

chan InterruptController = [0] of {short}; //for interrupt signals
chan InterruptRet = [0] of {short}; //for interrupt returns

bit pointersOk = 1;

//syscalls types
mtype = {syscall_sem_p, syscall_sem_v, syscall_delay, syscall_printf}
//sched strategy types
mtype = {sched_part_rms_strategy, sched_part_rr_strategy, sched_part_edf_strategy, sched_part_llf_strategy}

//string constants
#define P1T1_I_will_signal_semaphores 0
#define P1T1_pok_sem_signal_ret 1
#define P1T2_I_will_wait_for_the_semaphores 2
#define P1T2_pok_sem_wait_ret 3
#define P2T1_begin_of_task 4

short partitionByDataIndex[5] = {
        PARTITION1,  
        PARTITION1,
        PARTITION1,
        PARTITION1,
        PARTITION2
};

//-------------------------------------------------------------------------------
// Scheduler model
//-------------------------------------------------------------------------------


//scheduler model entry
inline runSched() {
    //run schedNonDeterministicInstance();
    run schedDeterministicInstance();
}


inline saveCurrentContext() {
    if 
    ::currentThread != IDLE_THREAD -> {
        partitions[currentPartition].threads[currentThread].context.IP = currentContext.IP;
        partitions[currentPartition].threads[currentThread].context.sp = currentContext.sp;
        partitions[currentPartition].threads[currentThread].context.r0 = currentContext.r0;
        partitions[currentPartition].threads[currentThread].context.r1 = currentContext.r1;
        partitions[currentPartition].threads[currentThread].context.r2 = currentContext.r2;
    } 
    :: else -> skip;
    fi
}

inline restoreCurrentContext() {
    if 
    ::currentThread != IDLE_THREAD -> {
        currentContext.IP = partitions[currentPartition].threads[currentThread].context.IP;
        currentContext.sp = partitions[currentPartition].threads[currentThread].context.sp;
        currentContext.r0 = partitions[currentPartition].threads[currentThread].context.r0;
        currentContext.r1 = partitions[currentPartition].threads[currentThread].context.r1;
        currentContext.r2 = partitions[currentPartition].threads[currentThread].context.r2;
    }
    :: else -> skip;
    fi
}




inline elect_next_partition(needPeakAThread) {
 if  
        :: (schedCurrentPartitionRunTime > partitions[currentPartition].timeSpacePerPartition) ->
        {
            currentPartition = (currentPartition + 1) % MAXPARTITIONS;

            schedCurrentPartitionRunTime = 0;
            schedCurrentThreadRunTime = 0; //we mean we change also the thread of the partition
            needPeakAThread = 1;
        }
        :: else -> skip;
    fi
}

// LLF (least laxity first) scheduling strategy (to be done)
inline sched_part_llf() {
   currentThread = (currentThread + 1) % MAXTHREADS;
}

// EDF (earliest deadline first) scheduling strategy (to be done)
inline sched_part_edf() {
   currentThread = (currentThread + 1) % MAXTHREADS;
}


// RMS (rate monothonic) scheduling strategy (to be done)
inline sched_part_rms() {
   currentThread = (currentThread + 1) % MAXTHREADS;
}

// RR round-robin scheduling strategy with sleeping and blocking threads support
inline sched_part_rr() {

//check: do we need actually a switching (time of thread is over or we should schedule)    
int currentMax = 0;
 if 
        ::(currentThread != IDLE_THREAD) ->
            currentMax = partitions[currentPartition].threads[currentThread].timeSpacePerThread;
        ::else -> {
            needPeakAThread = 1;
            currentThread = MAXTHREADS - 1;
        }
    fi

    if
        ::(needPeakAThread == 1) || (schedCurrentThreadRunTime > currentMax) -> {
            //find next non-locked and non-sleeping thread              
            short nextThread = (currentThread + 1) % MAXTHREADS;

            bit isNextFound = 0;
            do ::(nextThread != currentThread) && !isNextFound -> { //do while we interate all threads
                if 
                    ::(partitions[currentPartition].threads[nextThread].isLocked == 0) &&
                    (partitions[currentPartition].threads[nextThread].wakeUpTime == 0)  -> {
                        isNextFound = 1; //we found a non-locked and non-sleeping thread
                        break;
                    }
                    ::else -> skip;
                fi
                nextThread = (nextThread + 1) % MAXTHREADS; 
                }
               ::else -> break;
            od

            //if we found a good thread, change the variables values
            if 
                :: (isNextFound && nextThread != -1) -> {
                    //we found a next working thread to switch to
                    schedCurrentThreadRunTime = 0;
                    currentThread = nextThread;
                }
                :: else -> {
                    //we did not find a thread, but we need something to return - switch to a virtual one
                    currentThread = IDLE_THREAD;
                    currentContext.IP = 0;
                    schedCurrentThreadRunTime = 0; //?
                }
            fi
        }
        :: else -> skip; 
    fi

}


inline elect_next_thread(needPeakAThread) {
    if 
        :: (partitions[currentPartition].schedulingStrategy == sched_part_rms_strategy) -> sched_part_rms();
        :: (partitions[currentPartition].schedulingStrategy == sched_part_rr_strategy)  -> sched_part_rr();
        :: (partitions[currentPartition].schedulingStrategy == sched_part_llf_strategy) -> sched_part_llf();
        :: (partitions[currentPartition].schedulingStrategy == sched_part_edf_strategy) -> sched_part_edf();
        :: else -> skip;
    fi
}


//Scheduler logic - it was declared as inline to call it from sleep
inline schedDeterministicInstanceLogic() {

    //printf("sched in action...\n");
    //save current context
    saveCurrentContext(); 

    short currentPartitionC = currentPartition; //candidates to switch
    short currentThreadC = currentThread;

    //fix time for sleeping threads (clear waiting if possible)
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
                    threadIter++;
                }
                ::else -> break;
            od
            partIter++;
        }
        ::else -> break;
    od

    bit needPeakAThread = 0;

    //check run time and select a next partition
    elect_next_partition(needPeakAThread);

    //calulate run time and select a next thread
    elect_next_thread(needPeakAThread);

    if 
    ::currentThread != IDLE_THREAD ->
        printf("Elected thread: %d in partition %d\n", currentThread, currentPartition);
    ::else -> skip;
    fi
    //switch current context
    restoreCurrentContext();
}


proctype schedDeterministicInstance() {
    do
    ::(realTime < MAXTIMESIM) -> {
        realTime++;         //increase time on tick
        schedCurrentPartitionRunTime++;
        schedCurrentThreadRunTime++;
        if 
            ::(interruptsDisabled == 0) ->
            atomic {
                schedDeterministicInstanceLogic(); //run scheduling logic
            }
        ::else ->skip;
        fi
     }
    ::else -> {printf("Pardon, time is over!\n"); osLive = 0; break;}
    od
}

//simple scheduler for education that peaks random partitions and threads (currently is not used)
proctype schedNonDeterministicInstance() {
    do
    :: realTime < MAXTIMESIM -> {
        atomic {
            saveCurrentContext(); 

            //non-deterministic scheduler - rewrite?
            if
                ::true -> currentPartition = 0;
                ::true -> currentPartition = 1;
            fi
            if 
                ::(currentThread == 0) -> currentThread = 1; //stub
                :: else -> currentThread = 0;
            fi
            realTime++;
            restoreCurrentContext();
        }
     }
    :: else -> {printf("Pardon, time is over!\n"); osLive = 0; break;}
    od
}



//-------------------------------------------------------------------------------
// Syscalls model
//-------------------------------------------------------------------------------


//universal syscall executor - emulates interrupt caller
inline pok_do_syscall(N, param1, param2, ret) {
    atomic {
    //pass the params
    currentContext.r0 = N;
    currentContext.r1 = param1;
    if 
        ::(param2 != NOPARAM) -> currentContext.r2 = param2;
        ::else -> skip
    fi
    }
    //emit the interrupt
    InterruptController ! POK_INTERRUPT;
    //wait for iret
    InterruptRet ? ret;
}


//library available to user

inline pok_sem_signal(sid, ret) {
    printf("pok_sem_signal\n");
    pok_do_syscall(syscall_sem_v, sid, NOPARAM, ret);
}

inline pok_sem_wait(sid, ret) {
    printf("pok_sem_wait\n");
    pok_do_syscall(syscall_sem_p, sid, NOPARAM, ret);
}

inline pok_delay(time) {
    printf("pok_delay\n");
    pok_do_syscall(syscall_delay, time, NOPARAM, currentContext.r0);
}

inline pok_print(string) {
    pok_do_syscall(syscall_printf, string, NOPARAM, currentContext.r0);
}

inline pok_printf(string, param) {
    pok_do_syscall(syscall_printf, string, param, currentContext.r0);
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
                    //put islocked (not safe solution) 
                    semaphores[sid].threadAwaitingCount--;
                    short num = semaphores[sid].threadAwaitingCount;
                    short idd = semaphores[sid].theadsAwaiting[num]; 
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
                                    threadIter++;
                                }
                                ::else -> break;
                            od
                            partIter++;
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
            //save current thread calculated id into the semaphore waiting list
            printf("threadAwaitingCount = %d\n", semaphores[sid].threadAwaitingCount);
            semaphores[sid].theadsAwaiting[semaphores[sid].threadAwaitingCount] = currentPartition * MAXPARTITIONS + currentThread;
            semaphores[sid].threadAwaitingCount++;
        }
        ::else -> skip; 
    fi
}


inline sleep(sleepTime) {
    partitions[currentPartition].threads[currentThread].wakeUpTime = realTime + sleepTime;
    //call the scheduler now
    schedDeterministicInstanceLogic(); //buggy ?

}

//check if we are in the correct partition
inline checkPointer(expectedPartition, actualPartition) {
    if
        :: (expectedPartition != actualPartition) ->  {
            pointersOk = 0;
            printf("segmentation fault!\n");
        }
        :: else -> skip
    fi
}


inline print(string, param) {
    //for each string it is known where does it locate, so we can check it 
    checkPointer(partitionByDataIndex[string], currentPartition);
    if
        :: (string == P1T1_I_will_signal_semaphores) -> printf("[%d] P1T1: I will signal semaphores\n", realTime);
        :: (string == P1T1_pok_sem_signal_ret) -> printf("[%d] P1T1: pok_sem_signal_ret = %d\n", realTime, param);
        :: (string == P1T2_I_will_wait_for_the_semaphores) -> printf("[%d] P1T2: I will wait for the semaphores\n", realTime);
        :: (string == P1T2_pok_sem_wait_ret) -> printf("[%d] P1T2: pok_sem_wait ret = %d\n", realTime, param);
        :: (string == P2T1_begin_of_task) -> printf("[%d] P2T1: begin of task\n", realTime);
        :: else -> skip
    fi
}


//interrupts processing model
active proctype InterruptHandler() {
short intNum;

do 
:: true ->  {
    InterruptController ? intNum;
    atomic {
    int ret = 0; //stub
    int id = currentContext.r0;
    int param1 = currentContext.r1;
    int param2 = currentContext.r2;
    interruptsDisabled = 1; //stop the scheduler
    saveCurrentContext();
    if 
        :: (intNum == POK_INTERRUPT) -> { //we react on only one interrupt
            if
                :: (id == syscall_sem_v) -> sem_signal(param1);
                :: (id == syscall_sem_p) -> sem_wait(param1);
                :: (id == syscall_delay) -> sleep(param1);
                :: (id == syscall_printf) -> print(param1, param2);
                :: else -> skip; //unknown syscall id
            fi
        }
        :: else -> skip;
    fi
    //restore current context
    restoreCurrentContext();
    interruptsDisabled = 0;
    InterruptRet ! ret;
    }
    }
od
}



//-------------------------------------------------------------------------------
// User code
//-------------------------------------------------------------------------------


//user's thread logic
//model: see examples/semaphores in pok repo
proctype threadP1T1(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> 
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { pok_print(P1T1_I_will_signal_semaphores); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_signal(sid, currentContext.r0); currentContext.IP++; }
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { pok_printf(P1T1_pok_sem_signal_ret, currentContext.r0); currentContext.IP++; }
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_delay(2000); currentContext.IP = 0; /* inf loop */ }
                    ::else -> skip;
                    fi
                fi
            fi
        fi 
     }
 :: else -> break;
od
}


proctype threadP1T2(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> 
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { pok_print(P1T2_I_will_wait_for_the_semaphores); currentContext.IP++; }
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_sem_wait(sid, currentContext.r0); currentContext.IP++; }
            ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 2) -> 
                { pok_printf(P1T2_pok_sem_wait_ret, currentContext.r0); currentContext.IP++;}
                ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 3) -> 
                    { pok_sem_wait(sid, currentContext.r0); currentContext.IP++; }
                    ::else -> if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 4) -> 
                        { pok_printf(P1T2_pok_sem_wait_ret, currentContext.r0); currentContext.IP++;}
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
  :: else -> break;
  od
}

proctype threadP2T1(short myPartId; short myThreadId) {
do
 :: (osLive == 1) -> 
     atomic {
     if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 0) -> 
     { pok_print(P2T1_begin_of_task); currentContext.IP++;}
        :: else -> 
            if ::(currentPartition == myPartId && currentThread == myThreadId && currentContext.IP == 1) -> 
            { pok_delay(5000); currentContext.IP = 0; }
            ::else ->  skip;   
            fi
        fi 
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
    partitions[0].schedulingStrategy = sched_part_rr_strategy;
    partitions[1].timeSpacePerPartition = 100;
    partitions[1].schedulingStrategy = sched_part_rr_strategy;

    createThread(0, 0);
    partitions[0].threads[0].timeSpacePerThread = 50;
    createThread(0, 1);
    partitions[0].threads[1].timeSpacePerThread = 50;
    createThread(1, 0);
    partitions[1].threads[0].timeSpacePerThread = 100;
    createThread(1, 1);
    partitions[1].threads[1].timeSpacePerThread = 0;
    partitions[1].threads[1].isLocked = 1;
    partitions[0].mainThread = 0;
    partitions[0].mainThread = 0;

    semaphores[0].currentCount = 50;
    semaphores[0].maxCount = 50;
    semaphores[0].threadAwaitingCount = 0;
  
    currentThread = IDLE_THREAD;
    currentPartition = PARTITION1;

    //run scheduler instance
    runSched();

    //run all the threads
    run threadP1T1(PARTITION1, 0);
    run threadP1T2(PARTITION1, 1);
    run threadP2T1(PARTITION2, 0);
    
}

//LTL predicates to check
//to be: 
// - memory checks
// - "pointer verify" model like in pok
// - semaphores
// - scheduling: times, fairly? 

//demo formulas

//check correct lock count since we have a strong constraint of the size of locking threads list
//for this type of the system only one thread can be locked on semaphore waiting
ltl correct_lock_count {[] (semaphores[0].threadAwaitingCount < 2)}

//no violations to access a pointer from a wrong memory partition
ltl pointers_partitions {[] (pointersOk == 1)}

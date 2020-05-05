/*
@brief PoET leader selection demo (for my master student)
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

#define P 5 /* number of processes in the model */

chan SGX = [0] of {short}; /* channel for random number generation */

mtype = {STATE_INIT, STATE_GEN, STATE_WAITING, STATE_MINEBLOCK, STATE_NOMINEBLOCK}; /*type for state*/

mtype state = STATE_INIT; /* global network state */
mtype procStates[P]; /* status of network nodes */
short procTimes[P]; /* the waiting time of nodes */

bool isGenerating = false; /* during block generation will be true */
byte generator; /* process-generator of the last block */

short Nblock = 0; /* number of blocks */

ltl willBeGenerated { <> (Nblock > 0) };

/*
For the verification of the protocol model, we create a requirement in the form of a temporal logic formula. 
In this case, it is "always that when we have generated a block and selected the L process as a leader, it has the property of minimum waiting 
time and it only has the state of block generation, and all other processes have the state of detection that the block was 
generated by someone other". The rule can be expressed in a logical form: 
*/
ltl checkFor0 { [] (isGenerating && (generator == 0) ->  procTimes[0] <= procTimes[1] && procTimes[0] <= procTimes[2] && procTimes[0] <= procTimes[3] && procTimes[0] <= procTimes[4] 
&& procStates[0]==STATE_MINEBLOCK && procStates[1]==STATE_NOMINEBLOCK && procStates[2]==STATE_NOMINEBLOCK && procStates[3]==STATE_NOMINEBLOCK && procStates[4]==STATE_NOMINEBLOCK)
};



active proctype gen() {  
byte buf;
short nr;	
do
:: {
    SGX ? buf;
	do /* non-detereministic: */
        :: (nr < 32768) -> nr++; /* increment */
        :: (nr > 0) -> nr--;	 /* decrement */	
	    :: break /* or exit */
	od;
    SGX ! nr;
}
od
}


proctype PoET(byte N) {
do
:: {
    /* waiting for a next iteration -- for state STATE_INIT */
        do  
            :: (state == STATE_INIT) -> break;
            :: else -> skip;
        od

        procStates[N] = STATE_GEN;
        /* generate a random number by asking it from the special process */
        short nr = 0;
        SGX ! 1;
        SGX ? nr;
        procTimes[N] = nr;
        printf("Process pid = %d  got nr = %d \n", N, nr);
        procStates[N] = STATE_WAITING;

        /* simulate the waiting: in the loop we decrement count */
        short count = nr;
        do 
            :: (count >= 0) -> count--; 
            :: else -> break;
        od

        /* after the waiting we  check for the block present and try to generate it */
        bool ifOurBlock = false;
        if 
            :: (state != STATE_MINEBLOCK) -> {
                /* if not, we are the first and we name us the leader */
                atomic {
                    state = STATE_MINEBLOCK; /* we mark the the block is mined */
                    procStates[N] = STATE_MINEBLOCK; /* mark that the block is ours */
                    ifOurBlock = true; 
                }
                if  /*otherwise the block is not ours */
                    ::(procStates[N] != STATE_MINEBLOCK) -> 
                    procStates[N] = STATE_NOMINEBLOCK; 
                    ::else -> skip;
                fi
            }
            :: else -> procStates[N] = STATE_NOMINEBLOCK;
        fi
        /* next there is the logic of block generation */
        if 
            :: ifOurBlock == true -> {
                /* we think we are the leader - wait for other processes */
                do 
                :: {
                    count = P - 1;
                    short countReady = 0; 
                    short countLeaders = 0; 
                    do
                        :: (count >= 0) -> {
                            if
                                /* calculate count of non-leader processes */
                                :: (procStates[count] == STATE_NOMINEBLOCK) || 
                                /* and also new processes */
                                (procStates[count] ==  STATE_INIT) -> {
                                    countReady++; 
                                }
                                /* count the leaders */
                                :: (procStates[count] == STATE_MINEBLOCK) -> 
                                countLeaders++;
                                :: else ->  skip;
                            fi
                            count--;
                        }
                        :: else -> break;
                    od
                    if :: (countReady == P - 1) ->  
                    /* normal state: I am the leader and there are no others */
                    {
                        isGenerating = true;
                        generator = N;
                        Nblock++;
                        printf("BLOCK %d generated by process %d! \n", Nblock, N);
                        isGenerating = false;
                        break;
                    }
                    :: (countLeaders != 1) -> { 
                    /* something wrong: more than one leader, reelection */
                        printf("REELECTION! \n");
                            break;
                    }
                    :: else -> skip;
                    fi
                } od
                /* initiate a new round */
                state = STATE_INIT;
                printf("NEW ROUND INITIATED BY %d \n", N);
            }
            ::else -> skip;
        fi
    }
od
} 



active proctype main() {
	state = STATE_WAITING;
	short count = P - 1;
	do
		:: (count >= 0) -> {
			procStates[count] = STATE_INIT;
            printf("Main: run process %d...\n", count);
			run PoET(count);
			count--;
	}
		:: else -> break;
	od
	state = STATE_INIT;
}



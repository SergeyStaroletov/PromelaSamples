// POET concensus model 
// (c) Sergey Staroletov, 2020

#define BLOCK_CLAIM_DELAY 1
#define INITIAL_WAIT_TIME 3000
#define KEY_BLOCK_CLAIM_LIMIT 250 
#define POPULATION_ESTIMATE_SAMPLE_SIZE 50
#define REGISTRATION_RETRY_DELAY 10 
#define SIGNUP_COMMIT_MAXIMUM_DELAY 10
#define TARGET_WAIT_TIME 20
#define ZTEST_MAXIMUM_WIN_DEVIATION 3075 //3.075*1000
#define ZTEST_MINIMUM_WIN_COUNT 3

#define P 5

mtype = {CONSENSUS_NOTIFY_BLOCK_NEW, CONSENSUS_NOTIFY_BLOCK_VALID, 
    CONSENSUS_NOTIFY_BLOCK_INVALID, CONSENSUS_NOTIFY_BLOCK_COMMIT,
    CONSENSUS_NOTIFY_PEER_CONNECTED, CONSENSUS_NOTIFY_PEER_DISCONNECTED,
    CONSENSUS_NOTIFY_PEER_MESSAGE};

chan Network = [0] of {int};

bool exit = false;

typedef StartupState {
    int chain_head;
    int peers[P];
    int local_peer_info;
}

inline engine() {
    printf("engine");
}

//message handlers
inline _handle_new_block() {
    printf("_handle_new_block");
}

inline _handle_valid_block() {
    printf("_handle_valid_block");
}

inline _handle_invalid_block() {
    printf("_handle_invalid_block");
}

inline _handle_committed_block() {
    printf("_handle_committed_block");
}

inline _handle_peer_msgs() {
    printf("_handle_peer_msgs");
}




active proctype main() {
    short i;
	for (i : 0 .. P - 1) {
		run main_engine(i)
	}
}



proctype main_engine(short N) {
    printf("main_engine");

    //register me
    
    //run receiver 
    run driver_loop(N);
    
    //run engine 
    engine();
}




proctype driver_loop(short N) {
    printf("driver_loop");
    do
        ::exit -> break;
        ::else -> {
            mtype msg;
            Network ? msg;
            if
                ::(msg == CONSENSUS_NOTIFY_BLOCK_NEW) -> _handle_new_block();
                ::(msg == CONSENSUS_NOTIFY_BLOCK_VALID) ->  _handle_valid_block();
                ::(msg == CONSENSUS_NOTIFY_BLOCK_INVALID) -> _handle_invalid_block();
                ::(msg == CONSENSUS_NOTIFY_BLOCK_COMMIT) -> _handle_committed_block();
                ::(msg == CONSENSUS_NOTIFY_PEER_CONNECTED) -> _handle_peer_msgs();
                ::(msg == CONSENSUS_NOTIFY_PEER_DISCONNECTED) -> _handle_peer_msgs();
                ::(msg == CONSENSUS_NOTIFY_PEER_MESSAGE) ->  _handle_peer_msgs();
                ::else -> skip;
            fi 
        }
    od


}
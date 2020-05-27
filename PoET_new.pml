
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

typedef StartupState {
    int chain_head;
    int peers[P];
    int local_peer_info;
}

active proctype main() {
    short i;
	for (i : 0 .. P - 1) {
		run main_engine(i)
	}
}

proctype main_engine(short N) {
    printf("main_engine");
}

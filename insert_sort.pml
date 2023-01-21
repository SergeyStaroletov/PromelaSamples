
#define MAXLEN 100
#define MIN 0
#define MAX 1000
int A[MAXLEN];

bool correct = true; //control variable

active proctype insert_sort() {
    int j, i, key, A_len; 

    select(A_len: 2 .. MAXLEN);
    printf("Generating an array with len = %d...\n", A_len);

    for (j: 0 .. A_len - 1) {
        select(key: MIN .. MAX);
        A[j] = key;
        printf("%d): %d\n", j, A[j]);
    }

    printf("Sorting...\n");
    for (j: 1 .. A_len - 1) {
        key = A[j];
        i = j - 1;
        do
            ::(i >= 0) && (A[i] > key) -> {
                A[i + 1] = A[i];
                i = i - 1;
            }
            ::else -> break;
        od;
        A[i + 1] = key;
    }

    printf("Result: \n");
    for (j: 0 .. A_len - 1) {
        printf("%d): %d\n", j, A[j]);
    }

    //verification

    int idx_to_check;
    //peak a random index in [0..len-1)
    select(idx_to_check: 0 .. A_len - 2);
    //check the rule of sorting
    correct = A[idx_to_check] <= A[idx_to_check + 1];
}

ltl {[]correct} //always correct


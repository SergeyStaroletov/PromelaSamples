#define MAXN 100


bool check = true;

//for a given n return if it is divisable by 7
inline alg_check7(n, rez) {
    do 
        ::(n > 7) -> {
            byte last_digit = n % 10;
            int new_n = n / 10;
            byte last_digit2 = last_digit * 2;
            n = new_n - last_digit2;
        }
        ::else -> break;
    od
    rez = (n == 0 || n == 7 || n == -7);
} 

active proctype div7 () {
    //select a random base
    int base;
    select(base: 1 .. MAXN);
    //guaranted that n is divisable by 7
    int n = base * 7;  
    printf("selected N = %d\n", n);
    int rez_true;
    alg_check7(n, rez_true); // result should be true
    check = rez_true;
    if 
        ::check -> printf("ok divisable\n");
        ::else -> printf("bug, non divisable\n"); 
    fi
    //now select guaranted that n is not divisable by 7
    byte one_six;
    select(one_six: 1 .. 6);
    n = base * 7 + one_six; //div by 7 + 1..6
    printf("selected new N = %d\n", n);
    int rez_false;
    alg_check7(n, rez_false);  // result should be false
    check = !rez_false;
    if 
        ::check -> printf("ok non divisable\n");
        ::else -> printf("bug, divisable\n"); 
    fi
}

ltl {[]check}


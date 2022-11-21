/*
@brief Verified GF2 manipulation
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

#define MAXPOL 200
#define LEN_SHORT 31*11
#define LEN_LONG 93*11

//arrays to use for results
byte R[MAXPOL];
byte P1[MAXPOL];
byte P2[MAXPOL];
byte RemResult[MAXPOL];


#define getBit(data, b) ((data[(b) / 8] >> ((b) % 8)) & 1)
#define setBit(data, b, x) data[(b) / 8] = data[(b) / 8] ^ ((-x ^ data[(b) / 8]) & (1 << ((b) % 8)))

int i; //global iterator, do not use nesting


#define print_telegram_part(res, res_deg) {\
    int mi = res_deg - 1;\
    do \
      ::(mi >= 0) -> { \
        printf("%d", getBit(res, mi)); \
        mi = mi - 1; \
      }\
      ::else -> break\
    od\
  }


//polinom lib
inline GF2Addition(RDegree, P1Degree, P2Degree) {
  //printf("add %d + %d \n", P1Degree, P2Degree);
  int max_degree = P1Degree;
  if 
    ::(P2Degree > P1Degree) -> max_degree = P2Degree
    ::else -> skip
  fi
  for (i : 0 .. (max_degree / 8 + 1)) {
    R[i] = 0;
  }
  if 
    ::(P1Degree == P2Degree) -> {
      i = P1Degree - 1;
      do
        ::(i >= 0) -> {
          setBit(R, i, (getBit(P1, i) + getBit(P2, i)) % 2);
          i = i - 1;
        }
        ::else -> break
      od
    }
    ::else -> skip
  fi
  if 
    ::(P1Degree > P2Degree) -> {
      i = P1Degree - 1;
      do
        ::(i >= P2Degree) -> {
          setBit(R, i, getBit(P1, i));
          i = i - 1;
        }
        ::else -> break
      od
      i = P2Degree - 1;
      do
        ::(i >= 0) -> {
          setBit(R, i, (getBit(P1, i) + getBit(P2, i)) % 2);
          i = i - 1;
        }
        ::else -> break
      od
    }
    ::else -> skip
  fi
  if 
    ::(P1Degree < P2Degree) -> {
      i = P2Degree - 1;
      do
        ::(i >= P1Degree) -> {
          setBit(R, i, getBit(P2, i));
          i = i - 1;
        }
        ::else -> break
      od
      i = P1Degree - 1;
      do
        ::(i >=0 ) -> {
          setBit(R, i, (getBit(P1, i) + getBit(P2, i)) % 2);
          i = i - 1;
        }
        ::else -> break
      od
    }
    ::else -> skip;
  fi
  RDegree = max_degree;
}


inline GF2Multiplication(RDegree, P1Degree, P2Degree) {
  //printf("mult deg %d x %d\n", P1Degree, P2Degree);
  int mydeg = P1Degree + P2Degree + 1;
  //fill with 0 all the unused data in polynoms
  for (i : 0 .. MAXPOL - 1) {
    R[i] = 0;
  }
  for (i: P1Degree .. MAXPOL*8 - 1) {
    setBit(P1, i, 0);
  }
  for (i: P2Degree .. MAXPOL*8 - 1) {
    setBit(P2, i, 0);
  }

  i = P1Degree - 1;
  do
    ::(i >= 0) -> {
      int j = P2Degree - 1;
      do
        ::(j >= 0) -> {
          setBit(R, (i + j), (getBit(R, (i + j)) + getBit(P1, i) * getBit(P2, j)) % 2);
          j = j - 1;
        }
        ::else -> break
      od
      i = i - 1;
    }
    ::else -> break
  od  
  //correct resulting degree
  int deg2 = mydeg - 1;
  do
    ::(deg2 > 0)&&(getBit(R, deg2) == 0) -> deg2 = deg2-1;
    ::else->break;
  od
  RDegree = deg2 + 1 ;
}



inline GF2Division(RDegree, RemResultDegree, P1Degree, P2Degree, rez) { 
  do //loop to use breaks as returns
    ::true -> {
      for (i : 0 .. (P1Degree / 8 + 1)) {
        RemResult[i] = P1[i];
      }    
      int rem_degree = P1Degree;
      int q_degree = P1Degree - P2Degree + 1;
      //find first not_null bit
      do 
        ::((P2Degree > 0) && (getBit(P2, P2Degree - 1) == 0)) -> {
          P2Degree = P2Degree - 1;
        }
        ::else -> break
      od
      //check nul
      if 
        ::(P2Degree == 1 && getBit(P2, P2Degree - 1) == 0) -> {
            printf("we 0 ");
            rez = false;
            break
        }
        ::else -> skip
      fi
      //quotient= R
      //check if B>A
      if 
        ::(P2Degree > P1Degree) -> {
          R[0] = 0;
          RDegree = 1;
          RemResultDegree = rem_degree;
          rez = true;
          break
        }
        ::else -> skip;
      fi
      //check if B>A again
      if 
        ::(P2Degree == P1Degree) -> {
          bool low = false;
          for (i : 0 .. P2Degree - 1)
          {
            if 
              ::(getBit(P2, i) > getBit(P1, i)) -> {
                low = true;
                break;
              }
              ::else -> skip;
            fi
          }
          if 
            ::low -> {
              R[0] = 0;
              RemResultDegree = rem_degree;
              rez = true;
              break
            }
            ::else -> skip;
          fi
        }
        ::else -> skip;
      fi
      for (i : 0 .. q_degree - 1) {
        int kk =  getBit(RemResult, rem_degree - i - 1) / getBit(P2, P2Degree - 1);
        setBit(R, q_degree - i - 1, kk);
        int j;
        for (j : 0 .. P2Degree - 1)
        {
            setBit(RemResult, rem_degree - i - j - 1,
                   (getBit(RemResult, rem_degree - i - j - 1) + kk * getBit(P2, P2Degree - j - 1)) % 2); 
        }
      }
      //correct leading zeros
      do 
        ::(q_degree > 0 && getBit(R, q_degree - 1) == 0) -> q_degree--;
        ::else -> break
      od
      RDegree = q_degree;
      do 
        ::(rem_degree > 0 && getBit(RemResult, rem_degree - 1) == 0) -> rem_degree--;
        ::else -> break
      od
      RemResultDegree = rem_degree;
      rez = true;
      break;    
    }
  od
     int  q_degree = RDegree;
      do 
        ::(q_degree > 0 && getBit(R, q_degree - 1) == 0) -> q_degree--;
        ::else -> break
      od
      RDegree = q_degree;
    int rem_degree = RemResultDegree;
      do 
        ::(rem_degree > 0 && getBit(RemResult, rem_degree - 1) == 0) -> rem_degree--;
        ::else -> break
      od
      RemResultDegree = rem_degree;
}


//http://www.sharetechnote.com/html/Handbook_Communication_GF2.html
proctype test_from_handbook() {
  int p1deg = 10;
  int p2deg = 10; 
  int rdeg = 0;
  int remdeg = 0;
  int res = 0;
  setBit(P1, 0, 0);
  setBit(P1, 1, 1);
  setBit(P1, 2, 0);
  setBit(P1, 3, 1);
  p1deg = 4;
  setBit(P2, 0, 0);
  setBit(P2, 1, 1);
  setBit(P2, 2, 0);
  setBit(P2, 3, 0);
  p2deg = 4;
  printf("addition\n")
  GF2Addition(rdeg, p1deg, p2deg);
  print_telegram_part (R, rdeg);
  printf("\n");
  setBit(P1, 0, 1);
  setBit(P1, 1, 0);
  setBit(P1, 2, 1);
  setBit(P1, 3, 1);
  p1deg = 4;
  setBit(P2, 0, 1);
  setBit(P2, 1, 1);
  setBit(P2, 2, 0);
  setBit(P2, 3, 1);
  p2deg = 4;
  printf("mult\n")
  GF2Multiplication(rdeg, p1deg, p2deg);
  print_telegram_part (R, rdeg);
  printf("\n");

  setBit(P1, 0, 1);
  setBit(P1, 1, 0);
  setBit(P1, 2, 0);
  setBit(P1, 3, 1);
  setBit(P1, 4, 1);
  setBit(P1, 5, 0);
  setBit(P1, 6, 0);
  setBit(P1, 7, 1);
  setBit(P1, 8, 1);
  p1deg = 9;
  setBit(P2, 0, 1);
  setBit(P2, 1, 1);
  setBit(P2, 2, 0);
  setBit(P2, 3, 1);
  setBit(P2, 4, 0);
  setBit(P2, 5, 1);
  p2deg = 6;
  printf("div\n");
  GF2Division(rdeg, remdeg, p1deg, p2deg, res); 
  printf("rez\n");
  print_telegram_part (R, rdeg);
  printf("\nrem\n");
  print_telegram_part (RemResult, remdeg);
  printf("\n");
}

bool polyGood = true;

//active proctype verifypoly() {
active proctype verifypoly() {
  int mx = 10;//80;
  int idx = mx;
  int p1deg = mx;
  int p2deg = mx;
  int deg, remdeg, rdeg;
  bool res; //div ok/div by 0
  byte P1save[MAXPOL];
  byte P2save[MAXPOL];
  int p1degsave;
  int p2degsave;
  int iter;
    do
      ::!polyGood -> break;
      //change index
      ::(idx > 0) -> idx--;
      ::(idx < mx) -> idx++;
      //change degrees
      ::true -> p1deg = idx;
      ::true -> p2deg = idx;
      //change bit
      ::true -> setBit(P1, idx, 0); 
      ::true -> setBit(P2, idx, 0);
      ::true -> setBit(P1, idx, 1);
      ::true -> setBit(P2, idx, 1);
      ::p2deg > 0 && p1deg > p2deg -> {
        //guarantee the degrees
        if 
          ::p1deg > 0 -> setBit(P1, p1deg - 1, 1); 
          ::else -> skip;
        fi
        if 
          ::p2deg > 0 -> setBit(P2, p2deg - 1, 1);
          ::else -> skip;
        fi
        //save P1 P2
        for (iter : 0 .. p1deg / 8 + 1) {
          P1save[iter] = P1[iter];
        }
        p1degsave = p1deg;
        for (iter : 0 .. p2deg / 8 + 1) {
          P2save[iter] = P2[iter];
        }
        p2degsave = p2deg;

        printf("Go P1 %d / P2 %d...\n", p1deg, p2deg);
        printf("P1=")
        print_telegram_part(P1, p1deg);
        printf("\n");
        printf("P2=")
        print_telegram_part(P2, p2deg);
        printf("\n");

        //P1 / P2  => (R, RemResult)
        GF2Division(rdeg, remdeg, p1deg, p2deg, res); 

        printf("RDiv %d =", rdeg);
        print_telegram_part(R, rdeg);
        printf("\n");
        printf("RemDiv %d =", remdeg);
        print_telegram_part(RemResult, remdeg);
        printf("\n");
        if 
          ::res -> {
            //RemResult + R*P2 = P1 

            //save P1
            byte ideal[MAXPOL];
            for (iter : 0 .. p1deg / 8 + 1) {
              ideal[iter] = P1[iter];
            } 
            byte idealdeg = p1deg;
            //load R into P1
            for (iter : 0 .. rdeg / 8 + 1) {
              P1[iter] = R[iter];
            }
            p1deg = rdeg;
            //p2 is already in p2

            //r*p2
            GF2Multiplication(rdeg, p1deg, p2deg);
            
            printf("Mult %d =", rdeg);
            print_telegram_part(R, rdeg);
            printf("\n");

            //load R into P1
            for (iter : 0 .. rdeg / 8 + 1) {
              P1[iter] = R[iter];
            }
            p1deg = rdeg;
            //load Rem into P2
            for (iter : 0 .. remdeg / 8 + 1) {
              P2[iter] = RemResult[iter];
            }
            p2deg = remdeg
            //r*p2+rem
            GF2Addition(rdeg, p1deg, p2deg);

            //test : ideal == R
            printf("Conr %d =", rdeg);
            print_telegram_part(R, rdeg);
            printf("\n");

            if 
                :: (rdeg != idealdeg) -> {
                  polyGood = false;
                  printf ("wrong shape! %d vs %d\n",  rdeg, idealdeg);
                  break;
                }
                ::else->skip; 
              fi
            //check using getbit
            for (iter : 0 .. rdeg-1 ) {
              if 
                :: getBit(R, iter) != getBit(ideal,iter) -> {
                  polyGood = false;
                  printf ("bug in iter %d!\n", iter);
                }
                ::else->skip; 
              fi
            }
            if 
              ::!polyGood -> break;
              ::else -> skip
            fi
          } 
          ::else -> skip;
        fi
        //restore
        for (iter : 0 .. p1degsave / 8 + 1) {
          P1[iter] = P1save[iter];
        }
        p1deg = p1degsave;
        for (iter : 0 .. p1degsave / 8 + 1) {
          P2[iter] = P2save[iter];
        }
        p2deg = p2degsave;
      }
    od
}


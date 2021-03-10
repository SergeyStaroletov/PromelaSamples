/*
@brief Eurobalise encoder/decoder model
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

#define MAXPOL 200

#define getBit(data, b) ((data[(b) / 8] >> ((b) % 8)) & 1)
#define setBit(data, b, x) data[(b) / 8] = data[(b) / 8] ^ ((-x ^ data[(b) / 8]) & (1 << ((b) % 8)))

byte R[MAXPOL];
byte P1[MAXPOL];
byte P2[MAXPOL];
byte RemResult[MAXPOL];

inline GF2Addition(RDegree, P1Degree, P2Degree) {
  int max_degree = P1Degree;
  if 
    ::(P2Degree > P1Degree) -> max_degree = P1Degree
    ::else -> skip
  fi
  int i;
  for (i : 0 .. (max_degree / 8 + 1)) {
    R[i] = 0;
  }
  if 
    ::(P1Degree == P2Degree) -> {
      i = P1Degree - 1;
      do
        ::(i >= 0) -> {
          printf("%d\n", i);
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


inline GF2Multiplication(RDegree, P1Degree,P2Degree) {
  int max = P1Degree + P2Degree;
  int i;
  for (i : 0 .. (max / 8 + 1)) {
    R[i] = 0;
  }
  i = P1Degree - 1;
  do
    ::(i >= 0) -> {
      int j = P2Degree - 1;
      do
        ::(j >= 0) -> {
          setBit(R, i + j, (getBit(R, i + j) + getBit(P1, i) * getBit(P2, j)) % 2);
          j = j - 1;
        }
        ::else -> break
      od
      i = i - 1;
    }
    ::else -> break
  od  
  RDegree = max;
}



inline GF2Division(RDegree, RemResultDegree, P1Degree, P2Degree, result) { 
  int i;
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
            result = false;
            break
        }
        ::else -> skip
      fi
      //quotient= R
      ///
      //check if B>A
      if 
        ::(P2Degree > P1Degree) -> {
          R[0] = 0;
          RDegree = 1;
          RemResultDegree = rem_degree;
          result = true;
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
              result = true;
              break
            }
            ::else -> skip;
          fi
        }
        ::else -> skip;
      fi
      for (i : 0 .. q_degree - 1) {
        int k =  getBit(RemResult, rem_degree - i - 1) / getBit(P2, P2Degree - 1);
        setBit(R, q_degree - i - 1, k);
        int j;
        for (j : 0 .. P2Degree - 1)
        {
            setBit(RemResult, rem_degree - i - j - 1,
                   (getBit(RemResult, rem_degree - i - j - 1) + k * getBit(P2, P2Degree - j - 1)) % 2); 
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
      result = true;
      break;    
    }
  od
}

#define print_telegram_part(res, res_deg) {\
    int i = res_deg - 1;\
    do \
      ::(i >= 0) -> { \
        printf("%d", getBit(res, i)); \
        i = i - 1; \
      }\
      ::else -> break\
    od\
  }



active proctype main() {

  int p1deg = 10;
  int p2deg = 10; 
  int rdeg = 0;
  int remdeg = 0;
  int res = 0;
  setBit(P1, 10, 1);
  print_telegram_part (P1, 100);

  GF2Addition(rdeg, p1deg, p2deg);
  GF2Multiplication(rdeg, p1deg, p2deg);
  GF2Division(rdeg, remdeg, p1deg, p2deg, res); 
}
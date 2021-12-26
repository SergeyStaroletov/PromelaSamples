/*
@brief Eurobalise encoder/decoder model based on the official spec
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

#define MAXPOL 200

#define LEN_SHORT 31*11
#define LEN_LONG 93*11

#define getBit(data, b) ((data[(b) / 8] >> ((b) % 8)) & 1)
#define setBit(data, b, x) data[(b) / 8] = data[(b) / 8] ^ ((-x ^ data[(b) / 8]) & (1 << ((b) % 8)))

short words11 [1024] = {
    00101, 00102, 00103, 00104, 00105, 00106, 00107, 00110, 00111, 00112,
    00113, 00114, 00115, 00116, 00117, 00120, 00121, 00122, 00123, 00124,
    00125, 00126, 00127, 00130, 00131, 00132, 00133, 00134, 00135, 00141,
    00142, 00143, 00144, 00145, 00146, 00147, 00150, 00151, 00152, 00153,
    00154, 00155, 00156, 00157, 00160, 00161, 00162, 00163, 00164, 00165,
    00166, 00167, 00170, 00171, 00172, 00173, 00174, 00175, 00176, 00201,
    00206, 00211, 00214, 00216, 00217, 00220, 00222, 00223, 00224, 00225,
    00226, 00231, 00233, 00244, 00245, 00246, 00253, 00257, 00260, 00261,
    00272, 00273, 00274, 00275, 00276, 00301, 00303, 00315, 00317, 00320,
    00321, 00332, 00334, 00341, 00342, 00343, 00344, 00346, 00352, 00353,
    00357, 00360, 00374, 00376, 00401, 00403, 00404, 00405, 00406, 00407,
    00410, 00411, 00412, 00413, 00416, 00417, 00420, 00424, 00425, 00426,
    00427, 00432, 00433, 00442, 00443, 00445, 00456, 00457, 00460, 00461,
    00464, 00465, 00470, 00471, 00472, 00474, 00475, 00476, 00501, 00502,
    00503, 00504, 00505, 00506, 00507, 00516, 00517, 00520, 00521, 00522,
    00523, 00524, 00525, 00530, 00531, 00532, 00533, 00534, 00535, 00544,
    00545, 00546, 00547, 00550, 00551, 00552, 00553, 00554, 00555, 00556,
    00557, 00560, 00561, 00562, 00563, 00571, 00573, 00576, 00601, 00602,
    00604, 00605, 00610, 00611, 00612, 00613, 00614, 00615, 00616, 00617,
    00620, 00621, 00622, 00623, 00624, 00625, 00626, 00627, 00630, 00634,
    00635, 00644, 00645, 00646, 00647, 00650, 00651, 00652, 00653, 00654,
    00655, 00656, 00657, 00660, 00661, 00662, 00663, 00666, 00667, 00672,
    00674, 00675, 00676, 00701, 00712, 00713, 00716, 00717, 00720, 00721,
    00722, 00723, 00730, 00731, 00732, 00733, 00734, 00735, 00742, 00743,
    00744, 00745, 00746, 00747, 00750, 00751, 00752, 00753, 00754, 00755,
    00756, 00757, 00760, 00761, 00764, 00765, 00766, 00767, 00772, 00773,
    00776, 01001, 01004, 01005, 01016, 01017, 01020, 01021, 01022, 01023,
    01024, 01025, 01030, 01031, 01032, 01033, 01034, 01035, 01043, 01044,
    01045, 01046, 01047, 01054, 01057, 01060, 01061, 01062, 01075, 01076,
    01101, 01102, 01103, 01110, 01114, 01115, 01116, 01117, 01120, 01121,
    01122, 01123, 01124, 01125, 01126, 01127, 01130, 01131, 01132, 01133,
    01142, 01143, 01144, 01145, 01146, 01147, 01151, 01152, 01153, 01154,
    01155, 01156, 01157, 01160, 01164, 01166, 01167, 01176, 01201, 01214,
    01217, 01220, 01221, 01222, 01223, 01224, 01225, 01226, 01227, 01230,
    01231, 01232, 01233, 01243, 01244, 01245, 01253, 01254, 01255, 01256,
    01257, 01260, 01261, 01272, 01273, 01274, 01275, 01276, 01301, 01302,
    01303, 01305, 01306, 01307, 01317, 01320, 01321, 01332, 01334, 01335,
    01342, 01343, 01344, 01345, 01350, 01351, 01352, 01353, 01355, 01356,
    01357, 01360, 01361, 01364, 01365, 01370, 01371, 01372, 01373, 01374,
    01376, 01401, 01403, 01406, 01407, 01414, 01415, 01416, 01417, 01420,
    01424, 01425, 01431, 01433, 01434, 01435, 01443, 01445, 01456, 01457,
    01460, 01462, 01474, 01475, 01476, 01501, 01502, 01503, 01504, 01505,
    01516, 01517, 01520, 01524, 01532, 01533, 01544, 01546, 01550, 01551,
    01552, 01553, 01554, 01557, 01560, 01561, 01562, 01563, 01566, 01567,
    01576, 01601, 01603, 01604, 01605, 01606, 01607, 01610, 01611, 01612,
    01613, 01614, 01615, 01616, 01617, 01620, 01621, 01622, 01623, 01624,
    01625, 01626, 01630, 01631, 01632, 01633, 01635, 01643, 01644, 01645,
    01650, 01651, 01652, 01653, 01654, 01655, 01656, 01657, 01660, 01661,
    01672, 01674, 01675, 01676, 01701, 01720, 01744, 01745, 01746, 01747,
    01750, 01751, 01752, 01753, 01754, 01755, 01756, 01757, 01760, 01761,
    01762, 01763, 01764, 01765, 01766, 01767, 01770, 01771, 01772, 01773,
    01774, 01775, 02002, 02003, 02004, 02005, 02006, 02007, 02010, 02011,
    02012, 02013, 02014, 02015, 02016, 02017, 02020, 02021, 02022, 02023,
    02024, 02025, 02026, 02027, 02030, 02031, 02032, 02033, 02057, 02076,
    02101, 02102, 02103, 02105, 02116, 02117, 02120, 02121, 02122, 02123,
    02124, 02125, 02126, 02127, 02132, 02133, 02134, 02142, 02144, 02145,
    02146, 02147, 02151, 02152, 02153, 02154, 02155, 02156, 02157, 02160,
    02161, 02162, 02163, 02164, 02165, 02166, 02167, 02170, 02171, 02172,
    02173, 02174, 02176, 02201, 02210, 02211, 02214, 02215, 02216, 02217,
    02220, 02223, 02224, 02225, 02226, 02227, 02231, 02233, 02244, 02245,
    02253, 02257, 02260, 02261, 02272, 02273, 02274, 02275, 02276, 02301,
    02302, 02303, 02315, 02317, 02320, 02321, 02332, 02334, 02342, 02343,
    02344, 02346, 02352, 02353, 02357, 02360, 02361, 02362, 02363, 02370,
    02371, 02374, 02376, 02401, 02403, 02404, 02405, 02406, 02407, 02412,
    02413, 02416, 02417, 02420, 02421, 02422, 02424, 02425, 02426, 02427,
    02432, 02433, 02434, 02435, 02442, 02443, 02445, 02456, 02457, 02460,
    02470, 02471, 02472, 02474, 02475, 02476, 02501, 02502, 02503, 02504,
    02505, 02516, 02517, 02520, 02521, 02522, 02523, 02524, 02532, 02533,
    02534, 02544, 02545, 02546, 02547, 02550, 02551, 02552, 02553, 02554,
    02555, 02556, 02557, 02560, 02563, 02576, 02601, 02610, 02611, 02613,
    02617, 02620, 02621, 02622, 02623, 02624, 02625, 02626, 02630, 02631,
    02632, 02633, 02634, 02635, 02644, 02645, 02646, 02647, 02650, 02651,
    02652, 02653, 02654, 02655, 02656, 02657, 02660, 02661, 02662, 02663,
    02667, 02674, 02675, 02676, 02701, 02702, 02715, 02716, 02717, 02720,
    02723, 02730, 02731, 02732, 02733, 02734, 02742, 02743, 02744, 02745,
    02746, 02747, 02752, 02753, 02754, 02755, 02756, 02757, 02760, 02761,
    02772, 02773, 02776, 03001, 03004, 03005, 03010, 03011, 03012, 03013,
    03016, 03017, 03020, 03021, 03022, 03023, 03024, 03025, 03026, 03027,
    03030, 03031, 03032, 03033, 03034, 03035, 03042, 03043, 03044, 03045,
    03046, 03047, 03054, 03055, 03056, 03057, 03060, 03061, 03064, 03065,
    03076, 03101, 03102, 03103, 03105, 03110, 03111, 03114, 03115, 03116,
    03117, 03120, 03121, 03122, 03123, 03124, 03125, 03126, 03127, 03130,
    03131, 03132, 03133, 03142, 03143, 03147, 03150, 03151, 03152, 03153,
    03154, 03155, 03156, 03157, 03160, 03161, 03162, 03163, 03164, 03165,
    03166, 03167, 03172, 03173, 03175, 03176, 03201, 03204, 03206, 03214,
    03215, 03216, 03217, 03220, 03221, 03222, 03223, 03224, 03225, 03226,
    03227, 03230, 03231, 03232, 03233, 03242, 03243, 03244, 03245, 03246,
    03247, 03252, 03253, 03254, 03255, 03256, 03257, 03260, 03261, 03270,
    03271, 03272, 03273, 03274, 03275, 03276, 03301, 03302, 03303, 03305,
    03306, 03307, 03312, 03313, 03316, 03317, 03320, 03321, 03332, 03334,
    03335, 03344, 03345, 03350, 03351, 03352, 03353, 03357, 03360, 03361,
    03364, 03365, 03366, 03367, 03370, 03371, 03372, 03373, 03374, 03376,
    03401, 03403, 03417, 03420, 03424, 03425, 03431, 03433, 03434, 03435,
    03436, 03443, 03445, 03456, 03457, 03460, 03462, 03474, 03476, 03501,
    03502, 03503, 03504, 03505, 03516, 03517, 03520, 03524, 03531, 03532,
    03533, 03544, 03546, 03551, 03552, 03553, 03554, 03555, 03557, 03560,
    03561, 03563, 03566, 03571, 03576, 03601, 03602, 03603, 03604, 03605,
    03606, 03607, 03610, 03611, 03612, 03613, 03614, 03615, 03616, 03617,
    03620, 03621, 03622, 03623, 03624, 03625, 03626, 03627, 03630, 03631,
    03632, 03633, 03634, 03635, 03636, 03642, 03643, 03644, 03645, 03646,
    03647, 03650, 03651, 03652, 03653, 03654, 03655, 03656, 03657, 03660,
    03661, 03662, 03663, 03664, 03665, 03666, 03667, 03670, 03671, 03672,
    03673, 03674, 03675, 03676
};


//arrays to use for results
byte R[MAXPOL];
byte P1[MAXPOL];
byte P2[MAXPOL];
byte RemResult[MAXPOL];

int i; //global iterator, do not use nesting

//polinom lib
inline GF2Addition(RDegree, P1Degree, P2Degree) {
  int max_degree = P1Degree;
  if 
    ::(P2Degree > P1Degree) -> max_degree = P1Degree
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
  int max = P1Degree + P2Degree;
  for (i : 0 .. (max / 8 + 1)) {
    R[i] = 0;
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
  RDegree = max;
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
}

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

#define print_telegram_full(res, res_len) {\
    int mmi = res_len - 1;\
    do\
      ::(mmi >= 110) -> {\
         printf("%d", getBit(res, mmi));\
        mmi = mmi - 1;\
      }\
      ::else -> break\
    od;\
    printf(":");\
    mmi = 109;\
    do\
      ::(mmi >= 107) -> {\
        printf("%d", getBit(res, mmi));\
        mmi = mmi - 1;\
      }\
      ::else -> break;\
    od;\
    printf(":");\
    mmi = 106;\
    do\
      ::(mmi >= 95) -> {\
        printf("%d", getBit(res, mmi));\
        mmi = mmi - 1;\
      }\
      ::else -> break;\
    od;\
    printf(":");\
    mmi = 94;\
    do\
      ::(mmi >= 85) -> {\
        printf("%d", getBit(res, mmi));\
        mmi = mmi - 1;\
      }\
      ::else -> break;\
    od;\
    printf(":");\
    mmi = 84;\
    do\
      ::(mmi >= 0) -> {\
        printf("%d", getBit(res, mmi));\
        mmi = mmi - 1;\
      }\
      ::else -> break;\
    od; \
    printf("\n");\
}

//macro to iterate over bits
int currentBitReq = 0;
int currentNumber = 0;
int currentBit = 0;

#define getNextBit(data, res) {\
  int ret = (data[currentNumber] >> currentBitReq) & 1;\
  currentBitReq = currentBitReq + 1;\
  if \
    ::(currentBitReq == 8) -> {\
      currentBitReq = 0;\
      currentNumber = currentNumber + 1;\
    }\
    ::else -> skip;\
  fi;\
  res = ret;\
}

//result vector
byte result[MAXPOL];
//source data vector
byte from[MAXPOL] = {1,2,3,4,5,5,4,3,2,1};
bool isOk;


inline encodeOne(resultLen, originalLen) {
  bool ok = false;
  //loop through all the bits of 2^12 for sb
  short sb_state = 2001;
  //loop through all the bits of 2^10 for esb
  short esb_state = 99;
  {
    int m;
    if 
      ::(resultLen == LEN_LONG) -> m = 830;
      ::else -> m = 210
    fi
    int k = m / 10;
    short U[83];
    //int i = 0;
    for (i : 0 .. (resultLen / 8 + 1)) {
      result[i] = 0;
    }
    for (i : 0 .. originalLen) {
      result[i] = from[i];
    }
    printf("original:\n");
    print_telegram_part(result, resultLen);
    //for iteration
    currentBitReq = 0;
    currentNumber = 0;
    currentBit = 0;
    //collect k 10-bit words
    int w;
    for (w : 0 .. k) {
      short word = 0;
      int pow2 = 1;
      for (i : 0 .. 9) {
        short bitt;
        getNextBit(result, bitt)
        word = word + bitt * pow2;
        pow2 = pow2 << 1;
      }
      U[w] = word;
    }
    //change U[k];
    short uk = 0;
    for (i : 0 .. k) {
      uk = (uk + U[i]) % 1024;
    }
    U[k - 1] = uk;
    printf("\nU:\n");
    i = k - 1;
    do
      ::(i >= 0) -> {
        short printMe[2];
        printMe[0] = U[i];
        printMe[1] = U[i + 1]; //0..9 bit = 2 byte 
        print_telegram_part(printMe, 10);
        printf (" ");
        i  = i - 1;
      } 
      ::else -> break;
    od
    printf("\n");
    //now form some result bits
    //extra shaping bits (esb)
    int ESB = esb_state;
    for (i : 85 .. 94) {
      int bitt = (ESB) & 1;
      setBit(result, i, bitt);
      ESB = ESB  >> 1;
    }
    //control bits (cb)
    setBit(result, 109, 0);
    setBit(result, 108, 0);
    setBit(result, 107, 1);
    //12 scrambling bits
    printf("12 scrambling bits\n");
    int B = 0;
    int SB = sb_state;
    for (i : 95 .. 106) {
      int bitt = (SB) & 1;
      setBit(result, i, bitt);
      SB = SB >> 1;
    }
    B = sb_state;
    printf("B = %d\n", B);
    int S = (2801775573 * B) % 4294967296; //TODO check usingned
    printf("S = %u\n", S);
    //scrambling
    //https://ru.wikipedia.org/wiki/%D0%A0%D0%B5%D0%B3%D0%B8%D1%81%D1%82%D1%80_%D1%81%D0%B4%D0%B2%D0%B8%D0%B3%D0%B0_%D1%81_%D0%BB%D0%B8%D0%BD%D0%B5%D0%B9%D0%BD%D0%BE%D0%B9_%D0%BE%D0%B1%D1%80%D0%B0%D1%82%D0%BD%D0%BE%D0%B9_%D1%81%D0%B2%D1%8F%D0%B7%D1%8C%D1%8E
    //https://stackoverflow.com/questions/16891655/galois-lfsr-explanation-of-code
    int u = 0;
    int shift = S; //should BE UNSIGNED 
    //h = 11110101000000000000000000000001 = F5000001
    int toggle =  4110417921; //0xF5000001; //TODO: unsigned check
    for (i : 0 .. k - 1) {
      int bb;
      for (bb : 0 .. 9) {
        //m-1 clocks
        byte temp[2];
        temp[0] = U[i];
        temp[1] = U[i+1];
        // get the next user bit
        byte bitt = getBit(temp, bb);
        //most significant bit
        byte msb = (shift >> 31) & 1; //????
        //output = input xor msb(shift)
        setBit(temp, bb, (bitt ^ msb));
        U[i] = temp[0];
        U[i+1] = temp[1];
        //shift
        shift = shift << 1;
        //apply h
        if 
          ::(bitt > 0) -> shift = shift ^ toggle;
          ::else -> skip
        fi
      }
    }
    printf("\n After scrambling:\n");
    i = k - 1;
    do
      ::(i >= 0) -> {
        short printMe[2];
        printMe[0] = U[i];
        printMe[1] = U[i + 1]; //0..9 bit = 2 byte 
        print_telegram_part(printMe, 10);
        printf (" ");
      }
      ::else -> break;
    od
    //substitution
    for (i : 0 .. k - 1) {
      U[i] = words11[U[i]];
    }
    printf("\nU11:\n");
    i = k - 1;
    do
      ::(i >= 0) -> {
        short printMe[2];
        printMe[0] = U[i];
        printMe[1] = U[i + 1]; //0..10 bit = 2 byte 
        print_telegram_part(printMe, 11);
        printf (" ");
      }
      ::else -> break;
    od
    //from bit 110 there is the user data, just set in from the U array
      int bit_in_result = 110;
        for (i : 0 .. k - 1) {
          int bb;
          for (bb : 0 .. 10) {
            short printMe[2];
            printMe[0] = U[i];
            printMe[1] = U[i + 1];
            byte bitt = getBit(printMe, bb);
            setBit(result, bit_in_result, bitt);
            bit_in_result = bit_in_result + 1;
          }
      }
      //calculating checksum
      //fl = 11011011111 deg 10
      //gl = 101110001000 01110011100110100111101000101110 11010101001000111011101000010011 deg 75
      byte fl[2] = {223, 6};//{0x6DF};
      byte gl[10] = {19,186,35,213, 46,122,154,115, 136,11} ;//{0xD523BA13, 0x739A7A2E, 0xB88}; 
      //fs = 10110101011
      //gs = 100111110111 10010000110000101111111011110111 11001010010010100011110001001011 deg 75
      byte fs[2] = {171, 5};// {0x5AB};
      byte gs[10] = {75,60,74,202, 247,254,194,144, 247,9}; //{0xCA 4A 3C 4B, 0x90 C2 FE F7, 0x9F7};
      int fg_degree;
      int rem_deg;
      int div_deg;
      int crc_deg;
      //for division we need an array with continous data, for the first version-just copy it
      byte data_to_sign[MAXPOL];
      int bb = 0;
      for (i : 85 .. resultLen - 1) {
          setBit(data_to_sign, bb, getBit(result, i));
          bb++;
      }
      // crc = reminder(all_data ploynom f * g ) + g
      if 
        ::(resultLen == LEN_LONG) -> {
          short data_size = 1023 - 85;
          //prepare inputs
          for (i : 0 .. 1) {
            P1[i] = fl[i];
          }
          for (i : 0 .. (75 / 8 + 1)) {
            P2[i] = gl[i];
          }
          //mult, result in R
          GF2Multiplication(fg_degree, 10, 75);
          //copy resut to P2
          for (i : 0 .. (fg_degree / 8 + 1)) {
            P2[i] = R[i];
          }
          //copy data to P1
          for (i : 0 .. (data_size / 8 + 1)) {
            P1[i] = data_to_sign[i];
          }
          //div and get the reminder
          GF2Division(div_deg, rem_deg, data_size, fg_degree, isOk);
          //copy result to P1
          for (i : 0 .. (rem_deg / 8 + 1)) {
            P1[i] = RemResult[i];
          }
          //copy gl to P2
          for (i : 0 .. (75 / 8 + 1)) {
            P2[i] = gl[i];
          }
          //add
          GF2Addition(crc_deg, rem_deg, 75);
          //result will we in R
        } 
        ::else -> {//LEN_SHORT
          short data_size = 403 - 85;
          //prepare inputs
          for (i : 0 .. 1) {
            P1[i] = fs[i];
          }
          for (i : 0 .. (75 / 8 + 1)) {
            P2[i] = gs[i];
          }
          GF2Multiplication(fg_degree, 10, 75);
          //copy resut to P2
          for (i : 0 .. (fg_degree / 8 + 1)) {
            P2[i] = R[i];
          }
          //copy data to P1
          for (i : 0 .. (data_size / 8 + 1)) {
            P1[i] = data_to_sign[i];
          }
          //div and get the reminder
          GF2Division(div_deg, rem_deg, data_size, fg_degree, isOk);
          //copy result to P1
          for (i : 0 .. (rem_deg / 8 + 1)) {
            P1[i] = RemResult[i];
          }
          //copy gs to P2
          for (i : 0 .. (75 / 8 + 1)) {
            P2[i] = gs[i];
          }
          //add
          GF2Addition(crc_deg, rem_deg, 75);
          //result will we in R
        }
      fi
      //set 0..84 bit in result to crc86
      for (i : 0 .. 84) {
        setBit(result, i, getBit(R, i));
      }
      //change to static arrays in future
      printf("\nresult telegram: \n");
      print_telegram_full(result, resultLen);
      //TODO
      //ok = checkCandidate(result, resultLen);
    }
}


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
  //http://www.sharetechnote.com/html/Handbook_Communication_GF2.html
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

  //encodeOne(LEN_LONG, 10);
}

bool polyGood = true;

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
    ::true -> {
      //guarantee the degrees
      setBit(P1, p1deg, 1); 
      setBit(P2, p2deg, 1);
      //save P1 P2
      for (iter : 0 .. p1deg / 8 + 1) {
        P1save[iter] = P1[iter];
      }
      p1degsave = p1deg;
      for (iter : 0 .. p2deg / 8 + 1) {
        P2save[iter] = P2[iter];
      }
      p2degsave = p2deg;

      printf("Go P1 %d P2 %d...\n", p1deg, p2deg);
      //P1 / P2  => (R, RemResult)
      GF2Division(rdeg, remdeg, p1deg, p2deg, res); 
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

          if 
              :: (rdeg != idealdeg) -> {
                polyGood = false;
                printf ("wrong shape! %d vs %d\n",  rdeg, idealdeg);
              }
              ::else->skip; 
            fi

          for (iter : 0 .. rdeg / 8 + 1) {
            if 
              :: (R[iter] != ideal[iter]) -> {
                polyGood = false;
                printf ("bug!\n");
              }
              ::else->skip; 
            fi
          }
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

ltl foreverPoly {[] polyGood}
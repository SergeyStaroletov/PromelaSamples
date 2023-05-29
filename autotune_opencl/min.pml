/*
The model of execution of an abstract kernel on an abstract OpenCL platform intended for min calculation; 
** several devices, several units, several processing elements ** 
@author Natalia Garanina natta.garanina@gmail.com https://www.researchgate.net/profile/Natalia-Garanina
@conference LOPSTR-2022
@license GNU GPL
*/

inline min(a, b) {
 atomic { 
	if 
		:: a > b -> a = b;
		:: else -> skip;
	fi 
 }
}

// service vars
byte NRP_work = 0;	// the number of working running processing elements
byte NWD = 0;		// number of work devices
byte NWU = 0;		// number of work units
byte NWE = 0;		// number of work elements
byte allNWE = 0;	// number of all work elements
int time = 0;
bool FIN = false;
mtype : action = { done, stop, go, gowg, eoi, neoi, eow };
#define Tmin 10

// tuning parameters
int WG = 0;			// the size of the workgroup 
int WGs = 0;		// the number of the workgroups 
int TS = 0; 		// the tile size 
//int IC = 0;			// the number of kernel iteration 


// hardware parameters
#define NP 4		// 2^m -- the number of processing elements per unit --- COREs -- 
#define NU 1		// the number of units per device --- SMs
#define ND 1		// the number of devices --- GPCs 
#define GMT 4 		// the time of computations using the global memory
#define LM 8		// the size of local memory
byte loc[LM * NU]	// local memory 

// input 
#define n 4			// size = 2^n -- data size
#define size 16 	// the size of the input data
//byte size = 1 << n; 	// the size of the input data
byte glob[size];	// input data -- array of integers -- global memory



active proctype main() { 

byte i;

  //  DATA 
  for (i : 0 .. size-1)  { glob[i] = size - i }
  for (i : 0 .. LM*NU-1) { loc[i] = 255 }
  
  // WG selection
  select ( i : 2 .. n-1 );  
  WG = size >> (n - i); // Thread block = several warps
  // Tile size selection
  select ( i : 1 .. n-1 ); 
  TS = size >> (n - i);
  TS = (WG*TS > size -> size / WG : TS); 
  

  WGs = size / (WG * TS); 						// the number of working groups
  NWD = ( WGs <= NU * ND -> (WGs / NU) : ND ); 	// the number of working devices 
  NWD = (WGs / NU -> NWD : 1); 				// if WGs <= NU 
  NWU = ( WGs <= NU -> WGs : NU ); 			// the number of working units
  NWE = ( WG <= NP -> WG : NP); 			// the number of working elements
  allNWE = NWE * NWU * NWD;  
  //IC = size/(NP*WGs*TS)						// the number of kernel iteration 

  atomic{ run host(); run clock(); }
}


inline work_step() {
 atomic { cur_time = time;
	  NRP_work++;
	  time == cur_time + 1; 
	}
}


inline long_work (fct) {
    do  
    :: time > start_time + fct * TS -> break;
    :: else ->  work_step()
    od;
}


proctype pex (byte me; byte mu; chan pex_u; chan u_pex) { 

int start_time = 0;
int cur_time = 0;
byte shift; 	// shift in global memory
byte i; 		
byte iter;
byte nwg;
byte lid;
byte mymem = me + mu * NP; // my place in local memory

do // 89
	:: 	u_pex ? nwg, gowg ->
		do 
		:: u_pex ? iter, go ->
			atomic{ 
				start_time = time;
				cur_time = time;
			}
			lid = (WG > NP -> me + iter : me);
			shift = (WG > NP -> TS * (nwg * WG + me + iter * NP) : TS * (nwg * WG + lid));
			for ( i : 0 .. TS-1) { 	
				printf("In %d: glob[%d] = %d, i = %d\n", me, i + shift, glob[i + shift], i)
				printf("In %d: iter = %d, nwg = %d\n", me, iter, nwg)
				if 
				:: i + shift >= size -> break;
				:: else -> skip;
				fi
				min(loc[mymem], glob[ i + shift])	
				printf("In %d: loc[%d] = %d, i = %d\n", me, mymem, loc[mymem], i)
				long_work(GMT)
			}
			if 
			:: (iter+1) >= WG / NP -> pex_u ! eoi; break;
			:: else -> pex_u ! neoi;
			fi;
		od;
	:: 	u_pex ? 0, stop -> 
		if 
		:: me == 0 ->
			for (i : 1..(NWE-1)){ // REDUCE local
				min(loc[mu * NWE],loc[i + mu * NWE]) // access to local memory
				time++;
//				long_work(1)
			}
			// copy the result of this working group to global memory
			min(glob[0],loc[mu * NP]) 
			time = time + GMT;
			FIN = true;
//			start_time = time;
//			long_work(GMT)
		:: else -> skip;
		fi
		break;
od;
}


proctype unit (byte me; chan dev_u; chan u_dev) { 

 byte i;
 byte iter;
 byte nwg;
 byte num;
 mtype : action don;

 chan pex_u = [0] of {mtype : action}; 
 chan u_pex = [0] of {byte, mtype : action}; 
 
 xr pex_u;
 xs u_pex;
 
 atomic { for (i : 0..NWE-1) { run pex(i, me, pex_u, u_pex); } }
 do 
 :: dev_u ? nwg, go ->
		atomic{ for (i : 0..NWE-1) { u_pex ! nwg, gowg; u_pex ! 0, go; } }
		if 
		:: WG <= NP -> atomic{ for (i : 0..NWE-1) { pex_u ? eoi;} }
		:: else -> 
			iter = 1;
			num = 0;
			for (i : 0..WG-NP-1) { 
				atomic{ 
					pex_u ? don;
					if 
					:: don == eoi -> skip;
					:: else -> u_pex ! iter, go;
					fi
					num++;
					if 
					:: num >= NP -> iter++; num = 0;
					:: else -> skip;
					fi
				}
			}
			for (i : 0..(NWE-1)) { pex_u ? eoi; }
		fi;	
		u_dev ! done;
 :: dev_u ? 0, stop -> 
		atomic { for (i : 0..NWE-1) { u_pex ! 0, stop; } }
		break;
 od;
}


proctype device (chan d_hst; chan hst_d) { 
  
 byte i;
 byte num;
 byte nwg;

 chan dev_u = [0] of {byte, mtype : action};
 chan u_dev = [0] of {mtype : action};
 
 xr u_dev;
 xs dev_u;
 
 
  atomic { for (i : 0..NWU-1) { run unit (i, dev_u, u_dev); } } 
  do 
  :: hst_d ? go ->
		dev_u ! 0, go;
		if 
		:: WGs <= NU -> atomic { u_dev ? done; allNWE = allNWE - NWE; }
		:: else -> 
			nwg = 1;
			num = 0;				
			for (i : 0..WGs-2) {
					atomic { 
                                         u_dev ? done;
                                         dev_u ! nwg,go;
					 nwg++; num = 0;
					}
			}
                atomic { u_dev ? done; allNWE = allNWE - NWE; }
		fi;
        d_hst ! done;
 :: hst_d ? stop -> dev_u ! 0, stop;
			break;
 od;
}



proctype host () { 

 byte i = 0;

 chan d_hst = [0] of {mtype : action};
 chan hst_d = [0] of {mtype : action};
 
 xr d_hst; //remove?
 xs hst_d;
 
  FIN = false;
  run device (d_hst, hst_d);
  hst_d ! go;
  atomic { d_hst ? done; hst_d ! stop; }
//  FIN = true;
}


proctype clock (){ 
 do 
 :: FIN -> break;
 :: NRP_work == allNWE && allNWE != 0 -> atomic { NRP_work = 0; time++; }
 od;
}

// ltl p {[]!timeout } 

 ltl p {<> FIN } 

 ltl pp {[](FIN -> (<>(glob[0]==1)) )} 

 ltl p1 {[]!FIN } 

 ltl p2 {[]( FIN -> (time > Tmin)) } 

 // ltl NonTerm {[]!FIN } 

 // ltl OverTime {[]( FIN -> (time > Tmin)) } 
 

/*
The model of execution of an abstract kernel on an abstract OpenCL platform intended for auto-tuning; 
** several devices, several units, several processing elements ** 
@author Natalia Garanina natta.garanina@gmail.com https://www.researchgate.net/profile/Natalia-Garanina
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@conference LOPSTR-2022
@license GNU GPL
*/

// hardware parameters
byte NP = 0;		// the number of processing elements per unit
byte NU = 0;		// the number of units per device
byte ND = 0;		// the number of devices
byte GMT = 4; 		// the time of computations using the global memory

// tuning parameters
int WG = 0;			// the size of the workgroup 
int WGs = 0;		// the number of the workgroups 
int TS = 0; 		// the tile size 

// input 
int size = 0; 		//the size of the input data

// service vars
byte NRP_work = 0;	// the number of working running processing elements
byte NWD = 0;		// number of work devices
byte NWU = 0;		// number of work units
byte NWE = 0;		// number of work elements
byte allNWE = 0;	// number of all work elements
int time = 0;
int Tmin = 0;
bool FIN = false;
mtype : action = { done, stop, go };



inline work_step() {
  atomic { 
	  cur_time = time;
	  NRP_work++;
	  time == cur_time + 1;  //waiting
  }
}



inline long_work (fct) {
  do  
	  :: time > (start_time + fct * TS) -> break;
    :: else ->  work_step()
 od;
}



proctype pex (byte me; chan pex_b; chan b_pex; chan pex_u; chan u_pex) { 
  int start_time = 0;
  int cur_time = 0;
  byte i = 0;

  do 
    :: u_pex ? go ->
      atomic { 
        start_time = time;
        cur_time = time;
      }
      for (i : 0 .. size/TS-1) { 
        // access to global memory
        long_work(GMT)
        pex_b ! done;		 
        b_pex ? go;   // waiting for local co-workers  
        start_time = time;
            if 
              :: me % 2 -> long_work(1) // 'if' access to local memory
              :: else -> long_work(1)   // 'else' access to local memory
            fi;
        pex_b ! done;		 
        b_pex ? go;   // waiting for local co-workers  
      }
      // copy the result of this working item to global memory
      start_time = time;
      do  
        :: time > start_time + GMT -> break;
        :: else -> work_step()		
      od;
      pex_u ! done;  
    :: u_pex ? stop -> break;
  od;
}



proctype barrier (chan pex_b; chan b_pex) { 
  byte i = 0;
  do 
    :: pex_b ? done ->
      i = 1;
      do  
        :: i < NWE -> 
          atomic { 
            pex_b ? done;
            i++;
          }
        :: else -> break;
      od;	
      atomic { 
        for (i : 0 .. NWE-1) { 
          b_pex ! go; 
        } 
      } 
  :: pex_b ? stop -> break;
  od;
}



proctype unit (chan dev_u; chan u_dev) { 
  byte i = 0;
  chan pex_b = [0] of {mtype : action};
  chan b_pex = [0] of {mtype : action};
  chan pex_u = [0] of {mtype : action}; 
  chan u_pex = [0] of {mtype : action}; 
 
  run barrier (pex_b, b_pex);
  atomic {
    for (i : 0 .. NWE-1) { 
      run pex(i, pex_b, b_pex, pex_u, u_pex);
    }
  }
  do 
  :: dev_u ? go ->
      atomic {
        for (i : 0 .. NWE-1) {
          u_pex ! go;
        }
      }
      i = 0;
      if 
        :: WG <= NP -> 
          atomic {
            for (i : 0 .. NWE-1) {
              pex_u ? done;
            }
          }
        :: else -> 
          do 
            :: i < WG-NP -> 
              atomic { 
                pex_u ? done;
                u_pex ! go;
                i++; 
              }
            :: else -> break;
          od; 
        i = 0;
        do 
          :: i < NP -> 
            atomic { 
              pex_u ? done;
              i++; 
            }
          :: else -> break;
        od;
      fi;	
      u_dev ! done;
  :: dev_u ? stop -> 
      pex_b ! stop; 
      atomic { 
        for (i : 0 .. NWE-1) {
          u_pex ! stop;
        }
      }
      break;
  od;
}



proctype device (chan d_hst; chan hst_d) {   
 byte i = 0;
 chan dev_u = [0] of {mtype : action};
 chan u_dev = [0] of {mtype : action};

  atomic { 
    for (i : 0 .. NWU-1) { 
      run unit (dev_u, u_dev); 
    }
  } 
  do 
    :: hst_d ? go ->
      atomic { 
        for (i : 0 .. NWU-1) { 
          dev_u ! go;
        }
      }
      if 
        :: WGs <= NU -> 
          atomic {
            for (i : 0 .. NWU-1) { 
              u_dev ? done; 
              allNWE = allNWE - NWE; 
            }
          }					
        :: else ->
            i = 0;
            do 
              :: i < WGs - NU -> 
                atomic { 
                  u_dev ? done;
                  dev_u ! go;
                  i++; 
                }
              :: else -> break;
            od;
            i = 0;
            do 
              :: i < NU -> 
              atomic { 
                u_dev ? done;
                allNWE = allNWE - NWE;
                i++;
              }
              :: else -> break;
            od;	
      fi;
      d_hst ! done;
    :: hst_d ? stop -> 
      atomic { 
        for (i : 0 .. NWU-1) { 
          dev_u ! stop;
        }
      } 
      break;
  od;
}



proctype host () { 
  byte i = 0;
  chan d_hst = [0] of {mtype : action};
  chan hst_d = [0] of {mtype : action};
  
  FIN = false;
  atomic { 
    for (i : 0 .. NWD-1) {
      run device (d_hst, hst_d);
    }
  } 
  atomic { 
    for (i : 0 .. NWD-1) {
      hst_d ! go;
    }
  }
  if
    :: WGs <= NU*ND -> 
      atomic { 
        for (i : 0 .. NWD-1) {
          d_hst ? done; 
          hst_d ! stop;
        }
      }
    :: else -> 
      i = 0;
      do 
        :: i < (WGs / NU * ND) - ND -> 
          atomic { 
            d_hst ? done;
					  allNWE = allNWE + (NWE * NWU);
            hst_d ! go;
            i++; 
          }
        :: else -> break;
        od;
        i = 0;
        do 
          :: i < ND -> 
            atomic { 
				      d_hst ? done;
				      hst_d ! stop;
				      i++;
            }
          :: else -> break;
        od;	
  fi;
  FIN = true;
}



proctype clock () { 
  do 
    :: FIN -> break;
    :: NRP_work == allNWE && allNWE != 0 -> 
      atomic { 
        NRP_work = 0; 
        time++; 
      }
  od;
}



active proctype main(){ 
  byte d;

  NP = 4;		// the number of processing elements per unit
  NU = 2;		// the number of units per device
  ND = 1;		// the number of devices
 
  // size = 2^n -- data size
  byte n = 4;
  size = 1 << n;
  
  // WG selection
  select (d : 2 .. n-1);  
  WG = size >> (n - d); 
  // Tile Size selection
  select (d : 1 .. n-1); 
  TS = size >> (n - d);
  
  WGs = size / WG; 							                  // the number of working groups
  NWD = (WGs <= (NU * ND) -> (WGs / NU) : ND); 	// the number of working devices 
  NWD = (WGs / NU -> NWD : 1); 				            // if WGs <= NU 
  NWU = (WGs <= NU -> WGs : NU); 			          // the number of working units
  NWE = (WG <= NP -> WG : NP); 			              // the number of working elements
  allNWE = NWE * NWU * NWD;
  
  Tmin = 13; 

  atomic {
    run host(); 
    run clock(); 
  }
}

 ltl NonTerm  { [] !FIN } 
 ltl OverTime { [] (FIN -> (time > Tmin)) } 

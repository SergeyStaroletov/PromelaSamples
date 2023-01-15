//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//metadata && init
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
            
mtype:P__ = {
    Gremlin__sp,
    VarsSetter__sp,
    Helper__sp,
    Sun__p,
    Init__p,
    Controller__p,
    Battery__p,
    Generator__p,
    Consumer__p
}
chan __currentProcess = [1] of { mtype:P__ };

mtype:Sun__S = {
    Day__s,
    Night__s,
    Stop__s1,
    Error__s3
}
mtype:Sun__S Sun__cs = Day__s;
unsigned Sun__t : 26;

mtype:Init__S = {
    Init__s,
    Stop__s5,
    Error__s2
}
mtype:Init__S Init__cs = Init__s;

mtype:Controller__S = {
    Normal__s,
    energyLack__s,
    energyOverflow__s,
    Stop__s4,
    Error__s0
}
mtype:Controller__S Controller__cs = Stop__s4;

mtype:Battery__S = {
    active__s,
    Stop__s0,
    Error__s5
}
mtype:Battery__S Battery__cs = Stop__s0;

mtype:Generator__S = {
    Wait__s,
    Starting__s,
    Working__s,
    Stop__s3,
    Error__s4
}
mtype:Generator__S Generator__cs = Wait__s;
unsigned Generator__t : 22;

mtype:Consumer__S = {
    Off__s,
    On__s,
    Stopping__s,
    Stop__s2,
    Error__s1
}
mtype:Consumer__S Consumer__cs = Off__s;
unsigned Consumer__t : 22;

init {
    __currentProcess ! Gremlin__sp;
}



//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//program Environment
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

//constants
#define DAY_DURATION 50400000 //14h
#define NIGHT_DURATION 36000000 //10h

//input
bool clouds;

//output
bool sun__1;


//-----------------------------------------------------------------------------
//Sun
//-----------------------------------------------------------------------------

active proctype Sun() {
    do :: __currentProcess ? Sun__p ->
        atomic {
            if
                :: Day__s == Sun__cs -> {
                    sun__1 = !clouds;
                    if :: Sun__t > DAY_DURATION -> {
                        Sun__t = 1;
                        Sun__cs = Night__s;
                    } :: else -> Sun__t = Sun__t + 1; fi;
                }
                :: Night__s == Sun__cs -> {
                    sun__1 = false;
                    if :: Sun__t > NIGHT_DURATION -> {
                        Sun__t = 1;
                        Sun__cs = Day__s;
                    } :: else -> Sun__t = Sun__t + 1; fi;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Init__p;
        }
    od;
}



//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//program EnergyProvider
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

//constants
#define BATTERY_INIT_ENERGY 10
#define LACK_THRESHOLD 3
#define OVERFLOW_THRESHOLD 17

//input
bool sun__0;
bool generator__0;
bool consumer__0;
bool cityConsuming;

//output
bool generatorOn__0;
bool consumerOn__1;
bool batteryBroken;

//vars
byte batteryEnergy = BATTERY_INIT_ENERGY;


//-----------------------------------------------------------------------------
//Init
//-----------------------------------------------------------------------------

active proctype Init() {
    do :: __currentProcess ? Init__p ->
        atomic {
            if
                :: Init__s == Init__cs -> {
                    Battery__cs = active__s;
                    Controller__cs = Normal__s;
                    Init__cs = Stop__s5;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Controller__p;
        }
    od;
}


//-----------------------------------------------------------------------------
//Controller
//-----------------------------------------------------------------------------

active proctype Controller() {
    do :: __currentProcess ? Controller__p ->
        atomic {
            if
                :: Normal__s == Controller__cs -> {
                    if :: batteryEnergy <= LACK_THRESHOLD -> {
                        generatorOn__0 = true;
                        Controller__cs = energyLack__s;
                    } :: else -> skip; fi;
                    if :: batteryEnergy >= OVERFLOW_THRESHOLD -> {
                        consumerOn__1 = true;
                        Controller__cs = energyOverflow__s;
                    } :: else -> skip; fi;
                }
                :: energyLack__s == Controller__cs -> {
                    if :: batteryEnergy > LACK_THRESHOLD -> {
                        consumerOn__1 = false;
                        Controller__cs = Normal__s;
                    } :: else -> skip; fi;
                }
                :: energyOverflow__s == Controller__cs -> {
                    if :: batteryEnergy < OVERFLOW_THRESHOLD -> {
                        generatorOn__0 = false;
                        Controller__cs = Normal__s;
                    } :: else -> skip; fi;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Battery__p;
        }
    od;
}


//-----------------------------------------------------------------------------
//Battery
//-----------------------------------------------------------------------------

//constants
#define MAX_ENERGY 19
#define MIN_ENERGY 1

//vars
short change;

active proctype Battery() {
    do :: __currentProcess ? Battery__p ->
        atomic {
            if
                :: active__s == Battery__cs -> {
                    change = 0;
                    if :: sun__0 -> {
                        change = change + 1;
                    } :: else -> skip; fi;
                    if :: generator__0 -> {
                        change = change + 1;
                    } :: else -> skip; fi;
                    if :: consumer__0 -> {
                        change = change - 1;
                    } :: else -> skip; fi;
                    if :: cityConsuming -> {
                        change = change - 1;
                    } :: else -> skip; fi;
                    batteryEnergy = batteryEnergy + change;
                    if :: (batteryEnergy < MIN_ENERGY) | (batteryEnergy > MAX_ENERGY) -> {
                        batteryBroken = true;
                        Battery__cs = Error__s5;
                    } :: else -> skip; fi;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Generator__p;
        }
    od;
}



//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//program ReserveEnergyProvider
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

//input
bool generatorOn__1;

//output
bool generator__1;


//-----------------------------------------------------------------------------
//Generator
//-----------------------------------------------------------------------------

//constants
#define START_TIME 3600000 //1h

active proctype Generator() {
    do :: __currentProcess ? Generator__p ->
        atomic {
            if
                :: Wait__s == Generator__cs -> {
                    if :: generatorOn__1 -> {
                        Generator__t = 1;
                        Generator__cs = Starting__s;
                    } :: else -> skip; fi;
                }
                :: Starting__s == Generator__cs -> {
                    if :: !generatorOn__1 -> {
                        Generator__cs = Wait__s;
                    } :: else -> skip; fi;
                    if :: Generator__t > START_TIME -> {
                        generator__1 = true;
                        Generator__cs = Working__s;
                    } :: else -> Generator__t = Generator__t + 1; fi;
                }
                :: Working__s == Generator__cs -> {
                    if :: !generatorOn__1 -> {
                        generator__1 = false;
                        Generator__cs = Wait__s;
                    } :: else -> skip; fi;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Consumer__p;
        }
    od;
}



//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//program ReserveEnergyConsumer
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

//input
bool consumerOn__0;

//output
bool consumer__1;


//-----------------------------------------------------------------------------
//Consumer
//-----------------------------------------------------------------------------

//constants
#define STOP_TIME 3600000 //1h

active proctype Consumer() {
    do :: __currentProcess ? Consumer__p ->
        atomic {
            if
                :: Off__s == Consumer__cs -> {
                    if :: consumerOn__0 -> {
                        consumer__1 = true;
                        Consumer__cs = On__s;
                    } :: else -> skip; fi;
                }
                :: On__s == Consumer__cs -> {
                    if :: !consumerOn__0 -> {
                        Consumer__t = 1;
                        Consumer__cs = Stopping__s;
                    } :: else -> skip; fi;
                }
                :: Stopping__s == Consumer__cs -> {
                    if :: Consumer__t > STOP_TIME -> {
                        consumer__1 = false;
                        Consumer__cs = Off__s;
                    } :: else -> Consumer__t = Consumer__t + 1; fi;
                }
                :: else -> skip;
            fi;
            __currentProcess ! Gremlin__sp;
        }
    od;
}


//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//special processes
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

active proctype Gremlin__specialProcess() {
    do :: __currentProcess ? Gremlin__sp ->
        atomic {
            if
                :: cityConsuming = true;
                :: cityConsuming = false;
            fi;
            if
                :: clouds = true;
                :: clouds = false;
            fi;
            __currentProcess ! VarsSetter__sp;
        }
    od;
}

active proctype VarsSetter__specialProcess() {
    do :: __currentProcess ? VarsSetter__sp ->
        atomic {
            generatorOn__1 = generatorOn__0; //ReserveEnergyP__generatorOn <- Ene__generatorOn
            generator__0 = generator__1; //Ene__generator <- ReserveEnergyP__generator
            consumer__0 = consumer__1; //Ene__consumer <- ReserveEnergyC__consumer
            consumerOn__0 = consumerOn__1; //ReserveEnergyC__consumerOn <- Ene__consumerOn
            sun__0 = sun__1; //Ene__sun <- Env__sun
            __currentProcess ! Helper__sp;
        }
    od;
}

bool cycle__u;
active proctype Helper__specialProcess() {
    do :: __currentProcess ? Helper__sp ->
        cycle__u = true;
        atomic {
            cycle__u = false;
            __currentProcess ! Sun__p;
        }
    od;
}


//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
//ltl
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------

#define apply1__ltl(f, arg) f(arg)
#define apply2__ltl(f, arg) f(apply1__ltl(f, arg))
#define apply3__ltl(f, arg) f(apply2__ltl(f, arg))
#define apply4__ltl(f, arg) f(apply3__ltl(f, arg))
#define apply5__ltl(f, arg) f(apply4__ltl(f, arg))
#define apply6__ltl(f, arg) f(apply5__ltl(f, arg))
#define apply7__ltl(f, arg) f(apply6__ltl(f, arg))
#define apply8__ltl(f, arg) f(apply7__ltl(f, arg))
#define apply9__ltl(f, arg) f(apply8__ltl(f, arg))
#define apply10__ltl(f, arg) f(apply9__ltl(f, arg))
#define apply__ltl(n, f, arg) apply##n##__ltl(f, arg)

#define afterCycle__ltl(expr) (cycle__u U (!cycle__u W (cycle__u && (expr))))
#define afterNCyclesWith__ltl(n, cond, expr) (apply__ltl(n, (cond) -> afterCycle__ltl, expr))
#define afterNCyclesOrSoonerWith__ltl(n, cond, expr) afterNCyclesWith__ltl(n, (cond) && !(expr), expr)

//-----------------------------------------------------------------------------
//ltl between cycles
//-----------------------------------------------------------------------------

#define cltl(expr) (cycle__u -> (expr))
#define G__cltl(expr) [](cycle__u -> (expr))
#define F__cltl(expr) <>(cycle__u && (expr))
#define U__cltl(expr1, expr2) (cycle__u -> (expr1)) U (cycle__u && (expr2))
#define W__cltl(expr1, expr2) (cycle__u -> (expr1)) W (cycle__u && (expr2))
#define V__cltl(expr1, expr2) (cycle__u && (expr1)) V (cycle__u -> (expr2))

#define next__cltl(expr) (cycle__u -> afterCycle__ltl(expr))
#define afterNWith__cltl(n, cond, expr) (cycle__u -> afterNCyclesWith__ltl(n, cond, expr))
#define afterNOrSoonerWith__cltl(n, cond, expr) (cycle__u -> afterNCyclesOrSoonerWith__ltl(n, cond, expr))

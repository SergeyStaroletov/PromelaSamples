//(c) Margarita et al

#define NUM_BLOCKS 6                 // Количество блок-участков
#define TRAIN1 0                     
#define TRAIN2 1                     
bool blocks_occupied[NUM_BLOCKS];    // Массив занятости блоков поездами
byte block_signals[NUM_BLOCKS];      // Сигналы для каждого блока (0 – стоп, 1 – желтый, 2 – зеленый)
byte train_positions[2] = {0, 2};             // Текущая позиция поездов
bool train_manual_mode[2];           // Флаг ручного режима поезда
bool train_atp_active[2];            // Активна ли система ATP
bool train_moving[2];                // Движется ли поезд
chan dispatcher_train[2] = [1] of { byte }; // Канал диспетчер -> поезд
chan train_dispatcher[2] = [1] of { byte }; // Канал поезд -> диспетчер
chan atp_train[2] = [1] of { byte };       // Канал команд ATP для поездов
chan tcc_dispatcher = [2] of { byte };     // Канал TCC -> диспетчер
chan equipment_tcc[NUM_BLOCKS] = [1] of { byte };  // Каналы оборудование -> TCC по каждому блоку
chan tcc_equipment[NUM_BLOCKS] = [1] of { byte };  // Каналы TCC -> оборудование по блоку
proctype TCC() {
    byte eq_status;
    byte i;
    do
    :: i = 0;
       do
       :: i < NUM_BLOCKS ->
           if
           :: len(equipment_tcc[i]) > 0 ->     // Получение статуса от GroundEquipment
               equipment_tcc[i]?eq_status;
               printf("TCC: Received equipment status %d from block %d\n", eq_status, i);
               tcc_dispatcher!eq_status        // Передача диспетчеру
           :: else -> skip
           fi;
           i++
       :: else -> break
       od;
      
       i = 0;
       do
       :: i < NUM_BLOCKS ->
           tcc_equipment[i]!block_signals[i];  // Отправка сигналов на оборудование
           printf("TCC: Sent signal %d to block %d\n", block_signals[i], i);
           i++
       :: else -> break
       od
    od
}
proctype GroundEquipment() {
    byte i;
    bool old;
    byte signal;
    do
    :: i = 0;
       do
       :: i < NUM_BLOCKS ->
           old = blocks_occupied[i];  
           blocks_occupied[i] = (train_positions[TRAIN1] == i || train_positions[TRAIN2] == i); 
           if
           :: old != blocks_occupied[i] -> 
               if
               :: blocks_occupied[i] -> printf("Equipment: Block %d OCCUPIED\n", i)
               :: else -> printf("Equipment: Block %d FREE\n", i)
               fi;
               if
               :: blocks_occupied[i] -> signal = 1  
               :: else -> signal = 0     
               fi;
               equipment_tcc[i]!signal             
           :: else -> skip
           fi;
           if
           :: len(tcc_equipment[i]) > 0 ->  // Прием сигнала для блока от TCC
               tcc_equipment[i]?signal;
               printf("Equipment: Received signal %d for block %d\n", signal, i)
           :: else -> skip
           fi;
           i++
       :: else -> break
       od
    od
}
proctype SignalSystem() {
    byte i;
    do
    :: i = 0;
       do
       :: i < NUM_BLOCKS-2 ->
           if
           :: blocks_occupied[i+1] -> block_signals[i] = 0  
           :: !blocks_occupied[i+1] && !blocks_occupied[i+2] -> block_signals[i] = 2 
           :: else -> block_signals[i] = 1               
           fi;
           i++
       :: i == NUM_BLOCKS-2 ->     
           if
           :: blocks_occupied[i+1] -> block_signals[i] = 0
           :: else -> block_signals[i] = 1
           fi;
           i++
       :: else -> break
       od
    od
}
proctype ATP() {
    byte pos;
    do
    :: train_atp_active[TRAIN1] ->
        pos = train_positions[TRAIN1]; 
        if
        :: pos < NUM_BLOCKS-1 && block_signals[pos] == 0 -> atp_train[TRAIN1]!0
        :: pos < NUM_BLOCKS-1 && block_signals[pos] == 1 && !train_manual_mode[TRAIN1] -> atp_train[TRAIN1]!1
        :: else -> skip
        fi
    :: train_atp_active[TRAIN2] ->
        pos = train_positions[TRAIN2];
        if
        :: pos < NUM_BLOCKS-1 && block_signals[pos] == 0 -> atp_train[TRAIN2]!0
        :: pos < NUM_BLOCKS-1 && block_signals[pos] == 1 && !train_manual_mode[TRAIN2] -> atp_train[TRAIN2]!1
        :: else -> skip
        fi
    od
}
proctype OnboardComputer(byte train_id) {
    byte cmd;
    do
    :: len(atp_train[train_id]) > 0 -> 
        atp_train[train_id]?cmd;
        if
        :: cmd == 0 -> train_moving[train_id] = false; printf("Computer%d: STOP\n", train_id)
        :: cmd == 1 -> printf("Computer%d: REDUCE SPEED\n", train_id) 
        :: else -> skip
        fi
    :: (!train_moving[train_id] && train_atp_active[train_id]) ->
        atomic {
            if
            :: blocks_occupied[train_positions[train_id]] == false ->
                train_manual_mode[train_id] = true;     
                train_atp_active[train_id] = false;    
                train_moving[train_id] = true;      
                printf("Computer%d: Switching to manual mode\n", train_id)
            :: else -> skip
            fi
        }
    od
}
proctype Dispatcher() {
    byte msg;
    do
    :: len(tcc_dispatcher) > 0 ->  
        tcc_dispatcher?msg;
        printf("Dispatcher: TCC reports status %d\n", msg)
    :: len(train_dispatcher[TRAIN1]) > 0 ->
        train_dispatcher[TRAIN1]?msg;
        printf("Dispatcher: TRAIN1 message\n")
    :: len(train_dispatcher[TRAIN2]) > 0 ->
        train_dispatcher[TRAIN2]?msg;
        printf("Dispatcher: TRAIN2 message\n")
    od
}
proctype TrainProcess(byte train_id) {
    byte next;
    do
    :: train_moving[train_id] && train_positions[train_id] < NUM_BLOCKS-1 -> 
        atomic {
            next = train_positions[train_id]+1; 
            if
            :: blocks_occupied[next] -> printf("Train%d COLLISION %d\n", train_id, next)
            :: else ->
                blocks_occupied[train_positions[train_id]] = false; 
                train_positions[train_id] = next;                 
                blocks_occupied[next] = true;                     
                printf("Train%d moved to %d\n", train_id, next)
            fi
        }
    od
}
init {
    train_positions[TRAIN1] = 0;      
    train_positions[TRAIN2] = 2;
    
    train_moving[TRAIN1] = true;      
    train_moving[TRAIN2] = true;
    train_atp_active[TRAIN1] = true;  
    train_atp_active[TRAIN2] = true;
    train_manual_mode[TRAIN1] = false;
    train_manual_mode[TRAIN2] = false;
    blocks_occupied[0] = true; 
    blocks_occupied[2] = true;
    run TCC();                   
    run GroundEquipment();
    run SignalSystem();
    run ATP();
    run OnboardComputer(TRAIN1);
    run OnboardComputer(TRAIN2);
    run Dispatcher();
    run TrainProcess(TRAIN1);
    run TrainProcess(TRAIN2);
}
ltl no_collision { [] !(train_positions[TRAIN1] == train_positions[TRAIN2]) } 

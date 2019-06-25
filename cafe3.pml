/* channels - from the scheme*/
chan gc_to_man = [2] of {short};
chan man_to_gc = [2] of {short};
chan man_to_cook = [2] of {short};
chan cook_to_pincake=[2] of {short};
chan pincake_to_man=[2] of {short};
chan cook_to_kvass=[2] of {short};
chan kvass_to_man=[2] of {short};
chan goods_to_man=[2] of {short};
int count;
int nextClient=0;

active proctype HungryMan(){
int buf;
do
    ::{
    nextClient != 1; 
    printf("HungryMan: Creating order to a Manager\n");
    gc_to_man ! 1;
    do
	:: true ->{gc_to_man ! 1; gc_to_man ! 2; break}
	:: true ->{gc_to_man ! 2; gc_to_man ! 1; break}
    od
    printf("HungryMan: Waiting result from the Manager \n");
    man_to_gc ? buf; 
    printf("HungryMan: cycle done");
    }
od
}

active proctype Manager() {
int buf;
count = 0;
do
    :: {
    nextClient = 0;
    printf("Manager: Waiting order from a customer\n");
    gc_to_man ? buf;
    if 
    :: buf == 1 ->  {
	printf("Manager: asking cook for Kvass\n"); man_to_cook ! 1;
	printf("Manager: asking cook for Pincake\n"); man_to_cook ! 2;
    }
    :: buf == 2 -> {
	printf("Manager: asking cook for Pincake\n"); man_to_cook ! 2;
	printf("Manager: asking cook for Kvass\n"); man_to_cook ! 1;
    }
    fi
    printf("Manager: receiving goods\n");
    goods_to_man?buf;
    goods_to_man?buf;
    printf("Manager: returning result to customer\n ")
    man_to_gc ! 1;
    nextClient = 1;
    count++;
    } 
od
}

active proctype Cook () {
int buf;
do
:: {
    printf("Cook: Waiting for a request from Manager\n");
    man_to_cook? buf;
    if 
    ::buf ==1 -> 
    {
	printf("Cook: cooking kvass\n");
	cook_to_kvass ! 1;
    }
    ::buf == 2 ->
    {
	printf("Cook: cooking pincake\n");
	cook_to_pincake ! 1;
    }
    fi
}
od
}

active proctype Pincake () {
int buf;
do 
:: {
    printf("Pincake: receiving request from cook\n");
    cook_to_pincake? buf;
    printf("Pincake: sending me to Manager\n");
    goods_to_man ! 1;
}
od
}

active proctype Kvass () {
int buf;
do 
:: {
    printf("Kvass: receiving request from cook\n");
    cook_to_kvass? buf;
    printf("Kvass: sending me to Manager\n");
    goods_to_man ! 2;
} 
od
}

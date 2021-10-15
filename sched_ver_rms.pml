#define num_tasks 2
#define MAX_STACK 4
#define MAX_T 100
#define SCHED_PER 100

typedef Task {
  int task_id;
  short interval;
  short max_time;
  int last_t_run;
}

Task task[num_tasks];

typedef Stack {
  int task_id;
  int task_time;
}


Stack stack[MAX_STACK];
int sp = -1;


inline setup_tasks() {
  task[0].task_id = 1;	
  task[0].interval = 5;	
  task[0].max_time = 2;
  task[0].last_t_run = -1;

  task[1].task_id = 2;
  task[1].interval = 7;	
  task[1].max_time = 4;
  task[1].last_t_run = -1;
}




short current_task = -1;
int t = 0;
short current_runtime_slice = 0;
short current_runtime_task = 0;

bool is_preemptive = true;//false;


bool is_missed = false;
int n_missed = 0;
int time_missed = 0;

bool is_stack_overflow = false;

int processor_util = 0;


active proctype sched_rms() {

  setup_tasks();
  int i;

  do
    ::(t < MAX_T) -> {

    //no current task at t=t or our task has just ended
    if
      ::!(is_preemptive) && ((current_task == -1) || (current_runtime_task == task[current_task].max_time)) -> {
        //select a task which is not runned or its period is due now       
        printf("time to switch\n");
        i = 0;
        bool task_found = false;
        //loop over tasks
        do 
          ::(i < num_tasks) -> {
            if 
              ::(task[i].last_t_run == -1) || (task[i].last_t_run + task[i].interval <= t) -> {
                if 
                  ::(task[i].last_t_run != -1) && (task[i].last_t_run + task[i].interval < t) -> {
                    printf("[t = %d] task %d was missed!\n", t, i);
                    is_missed = true;
                  }
                  ::else->skip
                fi
                  //we should now select i-th task as a current
                  printf("[t = %d] task %d with period = %d and max_time = %d started!\n", t, task[i].task_id, task[i].interval, task[i].max_time);
                  current_task = i;
                  task[i].last_t_run = t; 
                  current_runtime_task = 0;
                  task_found = true;
                  break
                }
              ::else -> skip
            fi;
            i++
          }
          ::else -> break
        od
        if 
          ::(task_found == false) -> {
            current_task = -1;
          }
          ::else -> skip
        fi
      } 
      ::else -> skip;
    fi

    //task finished?
    if
      ::(current_task != -1) && (current_runtime_task >= task[current_task].max_time) -> {
        current_task = -1;
      }
      ::else->skip;
    fi
  
    //if the current task is due to finish -- check wheather we have a task in stack
    if 
      ::(is_preemptive && (current_task ==-1) && (sp > -1)) -> {
        current_task = stack[sp].task_id;
        current_runtime_task = stack[sp].task_time;
        task[current_task].last_t_run = task[current_task].last_t_run-1;//?
        sp--;

        printf("[t = %d] switch back to task%d [%d/%d done]\n", t, task[current_task].task_id, current_runtime_task, task[current_task].max_time);
      }
      ::else -> skip 
    fi   


    if
      ::(is_preemptive) -> {
        //select a task which is not runned or its period is due now       
        i = 0;
        bool task_found = false;
        //loop over tasks
        int task_to = current_task;
        if 
          ::(task_to == -1) -> task_to = num_tasks;
          ::else -> skip;
        fi

        do 
          ::(i < task_to) -> {
            if 
              ::(task[i].last_t_run == -1) || (task[i].last_t_run + task[i].interval <= t) -> {
                if 
                  ::(task[i].last_t_run != -1) && (task[i].last_t_run + task[i].interval < t) -> {
                    printf("[t = %d] task%d was missed with current task N %d!\n", t, task[i].task_id, current_task);
                    n_missed++;
                    time_missed = time_missed + t - (task[i].last_t_run + task[i].interval);
                    is_missed = true;
                  }
                  ::else->skip
                fi
                  //we should now select i-th task as a current

                if 
                  ::((current_task != -1) && (current_runtime_task < task[current_task].max_time)) -> {
                    //we have a task that is still running...
                    printf("[t = %d] switch task%d to task%d (%d left)!\n", t, task[current_task].task_id, task[i].task_id, (task[current_task].max_time - current_runtime_task));
                    if 
                      ::(sp == MAX_STACK) -> {
                        printf("t = %d] stack overflow!\n", t); 
                        is_stack_overflow = true;
                        break;
                      } 
                      ::else -> skip;
                    fi
                    sp++; 
                    stack[sp].task_id = current_task;
                    stack[sp].task_time = current_runtime_task;
                    }
                    ::else -> skip
                fi
                printf("[t = %d] task%d with period = %d and max_time = %d started!\n", t, task[i].task_id, task[i].interval, task[i].max_time);
                current_task = i;
                task[i].last_t_run = t; 
                current_runtime_task = 0;
                task_found = true;
                break;
                }
              ::else -> skip
            fi
            i++
          }
          ::else -> break;
        od
      } 
      ::else -> skip;
    fi


    if
      ::((current_task != -1) && (t != 0) && (t % SCHED_PER == 0)) -> {
        //sched sliсe is over -- TBD, not yet
            
        //check if we do not finished
            if 
              :: (current_runtime_task < task[current_task].max_time) ->
                  {
                    printf("suspend current task %d!\n", current_task);
                    //save time?
                    current_runtime_task = task[current_task].max_time;
                  }
              ::else -> skip;
            fi;
            current_runtime_slice = 0;
        }
      ::else -> skip;
    fi;

    printf("[t = %d] current task = task%d\n", t, task[current_task].task_id);   
    current_runtime_slice++;
    t++;
    current_runtime_task++;
    if 
      ::(current_task != -1) -> processor_util++;
      ::else -> skip;
    fi
  }
  ::else -> break;
  od

  printf("Processor utilization value: %d\n", 100 * processor_util / t);

  if 
    ::is_missed -> printf("Average missed time: %d with %d cases\n", time_missed / n_missed, n_missed);
    ::else -> skip
  fi
}
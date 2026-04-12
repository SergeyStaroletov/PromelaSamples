/* (c) Sergey Staroletov
   Integrated model of SMP system with interrupts (IOAPIC + Local APIC)
   based on my Linux interrupt handling paper and inspired by Intel 82093AA and 8259A datasheets.
   Two CPUs run prime number calculations; devices generate interrupts non‑deterministically.
   Interrupts are processed with context save/restore, EOI, and resumption of the interrupted thread.
   Test:  spin interrupts_intel.pml | grep "Found prime" 
*/

#define MAX_CPU         2
#define MAX_THREADS     4          /* threads per CPU: 3 user + 1 kworker */
#define USER_WORK_COUNT 6          /* number of threads to finish */
#define MAX_MEM         100        /* memory cells (words) */
#define MAX_IRQ_LINES   24
#define IDLE_THREAD     (MAX_THREADS * MAX_CPU)               /* =8 */
#define KWOKRER_BASE    3          /* index of kworker thread on each CPU (0‑based) */
/* Message types for channels */
mtype = { IRQ_RAISE, IRQ_MSG, IRQ_EOI, IRQ_FASTEOI };

/* Devices, domains, trigger types */
mtype = { timer, i8042, rtc0, acpi, ehci_hcd_usb, ath9k, i801_smbus,
          hpet, dmar, ahci, radeon, mei_me, snd_hda, enp3s0,
          io_apic, hpet_msi, dmar_msi, pci_msi,
          edge, fasteoi };

/* Channels:
   from_device_to_router – device raises an interrupt (device, line)
   router_to_domain[domain] – router forwards to specific domain controller
   ioapic_to_lapic[cpu]        – IOAPIC forwards to Local APIC (message, line, vector)
   lapic_to_cpu[cpu]           – Local APIC signals CPU (IRQ_RAISE, vector)
   cpu_to_lapic[cpu]           – CPU sends EOI (IRQ_EOI, vector)
   kworker_queue[cpu]          – fasteoi interrupts for kworker (vector)
*/
chan from_device_to_router = [1] of { mtype, byte };
chan router_to_domain[4] = [1] of { mtype, byte, byte }; /* up to 4 domains, indexed by domain_id */
chan ioapic_to_lapic[MAX_CPU] = [1] of { mtype, byte, byte };
chan lapic_to_cpu[MAX_CPU] = [1] of { mtype, byte };
chan cpu_to_lapic[MAX_CPU] = [1] of { mtype, byte };
chan kworker_queue[MAX_CPU] = [2] of { byte }; /* queue of vectors for kworker */

/* Domain identifiers for router */
#define DOM_IOAPIC   0
#define DOM_HPET_MSI 1
#define DOM_DMAR_MSI 2
#define DOM_PCI_MSI  3

/* Context of a thread  */
typedef CONTEXT {
    int ip; int rsp; int rbp; int eax; int ebx; int edx; int ecx;
    int edi; int esi; bit flag_z; bit flag_s; bit finished;
};

/* Thread storage: enough for all user threads + idle thread */
CONTEXT thread[IDLE_THREAD + 1];

/* Memory */
int memory[MAX_MEM / 4 * 3];

/* CPU structure extended with interrupt flags */
typedef CPU {
    int currentThread;
    CONTEXT context;
    bit finished;           /* whether this CPU has finished all tasks */
    bit intr_enabled;        /* interrupts are enabled (1) or disabled (0) */
    byte current_irq;        /* vector being serviced, 0xFF if none */
};

CPU cpu[MAX_CPU];
int idle_ticks[MAX_CPU];
int total_ticks[MAX_CPU];
int ready = 0;               /* number of CPUs that have finished */
bit goodBye = 0;            /* it's time to exit */

/* Macros for register access (use currentCPU as the parameter) */
#define IP          cpu[currentCPU].context.ip
#define RSP         cpu[currentCPU].context.rsp
#define RBP         cpu[currentCPU].context.rbp
#define EAX         cpu[currentCPU].context.eax
#define EBX         cpu[currentCPU].context.ebx
#define ECX         cpu[currentCPU].context.ecx
#define EDX         cpu[currentCPU].context.edx
#define EDI         cpu[currentCPU].context.edi
#define ESI         cpu[currentCPU].context.esi
#define FLAGZ       cpu[currentCPU].context.flag_z
#define FLAGS       cpu[currentCPU].context.flag_s
#define FINISH      cpu[currentCPU].finished
#define T           cpu[currentCPU].currentThread
#define THREAD      thread[T]

/* Instruction macros (identical to original c-code of finding primes) */
inline movl_rm(a, b)   { atomic { memory[(b)/4] = a; } }
inline movl_rr(a, b)   { atomic { b = a; } }
inline movl_mr(a, b)   { atomic { b = memory[(a)/4]; } }
inline movl_cm(a, b)   { atomic { memory[(b)/4] = a; } }
inline shrl(a, b)      { atomic { b = b >> a; } }
inline addl(a, b)      { atomic { b = a + b; } }
inline addl_cm(a, b)   { atomic { memory[(b)/4] = a + memory[(b)/4]; } }
inline sarl(a)         { atomic { a = a >> 1; } }
inline cltd()          { atomic { EDX = EAX; } }
inline idivl(b)        { atomic { EAX = EAX / memory[(b)/4]; EDX = EDX % memory[(b)/4]; } }
inline testl(a, b)     { atomic { FLAGZ = ((a)&(b))==0; FLAGS = ((a)&(b))<0; } }
inline cmpl_mr(a, b)   { atomic { FLAGZ = (b == memory[(a)/4]); FLAGS = (b < memory[(a)/4]); } }
inline cmpl_rm(a, b)   { atomic { FLAGZ = (memory[(b)/4] == a); FLAGS = (memory[(b)/4] < a); } }
inline nop()           { skip; }
#define NEXT_INSTRUCTION() atomic { IP++; }

/* Save context of the current thread on CPU currentCPU */
inline save_context(currentCPU) {
    atomic {
        THREAD.ip = IP;
        THREAD.rsp = RSP;
        THREAD.rbp = RBP;
        THREAD.eax = EAX;
        THREAD.ebx = EBX;
        THREAD.ecx = ECX;
        THREAD.edx = EDX;
        THREAD.edi = EDI;
        THREAD.esi = ESI;
        THREAD.flag_z = FLAGZ;
        THREAD.flag_s = FLAGS;
    }
}

/* Load context into CPU currentCPU from its current thread */
inline load_context(currentCPU) {
    atomic {
        IP = THREAD.ip;
        RSP = THREAD.rsp;
        RBP = THREAD.rbp;
        EAX = THREAD.eax;
        EBX = THREAD.ebx;
        ECX = THREAD.ecx;
        EDX = THREAD.edx;
        EDI = THREAD.edi;
        ESI = THREAD.esi;
        FLAGZ = THREAD.flag_z;
        FLAGS = THREAD.flag_s;
    }
}

/* CPU execution unit - finding primes!
   Executes one instruction per atomic step, but checks for interrupts first.
   If an interrupt is pending and enabled, it saves the current context,
   processes the interrupt (prints, sends EOI), then restores the context. */
proctype cpuProc(int currentCPU) {
    do
        :: atomic {
            /* Check for pending interrupt from Local APIC */
            if
                :: cpu[currentCPU].intr_enabled && len(lapic_to_cpu[currentCPU]) > 0 ->
                    mtype sig; byte vec;
                    lapic_to_cpu[currentCPU] ? sig, vec;
                    printf("CPU %d: interrupt vector %d received, saving context\n", currentCPU, vec);
                    /* Save context of interrupted thread */
                    save_context(currentCPU);
                    cpu[currentCPU].intr_enabled = 0;
                    cpu[currentCPU].current_irq = vec;

                    /* Simulate interrupt handler work (this is the "top half") */
                    printf("CPU %d: handling IRQ %d (top half, device action)\n", currentCPU, vec);

                    /* Send EOI to Local APIC */
                    cpu_to_lapic[currentCPU] ! IRQ_EOI, vec;

                    /* Restore context of interrupted thread */
                    cpu[currentCPU].intr_enabled = 1;
                    cpu[currentCPU].current_irq = 255;
                    load_context(currentCPU);
                    printf("CPU %d: context restored, resuming thread %d\n", currentCPU, T);

                :: else ->
                    /* No interrupt – execute next instruction of current thread */
                    if
                        ::(IP == 1) -> { movl_rr(RSP, RBP); IP = 4; }
                        ::(IP == 4) -> { movl_rm(EDI, -20+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 5) -> { movl_rm(ESI, -24+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 6) -> { movl_mr(-20+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 7) -> { movl_rm(EAX, -4+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 8) -> { IP = 36; }  /* jmp .L3 */
                        /* .L9: */
                        ::(IP == 9) -> { movl_mr(-4+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 10) -> { movl_rr(EAX, EDX); NEXT_INSTRUCTION(); }
                        ::(IP == 11) -> { shrl(31, EDX); NEXT_INSTRUCTION(); }
                        ::(IP == 12) -> { addl(EDX, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 13) -> { sarl(EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 14) -> { movl_rm(EAX, -16+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 15) -> { movl_cm(1, -8+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 16) -> { movl_cm(2, -12+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 17) -> { IP = 27; }  /* jmp .L4 */
                        /* .L7: */
                        ::(IP == 18) -> { movl_mr(-4+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 19) -> { cltd(); NEXT_INSTRUCTION(); }
                        ::(IP == 20) -> { idivl(-12+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 21) -> { movl_rr(EDX, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 22) -> { testl(EAX, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 23) -> { atomic { if :: (FLAGZ == 0) -> IP = 26; :: else -> NEXT_INSTRUCTION(); fi } }
                        ::(IP == 24) -> { movl_cm(0, -8+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 25) -> { IP = 30; }  /* jmp .L6 */
                        /* .L5: */
                        ::(IP == 26) -> { addl_cm(1, -12+RBP); NEXT_INSTRUCTION(); }
                        /* .L4: */
                        ::(IP == 27) -> { movl_mr(-12+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 28) -> { cmpl_mr(-16+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 29) -> { atomic { if :: (FLAGZ == 1 || FLAGS == 1) -> IP = 18; :: else -> NEXT_INSTRUCTION(); fi } }
                        /* .L6: */
                        ::(IP == 30) -> { cmpl_rm(0, -8+RBP); NEXT_INSTRUCTION(); }
                        ::(IP == 31) -> { atomic { if :: (FLAGZ == 1) -> IP = 35; :: else -> NEXT_INSTRUCTION(); fi } }
                        ::(IP == 32) -> { movl_mr(-4+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 33) -> { movl_rr(EAX, EDI); NEXT_INSTRUCTION(); }
                        ::(IP == 34) -> { printf("\nCPU %d THREAD %d ---------------------- Found prime: %d\n", currentCPU, T, EDI); NEXT_INSTRUCTION(); }
                        /* .L8: */
                        ::(IP == 35) -> { addl_cm(1, -4+RBP); NEXT_INSTRUCTION(); }
                        /* .L3: */
                        ::(IP == 36) -> { movl_mr(-4+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 37) -> { cmpl_mr(-24+RBP, EAX); NEXT_INSTRUCTION(); }
                        ::(IP == 38) -> { atomic { if :: (FLAGZ == 1 || FLAGS == 1) -> IP = 9; :: else -> NEXT_INSTRUCTION(); fi } }
                        ::(IP == 39) -> {
                            if :: !THREAD.finished ->
                                    printf("Task %d for CPU %d done!\n", T, currentCPU);
                                    THREAD.finished = true;
                                    atomic {ready++;}
                               :: else -> skip;
                            fi;
                        }
                        ::(IP == 1000) -> { nop(); }  /* idle loop */
                        :: else -> { printf("CPU %d: illegal IP %d\n", currentCPU, IP); break; }
                    fi;
            fi;

            if
                :: (FINISH) -> break;
                :: else -> skip;
            fi;
        }
    od;
}

/* Scheduler – periodically switches threads on a CPU
   (includes the kworker thread) */
proctype scheduler(int currentCPU; int startThread) {
    do
        :: {
            int currentThread = startThread;

            /* Select next ready thread (three user threads + kworker) */
            if
                :: !thread[startThread].finished -> currentThread = startThread;
                :: !thread[startThread+1].finished -> currentThread = startThread+1;
                :: !thread[startThread+2].finished -> currentThread = startThread+2;
                :: !thread[startThread+KWOKRER_BASE].finished -> currentThread = startThread+KWOKRER_BASE;
                :: else -> {
                    atomic {
                        if :: currentThread != IDLE_THREAD ->
                                printf("\n!!! CPU %d DONE !!!\n", currentCPU);
                                ready++;
                           :: else -> skip;
                        fi;
                    }
                    idle_ticks[currentCPU]++;
                    currentThread = IDLE_THREAD;
                }
            fi;

            total_ticks[currentCPU]++;

            atomic {
                /* Save context of current thread, switch, load new context */
                save_context(currentCPU);
                T = currentThread;
                load_context(currentCPU);
            }

            /* If all CPUs finished, break */
            goodBye = (ready == USER_WORK_COUNT);
            if
                :: (goodBye) ->
                     printf("CPU %d: %d%% idle\n", currentCPU,
                            100 - idle_ticks[currentCPU]*100 / total_ticks[currentCPU]); //?
                     break;
                :: else -> skip;
            fi;
        }
    od;
}

/* Kworker thread – handles fasteoi interrupts (bottom half)
   Runs on each CPU and processes vectors from the queue. */
proctype kworker(int my_cpu) {
    byte vec;
    do
        :: atomic {
            if
                :: len(kworker_queue[my_cpu]) > 0 ->
                    kworker_queue[my_cpu] ? vec;
                    printf("Kworker on CPU %d: processing bottom half for vector %d\n", my_cpu, vec);
                    /* Simulate some work */
                    // select?
                :: else -> skip;
            fi;
        }
        ::goodBye -> break;
    od;
}

/* -------------------------------------------------------------------------
   Interrupt configuration using mtypes (as in the sketch)
   ------------------------------------------------------------------------- */

typedef irq_setup {
    mtype device;
    mtype domain;
    mtype trig;
    byte line;
    byte vector;          /* assigned vector (for simplicity) */
    byte dest_cpu;        /* target CPU */
};

irq_setup irq_configs[30];
int num_configs = 0;




inline setup_interrupt(dev, ddom, trigg, lline, vecc, ccpu) {
    irq_configs[num_configs].device = dev; 
    irq_configs[num_configs].domain = ddom; 
    irq_configs[num_configs].trig = trigg; 
    irq_configs[num_configs].line = lline; 
    irq_configs[num_configs].vector = vecc;  
    irq_configs[num_configs].dest_cpu = ccpu; 
    num_configs++;
}



inline setup_interrupts() {
    setup_interrupt(timer, io_apic, edge, 2, 32, 0);
    setup_interrupt(i8042, io_apic, edge, 1, 33, 0);
    setup_interrupt(rtc0, io_apic, edge, 8, 34, 0);
    setup_interrupt(acpi, io_apic, fasteoi, 9, 35, 1);
    setup_interrupt(i8042, io_apic, edge, 12, 44, 1);
    setup_interrupt(ehci_hcd_usb, io_apic, fasteoi, 16, 48, 1);
    setup_interrupt(ath9k, io_apic, fasteoi, 17, 49, 0);
    setup_interrupt(i801_smbus, io_apic, fasteoi, 18, 50, 0);
    setup_interrupt(ehci_hcd_usb, io_apic, fasteoi, 23, 55, 1);

    /* HPET MSI domain (stub) */
    setup_interrupt(hpet, hpet_msi, edge, 3, 60, 0);
    setup_interrupt(hpet, hpet_msi, edge, 4, 61, 0);
    setup_interrupt(hpet, hpet_msi, edge, 5, 62, 0);
    setup_interrupt(hpet, hpet_msi, edge, 6, 63, 0);
    setup_interrupt(hpet, hpet_msi, edge, 7, 64, 0);

    /* DMAR MSI domain (stub) */
    setup_interrupt(dmar, dmar_msi, edge, 0, 65, 1);

    /* PCI‑MSI domain (stub) */
    setup_interrupt(ahci, pci_msi, edge, 510, 70, 0);
    setup_interrupt(radeon, pci_msi, edge, 104, 71, 1);
    setup_interrupt(mei_me, pci_msi, edge, 36, 72, 0);
    setup_interrupt(snd_hda, pci_msi, edge, 44, 73, 1);
    setup_interrupt(snd_hda, pci_msi, edge, 105, 74, 1);
    setup_interrupt(enp3s0, pci_msi, edge, 157, 75, 0);
}

/* -------------------------------------------------------------------------
   Interrupt router – receives raw interrupts from devices,
   looks up the configuration, and forwards to the appropriate domain controller.
   ------------------------------------------------------------------------- */
proctype irq_router() {
    mtype dev; byte line;
    do
        :: from_device_to_router ? dev, line ->
           /* find configuration for this device (simplified: assume unique device) */
           int i;
           for (i: 0 .. num_configs-1) {
               if :: (irq_configs[i].device == dev) ->
                    /* found */
                    byte domain_id;
                    if
                        :: irq_configs[i].domain == io_apic -> domain_id = DOM_IOAPIC;
                        :: irq_configs[i].domain == hpet_msi -> domain_id = DOM_HPET_MSI;
                        :: irq_configs[i].domain == dmar_msi -> domain_id = DOM_DMAR_MSI;
                        :: irq_configs[i].domain == pci_msi -> domain_id = DOM_PCI_MSI;
                    fi;
                    printf("Router: device %d line %d -> domain %d\n", dev, line, domain_id);
                    router_to_domain[domain_id] ! dev, line, irq_configs[i].vector;
                    break;
               :: else -> skip;
               fi;
           }
        :: goodBye -> break;
    od;
}

/* IO‑APIC controller (domain io_apic)
   Receives (dev, line, vector) from router.
   If trigger is fasteoi, it sends the interrupt to the kworker queue of the destination CPU.
   Otherwise (edge) it forwards to Local APIC (via ioapic_to_lapic) for immediate handling. */
proctype ioapic_controller() {
    mtype dev; byte line, vec;
    do
        :: router_to_domain[DOM_IOAPIC] ? dev, line, vec ->
           /* find configuration to get trigger and dest_cpu */
           int i;
           for (i: 0 .. num_configs-1) {
               if :: (irq_configs[i].device == dev) ->
                    if
                        :: irq_configs[i].trig == fasteoi ->
                            printf("IOAPIC: fasteoi line %d vector %d -> queue to CPU %d kworker\n",
                                   line, vec, irq_configs[i].dest_cpu);
                            kworker_queue[irq_configs[i].dest_cpu] ! vec;
                        :: else -> /* edge */
                            printf("IOAPIC: edge line %d vector %d -> CPU %d\n",
                                   line, vec, irq_configs[i].dest_cpu);
                            ioapic_to_lapic[irq_configs[i].dest_cpu] ! IRQ_MSG, line, vec;
                    fi;
                    break;
               :: else -> skip;
               fi;
           }
        :: goodBye -> break;
    od;
}

/* Stub controllers for other domains. */
proctype stub_controller(byte domain_id; int name) {
    mtype dev; byte line, vec;
    do
        :: router_to_domain[domain_id] ? dev, line, vec ->
           printf("Stub controller %d: received device %d line %d vector %d (not handled)\n",
                  name, dev, line, vec);
        :: goodBye -> break;
    od;
}

/* Local APIC (one per CPU)
   Accepts messages from IOAPIC (or other controllers that use lapic),
   delivers to CPU if no active interrupt, otherwise drops (no queue).
   Receives EOI from CPU and then can deliver the next pending (only one pending kept). */
proctype lapic(int my_cpu) {
    byte pending_vec = 0;
    byte active_vec = 0;

    do
        :: atomic {
            if
                :: len(ioapic_to_lapic[my_cpu]) > 0 ->
                    mtype sig; byte line, vec;
                    ioapic_to_lapic[my_cpu] ? sig, line, vec;
                    if
                        :: pending_vec == 0 && active_vec == 0 ->
                             pending_vec = vec;
                             printf("LAPIC %d: interrupt vector %d pending, signalling CPU\n", my_cpu, vec);
                             lapic_to_cpu[my_cpu] ! IRQ_RAISE, vec;
                             active_vec = vec;
                             pending_vec = 0;
                        :: else ->
                             printf("LAPIC %d: CPU busy, interrupt vector %d lost\n", my_cpu, vec);
                    fi;

                :: len(cpu_to_lapic[my_cpu]) > 0 ->
                    mtype cmd; //byte vec;
                    cpu_to_lapic[my_cpu] ? cmd, vec;
                    if
                        :: cmd == IRQ_EOI ->
                             printf("LAPIC %d: EOI for vector %d\n", my_cpu, vec);
                             active_vec = 0;
                             if :: pending_vec != 0 ->
                                     lapic_to_cpu[my_cpu] ! IRQ_RAISE, pending_vec;
                                     active_vec = pending_vec;
                                     pending_vec = 0;
                                :: else -> skip;
                             fi;
                        :: else -> skip;
                    fi;
            fi;
        }
        :: goodBye -> break;
    od;
}

/*  Device models – generate interrupts on a specific line (using device mtype) */
proctype device_proc(mtype dev; byte line) {
    do
        :: true ->
            /* random delay */
            byte l;
            select(l:1..5);
            atomic {
                printf("Device %d (line %d): raising interrupt\n", dev, line);
                from_device_to_router ! dev, line;
            }
        :: goodBye -> break;
    od;
}

/* Main: initialisation and process startup */
active proctype main() {
    int i, cpu_id;

    /* Initialize idle thread */
    thread[IDLE_THREAD].ip = 1000;

    /* Threads for CPU 0 (indices 0,1,2 = user, index 3 = kworker) */
    thread[0].rsp = MAX_MEM/2;      thread[0].edi = 100; thread[0].esi = 500; thread[0].ip = 1;
    thread[1].rsp = MAX_MEM;        thread[1].edi = 51;  thread[1].esi = 100; thread[1].ip = 1;
    thread[2].rsp = MAX_MEM/2 + MAX_MEM; thread[2].edi = 1; thread[2].esi = 50; thread[2].ip = 1;
    thread[3].ip = 1000;  /* kworker, will be overwritten by its own process? Actually kworker is a separate proctype, not a thread. We'll run it as a process, not as a thread. */
    /* But we need a thread context for the kworker on this CPU. We'll use a separate proctype that runs independently. */
    /* However, the scheduler only switches between threads stored in 'thread' array. So kworker must be represented as a thread in that array. */

    /* Threads for CPU 1 (indices 4,5,6 = user, index 7 = kworker) */
    thread[4].rsp = MAX_MEM*2;      thread[4].edi = 101; thread[4].esi = 200; thread[4].ip = 1;
    thread[5].rsp = MAX_MEM*2 + MAX_MEM/2; thread[5].edi = 51; thread[5].esi = 100; thread[5].ip = 1;
    thread[6].rsp = MAX_MEM*3;      thread[6].edi = 1;   thread[6].esi = 50;  thread[6].ip = 1;
    /* thread[7] unused for kworker now */

    /* Initialize CPUs */
    for (cpu_id: 0 .. MAX_CPU-1) {
        cpu[cpu_id].currentThread = cpu_id * 3; /* start with first user thread */
        cpu[cpu_id].intr_enabled = 1;
        cpu[cpu_id].current_irq = 255;
        cpu[cpu_id].finished = 0;
        load_context(cpu_id);
    }

    /* Setup interrupt configuration */
    setup_interrupts();

    /* Start system processes */
    run irq_router();
    run ioapic_controller();
    run stub_controller(DOM_HPET_MSI, 1);
    run stub_controller(DOM_DMAR_MSI, 2);
    run stub_controller(DOM_PCI_MSI, 3);
    for (cpu_id: 0 .. MAX_CPU-1) {
        run lapic(cpu_id);
        run scheduler(cpu_id, cpu_id*3);
        run cpuProc(cpu_id);
        run kworker(cpu_id); // change it?
    }

    /* Start devices */
    run device_proc(timer, 2);
    run device_proc(i8042, 1);
    run device_proc(rtc0, 8);
    run device_proc(acpi, 9);
    run device_proc(ehci_hcd_usb, 16);
    run device_proc(ath9k, 17);
    run device_proc(i801_smbus, 18);
    run device_proc(hpet, 3);
    run device_proc(dmar, 0);
    run device_proc(ahci, 510);
}
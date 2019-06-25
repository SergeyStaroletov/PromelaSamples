int secrets = 0;
int success = 0;
int fails = 0;
int total = 0;

//variables state that a corresponding window is opened
bool windowLogin = false;
bool windowSecret = false;
bool windowNoSecret = false;

//LTL formulas to check
ltl secret_to_success_password { [] (secrets<=success)} //count of opening secret window not more than count of success logins 
ltl check_total { [] (total == success+fails || total+1== success+fails)} //total count of tryings = success + fails and +1 for time of increasing the value)
ltl we_open_nosecret { <> (windowNoSecret) } //sometime we open this window
ltl we_open_secret { <> (windowSecret) } //sometime we open this window
ltl we_open_any { [] <> (windowSecret || windowNoSecret)} //always sometime we open this window or that window
ltl login_check { <> windowLogin -> <> windowSecret} //sometime after the login we reach secret window
ltl no_secret_nosecret { [] !(windowSecret&&windowNoSecret) } //always the  two windows are not open at the same time

//channels for interprocess communication
chan login=[0] of {short};
chan nonsecret = [0] of {short};
chan secret = [0] of {short};

//main window proc
active proctype MainWindow(){
int buf;
printf("Main started");
do
    //infinite loop
    :: {
    printf("Main: go to Login window");
    //query login
    login! 1;
    //get the answer
    login? buf;
    if 
	:: buf == 1 ->  { //correct password
	    success++;
	    printf("Main: open secret window");
	    //open secret window
	    secret ! 1;
	    secret ? buf;//and wait for it
	}
	:: buf == 0 ->  { //incorrect password
	    fails++;
	    printf("Main: open nosecret window");
	    //open window nosecret
	    nonsecret ! 1;
	    nonsecret ? buf//and wait for it
	}
    fi
}
od
}

active proctype LoginWindow(){
int buf;
printf("Login started");
do
:: {
    login? buf;
    windowLogin = true;
    if //non-deterministic if
	::true-> { printf("Login fail"); windowLogin = false; login ! 0 }
	::true-> { printf("Login fail"); windowLogin = false; login ! 0 }
	::true-> { printf("Login ok!"); windowLogin = false; login ! 1 }
		//with the probability of 1/3 password is correct
    fi
}
od
}

active proctype NonSecretWindow(){
int buf;
printf("Non Secret started");
do
:: {
    nonsecret ? buf;
    printf("Non Secret window opened");
    windowNoSecret = true;
    total++;
    windowNoSecret = false;
    nonsecret ! 1;
    printf("Non Secret window closed");
}
od
}

active proctype SecretWindow(){
int buf;
printf(" Secret started");
do
:: {
    secret ? buf;
    printf("Secret window opened");
    windowSecret = true;
    secrets++; //increase secret count
    total++;
    windowSecret = false;
    secret ! 1;
    printf("Secret window closed");
}
od
}

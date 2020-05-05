/*
@brief Non-deterministic counter sample 
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

    int var = 2;
    int count = 0;
    ltl formula {[] (var >= 0)}
    active proctype main()
    {			
    do
	:: count != 3 ->
	{
	if
	    ::  true->  var = var + 1;
	    ::  true->  var = var - 1;
        fi
	count = count + 1;
	}
	:: else ->
	    break
    od
    }

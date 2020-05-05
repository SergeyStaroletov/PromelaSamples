/*
@brief Hanoi sample for using counterexample-driven approach to solve puzzles
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@license GNU GPL
*/

#define N 5
byte rod1 [N];
byte rod2 [N];
byte rod3 [N];
byte count1, count2, count3;
byte moves;

ltl count_check  { [] (count3 != 5) }

active proctype Step(){ 

count1 = N;
moves = 0;
rod1[0] = 5;
rod1[1] = 4;
rod1[2] = 3;
rod1[3] = 2;
rod1[4] = 1;

byte disk;
do 
		:: moves == 250 -> break;
		:: count1 > 0 -> {
	        	disk = rod1[count1-1]; 
			//на 2 стержень
			if 
			::(count2==0 || (count2 < N && rod2[count2-1] > disk )) -> {
				printf("Disk %d  from 1 to 2 \n", disk);
				rod2[count2] = disk;
				moves++;
				count1--;
				count2++;
			}
			::(count2==0 || (count2 < N && rod2[count2-1] > disk )) -> 				skip;
			fi
		} 
	
		:: count1 > 0 -> {
	        	disk = rod1[count1-1]; 
			//на 3 стержень
			if 
			::(count3==0 || (count3 < N && rod3[count3-1] > disk )) -> {
				rod3[count3] = disk;
					printf("Disk %d  from 1 to 3 \n", disk);
				moves++;
				count1--;
				count3++;
			}
			::(count3==0 || (count3 < N && rod3[count3-1] > disk )) -> 				skip;
			fi
		}
		:: count2 > 0 -> {
	        	disk = rod2[count2-1]; 
	
			//на 1 стержень
			if 
			::(count1==0 || ( count1 < N && rod1[count1-1] > disk  )) -> {
				rod1[count1] = disk;
				printf("Disk %d  from 2 to 1 \n", disk);
				moves++;
				count2--;
				count1++;			
			}
			::(count1==0 || (count1 < N && rod1[count1-1] > disk )) -> 				skip;
			fi
		} 

		:: count2 > 0 -> {
	        	disk = rod2[count2-1]; 
			//на 3 стержень
			if 
			::(count3==0 || (count3 < N && rod3[count3-1] > disk)) -> {
				rod3[count3] = disk;
				printf("Disk %d  from 1 to 3 \n", disk);
				moves++;
				count2--;
				count3++;
				
			}
			::(count3==0 || (count3 < N && rod3[count3-1] > disk)) -> 				skip;
			fi
		}

		:: count3 > 0 -> {
	        	disk = rod3[count3-1]; 
	
			//на 1 стержень
			if 
			::(count1==0 || (count1 < N && rod1[count1-1] > disk )) -> {
				rod1[count1] = disk;
				printf("Disk %d  from 3 to 1 \n", disk);
				moves++;
				count3--;
				count1++;
				
			}
			::(count1==0 || (count1 < N && rod1[count1-1] > disk )) -> 				skip;
			fi
		} 
		:: count3 > 0 -> {
	        	disk = rod3[count3-1]; 
			//на 2 стержень
			if 
			::(count2==0 || (count2 < N && rod2[count2-1] > disk )) -> {
				rod2[count2] = disk;
				printf("Disk %d  from 3 to 2 \n", disk);
				moves++;
				count3--;
				count2++;	
			}
			::(count2==0 || (count2 < N && rod2[count2-1] > disk )) -> 				skip;
			fi
		}
od
}


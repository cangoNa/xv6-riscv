#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"

int pipeline(int[]);

int
main(int argc, char *argv[])
{

	int nums[32];
	for(int i = 2; i <= 32; i++) {
		nums[i-2] = i;
	}
	nums[31] = 0;

	pipeline(nums);

	exit(0);
}

int pipeline(int given[]){
	// create pipe
	int p[2];
	pipe(p);
	int status;
	
	char buf[2];

	// child process
	if(fork() == 0) {
		int prime, reached;
		int c = 0;
		int nums[31];

		read(p[0], buf, sizeof(buf));
		// the first one if prime
		prime = atoi(buf);
		if(prime != 0) {
			printf("prime %d\n", prime);
			while(1) {
				memset(buf, 0, sizeof(buf));
				read(p[0], buf, sizeof(buf));
				reached = atoi(buf);
				printf("reached %d\n", reached);

				// cannnot decide
				if(reached % prime != 0) {
					nums[c] = reached;
					c ++;
				}

				// finish connect with 0
				else if(reached == 0){
					nums[c] = reached;
					break;
				}
			}
			pipeline(nums);
			close(p[0]);
			close(p[1]);
		}
		else {
			close(p[0]);
			close(p[1]);
			exit(0);
		}
	}
	// parent process
	else {
		for(int i = 0; i < 31; i++) {
			fprintf(p[1], "%d", given[i]);
			sleep(2);
		}

		wait(&status);

		close(p[0]);
		close(p[1]);
	}
	exit(0);
}
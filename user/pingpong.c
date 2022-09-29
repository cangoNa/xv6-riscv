#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"

int
main(int argc, char *argv[])
{
	// create pipe
	int p[2];
	pipe(p);
	
	char buf[32];

	// child process
	if(fork() == 0) {
		int pid;
		pid = getpid();

		// read -> print -> write back
		read(p[0], buf, sizeof(buf));
		printf("<%d>: received ping\n", pid);
		write(p[1], "pong\n", 5);

		close(p[0]);
		close(p[1]);
	}
	// parent process
	else {
		int pid;
		pid = getpid();

		// write -> read -> print
		write(p[1], "ping\n", 5);
		read(p[0], buf, sizeof(buf));
		printf("<%d>: received pong\n", pid);

		close(p[0]);
		close(p[1]);
	}

	exit(0);
}
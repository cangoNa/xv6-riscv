#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"

int
main(int argc, char *argv[])
{
	int p[2];
	pipe(p);
	char buf[32];

	if(fork() == 0) {
		int pid;
		pid = getpid();

		close(0);
		dup(p[0]);

		read(p[0], buf, sizeof(buf));
		printf("<%d>: received ping\n", pid);
		write(p[1], "pong\n", 5);

		close(p[0]);
		close(p[1]);
	}
	else {
		int pid;
		pid = getpid();

		write(p[1], "ping\n", 5);
		read(p[0], buf, sizeof(buf));
		printf("<%d>: received pong\n", pid);

		close(p[0]);
		close(p[1]);
	}

	exit(0);
}
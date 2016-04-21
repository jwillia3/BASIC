#include <stdio.h>
#include "basic.h"

PRINTS_() { puts((char*)*sp++); STEP; }

kwdhook_(char *msg) {
	if (!strcmp(msg,"PRINTS"))
		expr(), emit(PRINTS_);
	else	return 0;
	return 1;
}

main(int argc, char **argv) {
	FILE *sf=stdin;
	initbasic(0);
	kwdhook=kwdhook_;
	if (argv[1])
		if (sf=fopen(argv[1],"r"))
			compile++;
		else {
			printf("CANNOT OPEN: %s\n", argv[1]);
			return 255;
		}
	return interp(sf);
}

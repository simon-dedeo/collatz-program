CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11

# macOS / clang (no OpenMP): sequential build
mac: wfar

wfar: wfar.c
	$(CC) $(CFLAGS) -o wfar wfar.c

# Linux / gcc with OpenMP: parallel build
linux: wfar.c
	gcc $(CFLAGS) -fopenmp -o wfar wfar.c

test: wfar
	./wfar --selftest

clean:
	rm -f wfar

.PHONY: mac linux test clean

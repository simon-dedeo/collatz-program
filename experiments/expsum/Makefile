CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11

# macOS / clang (no OpenMP): sequential build
mac: expsum

expsum: expsum.c
	$(CC) $(CFLAGS) -o expsum expsum.c -lm

# Linux / gcc with OpenMP: parallel build
linux: expsum.c
	gcc $(CFLAGS) -fopenmp -o expsum expsum.c -lm

test: expsum
	./expsum selftest

clean:
	rm -f expsum

.PHONY: mac linux test clean

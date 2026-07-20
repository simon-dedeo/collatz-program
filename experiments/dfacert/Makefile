CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11

# macOS / clang (no OpenMP): sequential build
mac: dfacert

dfacert: dfacert.c
	$(CC) $(CFLAGS) -o dfacert dfacert.c

# Linux / gcc with OpenMP: parallel build
linux: dfacert.c
	gcc $(CFLAGS) -fopenmp -o dfacert dfacert.c

test: dfacert
	./dfacert --selftest

clean:
	rm -f dfacert

.PHONY: mac linux test clean

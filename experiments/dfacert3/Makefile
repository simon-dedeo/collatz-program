CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11

# macOS / clang (no OpenMP): sequential build
mac: dfacert3

dfacert3: dfacert3.c
	$(CC) $(CFLAGS) -o dfacert3 dfacert3.c

# Linux / gcc with OpenMP: parallel build
linux: dfacert3.c
	gcc $(CFLAGS) -fopenmp -o dfacert3 dfacert3.c

test: dfacert3
	./dfacert3 --selftest

clean:
	rm -f dfacert3

.PHONY: mac linux test clean

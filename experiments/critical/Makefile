# crit — BB-cryptid critical-drift experiment
CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra
LDLIBS   = -lm

all: crit

crit: crit.c
	$(CC) $(CFLAGS) -o crit crit.c $(LDLIBS)

omp: crit.c
	gcc -O3 -march=native -fopenmp -Wall -Wextra -o crit crit.c -lm

clean:
	rm -f crit

.PHONY: all omp clean

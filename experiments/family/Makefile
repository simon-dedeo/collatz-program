# family — fate census across families of generalized Collatz maps
#
#   make            portable build (macOS cc: sequential, no OpenMP)
#   make omp        Linux/gcc OpenMP build for the 32-core box
#   make selftest   build + run ground-truth selftests

CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra
LDLIBS   = -lm

all: family

family: family.c
	$(CC) $(CFLAGS) -o family family.c $(LDLIBS)

omp: family.c
	gcc -O3 -march=native -fopenmp -Wall -Wextra -o family family.c -lm

selftest: family
	./family --selftest

clean:
	rm -f family

.PHONY: all omp selftest clean

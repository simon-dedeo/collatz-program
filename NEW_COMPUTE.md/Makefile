CC ?= cc
CFLAGS ?= -O3 -march=native -std=c11 -Wall -Wextra -Wpedantic -fopenmp
LDLIBS ?= -lm

PROGRAMS = kl_soft_spectrum kl_frustration_scan kl_coercivity_atlas carry_budget minplus_profile zero_carry_champions hensel_atlas

.PHONY: all clean smoke

all: $(PROGRAMS)

kl_soft_spectrum: kl_soft_spectrum.c npy.h
	$(CC) $(CFLAGS) -o $@ kl_soft_spectrum.c $(LDLIBS)

kl_frustration_scan: kl_frustration_scan.c npy.h
	$(CC) $(CFLAGS) -o $@ kl_frustration_scan.c $(LDLIBS)

kl_coercivity_atlas: kl_coercivity_atlas.c npy.h
	$(CC) $(CFLAGS) -o $@ kl_coercivity_atlas.c $(LDLIBS)

carry_budget: carry_budget.c
	$(CC) $(CFLAGS) -o $@ carry_budget.c -lgmp $(LDLIBS)

minplus_profile: minplus_profile.c
	$(CC) $(CFLAGS) -o $@ minplus_profile.c -lgmp $(LDLIBS)

zero_carry_champions: zero_carry_champions.c
	$(CC) $(CFLAGS) -o $@ zero_carry_champions.c $(LDLIBS)

hensel_atlas: hensel_atlas.c
	$(CC) $(CFLAGS) -o $@ hensel_atlas.c -lgmp $(LDLIBS)

smoke: all
	mkdir -p results/smoke
	rm -f results/smoke/*.tsv
	./kl_soft_spectrum 8 1.9 4 200 1e-8 results/smoke/kl-soft.tsv -
	./kl_frustration_scan /ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k14.npy 1.8307718 results/smoke/kl-frustration.tsv
	./kl_coercivity_atlas /ocean/projects/mth260010p/sdedeo/collatz/kl/eigvec_k14.npy 1.8307718 1 results/smoke/kl-coercivity.tsv
	./carry_budget 50 8 20 results/smoke/carry.tsv
	./minplus_profile 10000 8 4 10000 results/smoke/minplus.tsv
	./zero_carry_champions 8 64 results/smoke/zero-champion.tsv
	./hensel_atlas 1000 2 2 2 results/smoke/hensel.tsv
	python3 verify_smoke.py results/smoke

clean:
	rm -f $(PROGRAMS)

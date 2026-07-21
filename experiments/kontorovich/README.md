# Kontorovich challenge: exact program synthesis

This directory turns the “Collatz hardware, seed as software” proposal into
exact search objects.  It uses the accelerated odd map

```text
T(x)=(3x+1)/2^v2(3x+1)
```

on positive integers coprime to `6`.  Nothing here treats a long finite path
as a counterexample.

## Exact compiler and certificate verifier

`path_compiler.py` compiles every finite positive valuation word into the
canonical least seed in either admissible class modulo `6`.  For a word
`k_0,...,k_(N-1)`, put `S_j=sum_(i<j) k_i` and

```text
A_N = sum_(j<N) 3^(N-1-j) 2^S_j.
```

The compiler checks by exact replay that

```text
2^S_N T^N(x) = 3^N x+A_N.
```

Exactness of the final valuation fixes `x` modulo `2^(S_N+1)`; CRT with one
class modulo `3` gives the Kontorovich--Sinai progression modulo
`3*2^(S_N+1)=6*2^S_N`.  The thread's example reproduces exactly:

```bash
python3 path_compiler.py selftest
python3 path_compiler.py compile 1,1,2,2 --class 1
```

The second command returns canonical seed `199`.  JSON integers that may
exceed the interoperable 53-bit range are strings.  A stored certificate is
independently replayed with

```bash
python3 path_compiler.py verify certificate.json
```

For a cycle word, closure requires

```text
x = A_N/(2^S_N-3^N).
```

`path_compiler.py cycle WORD` emits a certificate only when the denominator
is positive, division is exact, the seed is positive and coprime to `6`, every
claimed valuation replays exactly, and the endpoint equals the seed.  Seed
`1` is explicitly classified as the trivial accelerated cycle.  Any seed
greater than `1` would be a machine-checkable disproof candidate.

## Bounded adversarial searches

`search_programs.py` has two exact modes, run together:

1. exhaustive ordered compositions through a stated total-halving bound;
2. every binary uniform substitution prolongable on `0`, through a stated
   uniform width, every coding of its two symbols by bounded positive
   valuations, and every substitution depth below an expanded-length bound.

The second family is a deliberately low-description “glider” ansatz.  Besides
cycle closure, the search asks whether the least ordinary seed stabilizes as
nested morphic prefixes grow.  Stabilization is necessary for an infinite
prescribed 2-adic program to become one fixed ordinary positive seed.  Finite
stabilization remains only a prefix event.  Lean commit `ad36f08` proves the
infinite statement exactly: in a fixed admissible mod-6 class, a stream is
legal for an ordinary positive seed if and only if its canonical prefix seeds
eventually stabilize at that seed.

```bash
python3 search_programs.py --selftest
python3 search_programs.py \
  --max-total-halvings 22 \
  --max-uniform-width 4 \
  --max-k 4 \
  --max-word-length 16384 \
  --max-seed-word-length 512 \
  --output search_results.json
```

The result file records all bounds, exact counts, any cycle certificates, the
strongest seed-stabilization event, and a SHA-256 digest of the two source
files.  Cycle divisibility is tested through `--max-word-length`; the more
expensive CRT seed-stabilization test has its separately reported
`--max-seed-word-length` bound.  A negative result excludes only this finite
template class.  It does not improve the global computational verification
frontier.

## Distributed non-uniform morphic search

`search_nonuniform.py` expands the template class to every nonempty binary
morphism

```text
0 -> u,  1 -> v,
```

where `u` begins in `0` (so the fixed point is nested) and `u,v` have bounded,
not necessarily equal lengths.  Non-uniform images create growing gaps and
simple one-counter-like geometry unavailable to the uniform sweep.  The
worker carries compressed exact `(3^N,2^S,A_N)` blocks and is deterministically
sharded by morphism index.  Each shard still expands and literally replays
every closure or seed-stabilization hit.

`merge_nonuniform.py` requires every shard exactly once, checks common source
hashes and bounds, proves complete morphism-index coverage, and independently
replays any nontrivial cycle artifact.  A small two-shard regression is part
of `search_nonuniform.py --selftest`.

```bash
python3 search_nonuniform.py --selftest

# Example shard
python3 search_nonuniform.py \
  --max-image-length 6 --max-k 4 --max-depth 12 \
  --max-word-length 4096 --max-seed-word-length 512 \
  --shard-index 0 --shards 32 --output shard-000.json

# Merge only succeeds when all 32 consistent shards are present.
python3 merge_nonuniform.py --expect-shards 32 \
  --output nonuniform_results.json shard-*.json
```

`psc_nonuniform.sbatch` is the current Bridges-2 64-way launch prescription.
Its bounds are part of every shard artifact; changing the launch file creates
a different finite search and must not be silently merged with an earlier run.

## One-counter shadows of negative cycles

`search_shadow.py` turns a supercritical negative cycle into a finite carry
controller.  This does **not** use a negative integer as a counterexample.  For
the controller state `c<0`, valuation word `w`, and

```text
P=3^|w| > Q=2^sum(w),
```

a positive state `x=c+Q^M h` with odd `h` shadows `w` for `M` repetitions.
If the last valuation gains exactly `e` further powers of two, exact replay
gives the collision endpoint

```text
x'=(c+P^M h)/2^e.
```

The one-counter ansatz asks that `x'=c+Q^(M+1)h'`, replenishing the precision
spent by the collision.  With bounded `e`, sufficiently large successful
macrosteps grow because `(P/Q)^M/2^e>1`.  An infinite exact renewal would be a
candidate for the Lean `MacroGlider` endpoint; any finite chain is only a
prefix event.

```bash
python3 search_shadow.py --selftest
python3 search_shadow.py \
  --max-start-level 6 --max-extra 8 --max-program-depth 4 \
  --output shadow_results.json
```

The committed artifact exhausts the negative cycles at `-5` with word
`(1,2)` and `-17` with word `(1,1,1,2,1,1,4)`, every start level `1..6`, all
extra-valuation words over `{1,...,8}` of length at most four, and both
admissible classes modulo `6`.  All `112,320` compiled paths pass literal
valuation and shifted-coordinate replay.  There are zero ordinary-seed
stabilization events and zero terminal next-level renewals in this stated
class.  Source digest:
`dc33070c7d14db452aafe19c59ce097e301e895c593e2c0ec2d89424b2d72696`.

## Phase-changing shadow collisions

`search_phase_shadow.py` allows a carry collision to land near a different
phase of the same negative cycle.  At level `M`, a symbol `(i,e)` means: start
near negative phase `c_i`, run `M` copies of the valuation word rotated to
that phase, and add `e` powers of two at the terminal collision.  The next
symbol must start near its selected phase modulo `Q^(M+1)`.  The worker checks
the shifted-coordinate formula and literally replays every positive path.

Two committed runs use different bounds because the cycles have two and seven
phases:

```bash
python3 search_phase_shadow.py --selftest
python3 search_phase_shadow.py --cycle minus5 \
  --min-start-level 1 --max-start-level 12 \
  --max-extra 8 --max-program-depth 4 \
  --output phase_minus5_results.json
python3 search_phase_shadow.py --cycle minus17 \
  --min-start-level 1 --max-start-level 6 \
  --max-extra 4 --max-program-depth 3 \
  --output phase_minus17_results.json
```

The `-5/-7` artifact exhausts `838,848` phase/extra programs and `1,677,696`
compiled paths in the two mod-6 classes.  It finds 15 terminal next-level
renewals and 10 one-extension canonical-seed stabilizations.  All renewals
start at level one or two, every next macro shrinks, and every event loses
alignment immediately after that added macro.  A compact regression is

```text
phase/extra:  (-7,2), (-5,3), (-7,1), (-7,1)
levels:       1,      2,      3,      4
macro states: 53403857 -> 15019835 -> 2376185 -> 1691641 -> 1354843.
```

The same ordinary seed is canonical before and after the fourth macro, but
`1354843` is in neither negative phase class at precision level five.  This is
an exact finite carry-renewal example, not a divergent orbit.

The seven-phase `-17` artifact exhausts `136,584` programs and `273,168`
compiled paths; it finds no stabilization or renewal.  Together the artifacts
check `1,950,864` paths.  Their common source digest is
`b830ebcea08fb1822b204bfcd60a1570870ffa5a170b14f0d12fbb68bcc857cc`.

The soundness endpoint is kernel-checked.  Lean commits `3d9cedc`/`93cafe1`
prove the shifted-coordinate identity, eventual strict growth when collision
extras are uniformly bounded, and the literal negation of Collatz from an
infinite exact phase-renewal witness.  Commits `edcee1a`/`0d8c3d2` check the
signed `-5` and `-17` cycles and prove that every rotated phase supplies the
required affine controller.  The finite artifacts above do not instantiate
the infinite witness type.

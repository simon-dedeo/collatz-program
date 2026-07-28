# Six Bridges-2 RM computations

Status: RM campaign complete, proof-facing synthesis written 2026-07-28.

This directory is intentionally named `NEW_COMPUTE.md/` at the user's
request.  It contains specifications, native workers, launch files, and the
eventual job ledger.  Results live on PSC under
`/ocean/projects/mth260010p/sdedeo/new_compute/results/` and are not claims
until their stated checks complete.

The campaign charged approximately 12,374.36 RM core-hours.  Its exact finite
results, floating KL diagnostics, hashes, failed-checkpoint caveats, and two
new kernel-checked promotion interfaces are summarized in
[`RM_RESULTS_2026-07-28.md`](RM_RESULTS_2026-07-28.md).  No job found a Collatz
counterexample.

## Current mathematical boundary

### KL proof

The portable `k=12` certificate and its counting consequence are Lean-native.
The local exact `k=19` record gives every fixed predecessor exponent below
`0.9094372617` under the documented mixed exact-Python/kernel-Lean policy.
An infinite strict feasible ladder is proved, but no quantitative rate forces
`lambda_k` to two.  The two direct open consumers are:

1. an amortized selected hard-min gain with divergent effective sum; or
2. a positive soft subeigenvector whose factor exceeds `3^(1/beta)`.

The finite selected records support a quadratic coarse-minimum gain, terminal
defect of order `1/k`, and terminal Pearson energy of order `1/k^2`; none is
an all-level theorem.  Generic feasible vectors, generic simplex divergence,
unweighted shell `L2`, and unrestricted larger-level numerics are recorded
closed lanes.  Jobs K1 and K2 therefore interrogate the two named live seams,
not merely another hard-min eigenvector at a larger level.

### Counterexample search

No positive Collatz counterexample is known.  Long finite programs, negative
2-adic cycles, independent finite cylinders, periodic schedules, and wider
generic charge scans have failed the ordinary-root/coherence gate.  For the
complete small first-passage subcode `{1,011,010111}`, exact Bellman search
excludes total extension-carry budgets `0,...,28`; bounded carry would have to
collapse to an eventually zero-carry aperiodic ray.  The reduced zero-carry
map is

```text
H even       -> 3H/2
H=5  mod 8   -> (9H+3)/8
H=49 mod 64  -> (81H+63)/64.
```

Every branch grows and every eventually periodic address is impossible for
positive `H`.  A rare exact `c->2->2` singular renewal first occurs at
`c=11626231`, but fails at its next writer.  Jobs C1--C4 attack bounded carry,
the growing triadic minimum profile, thin aperiodic cylinders, and generalized
singular resonances respectively.

## K1 — fixed-temperature KL saturation

Worker: `kl_soft_spectrum.c` (OpenMP, 128 cores).

It applies the literal power-mean KL operator without materializing index
arrays, and reports a floating Collatz--Wielandt bracket at large `k` and cold
`beta`.  The decisive finite event would be

```text
CW lower bound > 3^(1/beta).
```

That event is still only floating until an interval/exact certificate checks
the saved vector.  A persistent positive gap from the annealed value would
instead be a kill signal for fixed-temperature saturation.  This is the most
direct numerical probe of the kernel-checked soft-to-hard consumer.

## K2 — KL curvature and endogenous frustration at `k=20`

Worker: `kl_frustration_scan.c` (OpenMP, 128 cores).

It streams the existing 9.3 GB floating `k=20` Perron vector, constructs its
first and iterated ternary minima, and measures on every branch edge:

- the exact-form hard transport/branch mismatch;
- the endogenous second-gap frustration lower bound;
- finite-temperature Jensen curvature at six coldness scales;
- the sharp smoothing-error allowance; and
- every later minimum-profile defect.

The main diagnostic is whether `curvature - error` clears a positive multiple
of `G epsilon^2`, and whether the hard/frustration ratios continue the
selected `k=12,...,15` trend.  Inputs and outputs are floating, so this job
orients a theorem and cannot establish one.

### K2b — multiscale cold-error and transport-block coercivity atlas

Worker: `kl_coercivity_atlas.c` (OpenMP, five-node Slurm array).

K2 completed far below its wall-time cap because it was a streaming
first-stage diagnostic.  Its `k=20` pass found hard gain `2.5343` times the
quadratic target and second-gap frustration `1.5517` times the target, but
the uniform smoothing allowance still made the conservative finite-beta
quantity negative at `beta=256`.  K2b attacks that exact separation between
strong hard signal and weak soft control.

The five array elements scan every branch edge of the existing `k=16,...,20`
vectors concurrently, one full 128-core RM node per level.  For every
available projection depth they compute:

- eleven cold scales from `beta=64` through `65536`;
- the actual absolute cold-to-hard discrepancy and a row-specific safe
  smoothing envelope, separately from the old global worst-case allowance;
- hard gain and second-gap frustration arranged around the complete affine
  transport cycle; and
- every ternary block length, including minimum/maximum gain relative to its
  mean, low-gain window fractions, coefficient of variation, and the longest
  frustration-free run.

This is a direct kill test for the proposed amortized/checkpoint bridge.  If
transport-block minima stabilize above a positive fraction of their mean,
they suggest a block coercivity theorem.  If arbitrarily long nearly empty
blocks persist as the level grows, that simple theorem is not viable.  Later
projected profiles are supersolutions with inherited slack, so their rows are
reported separately and are not mislabeled as critical eigenvectors.  All
K2b quantities remain floating diagnostics; even the integer-input levels
need an exact follow-up before promotion.

The first production atlas completed all five levels in 4--93 seconds.  Its
hard and transport-block columns are finite and reproduce K2 at the shared
levels.  The cold columns at `k=19,20` are invalid (`NaN`): the first stable
subtraction fix did not cover the full dynamic range.  Build `42720091`
therefore adds strict input validation, evaluates conditional ratios in the
log domain, and uses homogeneity before applying branch weights.  The
two-level repair array fails loudly if any nonfinite token remains.

### Aggressive follow-up K1b/C2b/C3b

The first jobs established that the useful kernels were much faster than
their caps.  Three bounded extensions redeploy the released allocation:

- `psc_k1b_frontier.sbatch`: six simultaneous full nodes, one for each
  `lambda=1.84,...,1.89`, scanning levels 20--22 and
  `beta=64,...,2048`.  This maps whether the floating soft-to-hard crossing
  frontier moves toward two.  Every completed case and every 25-iteration
  bracket survives wall time; no large vectors are saved.
- `psc_c2b_minplus.sbatch`: an exact exhaustive profile through
  `B=5.5*10^12`, depth 160, and triadic exponent 10.  The target follows the
  completed `B=5*10^11` pass, which used 99.48% CPU efficiency and had no
  surviving global slice at depth 72.
- `psc_c3b_shard.sbatch`: the exact depth-27 zero-carry census partitioned
  into three disjoint congruence shards, each on a full node.  A dependent
  one-core collector checks every shard hash, proves that the shard indices
  and schedule counts partition `3^27`, sums the histograms, and selects the
  champion with the same deterministic tie rule as the unsharded worker.

These are still bounded computations.  A K1b crossing is floating; C2b says
nothing above its printed source bound; and C3b says nothing about schedules
past its printed cylinder depth.

## B1 — bouncer backward-cylinder atlas

Worker: `bouncer_atlas.c` (exact GMP arithmetic + OpenMP, four-node array).

This is the first PSC computation aimed directly at the autonomous
valuation-selected unit-charge bouncer rather than a prescribed opcode
schedule.  For every triple `(m,h,m')` in a finite box, it derives the exact
affine family of positive odd fixed-register inputs whose literal bouncer
step has input phase `m`, collision phase `h`, and next input phase `m'`.
It then links those families backward by exact generalized CRT.  Failed links
are genuine empty cylinder intersections; successful links retain the least
positive ordinary root, the full affine stride, and an exact replay code.

The production array uses

```text
1 <= m,h,m' <= 12,  five linked bouncer blocks,  four disjoint shards.
```

There are 1,728 one-block edge families, 248,832 two-block prefix tasks,
5,159,780,352 possible depth-four paths, and at most 743,008,370,688 linked
depth-five opcode paths.  The final numbers are upper bounds because
incompatible intermediate cylinders are pruned.  The
atlas records link failures, canonical-root stabilizations/decreases,
nonoutward finite paths, and the least root and least root increment at every
depth.  These statistics are designed to expose either an unexpectedly
coherent backward ray or a finite obstruction suitable for a height theorem.

Every edge is independently replayed in C at two affine parameters.  A
separate Python verifier reconstructs the complete small box from the
literal bouncer formula and independently recomputes all pairwise links.
The production shards are SHA-256 pinned; a dependent collector checks their
partition and identical edge tables before combining them.

This remains a finite atlas, not a counterexample.  In particular, a finite
root stabilization is not an infinite compatible ray.  The worker receives
a pre-wall-time signal, checkpoints only completed prefix batches, writes
`status=partial`, and exits cleanly.  Thus even a wall-time-limited run leaves
exact linked-cylinder data for later proof iterations, while only full
coverage can receive `status=complete`.

The Cook catalytic-memory follow-up changes the interpretation of the fixed
register.  Exact stride arithmetic gives every consecutive bouncer link a
tail-refinement index divisible by `2^(154*h'+23*m'')`, hence at least
`2^177`.  The bounded `m,h,m'<=12` audit checks all 248,832 links and finds
no index-one clean tail.  Thus the natural affine address tail is consumed,
not restored as a reusable catalyst.  The backward atlas remains useful as a
precision/obstruction dataset, but any genuinely autonomous bouncer now needs
a different nonlinear catalyst coordinate with a fixed interface.  The
generic algebra is research-side pending formalization; the displayed finite
scan is exact and rebuildable in `ias_cook_bouncer_catalyst.py`.

## B2 — exact finite Bellman-potential CEGIS

Worker: `carry_policy_cegis.c` (GMP + OpenMP, four-node array).

The extension carry is the natural Yap-style integer local energy.  B2 looks
for an arithmetic potential `V` and a legal extension at each sampled exact
state satisfying

```text
q(s,w) + scale*V(s*w) <= scale*V(s).
```

Each worker constructs independently seeded training and held-out corpora of
8,192 literally reachable states.  It evaluates all legal words at each state
using the same exact carry equation as C1.  The 25-term grammar contains
`D,c,bitlen(z)`, three capped exact valuations, a quadratic in `(D,c)`, and a
16-entry `z mod 16` table.  Integer coefficients are searched in parallel;
the required positive scale is recovered exactly from each strict inequality.

Two shards use the three-word code and two use the larger source-residue-250
code.  Within each pair, one shard enforces a positive-definite quadratic and
nonnegative unbounded-feature coefficients, a sufficient lower-boundedness
gate; the other is relaxed to diagnose which coercivity condition prevents a
fit.  Every saved candidate is independently reconstructed and rescored in
Python on both corpora before collection.

This is finite stochastic CEGIS, not an exhaustive coefficient search or an
all-state certificate.  Even a perfect two-corpus fit is only a conjectured
formula to attack symbolically.  A miss supplies exact obstruction states and
grammar diagnostics.  Only a separately proved all-state inequality, literal
policy closure, and nonnegative potential could bound total carry and promote
the construction.

## C1 — enlarged exact carry Bellman frontier

Worker: `carry_budget.c` (GMP + OpenMP, at least 1,024 independent prefix
chunks).

It rebuilds the complete finite first-passage code selected by a canonical
source-residue bound and exhausts every compatible schedule prefix below a
stated cumulative carry budget.  Each node uses exact `mpz_t` values for the
canonical source, endpoint, and powers of two and three.  Extinction at depth
`d` proves that budget impossible for that finite code; survival to a depth
cap proves nothing beyond the cap.  The production sweep moves beyond budget
28 and then enlarges the code from 3 to 4, 13, and 20 words.

## C2 — growing triadic min-plus profile and tax slice

Worker: `minplus_profile.c` (OpenMP, 128 source shards, shared atomic minima).

For every source in the exact interval `1<=x<=B`, it evaluates literal
first-passage blocks and fills

```text
m_n(k,a)=min{x: x survives n blocks and x=a mod 3^k}.
```

It reports the selected residue-two minimum and the least-survivor tax as well
as occupancy summaries at every triadic precision.  This is the repository's
specified successor to simply widening a seed interval: the finite scan is
organized around the growing-precision inverse-renewal state.  Checked
overflow and step caps make failure loud rather than silently inexact.

## C3 (weird) — canonical zero-carry cylinder champions

Worker: `zero_carry_champions.c` (OpenMP, 128 schedule shards).

Every branch word of a fixed depth determines one dyadic cylinder.  The
worker constructs its least nonnegative ordinary representative exactly,
then asks how many total and additional deterministic zero-carry branches that same
ordinary integer survives.  This is an Archimedean-height probe of a thin
2-adic full shift: a surprising champion would expose a recursively useful
address, while an ordinary-looking tail distribution would calibrate how
strong the missing height theorem must be.  It is exhaustive only at the
displayed prefix depth and is not a counterexample search by interval.

## C4 (weird) — singular Hensel-resonance atlas

Worker: `hensel_atlas.c` (GMP + OpenMP, 128 contiguous `c` shards).

For fixed small target counters `(d,e,f)`, it scans canonical sources in
increasing `c` using modular recurrences rather than constructing the enormous
integer.  It tests exact two- and three-link divisibility for

```text
2^(M_d+d+4) q' = 3^(M_c+d+1) q + 7*3^(d+1)+2^(d+4),
M_j=2*3^j.
```

This generalizes the unexpectedly sparse `c->2->2` hit.  A three-link hit is
a finite CEGIS witness to replay and extend, not a Collatz counterexample.

## PSC allocation and launch envelope

The live `projects` ledger on 2026-07-27 showed 11,875 Regular Memory SUs and
1,993 GPU SUs.  Bridges-2 defines one RM SU as one core-hour; a full RM node is
128 cores and therefore costs 128 SUs/hour.  Each of the original six
production scripts requests one full node for 13 hours.  Their simultaneous
caps give

```text
6 jobs * 128 cores * 13 hours = 9,984 SUs,
```

leaving 1,891 RM SUs before short smoke-test charges.  See the official
[Bridges-2 accounting guide](https://www.psc.edu/resources/bridges-2/user-guide/#accounting-for-bridges-2-use).

K2 actually completed in 77 seconds, K1 in 75 minutes, C2 in 55 minutes, and
the original C1 stopped after 22:40, so most of their unused caps were not
charged.  K2b's five levels then took only 4--93 seconds.  The aggressive
follow-up caps are 2,304 SUs for six K1b nodes, 1,536 SUs for C2b, 2,496 SUs
for three C3b shards, and about 85 SUs for the K2b repair.  Adding those caps
to the three original jobs still running, their elapsed work, the completed
jobs, and short build/scaling charges keeps the all-caps envelope near the
11,876-SU grant.  Expected use is around the requested 10k SUs, but actual
accounting remains runtime-based.

The user has authorized B1 against an additional roughly 2,000 RM SUs expected
to arrive.  Its four 128-core tasks request four hours each (a 2,048-SU hard
cap), but signal themselves five minutes before wall time, making the intended
maximum productive charge about 2,005 SUs plus a negligible shared-node build
and collector.  If it finishes early, PSC charges only elapsed core-hours.

B2 adds four two-hour full-node caps (1,024 SUs).  Its workers stop their
search internally after 6,800 seconds, so intended use is about 967 SUs plus
verification.  This launch was explicitly requested after the Bellman-energy
formulation; accounting remains elapsed-time based and the live PSC ledger is
authoritative.

All production scripts set `OMP_NUM_THREADS=128`, bind one thread per core,
and log CPU binding plus elapsed time.  File transfer uses the DTN
`data.bridges2.psc.edu`; jobs are submitted only from the login node.

## Verification and promotion rules

1. `psc_compile_smoke.sbatch` compiles the original workers with GCC;
   `psc_bouncer_build.sbatch` separately compiles B1 and runs its independent
   unsharded, sharded-collector, and scale regressions without disturbing
   executables needed by already queued jobs.
2. Production logs must show 128 OpenMP threads and a successful exit.
3. K1/K2 remain explicitly floating diagnostics.  Any proposed KL promotion
   needs interval or exact certificate verification and then the existing
   formal consumer.
4. C1/C2/C3/C4 are exhaustive only inside their printed bounds.  Their source
   and result files will be SHA-256 pinned after completion.  Any candidate is
   replayed by independent Python big-integer code before it is described as
   more than a candidate.
5. Every artifact retains `counterexample=null` unless a positive seed is
   literally replayed and certified never to reach one; no current worker can
   make that infinite claim by itself.

### Wall-time resilience

The 13-hour limits are caps, not assumptions that every final box completes.
K1 appends a valid floating CW bracket every 25 iterations and atomically
saves a resumable raw vector every 250.  K2 completes and copies a `k=18`
checkpoint before its `k=20` pass.  K2b flushes each complete projection
stage and each hard/frustration block family before moving onward.  C1 runs
all budget-28/code-size baselines before harder budgets; C2 writes and hashes
each of `B=10^8`, `10^10`, and `5*10^11`; C3 writes one file per completed
prefix depth; and C4 writes one file per completed counter triple.  K1b
retains every completed parameter case and live 25-iteration brackets.  C3b
retains independently hashed shards, but only its dependent collector may
label their union exhaustive.  Thus a wall-time exit leaves completed bounded
boxes plus explicit partial diagnostics.  A later driver must never call an
interrupted box exhaustive merely because its job consumed the full
allocation.

## Job ledger

| job | script | cap | PSC job id | state/result |
|---|---|---:|---:|---|
| build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42712025 | failed safely: carry terminal-state bug |
| build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42712088 | compiled; first smoke suite passed |
| build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42712131 | native runs passed; checker hit old Python syntax |
| build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42712163 | native runs passed; corrected bad expected min-profile row |
| build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42712182 | six-worker independent smoke verification passed |
| scale | `psc_scaling.sbatch` | 64 SU | 42712200 | failed safely on old 128-bit word cap |
| scale | `psc_scaling.sbatch` | 64 SU | 42712368 | six kernels completed; KL used ~111–115 cores |
| K1 | `psc_k1_soft.sbatch` | 1,664 SU | 42712598 | completed in 75:02 at 94.03% CPU efficiency; output/hash and four checkpoints present |
| K2 | `psc_k2_curvature.sbatch` | 1,664 SU | 42712599 | completed in 77 s; output and hashes present |
| C1 | `psc_c1_carry.sbatch` | 1,664 SU | 42712600 | three K=28 baselines saved; stopped safely at B=500 on a prefix-fanout guard |
| C2 | `psc_c2_minplus.sbatch` | 1,664 SU | 42712601 | completed through exact B=5*10^11 in 54:31 at 99.48% CPU efficiency |
| C3 | `psc_c3_champions.sbatch` | 1,664 SU | 42712602 | completed depth 26; champion total survival 87; `counterexample=null` |
| C4 | `psc_c4_hensel.sbatch` | 1,664 SU | 42712603 | completed all seven exact boxes; sparse links, no counterexample |
| rebuild | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42715864 | fanout fix compiled; six-worker smoke verification passed |
| C1 resume | `psc_c1_carry_resume.sbatch` | 1,664 SU | 42715865 | completed; at B=500, K=29 first empty depth is 171 |
| K2b build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42718933 | first atlas smoke passed; exposed a cold-subtraction precision issue |
| K2b rebuild | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42718988 | stable `expm1` cold excess; seven-worker smoke verification passed |
| K2b | `psc_k2b_coercivity.sbatch` | 5 × 256 SU | 42719003_[0-4] | completed in 4--93 s; hard/block columns valid, cold columns invalid at k=19,20 |
| aggressive build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42720091 | log-domain cold fix and exact three-shard merge regression passed |
| K2b repair | `psc_k2b_coldfix.sbatch` | 2 × 42.7 SU | 42720120_[0-1] | completed; valid k=19,20 cold columns and hashes |
| K1b | `psc_k1b_frontier.sbatch` | 6 × 384 SU | 42720134_[0-5] | timed out safely; each shard retained 16 complete rows, including four floating crossings at lambda 1.89 |
| C2b | `psc_c2b_minplus.sbatch` | 1,536 SU | 42720135 | completed exact B=5.5*10^12 profile; first null selected slice at depth 88 |
| C3b | `psc_c3b_shard.sbatch` | 3 × 832 SU | 42720136_[0-2] | timed out; intended checkpoint was not written, so no exhaustive shard result |
| C3b collector | `psc_c3b_collect.sbatch` | 0.33 SU | 42720137 | stranded `DependencyNeverSatisfied`; no combined claim |
| B1 build | `psc_bouncer_build.sbatch` | 1.33 SU | 42720597 | failed safely: independent replay exposed missing pre-division modulus in edge CRT |
| B1 build | `psc_bouncer_build.sbatch` | 1.33 SU | 42720641 | cancelled during smoke after task-count name shadowing was diagnosed |
| B1 build | `psc_bouncer_build.sbatch` | 1.33 SU | 42720651 | C smoke passed; old PSC Python rejected modern annotation syntax |
| B1 build | `psc_bouncer_build.sbatch` | 1.33 SU | 42720654 | exact C/Python replay and four-shard merge passed |
| B1 signal build | `psc_bouncer_build.sbatch` | 1.33 SU | 42720663 | exact replay, merge, scale, and clean partial-checkpoint signal tests passed |
| B1 | `psc_bouncer_atlas.sbatch` | 4 × 512 SU | 42720684_[0-3] | wall-time partial; exact checkpoints cover 87,040/248,832 prefix tasks |
| B1 collector | `psc_bouncer_collect.sbatch` | 0.33 SU | 42720685 | combined and hashed the exact partial coverage |
| B2 build | `psc_carry_policy_build.sbatch` | 1.33 SU | 42721689 | cancelled safely: first independent verifier attempted an exponential word generator |
| B2 build | `psc_carry_policy_build.sbatch` | 1.33 SU | 42721705 | exact C corpus and independent Python reconstruction agreed |
| B2 | `psc_carry_policy.sbatch` | 4 × 256 SU | 42721735_[0-3] | completed; strict held-out coverage 8189/8192 and 8190/8192, relaxed 8192/8192 but noncoercive |
| B2 collector | `psc_carry_policy_collect.sbatch` | 0.5 SU | 42721737 | completed; hashes checked and all four corpora independently rebuilt exactly |

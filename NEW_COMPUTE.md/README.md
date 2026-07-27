# Six Bridges-2 RM computations

Status: implementation and smoke testing in progress, 2026-07-27.

This directory is intentionally named `NEW_COMPUTE.md/` at the user's
request.  It contains specifications, native workers, launch files, and the
eventual job ledger.  Results live on PSC under
`/ocean/projects/mth260010p/sdedeo/new_compute/results/` and are not claims
until their stated checks complete.

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

K2 actually completed in 77 seconds and the original C1 stopped after 22:40,
so their unused caps were not charged.  The K2b follow-up is a five-element
array capped at two hours per 128-core element, or 1,280 SUs total.  Counting
the four still-running original jobs, the C1 resume, the two short completed
jobs, and K2b gives a conservative production ceiling of about 9,650 SUs,
plus the small build/scaling charges.  Thus the follow-up reuses released
capacity rather than silently turning the requested roughly-10k-SU campaign
into a much larger one.

All production scripts set `OMP_NUM_THREADS=128`, bind one thread per core,
and log CPU binding plus elapsed time.  File transfer uses the DTN
`data.bridges2.psc.edu`; jobs are submitted only from the login node.

## Verification and promotion rules

1. `psc_compile_smoke.sbatch` must compile every worker with GCC and run all
   seven tiny regressions.
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
stage and each hard/frustration block family before moving onward.  C1 runs all budget-28/code-size baselines
before harder budgets; C2 runs `B=10^7`, then `10^8`, then `10^9`; C3 writes
one file per completed prefix depth; and C4 writes one file per completed
counter triple.  Thus a wall-time exit leaves completed bounded boxes plus
explicit partial diagnostics.  A later driver must never call an interrupted
box exhaustive merely because its job consumed the full allocation.

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
| K1 | `psc_k1_soft.sbatch` | 1,664 SU | 42712598 | running on `r302`; brackets/checkpoints present |
| K2 | `psc_k2_curvature.sbatch` | 1,664 SU | 42712599 | completed in 77 s; output and hashes present |
| C1 | `psc_c1_carry.sbatch` | 1,664 SU | 42712600 | three K=28 baselines saved; stopped safely at B=500 on a prefix-fanout guard |
| C2 | `psc_c2_minplus.sbatch` | 1,664 SU | 42712601 | running; B=10^8 and 10^10 outputs and hashes present |
| C3 | `psc_c3_champions.sbatch` | 1,664 SU | 42712602 | running; depth-19 and depth-22 outputs and hashes present |
| C4 | `psc_c4_hensel.sbatch` | 1,664 SU | 42712603 | running; first three B=10^9 boxes and hashes present |
| rebuild | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42715864 | fanout fix compiled; six-worker smoke verification passed |
| C1 resume | `psc_c1_carry_resume.sbatch` | 1,664 SU | 42715865 | running on `r456` |
| K2b build | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42718933 | first atlas smoke passed; exposed a cold-subtraction precision issue |
| K2b rebuild | `psc_compile_smoke.sbatch` | 4 cores × 20 min | 42718988 | stable `expm1` cold excess; seven-worker smoke verification passed |
| K2b | `psc_k2b_coercivity.sbatch` | 5 × 256 SU | 42719003_[0-4] | submitted; five levels pending for RM nodes |

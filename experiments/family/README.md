# family — fate census across families of generalized Collatz maps

Phase-diagram generator for Michel's generalized Collatz mappings. Fix a
modulus `d` and coefficient rows `(a_i, b_i)`, `i = 0..d-1`; the map is

    f(m) = a_i * q + b_i        where m = d*q + i    (i = m mod d)

v1 restricts to nonnegative maps: `a_i >= 0`, `b_i >= 0`, and `f(m) >= 1`
for all `m >= 1`, which (rows being monotone in `q`) reduces to

    row 0     :  a_0 + b_0 >= 1     (smallest argument is q = 1)
    row i > 0 :  b_i       >= 1     (q = 0 gives f(i) = b_i)

All rows are total, so orbits are defined forever. The per-map engine is the
validated `../fate.c` architecture: ascending `n` with drop-below-start fate
inheritance, Brent cycle detection, `u128` values, overflow cap `2^100`,
step cap `50000`.

## Named anchors (d = 2)

| name    | rows            | equivalent            | ground truth at N = 10^5..10^6 |
|---------|-----------------|-----------------------|--------------------------------|
| COLLATZ | (1,0),(6,4)     | 3m+1                  | 1 cycle (min 1, len 3), 100% absorbed |
| NEG3X   | (1,0),(6,2)     | 3m-1                  | 3 cycles, mins 1, 5, 17; all absorbed |
| FIVEX   | (1,0),(10,6)    | 5m+1                  | 3 cycles, mins 1, 13, 17; majority overflow |
| HYDRA   | (3,0),(3,1)     | floor(3m/2)           | fixed point 1; every n > 1 overflows |
| RIGID   | (1,0),(1,1)     | f(2q)=q, f(2q+1)=q+1  | all n -> 1; H(fate|residue) = 0 |

## Build

    make          # macOS / portable: cc -O2 -Wall -Wextra (sequential)
    make omp      # Linux 32-core box: gcc -O3 -march=native -fopenmp

Zero warnings under `-Wall -Wextra` with both clang and gcc.

## Usage

    ./family --selftest                # mandatory ground-truth checks
    ./family anchors  [N]              > anchors.tsv
    ./family grid2    [A] [B] [N]      > grid2.tsv     # defaults 9 9 1e6  (8910 maps)
    ./family critical [Bmax] [N]       > critical.tsv  # defaults 63 1e6   (12096 maps)
    ./family grid3    [NSAMP] [N]      > grid3.tsv     # defaults 20000 1e6

TSV goes to stdout, progress to stderr. Maps are parallelized with
`omp for schedule(dynamic)` (each map's census is sequential); rows are
buffered and emitted in deterministic map order, so output is
run-to-run identical regardless of thread count.

Modes:

- **grid2** — all valid d=2 maps with `a_i <= A`, `b_i <= B` (invalid rows
  skipped). Defaults give 99 x 90 = 8910 maps.
- **critical** — the d=2 zero-drift line `a_0 * a_1 = d^2 = 4`:
  `(a_0,a_1) in {(1,4),(2,2),(4,1)}`, `b_i <= Bmax`. Note `(2,2)` maps are
  *additive* (`f(m) = m + const` per residue); their step-capped orbits are
  resolved analytically by the translation-trap fast path (see Performance).
- **grid3** — d=3, all coefficients `<= 6` (84,672 valid maps), fixed-seed
  xorshift64 partial Fisher-Yates subsample (deterministic).
- **anchors** — the 5 named maps above.

## Output columns

One row per map:

| column | meaning |
|---|---|
| `d`, `a0 b0 a1 b1 a2 b2` | map coefficients (`-` for unused rows when d < 3) |
| `drift` | naive log-drift `(1/d) * sum_i ln(a_i/d)` (nats) |
| `drift_flag` | 1 if some `a_i = 0` (those rows contribute `ln(1/d)`) |
| `n_cycles` | distinct cycles found (registry cap 32; 32 means "at least 32", and a stderr note is emitted when the registry saturates — extra cycles are lumped into one "extra cycle" fate class) |
| `cycle_mins` | minima of the top 4 cycles by basin size, semicolon-joined (`-` if none) |
| `frac_c1..frac_c4` | fraction of [1,N] absorbed into each of the top 4 cycles |
| `frac_overflow` | fraction exceeding 2^100 (presumed divergent) |
| `frac_cap` | fraction unresolved after the step cap (additive drifters, slow zero-drift walks) |
| `fate_H` | marginal fate entropy H(fate) in bits over n in (N/2, N] (baseline for the rigidity probe) |
| `rigidity_min_H` | min over m in {2,3,4,6,8,9,12,16,18,24,27,36} of H(fate \| n mod m), bits, over n in (N/2, N] |
| `rigidity_argmin_m` | smallest modulus achieving that minimum |
| `max_exc_log2` | log2 of the largest value reached before fate resolution, over all n |
| `mean_steps` | mean steps to fate *resolution* (drop below start / cycle closure / overflow / cap) |
| `name` | anchor name, `-` for swept maps |

Interpretation: a rigid / solved-type map (fate eventually constant on
residue classes) has `rigidity_min_H ~ 0`; a mixing map has
`rigidity_min_H ~ fate_H`. Maps with a single global attractor have
`fate_H = 0`, making rigidity trivially 0 — always read `rigidity_min_H`
against `fate_H`.

### Caveats

- **drift** is the uniform-residue heuristic; it ignores forced-residue
  correlations. E.g. COLLATZ in this (non-accelerated) representation has
  drift `+0.203` yet converges, because `6q+4` is always even. The shortcut
  Collatz `(1,0),(3,2)` (i.e. `T(m) = (3m+1)/2`) appears in grid2 with drift
  `-0.144`. Deviations between drift sign and observed fate are exactly the
  rigidity signal this dataset is for.
- **max_exc / mean_steps** are measured up to fate *resolution* (inheritance
  truncates at the first drop below the starting point), the same semantics
  as fate.c blocks — not full-orbit statistics.
- Fractions `frac_c1..4 + frac_overflow + frac_cap` need not sum to 1 when
  there are more than 4 cycles.

## Selftest

`./family --selftest` (N = 10^5) checks the validity rules plus the anchor
ground truths listed above, including exact cycle (min, length) sets:
COLLATZ (1,3); NEG3X (1,2),(5,5),(17,18); FIVEX (1,7),(13,10),(17,10);
HYDRA and RIGID (1,1). RIGID must give `rigidity_min_H = 0` exactly;
NEG3X must give `rigidity_min_H > 0.1` (mixing). Exit status 0 iff all pass.

## Performance notes

- Memory: one `(N+1)`-byte fate array per thread (1 MB/thread at N = 10^6),
  plus ~64 B/row output buffer.
- Convergent and strongly divergent maps cost O(10-300) steps per n.
- **Translation traps are resolved analytically.** Rows with `a_i = d` are
  translations (`f(m) = m + b_i - i`) whose next residue depends only on the
  current residue; once an orbit sits on a residue loop made entirely of such
  rows, its increments are periodic forever. With nonzero period sum the
  generic engine would grind to the step cap (e.g. every `(2,2)` map in the
  `critical` sweep, at N x STEPCAP = 5*10^10 steps per map); `family` instead
  computes the exact outcome — same fate code, step count, and excursion as
  the generic loop, verified byte-identical on full sweeps — in O(d).
  `FAMILY_NOTRAP=1` disables the shortcut for A/B re-verification.
  (Measured: grid2 A=B=3, N=1e5: 166 s -> 1.3 s, identical TSV.)
- Remaining step-capped cost is genuine zero-drift multiplicative walks
  (`(1,4)`/`(4,1)` critical maps): a few % of starts cap at full budget.
  `FAMILY_STEPCAP=5000 ./family critical ...` trades cap-boundary resolution
  for speed if needed; overflow/cycle results are unaffected by the cap value.
- Suggested production runs (32-core Linux, `make omp`):

      ./family anchors            > results/anchors.tsv
      ./family grid2              > results/grid2.tsv
      ./family critical           > results/critical.tsv     # slowest; see note above
      ./family grid3              > results/grid3.tsv

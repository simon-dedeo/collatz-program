# expsum — exponential sums at the Collatz cycle modulus M = 2^K − 3^L

Compute tool for **Crack 3** of `docs/CRACKS.md` ("Exponential sums at the cycle
modulus", Lee–Yang framing; brief:
`docs/cracks/MSC-82B05-82B20-05A15-with-11B3737A45-contact--Sta.json`).

If a uniform power saving `|S_{K,L}(ξ)| ≤ C(K,L)^{1−δ}` for all `ξ ≠ 0` held at
admissible signatures, finiteness of Collatz cycles would follow (the word count
`C ≈ 2^{0.95K}` is exponentially smaller than `M ≈ 2^K`). This tool maps
`|S|/C` empirically.

---

## 1. The cycle equation, derived (and the convention we use)

**Map convention.** We use the *accelerated* Collatz map

    T(n) = n/2         if n even
    T(n) = (3n + q)/2  if n odd        (q = +1: Collatz; q = −1: the 3x−1 map)

Every T-step performs exactly one halving (an odd step's `3n+q` is even, so the
halving can be fused into the step). Uniformly, with `v = n mod 2`:

    T(n) = (3^v · n + q·v) / 2.

**Iterate K steps.** Let `n_0, n_1, …, n_K` with `v_j = n_j mod 2` (the *parity
word* `v = v_0 v_1 … v_{K−1}`), and `L = Σ v_j`. Unrolling
`2·n_{j+1} = 3^{v_j} n_j + q·v_j`:

    2^K · n_K = 3^L · n_0 + q · Σ_{j=0}^{K−1} v_j · 3^{(# ones strictly after j)} · 2^j .

(The `q·v_j` injected at step `j` is multiplied by 3 once for each **later** odd
step and enters *before* its own halving, hence exactly `2^j` from the common
denominator `2^K`.) Indexing the ones `b_0 < b_1 < … < b_{L−1}` (0-based
positions in `v`), the one at `b_i` has `L−1−i` ones after it, so for a **cycle**
(`n_K = n_0`):

    n_0 · M = q · W(v),        M = 2^K − 3^L,
    W(v)   = Σ_{i=0}^{L−1} 3^{L−1−i} · 2^{b_i}.                        (★)

**Positions b_i, not even-step counts c_i.** With
`c_i := # even steps strictly before the (i+1)-th odd step`, one has
`b_i = i + c_i` (the i earlier *odd* steps also occupy positions). The variant
formula `W = Σ 3^{L−1−i} 2^{c_i}` that appears in the crack brief is the same
identity in the **plain-map** convention `U(n) = 3n+q | n/2`, where the modulus
is `2^E − 3^L` with `E = # halvings` (there, `c_i` = # halvings before the
(i+1)-th odd step):

    n_0 · (2^E − 3^L) = q · W_plain(v),   W_plain = Σ 3^{L−1−i} 2^{c_i}.

Since the task fixes `M = 2^K − 3^L` with `K = total T-steps`, the exponents
**must** be the positions `b_i`. (Concretely: the trivial-cycle word `1010` at
`(K,L) = (4,2)`, `M = 7` gives `W = 3·2^0 + 1·2^2 = 7 ≡ 0` with (★) — correct —
but `3·2^0 + 1·2^1 = 5 ≢ 0` with the `c_i` exponents, which would make the
counting identity miss the trivial cycle.) Note `CRACKS.md` itself defines the
`b_i` as odd-step *positions*; the `c_i` phrasing is the plain-map variant.

**Numerical verification (all run by `expsum selftest`, mode (c)):**

| cycle | map | word | K (or E) | L | M | W | n·M = q·W |
|---|---|---|---|---|---|---|---|
| {1,2} | accel, q=+1 | `10` | 2 | 1 | 1 | 1 | 1·1 = +1 ✓ |
| {1} | accel, q=−1 | `1` | 1 | 1 | −1 | 1 | 1·(−1) = −1 ✓ |
| {5,7,10} | accel, q=−1 | `110` | 3 | 2 | −1 | 5 | 5·(−1) = −5 ✓ |
| 17-cycle | accel, q=−1 | — | 11 | 7 | −139 | 2363 | 17·(−139) = −2363 ✓ |
| {1,4,2} | plain, q=+1 | — | E=2 | 1 | 1 | 1 | ✓ |
| {5,14,7,20,10} | plain, q=−1 | — | E=3 | 2 | −1 | 5 | ✓ |

(The 3x−1 map furnishes genuine nontrivial cycles for sign-flipped
verification; `{5,7,10}` is the accelerated form of the plain 3x−1 cycle
`{5,14,7,20,10}`.)

**Existence.** A positive-integer T-cycle with signature `(K,L)` exists **iff**
some word `v` with `L` ones satisfies (i) `M | W(v)`, (ii) `n := W(v)/M ≥ 1`,
and (iii) `v` is the actual parity word of `n` (equivalently: all intermediate
iterates are integers). Condition (i) alone gives counting *upper bounds*;
divisible words violating (ii)/(iii) are "rational cycles" (e.g. every
`(K,L) = (2m, m)` contains the 2 rotations of `(10)^m`, which are the trivial
cycle traversed m times, `n = 1`). `count = 0` **excludes** the signature.

## 2. Counting identity and the exponential sum

For `M = 2^K − 3^L > 0`, over **all** `C(K,L)` length-K words with `L` ones
("admissibility = all words with L ones" per the program brief; realizability
refinements are handled by the classification columns instead):

    S_{K,L}(ξ) = Σ_v e(ξ·W(v)/M),      e(x) = e^{2πix},
    #{v : M | W(v)} = (1/M) Σ_{ξ mod M} S_{K,L}(ξ),      S(0) = C(K,L).

Since `C(K,L) ≈ 2^{0.95K} ≪ M ≈ 2^K` at admissible signatures, a uniform bound
`max_{ξ≠0} |S| ≤ C^{1−δ}` forces the count below 1 for large K — cycle
finiteness. Square-root cancellation (`|S| ≈ C^{1/2}·polylog`) is the
benchmark; we record `α(ξ) = log|S(ξ)| / log C` (so `α ≈ 1/2` = square-root).
Caution: by Parseval `Σ_ξ |S|² ≥ M·C`, so the **rms** of `|S|` over all ξ is
automatically `≥ √C`; the meaningful statistic is the **max** (and the shape of
the upper tail), not the mean.

## 3. The DP (inhomogeneous transfer matrix)

Process positions `j = 0..K−1`; state `i` = # ones placed so far (`0..L`).
Placing the `(i+1)`-th one at position `j` multiplies by the phase
`e(r(i,j)/M)`, `r(i,j) = ξ·3^{L−1−i}·2^j mod M`. Residues are maintained
exactly in unsigned 128-bit arithmetic: `R[i] ← ξ·3^{L−1−i} mod M` at `j = 0`
(built by successive `×3 mod M`), then doubled mod M once per position. Cost
`O(K·L)` complex operations per ξ; accumulators are `long double complex`.
No multiplication of two full residues ever occurs in the DP (only doubling
and add), so `M < 2^126` is safe; the brute-force check uses a peasant
`mulmod`. **Caps:** exhaustive `K ≤ 40` (and `M < 2^62` for the ξ loop);
sampled `K ≤ 118` (`M < 2^118`; beyond that 3^L/2^K leave u128 — big-int
territory, deliberately out of scope for v1).

## 4. Rotation covariance and the ⟨2⟩-orbit symmetry (measured, and corrected)

**Lemma (exact, integer level).** Let `ρ` = left rotation of the word
(`ρv` = parity word of `n_1` when `v` = parity word of `n_0`). Then

    v_0 = 0  ⇒  W(v)        = 2·W(ρv)
    v_0 = 1  ⇒  3·W(v) + M  = 2·W(ρv)

*Proof.* Leading 0: all positions shift down by one, `b_i ↦ b_i − 1`.
Leading 1 (`b_0 = 0`): the remaining ones shift down and re-index
(`i+1 ↦ i`, gaining a factor 3 each), and a new last one appears at position
`K−1` with weight `3^0`:
`W(ρv) = Σ_{i≥1} 3^{L−i} 2^{b_i −1} + 2^{K−1}`, so
`2W(ρv) = 3(W(v) − 3^{L−1}) + 2^K = 3W(v) + M`. ∎

**Corollary 1.** `M` is odd and coprime to 3, so `M | W(v) ⟺ M | W(ρv)`: the
divisible set is a union of full rotation classes (as it must be — each cycle
element contributes its own word).

**Corollary 2 (intertwining).** Splitting `S = S₀ + S₁` by the first bit,
substituting `v = ρu` (a bijection) into `S(2ξ)`:

    S(2ξ) = S₀(ξ) + S₁(3ξ).

**Consequence: the naive symmetry `|S(2ξ)| = |S(ξ)|` is FALSE in general.**
Smallest counterexample: `K=3, L=1, M=5`, W-multiset `{1,2,4}`:
`|S(1)| = 2cos(3π/5) ≈ 0.618` but `|S(2)| = 2cos(π/5) ≈ 1.618`. The selftest
(mode (d)) measures the violation at `(14,8), (16,10), (18,11)` — typical max
deviation `~0.05·C`, for the `v_0=1` ensemble too — and verifies the
intertwining relation to machine precision (`~2e-17`), i.e. the *cyclic-rotation
covariance is real, but what it yields is the intertwining, not ⟨2⟩-invariance
of `|S|`.* What does hold exactly: `|S(−ξ)| = |S(ξ)|` (conjugation). Chaining
Corollary 2 relates the pair `(S₀, S₁)` along mixed ⟨2,3⟩-multiplier orbits —
the `2^K ≡ 3^L (mod M)` structure enters through the closure of these chains
(one full necklace loop multiplies W by `3^L 2^{−K} ≡ 1`).

Accordingly, **sampled mode does not dedupe ξ by ⟨2⟩-orbits**; instead it
*measures* orbit variation (`orbit_dev` column: max over sampled orbits of
`(max|S| − min|S|)/C` along `ξ, 2ξ, 4ξ, …`).

## 5. Modes

```
./expsum selftest
./expsum exhaustive KMIN KMAX                    # K ≤ 40; ALL ξ mod M (OpenMP over ξ)
./expsum sampled KMIN KMAX [NRAND] [SEED] [NORBITS]   # K ≤ 118; default 100000, 20260720, 3
```

- **selftest** — (a) DP vs brute-force enumeration of `S` at random ξ for
  six `(K,L)` up to `K=16`, all three ensembles (all words / `v_0=0` / `v_0=1`),
  tolerance `1e-12·C(K,L)` (measured ≈ `5e-13` absolute); (b) count identity
  `(1/M)Σ_ξ S` vs brute count for `M ≤ 10^5` (`(8,5), (13,8), (16,10), (18,11)`)
  plus the exact known value at `(6,3)` (`M=37`: exactly 2 divisible words, both
  the trivial cycle); (c) the cycle-equation table of §1; (d) the symmetry
  checks of §4.
- **exhaustive** — per admissible signature (`L = ⌊K·log2/log3⌋ − 2 … + 2`
  clamped to `M > 0`; the `+1/+2` values almost always have `M < 0` and drop
  out), loops all `ξ ∈ [1, M−1]`, records max/mean of `|S|/C`, the argmax ξ,
  `log|S|/log C` stats, and the divisible count `(1/M)Σ_ξ S` (with residual as
  an accumulation sanity check). When `C(K,L) ≤ 5·10^7` the divisible words are
  also enumerated and classified: `n_pos` = those with `W/M ≥ 1`, `n_real` =
  actual parity words of `n = W/M` (integer cycles; for 3x+1 only trivial-cycle
  words should ever appear). A DP-vs-enumeration count mismatch prints a
  WARNING on stderr (none observed).
- **sampled** — ξ from (i) `1..1000`, (ii) NRAND randoms (splitmix64, fixed
  seed, per-signature offset), (iii) NORBITS ⟨2⟩-orbit sweeps (≤192 doublings,
  diagnostic only, see §4). Records the same ratio/alpha statistics plus the
  top-5 `|S|/C` outliers and `orbit_dev`.

## 6. Output columns (TSV, one row per signature)

| column | meaning |
|---|---|
| `mode K L M C` | signature; `M = 2^K−3^L`, `C = C(K,L)` (decimal strings) |
| `n_xi` | # ξ evaluated (`M−1` + ξ=0 analytic, in exhaustive) |
| `div_count` | `(1/M)Σ_ξ S` = # words with `M \| W` (exhaustive only) |
| `resid` | distance of the count from the nearest integer (sanity) |
| `n_pos`, `n_real` | of the divisible words: # with `W/M ≥ 1`; # realizable (= genuine cycles) |
| `max_ratio`, `argmax_xi` | `max_{ξ≠0} |S|/C` and its ξ |
| `mean_ratio` | mean of `|S|/C` over tested ξ≠0 |
| `max_alpha`, `mean_alpha` | max/mean of `α = ln|S|/ln C` (α ≈ 0.5 = square-root cancellation) |
| `n_zeroS` | # ξ with `|S| < 1e-12` (excluded from α stats) |
| `orbit_dev` | sampled mode: max ⟨2⟩-orbit variation of `|S|/C` (§4) |
| `top5_xi` | sampled mode: top-5 outliers as `ξ:ratio` |

## 7. Build

```
make            # cc -O2 -Wall -Wextra (sequential; macOS default)
make linux      # gcc -fopenmp (parallel over ξ)
make test       # runs the selftest
```

Compiles clean with `-Wall -Wextra`. OpenMP is `#ifdef`-guarded like the other
tools in `experiments/`.

## 8. Initial findings (exhaustive K ≤ 22 + sampled K = 20–22, sequential, ~1 min)

Data: `exhaustive_K22.tsv` (all ξ, all admissible (K,L), K ≤ 22),
`sampled_K2022.tsv` (1000 + 10^5 random ξ, seed 20260720).

- **Counts.** `div_count = 0` for *every* admissible signature except the
  trivial-cycle carriers `(2m, m)`, m ≤ 11 (each: exactly 2 divisible words,
  both realizable, n = 1 — the trivial cycle). DP counts match brute-force
  enumeration at every signature; `resid ≤ 5e-14`.
- **Typical ξ: square-root cancellation on the nose.** Fit over all band rows
  K ≥ 10: `mean_{ξ≠0}|S| ~ C^0.471` with R² = 0.9999; `mean_alpha` ≈ 0.43,
  flat in K (log-mean sits slightly below the Parseval-forced rms exponent 1/2).
- **The max lives on 3-power major arcs.** For almost every signature the
  argmax over all ξ ≠ 0 is within distance < 1 of `(j/3^t)·M`, t ≤ 3
  (denominator 27 dominates for 11 ≤ K ≤ 22; e.g. K=22, L=12: ξ/M = 5/27,
  K=18, L=10: 1/27, K=16, L=9: 23/27). Random sampling reproduces this at the
  next level: its top outliers sit at denominators 9 and 81
  (K=21, L=11: 1/9; K=22, L=12: 2/81 ≈ 0.024691).
- **Max decay is real but slow, with a drifting exponent.** Per-K best
  `max_ratio`: 0.43 (K=8) → 0.31 (K=12) → 0.24 (K=16) → 0.21 (K=22), while C
  grows 10^4-fold; `max_alpha` drifts *up*: 0.79 → 0.83 → 0.85 → 0.88.
  A single power law `max|S| ~ C^0.946` fits globally (R² = 0.995) but the
  drift means no stable uniform power saving is visible on this range; the
  behaviour is more consistent with polylog-type decay of the ratio
  (`max_ratio ~ K^−0.57`, noisy R² = 0.44 with an even/odd-K oscillation)
  driven entirely by the 3-power arcs. The Crack-3-relevant reading: minor
  arcs already exhibit square-root cancellation; any uniform-power-saving
  theorem must (only) beat the `ξ ≈ jM/3^t` major arcs — precisely the regime
  of Tao's 3-adic skew-walk mechanism (arXiv:1909.03562 §5–6).
- **⟨2⟩-orbit variation at scale** (`orbit_dev`, K = 20–22): |S|/C varies by
  0.006–0.03 along ⟨2⟩-orbits — same order as max_ratio itself, confirming
  quantitatively that |S| is far from constant on ⟨2⟩-orbits (§4).

Reproduce: `./expsum exhaustive 2 22` (~1 min sequential),
`./expsum sampled 20 22 100000 20260720 5` (~2 s).

## 9. Caveats

- `div_count` counts **divisible words**, not cycles: no `W/M ≥ 1` or
  realizability filter (see `n_pos`/`n_real`), and each genuine cycle appears
  K times (all rotations) modulo periodic-word subtleties.
- Exhaustive `K ≤ 40` by u64 ξ-loop; sampled `K ≤ 118` by u128 phases. `K > 118`
  needs big-int residues — **skipped in v1** by design.
- On Apple silicon `long double` = `double` (53-bit); phases are exact integer
  residues converted once, so errors stay at the `1e-13`-relative level seen in
  the selftest — irrelevant for `|S|` statistics but do not trust digits of
  `resid` below `~1e-9` at large M.
- The ⟨2⟩-orbit symmetry claim of the brief is empirically and provably false
  as stated (§4); any frequency-space collapse must use the intertwining
  `S(2ξ) = S₀(ξ) + S₁(3ξ)` instead.

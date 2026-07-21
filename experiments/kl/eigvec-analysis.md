# KL extremal eigenvectors k = 12…19: oscillation, the geometry of the high-oscillation set, and the dichotomy

**Calibration update (2026-07-21).** This is a finite floating-point analysis,
not an asymptotic result. Statements below that a mass “goes to zero,” that a
dimension or closed limiting set exists, or that `λ∞=2` is decided are now
read only as hypotheses suggested by `k≤19`. A local floating k20 scan has
absolute tails still decreasing but ratios near `0.824`, above the
preregistered slow-decay discriminator. The exact certified arrays are
feasible subeigenvectors rather than exact critical eigenvectors; see
`docs/notes/fiber-geometry.md` for the current status.

2026-07-20. Data: `eigvecs/eigvec_k{12..19}.npy` (Bridges2 GPU runs, `kl_gpu.py`; all files
validated: length 3^{k−1}, strictly positive, max = 1). Indexing: with
`ms = arange(2, 3^k, 3)`, the depth-d fiber of the level-(k−d) parent with index p is
`c_k.reshape(3^d, 3^{k-d-1})[:, p]`, row 0 = canonical lift — **verified by brute force
against `build()` at k = 4, 5** (`verify_indexing.py`). Definitions: for a depth-1 fiber
(3 values), `osc = (max−min)/mean`; the limit-object note's quantities are
`δ_k = Σ_r(mean_r−min_r) / Σ_m c^m` and `ε_k = max_r (1 − min/max)`; α = log₂3.
Framework and pre-registered predictions: `docs/notes/kl-limit-object.md`.
Scripts: `eigvec_analysis.py`, `geometry_pass.py`, `rho_at_2.py`, `compare_stationarity.py`,
`make_plots.py`, `make_badset_plots.py`. CSVs in `analysis_cache/`
(`tail_mass.csv`, `persistence.csv`, `identity.csv`).

New thresholds (GPU float solver, ev = 1 to 12 digits):

| k | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 |
|---|---|---|---|---|---|---|---|---|
| λ_k | 1.8064236 | 1.8188238 | 1.8307724 | 1.8419684 | 1.8522348 | 1.8616888 | 1.8703250 | 1.8783132 |
| γ_k | 0.8531362 | 0.8630058 | 0.8724524 | 0.8812483 | 0.8892670 | 0.8966119 | 0.9032890 | 0.9094376 |

---

## 1. Fiber oscillation (equicontinuity test)

`osc(r) = (max−min)/mean` over the 3 refinements of each level-(k−1) residue r
(figure `fig_oscillation.png`):

| k | mean | median | p90 | p99 | **max** |
|---|------|--------|-----|-----|---------|
| 12 | 0.0946 | 0.0833 | 0.1735 | 0.2736 | 0.6083 |
| 13 | 0.0859 | 0.0753 | 0.1574 | 0.2572 | 0.5985 |
| 14 | 0.0780 | 0.0678 | 0.1436 | 0.2423 | 0.5908 |
| 15 | 0.0707 | 0.0610 | 0.1306 | 0.2290 | 0.5943 |
| 16 | 0.0644 | 0.0549 | 0.1193 | 0.2156 | 0.6066 |
| 17 | 0.0588 | 0.0498 | 0.1095 | 0.2033 | 0.6139 |
| 18 | 0.0539 | 0.0452 | 0.1005 | 0.1916 | 0.6150 |
| 19 | 0.0494 | 0.0412 | 0.0925 | 0.1804 | 0.6235 |

- **Bulk decays geometrically**: per-level ratios — mean 0.908 → 0.917, median
  0.900 → 0.911, p99 steady at 0.942. No plateau through k = 19.
- **Sup does NOT decay**: max osc ≈ 0.60–0.62, slowly *rising*. (In the note's ε
  normalization this is the flat ε_k ≈ 0.46–0.48: for the extreme fiber
  (θ, B, 1)·c(−1), ε = 1 − θ/B = 1 − 0.691/1.317 = 0.475.)
- **Depth-d moduli** (mean osc over the 3^d refinements of level-(k−d) cells): at k = 19,
  d = 1/2/3 → 0.0494 / 0.1150 / 0.2093. Each extra digit of refinement roughly doubles the
  oscillation across a *fixed* coarse cell (osc(k, d)/osc(k−1, d−1) ≈ 1.8–2.1): variation
  keeps accumulating inside any fixed ball, so there is **no uniform modulus of
  continuity**, even though at fixed depth every statistic except the max decays in k.

So: equicontinuity holds Haar-typically (ratio ≈ 0.91/level) and **fails on a thin
persistent set**. The rest of the analysis characterizes that set.

## 2. Geometry of the high-oscillation set

### 2.1 Tail mass (Haar)

Fraction of fibers with osc > t (`tail_mass.csv`, fig `fig_badset.png`(a,b)):

| k | t=0.05 | t=0.1 | t=0.2 | t=0.3 | t=0.4 |
|---|--------|-------|-------|-------|-------|
| 12 | 0.765 | 3.88e-1 | 5.63e-2 | 4.73e-3 | 6.8e-5 |
| 15 | 0.616 | 2.06e-1 | 1.99e-2 | 1.40e-3 | 2.5e-6 |
| 19 | 0.382 | 8.02e-2 | 6.21e-3 | 4.27e-4 | 7.0e-8 |

Counts N_k(t) grow as 3^{D(t)·k} with **box dimension D(t) = slope of log₃N_k**
(last 4 levels): D(0.05) ≈ 0.89, D(0.1) ≈ 0.79, **D(0.2) ≈ 0.74, D(0.3) ≈ 0.74**
(stable plateau), D(0.4) ≈ 0.04 (a finite germ: N ≈ 4–9 fibers at all k). Equivalently the
Haar tail decays like 3^{−(1−D)k}: a genuine fractal exceptional set of dimension ≈ 3/4,
Haar measure → 0.

### 2.2 Parent–child persistence (nestedness)

P(child fiber > t | enclosing parent fiber > t), with enrichment over the base rate in
brackets (`persistence.csv`, fig (c)):

| k | t=0.1 | t=0.2 | t=0.3 |
|---|-------|-------|-------|
| 13 | 0.482 [×1.5] | 0.282 [×7] | 0.204 [×71] |
| 16 | 0.392 [×2.4] | 0.293 [×20] | 0.212 [×208] |
| 19 | 0.366 [×4.6] | 0.300 [×48] | 0.213 [×500] |

The conditional rate **stabilizes** (≈ 0.30 at t = 0.2, ≈ 0.21 at t = 0.3) while the base
rate collapses — the high-osc set is strongly nested and converges to a closed subset of
Y = 2+3ℤ₃ along the tower. It is *not purely* nested: only ≈ 28% of bad children sit under
bad parents; the rest are freshly seeded each level, exactly as a growing preimage tree
requires (§2.3). The stabilized branching number 3 × 0.21 ≈ 0.64 < 1 per old node, plus
seeding, nets out to the D ≈ 0.74 growth of §2.1.

### 2.3 Localization: the set is the backward orbit of −1

Top-50 oscillating fibers printed in base-3 (LSB→MSB) at k = 16–19
(`analysis_cache/geometry_pass.log`): three visible families —

1. **−1 itself and its 3-adic neighborhood**: the #1 fiber at *every* k is the all-2s
   string (r = 3^{k−1}−1 ≡ −1), osc 0.61–0.62; runners-up share long all-2 LSB prefixes
   (≡ −1 mod 3^j, large j).
2. **Periodic-digit classes = −4^{−n}**: `202020…` = −1/4, `210021002100…` = −1/16
   (block "2100" = 5, 5/(1−81) = −1/16), and shifts — i.e. **S-preimages 4^{−n}(−1)** of
   −1 (S(x) = 4x is the isometry branch).
3. General strings that are exact members of the **backward orbit of −1** under the
   constraint-graph maps {S⁻¹ = ×4⁻¹, R₂⁻¹: y ↦ (3y+2)/4 when ≡2(9), R₈⁻¹: y ↦ (3y+1)/2
   when ≡8(9)}: BFS to depth 10 (27 834 classes mod 3^18) shows most of the top-50 agree
   with an orbit node to *full available precision* (orbit_depth = k−1). Top-1000 mean
   agreement depth 15.5 (k = 19) vs 10.4 for random fibers — ≈ 3^5 enrichment; median 17.

   Candidate-address scan (top-1000, k = 19): only −1 stands out (max depth 18, i.e.
   exact). The negative T-cycles (−7 for {−5,−7}; −25, −37, −55, −82, −91, … for the −17
   cycle), 1/5, and the R₂-fixed point x = 2 all sit at baseline. −5, −17, −1/2 are ≢ 2
   (mod 3), hence not addresses of any fiber.

**Mechanism, verified exactly** (`germ_minus1.json`): −1 is the unique fixed point of
R₈(x) = (2x−1)/3 in Y, and −1 ≡ 8 (mod 9), so the constraint at m = −1 is
self-referential through the *advanced* weight w₈ = λ^{α−1} > 1:
c(−1) = λ^{−2}c(−4) + w₈·min-fiber(−1). A continuous limit would force
min-fiber = c(−1) and hence 1 = λ^{−2}c(−4)/c(−1) + w₈ > 1 — impossible. The eigenvector
therefore *must* carry a fiber defect at −1:

  θ_k := min-fiber(−1)/c(−1) = λ_k^{1−α}·(1 − λ_k^{−2}c(−4)/c(−1)).

Measured: θ_19 = 0.691395 vs λ_19^{1−α} = 0.691602 (the tiny difference is the 4m term);
agreement holds at every k = 12…19 and tightens with k. The germ over −1 is a bona fide
renormalization fixed point: fiber pattern (θ, B, 1)·c(−1) with B ≈ 1.30–1.32, positions
swapping with the parity of k because R₈ acts on the lost digit as t ↦ 2t (mod 3); the
depth-2 germ (9 values) reproduces the same multiset at every k (e.g. θ² = 0.478 appears
as the corner value). As λ → 2, w₈ → 3/2 and the forced defect **θ → 2/3 exactly**; the
germ predicts sup-osc → ≈ 0.65 (observed drift 0.608 → 0.624 tracks θ_k = λ_k^{1−α} ↓).
Oscillation then propagates from −1 outward along preimages (S⁻¹ with weight λ^{−2},
R⁻¹ with weights w₂, w₈ and digit dilution), which is exactly the orbit-tree geometry
found above, with D ≈ 0.74 the dimension of the weighted preimage tree pruned at
threshold t.

### 2.4 Eigenvector-mass weighting (does the adversary's advantage survive?)

The exact oscillation law (note, Thm 3.2) is already the mass-weighted statement: δ_k =
(1/3) × [eigenvector-mass-weighted mean of the relative fiber defect (mean−min)/mean].
Identity check, s(λ_k) − 1 = (λ_k^{α−2}+λ_k^{α−1})·δ_k (`identity.csv`):

| k | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 |
|---|---|---|---|---|---|---|---|---|
| δ_k | 0.017459 | 0.016061 | 0.014755 | 0.013566 | 0.012506 | 0.011554 | 0.010705 | 0.009935 |
| identity ratio | 1.0000002 | 1.0000000 | 0.9999997 | 1.0000004 | 1.0000000 | 0.9999996 | 0.9999997 | 0.9999998 |

(extends the note's k ≤ 12 verification to k = 19 at ≤ 4×10⁻⁷ relative). Mass vs Haar on
the tails (fig (a,d)): the eigenvector **up-weights** the bad set — mass/Haar ratio at
t = 0.3 grows 4.8 → 8.5 (k = 12 → 19), consistent with osc rising with parent c-value
(top decile ≈ 2× bottom decile, stationary in k) — but the up-weighting (≈ ×1.08/level)
is far too weak against the Haar collapse (≈ ×0.76/level at t = 0.3): **absolute
eigenvector mass of the bad set still → 0** (2.2e-2 → 3.6e-3 at t = 0.3), and δ_k itself
decays geometrically with per-level ratio 0.920 → 0.928. In the pressure functional the
adversary's surviving advantage is δ_k, and it is vanishing: on current data the
adversary does **not** retain positive value.

## 3. λ_k, ρ_k(2), and the dichotomy

- **Pre-registered discriminator** (note §4): observed γ₁₅ = 0.88125 > 0.8807 ⇒ rejects
  every pre-registered Model B with γ∞ ≤ 0.95; Model A (γ∞ = 1, q = 0.930) predicted
  γ₁₅…γ₁₈ to (−0.3, −0.6, −0.9, −1.4)×10⁻³ — small but *systematically growing*
  undershoot.
- **Gap ratios** (2−λ_{k+1})/(2−λ_k): 0.9360, 0.9338, 0.9338, 0.9354, 0.9357, 0.9378,
  0.9384 — drifting slowly **up**, the predicted signature of either (B) with γ∞ just
  below 1, or (A) with a subgeometric correction.
- **Secondary observable** ρ_k(2) (warm-started power iteration, Collatz–Wielandt pinch
  ≤ 1e-9; extends the note's k ≤ 14 values exactly): 0.939840 (12), 0.945049, 0.949977,
  0.954504, 0.958519, 0.962085, 0.965243 (18), 0.968180 (19). 1−ρ_k(2) ratios ≈
  0.910–0.917, geometric, no plateau — consistency with (A).
- **Updated fits on k = 12…19**: Model A′ (γ∞ = 1, gap = C·q^k·k^{−θ}: q = 0.946,
  θ = 0.21) and Model B (γ∞ = 0.9813 ⇒ λ∞ = 1.9742, q = 0.920) fit equally well
  (SSE 8.8e-6 vs 7.3e-6, both ≪ pure-A). Their γ_k predictions separate by 10⁻³ only at
  k ≈ 24. **The level sequence alone can no longer decide**; certified thresholds at
  k ≈ 22–24 would.
- Under (B) with λ∞ = 1.974, Corollary 3.4 forces δ_k to level off at
  ≥ (s(1.974)−1)/2.25 ≈ 1.8e-3; current δ_19 = 9.9e-3 falling ×0.93/level would meet that
  floor only near k ≈ 40 — not directly testable soon.

**Verdict (which branch does the data support).** Everything structural points to **(A)
λ∞ = 2 with a tame, exactly-characterized singular set**: the equicontinuity failure is
*not* a diffuse fractal obstruction but the forced defect at the single self-referential
point −1 (θ → 2/3 as λ → 2 — finite, consistent, and localized), spread along its
backward orbit of dimension ≈ 0.74 < 1 whose Haar *and* eigenvector mass both vanish;
the mass-weighted oscillation δ_k — the exact quantity equivalent to λ_k → 2 — decays
geometrically with no floor in sight; and ρ_k(2) ↑ 1 geometrically. What the data cannot
yet exclude is a stall at λ∞ ∈ [1.97, 2): the slow upward drift of every decay ratio is
the one caveat, and it is exactly as compatible with a k^{−0.2} correction to geometric
decay (A′) as with a stall (B). No pre-registered B representative (γ∞ ≤ 0.95) survives.

## 4. Cross-level structure and the refinement kernel (secondary)

- **Projections** (fig `fig_cross_level.png`): comparing c_k projected to level k−1
  (fiber-mean / fiber-min / canonical-lift) with c_{k−1}: unit-norm L2 distances decay
  geometrically (min-projection 0.0174 → 0.0105, ratio ≈ 0.92/level; correlations
  0.9997 → 0.99993) ⇒ the coarse profile is Cauchy in L2: **an L2 limit profile exists**.
  L∞ distances do *not* decay (≈ 0.17 flat) — localized on the bad set, as required.
- **Refinement kernel** (fig `fig_kernel.png`, `compare_stationarity.py`): conditional
  mean patterns per (parent mod 27 × parent-value decile) are ≈ (1,1,1) to < 0.005 in
  units of the median osc at every k — the kernel is a **centered fluctuation**, no
  deterministic bias; which child is the fiber minimum is uniform (1/3, 1/3, 1/3 by
  k ≥ 16). The pattern distribution is **shape-stationary after rescaling** by the
  per-level median osc (TV distance between consecutive levels 0.018 → 0.004), while raw
  distributions contract by the ≈ 0.91 factor per level (raw TV ≈ const 0.04). Empirical
  renormalization map: *lift the profile, multiply by a centered fluctuation field of
  fixed shape whose scale contracts by ≈ 0.91–0.93 per level, keep the −1 germ fixed at
  (θ_k, B, 1) with θ_k = λ_k^{1−α}*.

## 5. Proposed fixed-point problem for λ∞ (not solved here)

On Y = 2+3ℤ₃ let f be bounded, positive, lower-semicontinuous, continuous off the
backward orbit O⁻(−1), and let f_*(y) = liminf_{y′→y} f(y′) (= the limit of fiber minima).
The limit eigenproblem at λ = 2 has exactly rational weights (2^{α−2} = 3/4,
2^{α−1} = 3/2):

  f(x) = ¼·f(4x) + ¾·f_*((4x−2)/3)  (x ≡ 2 mod 9)
  f(x) = ¼·f(4x)                    (x ≡ 5 mod 9)
  f(x) = ¼·f(4x) + 3/2·f_*((2x−1)/3) (x ≡ 8 mod 9)

with the forced boundary condition at the R₈-fixed point:
f_*(−1)/f(−1) = θ = (2/3)·(1 − ¼·f(−4)/f(−1)) < 2/3. **λ∞ = 2 iff this system admits a
positive solution** (λ < 2 versions use weights λ^{−2}, λ^{α−2}, λ^{α−1}; existence for
all λ < λ∞ by lifting certificates). Two-sided program: (i) *lower bounds*: continue the
exact-rational certificates (as in `certify.py`) at k = 20–24 — decisive for the fit
ambiguity above; (ii) *upper bound*: λ∞ ≤ 2 is already exact (annealed identity, note
Prop 1.4); (iii) *closing the gap*: prove the empirical contraction — the renormalization
of §4 contracts fluctuations by ρ* ≤ 0.93 < 1 per level away from O⁻(−1), and the germ at
−1 is an explicitly solvable finite recursion (digit rotation t ↦ 2t, weights ¼, 3/2) —
then 1 − ρ_k(2) ≤ C·ρ*^k gives λ_k → 2 by continuity of ρ in λ (note Lemma 2.2). The
germ subsystem should be solved with interval arithmetic to certified two-sided bounds
on (θ, B, depth-2 profile) at λ = 2; a global test function assembled from a certified
finite-k bulk + the certified germ, verified as a sub-eigenvector in exact arithmetic,
would make each step of the chain rigorous.

## Files

- Figures: `fig_oscillation.png`, `fig_badset.png`, `fig_cross_level.png`,
  `fig_kernel.png`, `fig_profile_lambda.png`.
- CSVs: `analysis_cache/{tail_mass,persistence,identity}.csv`.
- JSON: `analysis_cache/{analysis_results,geometry_results,stationarity,germ_minus1,rho_at_2}.json`.
- Logs: `analysis_cache/geometry_pass.log` (top-50 digit strings, k = 16–19).
- Eigenvectors: `eigvecs/eigvec_k{12..19}.npy` (k = 20 not produced — the 19–20 GPU job
  reached k = 19; k = 20 needs ≳ 60 GB device memory).

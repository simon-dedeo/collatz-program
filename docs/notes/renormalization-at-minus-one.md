# The local renormalization at −1: exact solution of the fiber law, the doubling relabeling, and the marginal transversal mode

2026-07-20 (later still). Resolves the solvable part of Conjecture C2 of
`fiber-geometry.md` (v2) and delimits exactly what is *not* locally solvable.
Data: certified eigenvectors k = 15..19 (`experiments/kl/cert_k{15..19}_C.npy`,
exact integer vectors; λ_k the certified rationals of `cert_k*_report.json`).
Scripts: `experiments/kl/renorm_{common,extract,chains,window,annuli,limit_solve}.py`;
tables: `experiments/kl/renorm_{profiles,argmins,growth,chains,window,global,annuli,limit_table}.csv`.
Notation as in `kl-limit-object.md`: α = log₂3, level-k states [3^k] = {m mod 3^k :
m ≡ 2 (3)}, branch = residue mod 9, fiber of a level-(k−1) state r = {r + j·3^{k−1}}.

**Standing hypothesis (E).** c is a strictly positive *exact* eigenfunction of
the level-k operator, c = F_λ(c) (kl-limit-object.md §1.2), λ ∈ (1,2). The
certified vectors satisfy c ≤ F_λ(c) with relative slack ≤ 1.3×10⁻⁷ (and W₂,W₈
rational lower bounds for the weights), so every "exact" identity below is
verified on the data up to that margin; measured residuals are reported. All
k-asymptotics assume (H_k) along the tower, as elsewhere in this program.

Provenance: §§1–5 derived here and verified against the certified data; the
chain recursion (5) below was independently derived by the external model
gpt-5.6-sol from our brief, as were the two extremal constructions in §7.2;
sol's independent solution of the limit system agrees with ours on every
overlapping claim (min-constraint exact and unique; no pure-branch pinning;
transversal marginality). The heavy annulus/mass measurements were run by a
subagent (`renorm_annuli.py`); everything else run directly.

---

## 1. Exact local geometry at −1 (derived, not assumed)

Write −1 for the state 3^k − 1 ∈ [3^k]; −1 ≡ 8 (mod 9), and R₈(−1) =
(2(−1)−1)/3 = −1: −1 is the fixed point of the advanced branch.

**Lemma 1 (window geometry).** For 1 ≤ ν ≤ k−2 let B_ν := {−1 + u·3^{k−ν}
mod 3^k : u ∈ ℤ/3^ν} (the 3-adic ball of radius 3^{−(k−ν)} around −1 inside
[3^k]; B_ν ⊂ B_{ν+1}). Then:
(a) every x ∈ B_{k−2} satisfies x ≡ 8 (mod 9);
(b) for x = −1 + u·3^{k−ν} ∈ B_ν, R₈(x) = −1 + 2u·3^{k−ν−1} mod 3^{k−1},
and the three level-k lifts of R₈(x) are −1 + (2u + i·3^ν)·3^{k−ν−1}, i = 0,1,2
— elements of B_{ν+1};
(c) the transport reference 4x = −4 + 4u·3^{k−ν} lies in the corresponding
ball around −4, outside every B_μ (|−4−(−1)|₃ = 1/3).

*Proof.* (a) x ≡ −1 (mod 3^{k−ν}) and k−ν ≥ 2. (b) (2x−1)/3 =
(2u·3^{k−ν} − 3)/3; lifts add i·3^{k−1} = i·3^ν·3^{k−ν−1}. (c) immediate. ∎

**Offset coordinates.** Encode x = −1 + u·3^{k−ν} by q = u/3^ν in the Prüfer
group ℤ(3^∞) = ℤ[1/3]/ℤ (well-defined: (u, ν) and (3u, ν+1) give the same x).
Let ν(q) be the exact denominator exponent. By Lemma 1(b) the branch-min at q
is over the three solutions y of 3y = 2q — call them the **children** of q.
Every q has 0 as an iterated ancestor (the parent map q ↦ (3/2)q lowers ν(q) by
1), and **0 is its own child** (i = 0), the self-loop that anchors everything.
The fiber of the level-(k−1) state at offset q consists of the offsets
(q+i)/3, so **fibers = child-triples** (of q/2; ×2 is an automorphism).

The eigen-equation on the window, in these coordinates: with A := λ^{α−1} > 1,
t := λ^{−2}, and p(q) := c(−1 + q·3^k)/c(−1) (so p(0) = 1),

  (W)  p(q) = A · min{ p(y) : 3y = 2q } + t·c(4x_q)/c(−1),  q with ν(q) ≤ k−3.

## 2. Theorem 1: the exact fiber law at −1 and the closed form for a

Since R₈(−1) = −1 mod 3^{k−1}, the min in the eigen-equation *at* −1 is over
the fiber of −1 itself. This gives, with no approximation:

**Theorem 1 (fiber-min law).** Under (E), for every k ≥ 4:

  (I)  min_j c(−1 + j·3^{k−1}) / c(−1) = λ^{1−α} − λ^{−1−α} · c(−4)/c(−1).

In particular the min-normalized small lift is
a_k = λ^{1−α} − λ^{−1−α}/σ_k with σ_k := c(−1)/c(−4) the spike ratio, and
a_k → a* := **λ^{1−α}** whenever σ_k → ∞. At λ = 2, a* = 2^{1−α} = **2/3
exactly** (2^α = 3); at λ₁₈ = 1.8703245, a* = 0.693328.

*Proof.* The eigen-equation at m = −1 reads c(−1) = λ^{−2}c(−4) +
λ^{α−1}·min_j c(−1+j·3^{k−1}); solve for the min. ∎

**Verification** (renorm_limit_solve.py; full table renorm_limit_table.csv).
Residual of (I) on the certified vectors: ≤ 2.4×10⁻⁷ (= certificate slack,
correct sign). Both sides to 6 decimals:

| k | λ_k | RHS of (I) | measured min/c(−1) | a* = λ^{1−α} | mean-norm. a | c(−1)/mean |
|---|-----|-----------|--------------------|--------------|--------------|------------|
| 15 | 1.8419679 | 0.698494 | 0.698494 | 0.699552 | 0.701036 | 1.003640 |
| 16 | 1.8522343 | 0.696591 | 0.696591 | 0.697281 | 0.696643 | 1.000075 |
| 17 | 1.8616883 | 0.694750 | 0.694750 | 0.695208 | 0.693773 | 0.998593 |
| 18 | 1.8703245 | 0.693015 | 0.693015 | 0.693328 | 0.692709 | 0.999559 |
| 19 | 1.8783127 | 0.691395 | 0.691395 | 0.691602 | 0.689559 | 0.997344 |

The closed form matches the measured minimum to **six decimals** (it is an
identity); against C2's mean-normalized target a = 0.6925 ± 0.0003 it matches
through the third decimal, the residue being the pinning factor c(−1)/mean =
1 ± 0.004 (§5). Consequences: sup-osc of the −1 fiber = (max−min)/mean →
2(1−a*) if pinning holds (measured 0.594→0.624 vs predicted 0.601→0.617,
column suposc in the CSV); at λ = 2 the limit would be exactly 2/3.

## 3. Lemma 2: growth along the tower and transport suppression

**Lemma 2 (two-sided spike growth).** Under (E), for k ≥ 4:
(i) c(−1) ≥ λ^{(α−1)(k−2)} · min c;
(ii) c(−1) ≤ K(λ) · λ^{(α−1)(k−2)} · max c, with K(λ) = 1 + λ^{−2}/(1−λ^{1−α}).

*Proof.* Let m_ν := min_{B_ν} c, M_ν := max_{B_ν} c. Every x ∈ B_ν (ν ≤ k−3)
is 8-branch with children in B_{ν+1} (Lemma 1), so c(x) ≥ A·m_{ν+1} (transport
≥ 0), giving m_ν ≥ A·m_{ν+1}; iterate from ν = 0 ({−1}) to ν = k−2 and use
m_{k−2} ≥ min c. For (ii), c(x) ≤ t·max c + A·M_{ν+1} gives M_ν ≤
A^{k−2−ν}·max c + t·max c·Σ_{r≥0}A^{−r}·A^{k−2−ν}·… collapsing to (ii). ∎

So c(−1)/min c ≍ λ^{(α−1)k}: the dominant balance is the advanced branch, and
the per-level growth rate is **λ^{α−1}** (= 1.4423 at λ₁₈). Checks: measured
c(−1)/min c = 368.8, 553.7, 837.3, 1267.3, 1921.0 (k = 15..19), i.e. within
[bound, 3.7×bound] of (i) with stable ratio; growth ratios 1.501, 1.512,
1.514, 1.516. The spike σ_k = c(−1)/c(−4) = **194.8, 294.4, 438.4, 633.2**,
947.4 grows by 1.511, 1.489, 1.444, 1.496 per level — λ_k^{α−1} = 1.43–1.45
plus the λ_k-drift correction (λ_{k+1}/λ_k)^{(α−1)(k+1)} ≈ 1.05, which brackets
the measurements. (c(−4) tracks the global scale: σ_k ≈ 0.5·c(−1)/min c.)
The global maximum of c is itself in the window, at depth-4 offset
(orbit 58→35→70 under doubling), with max c = λ^{α−1}c(−1)(1 ± 0.005) — KL's
C^max_k is exactly the −1 spike.

**Corollary (transport suppression).** The relative transport at −1 is
t·c(−4)/c(−1) = λ^{−2}/σ_k: measured 1.51e−3, 9.90e−4, 6.58e−4, 4.52e−4,
2.99e−4 — per-level ratios 0.655, 0.665, 0.687, 0.662 ≈ **λ^{1−α} = 1/(spike
growth) ≈ 0.66–0.69 per level**. This corrects both earlier statements: the
v1 "0.28^k" and the review's "λ^{−1−α} ≈ 0.20 per level" — λ^{−1−α} is the
one-time weight ratio (transport weight λ^{−2} vs branch weight λ^{α−1});
the *rate* of relative suppression per level is λ^{1−α}. (0.67⁴ ≈ 0.20 over
four levels is the numerical coincidence that caused the conflation.)

Within one eigenvector, the same suppression appears per depth: along any
argmin chain x_0 = −1, x_{n+1} = argmin child, the eigen-equation gives the
exact recursion (in H_n := Aⁿ·c(x_n)/c(−1); derived independently by sol)

  (5)  H_{n+1} = H_n − t·Aⁿ·c(4x_n)/c(−1),

so H is constant along chains up to the accumulated transport forcing; the
measured H-drift per step equals the measured transport fraction to all
digits shown (renorm_chains.csv).

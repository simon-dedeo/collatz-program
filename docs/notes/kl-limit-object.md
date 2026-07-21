# The KL system at infinite precision: a 3-adic limit object, an adversarial ergodic value, and the dichotomy λ∞ = 2 vs λ∞ < 2

2026-07-20. Status: **conceptual note with proofs** (finite-k structure theory is proved;
the limit question is posed as a sharp open problem with a pre-registered numerical test).
Written **before** the k = 15–18 supercomputer data exist; §4 records the predictions of the
two competing hypotheses so that the incoming data discriminate cleanly.
Context: `experiments/kl/THEOREM.md` (exact KL hypotheses, certified values),
`experiments/kl/kl_perron_solver.py` (the solver whose operator is analyzed here),
`experiments/kl/kl_paper.txt` (pdftotext of Krasikov–Lagarias, arXiv:math/0205002v1 =
Acta Arith. 109 (2003) 237–258; line references below are to this file).
All numerical claims in this note are reproduced by `experiments/kl/limit_object_checks.py`.

**Successor update (2026-07-21).** An independently audited argument now proves
the conditional implication `(H_k) => lambda_(k+1)>lambda_k`: the ordinary
copy lift has nonzero branch slack, and superadditive orbit-averaging spreads
that slack around the full fine transport cycle. Combined with the later
literature-backed research proof of `(H_k)` in `adversarial-operator.md`, this
settles qualitative strict growth at research-proof level whenever
`lambda_k<2`. Neither component is yet kernel-checked. The gain is
dimension-dependent and can be exponentially small, so this does not address
`lambda_k->2`. The lift proof is recorded in
`docs/notes/annealed-critical-coding.md §5.3`.

Ledger (details in §5): **proved here** — Lemmas 1.1–1.3, Propositions 1.4, 2.1, 2.2,
3.1, Theorem 3.2, Corollaries 1.5, 3.3, 3.4. **Verified numerically, not proved** —
hypothesis (H_k) (positivity/attainment of the extremal eigenvector, = KL's §6 conditions
(1)+(2)), strict decrease of ρ_k(λ) in λ. **Later research proofs, not yet
formalized** — `(H_k)` and the implication
`(H_k) => lambda_(k+1)>lambda_k`. **Open** — the
dichotomy itself (Problem 3.5).

---

## 0. Summary

Krasikov–Lagarias (KL) certify Collatz predecessor-counting exponents γ_k = log₂ λ_k from
a finite feasibility system at "precision k" (residues mod 3^k). The certified record now
stands at

| k | 11 | 12 | 13 | 14 |
|---|----|----|----|----|
| γ_k | 0.8417566 | 0.8531358 | 0.8630053 | 0.8724520 |

(k = 11 is KL 2003; k = 12–14 are our exact-rational certificates, `cert_k1*.json`.)

This note organizes the family over all k into a single object: the level-k system is the
precision-3^{−k} section of a fixed pair of maps on the 3-adic set Y = 2 + 3ℤ₃ — the
isometry x ↦ 4x and two 3-expanding division maps — with a min over a lost 3-adic digit
played by an adversary. We prove: λ_k is nondecreasing (Lemma 1.2), λ_k ≤ 2 for every k
via an exact "annealed" computation (Proposition 1.4: averaging the adversary's digit
gives a linear operator whose Perron root is s(λ) = λ^{−2} + (λ^{α−2}+λ^{α−1})/3,
independent of k, with s(2) = 1 exactly), hence λ∞ := lim λ_k exists in (1.8307, 2].
We rewrite the eigenproblem as a zero-sum ergodic control problem (§2) and prove an
**oscillation law** (Theorem 3.2): at the extremal eigenvector,

  s(λ_k) − 1 = (λ_k^{α−2} + λ_k^{α−1}) · δ_k,   δ_k = mean fiber oscillation,

an exact identity, so that **λ_k → 2 if and only if the extremal eigenvectors flatten over
3-adic fibers in mean**. The dichotomy (Problem 3.5): (A) λ∞ = 2, conditionally
giving π_a(x) ≥ x^{1−ε} through the repaired KL trust chain (§3.1); or (B) λ∞ < 2, in which case λ∞
is a new invariant — the asymptotic value of adversarial digit control on ℤ₃ — and the
entire KL difference-inequality method has the intrinsic ceiling γ∞ = log₂ λ∞ < 1.
§4 pre-registers what γ_15–γ_18 should look like under (A) vs (B).

Throughout α := log₂ 3 = 1.5849625…, β := log₂ λ, γ_k := log₂ λ_k.

---

## 1. The finite systems as sections of one 3-adic object

### 1.1 The space and the three maps

Let ℤ₃ be the 3-adic integers, |·|₃ the 3-adic absolute value, μ Haar measure with
μ(ℤ₃) = 1. Define the clopen set

  **Y := {x ∈ ℤ₃ : x ≡ 2 (mod 3)} = 2 + 3ℤ₃**,  μ(Y) = 1/3,

and its clopen partition Y = Y₂ ⊔ Y₅ ⊔ Y₈ with Y_i := i + 9ℤ₃ (i = 2, 5, 8). Write
Y_k := Y / 3^k ℤ₃ for the level-k quotient; Y_k is canonically identified with
[3^k] := {m mod 3^k : m ≡ 2 (mod 3)}, of cardinality 3^{k−1}, and π_{k+1,k}: Y_{k+1} → Y_k
denotes reduction. (This [3^k] is exactly KL's index set, their eq. (2.2).)

**Lemma 1.1 (the three maps).**
(a) S(x) := 4x is a bijective isometry of Y preserving μ|_Y (4 is a 3-adic unit and
4·2 ≡ 2 mod 3). It induces the bijection m ↦ 4m mod 3^k of Y_k for every k.
(b) R₂(x) := (4x−2)/3 maps Y₂ homeomorphically onto Y, expands the metric by exactly 3
(|R₂x − R₂x′|₃ = 3|x−x′|₃), and triples Haar measure: μ(R₂E) = 3μ(E).
(c) R₈(x) := (2x−1)/3 maps Y₈ homeomorphically onto Y with the same expansion and
measure-tripling.
(d) Coherence with the tower: knowing x mod 3^k determines Sx mod 3^k but R₂x, R₈x only
mod 3^{k−1}. The induced maps r₂^{(k)}: Y_k ∩ (2 mod 9) → Y_{k−1},
r₈^{(k)}: Y_k ∩ (8 mod 9) → Y_{k−1} commute with the projections:
r^{(k)} ∘ π_{k+1,k} = π_{k,k−1} ∘ r^{(k+1)}.

*Proof.* (a) is immediate. (b): parametrize Y₂ = {2 + 9s : s ∈ ℤ₃}; then
R₂(2+9s) = (6+36s)/3 = 2 + 12s, and 12ℤ₃ = 3ℤ₃ (12 = 3·4, 4 a unit), so the image is
2 + 3ℤ₃ = Y, bijectively. R₂ is affine with linear part 4/3 and |4/3|₃ = 3; an affine map
x ↦ ax + b scales the metric by |a|₃ and Haar by |a|₃. (c): R₈(8+9s) = (15+18s)/3
= 5 + 6s, and 5 + 6ℤ₃ = 5 + 3ℤ₃ = Y (6 = 3·2, 2 a unit; 5 ≡ 2 mod 3). (d): if
x ≡ x′ (mod 3^k) then R₂x − R₂x′ = (4/3)(x−x′) has |·|₃ ≤ 3·3^{−k}, i.e. R₂x ≡ R₂x′
(mod 3^{k−1}); the same for R₈; commutation is then just the statement that the finite maps
are induced by the fixed maps R₂, R₈ on Y. ∎

So one 3-adic digit of precision is a conserved resource under S and is *spent* by each
division map. The fiber π_{k,k−1}^{−1}(r) of a level-(k−1) point r consists of the 3
lifts {r + j·3^{k−1} : j = 0,1,2}, which are mutually at 3-adic distance 3^{−(k−1)}.

### 1.2 The level-k operator and threshold

For c: Y_k → (0,∞) define (this is precisely the reduced KL feasibility system, THEOREM.md
§2, and precisely the iteration in `kl_perron_solver.py::eigval`):

  **(F_λ^{(k)} c)^m := λ^{−2} c^{4m mod 3^k}
   + 1_{m≡2(9)} · λ^{α−2} · min_{j=0,1,2} c^{r₂(m)+j·3^{k−1}}
   + 1_{m≡8(9)} · λ^{α−1} · min_{j=0,1,2} c^{r₈(m)+j·3^{k−1}}**,

with r₂(m) = (4m−2)/3 mod 3^{k−1}, r₈(m) = (2m−1)/3 mod 3^{k−1}. F_λ^{(k)} is monotone
(c ≤ c′ ⟹ Fc ≤ Fc′), positively homogeneous of degree 1, and concave (a min of finitely
many nonnegative linear maps). KL's LP L^NT_k(λ) is feasible iff there is c ≥ 1 with
c ≤ F_λ^{(k)}(c) (THEOREM.md §2, "reduced feasibility criterion"). Define

  **λ_k := sup{ λ ∈ [1,2] : L^NT_k(λ) feasible },  γ_k := log₂ λ_k.**

(The restriction to [1,2] matches KL's Theorem 2.2, whose hypothesis is 1 ≤ λ ≤ 2; see the
remark after Proposition 1.4 for what happens outside.) The cone spectral radius
ρ_k(λ) := lim_n ‖(F_λ^{(k)})^n(1)‖_∞^{1/n} exists by submultiplicativity
(F^{n+m}(1) ≤ ‖F^m(1)‖_∞ F^n(1)); feasibility implies ρ_k(λ) ≥ 1 (if c ≥ 1 and c ≤ F(c),
then F^n(1) ≥ F^n(c)/max c ≥ c/max c, so ρ ≥ 1). In 3-adic language: F_λ^{(k)} couples the
isometry branch (weight λ^{−2}) with the two expanding branches (weights λ^{α−2}, λ^{α−1}),
and **the min over the fiber is an adversary choosing the digit at scale 3^{−(k−1)} that
the division map lost**.

### 1.3 Monotonicity in k

**Lemma 1.2 (λ_k is nondecreasing; lifting works, pushforward does not).**
If L^NT_k(λ) is feasible then so is L^NT_{k+1}(λ). Hence λ_k ≤ λ_{k+1}.

*Proof.* Let c ≥ 1 satisfy c ≤ F_λ^{(k)}(c) on Y_k and set ĉ := c ∘ π_{k+1,k}, i.e.
ĉ^{m′} := c^{m′ mod 3^k} for m′ ∈ [3^{k+1}]. Fix m′ ∈ [3^{k+1}] and put m := m′ mod 3^k.
Since k ≥ 2, m′ ≡ m (mod 9), so m′ and m are in the same branch class.
(i) 4m′ mod 3^{k+1} reduces to 4m mod 3^k, so ĉ^{4m′} = c^{4m}.
(ii) If m′ ≡ 2 (mod 9): the level-(k+1) fiber is {r′ + j·3^k}, r′ := r₂^{(k+1)}(m′) ∈ [3^k];
all three lifts reduce mod 3^k to r′, so min_j ĉ^{r′+j·3^k} = c^{r′}. By Lemma 1.1(d),
r′ mod 3^{k−1} = r₂^{(k)}(m), i.e. **r′ is itself one of the three lifts of r₂^{(k)}(m)**;
hence c^{r′} ≥ min_j c^{r₂(m)+j·3^{k−1}}. The same for m′ ≡ 8 (mod 9).
Therefore (F_λ^{(k+1)} ĉ)^{m′} ≥ (F_λ^{(k)} c)^m ≥ c^m = ĉ^{m′}, and ĉ ≥ 1. ∎

This is the construction KL state in §6 (kl_paper.txt lines 1031–1041:
"c^{m+j·3^k}_{k+1} := c^m_k"); the proof is written out here because the *direction*
matters. The opposite direction — pushing a level-(k+1) solution down by taking min (or
max) over fibers — fails: for c̃^m := min_{π(m′)=m} c^{m′}, the needed bound
c̃^m ≤ λ^{−2} c̃^{4m} + … breaks because the minimizing lift m′* has c^{4m′*} ≥ c̃^{4m}
with no matching upper bound. Interpretation: **in passing from level k to level k+1, one
digit that the adversary controlled becomes an honest dynamical output** (the value r′ is
computed from m′ rather than chosen); refinement can only weaken the adversary, so the
value λ_k can only go up. KL, lines 1041–1042, asked whether it goes up
strictly. The successor argument cited at the top of this note proves strict
growth whenever the positive extremal eigenvector in `(H_k)` is attained;
kernel-formalizing `(H_k)` uniformly remains open. Empirically the growth is strict on the
reported finite levels (Table, §4).

### 1.4 The annealed comparison: λ_k ≤ 2 exactly

Replace the adversary's min by the *average* over the three lifts ("annealed" = the lost
digit is uniformly random instead of worst-case): define the **linear** operator

  (A_λ^{(k)} c)^m := λ^{−2} c^{4m}
   + 1_{m≡2(9)} · λ^{α−2} · (1/3)Σ_{j=0}^{2} c^{r₂(m)+j·3^{k−1}}
   + 1_{m≡8(9)} · λ^{α−1} · (1/3)Σ_{j=0}^{2} c^{r₈(m)+j·3^{k−1}}.

Since min ≤ average, F_λ^{(k)}(c) ≤ A_λ^{(k)}(c) for every c ≥ 0. Set

  **s(λ) := λ^{−2} + (λ^{α−2} + λ^{α−1})/3.**

**Lemma 1.3 (annealed value, exact).** For every k ≥ 2 and λ > 0:
(i) every column sum of the matrix A_λ^{(k)} equals s(λ);
(ii) consequently the all-ones vector is a strictly positive *left* Perron eigenvector and
ρ(A_λ^{(k)}) = s(λ), independent of k;
(iii) s(2) = 1 and s(4) = 1 exactly, s is strictly decreasing on [1,2] with s(1) = 5/3,
and s′(2) = 3(α−2)/8 = −0.1556391….

*Proof.* (i) Three counting facts. (1) m ↦ 4m mod 3^k is a bijection of [3^k], so each
column m′ receives the weight λ^{−2} exactly once. (2) m ↦ r₂(m) is a *bijection*
{m ∈ [3^k] : m ≡ 2 (9)} → [3^{k−1}]: writing m = 2 + 9t with t mod 3^{k−2} free,
r₂(m) = (4m−2)/3 = 2 + 12t = 2 + 3·(4t) mod 3^{k−1}, and t ↦ 4t is a bijection mod
3^{k−2}; so r₂ hits each class in [3^{k−1}] exactly once. (3) Likewise m = 8 + 9t gives
r₈(m) = 5 + 6t = 5 + 3·(2t) mod 3^{k−1}, a bijection onto [3^{k−1}]. Now each column
m′ ∈ [3^k] lies in exactly one fiber (that of m′ mod 3^{k−1}), so it receives λ^{α−2}/3
from exactly one row of type 2 (by (2)) and λ^{α−1}/3 from exactly one row of type 8
(by (3)). Total: s(λ), for every column.
(ii) If u > 0 and uᵀA = s uᵀ, then Aᵀ has the positive eigenvector u with eigenvalue s, so
(Aᵀ)ⁿu = sⁿu gives (Aⁿ)ᵀ_{ij} ≤ sⁿ (max u)/(min u) entrywise, whence ρ(A) = ρ(Aᵀ) ≤ s; and
s is an eigenvalue, so ρ(A) = s.
(iii) Using 2^α = 3: s(2) = 1/4 + (2^{α−2} + 2^{α−1})/3 = 1/4 + (3/4 + 3/2)/3
= 1/4 + 3/4 = 1. Using 4^α = 9: s(4) = 1/16 + (9/16 + 9/4)/3 = 1/16 + 15/16 = 1.
Monotonicity: 3λ^{3−α} s′(λ) = −6λ^{−α} + (α−2) + (α−1)λ is increasing in λ and equals
3α − 6 < 0 at λ = 2, so s′ < 0 on (0,2]. Values: s(1) = 1 + 2/3; s′(2) = −2·2^{−3}
+ ((α−2)2^{α−3} + (α−1)2^{α−2})/3 = −1/4 + ((α−2)·3/8 + (α−1)·3/4)/3 = 3(α−2)/8. ∎

Note what happens at λ = 2 in detail (this is the "annealed value = 2" claim made exact):
the **constant vector is the left eigenvector, not the right one** — the row sums of
A_2^{(k)} are 1/4 (class 5 mod 9), 1/4 + 3/4 = 1 (class 2 mod 9), 1/4 + 3/2 = 7/4
(class 8 mod 9) — but a nonnegative matrix with a strictly positive left eigenvector has
that eigenvalue as its spectral radius, and all column sums equal means the uniform
measure on [3^k] is exactly stationary for the mass flow. Equivalently, in the limit
object: for the linear transfer operator on C(Y),
(L_λ c)(x) = λ^{−2}c(4x) + 1_{Y₂}(x) λ^{α−2} c(R₂x) + 1_{Y₈}(x) λ^{α−1} c(R₈x),
a change of variables with Lemma 1.1(b,c) (each division branch has domain of relative
Haar measure 1/3 in Y and maps it onto all of Y tripling measure) gives
∫_Y L_λ c dμ = s(λ) ∫_Y c dμ: **normalized Haar measure on Y is an eigenmeasure of the
limit operator with eigenvalue s(λ), at every λ**. A_λ^{(k)} is the level-k section of
L_λ, which is why its Perron value is independent of k. The heuristic content of
s(2) = 1 is the classical density heuristic "π_a(x) ≍ x" (exponent 1 = γ, λ = 2).

**Proposition 1.4 (λ_k ≤ 2 for all k).** If L^NT_k(λ) is feasible and λ ∈ [1,2], then
s(λ) ≥ 1; hence λ ≤ 2, and so λ_k ≤ 2.

*Proof.* Let c ≥ 1, c ≤ F_λ^{(k)}(c). Sum over m ∈ [3^k] and use F ≤ A and Lemma 1.3(i):
Σ_m c^m ≤ Σ_m (A_λ^{(k)} c)^m = Σ_{m′} (column sum)·c^{m′} = s(λ) Σ_m c^m. Since
Σ c^m ≥ 3^{k−1} > 0, s(λ) ≥ 1. By Lemma 1.3(iii), s is strictly decreasing on [1,2] with
s(2) = 1, so λ ≤ 2. ∎

Remarks. (1) KL perform this summation themselves (kl_paper.txt lines 1005–1018:
"Adding up all the inequalities in L^NT_k(λ) leads to c̄_{k,k} ≤ λ^{−2} c̄_{k,k}
+ (1/3)(λ^{α−1}+λ^{α−2}) c̄_{k−1,k}") but state it as a diagnostic, not as the bound
λ_k ≤ 2; combined with c̄_{k−1,k} ≤ c̄_{k,k} (their auxiliary variables are fiber minima)
it *is* the proof above. We sharpen it to an identity in Theorem 3.2.
(2) Without the restriction λ ≤ 2 the argument only forbids λ ∈ (2,4) — s(λ) < 1 exactly
on (2,4), with s(4) = 1 again (the two roots of s = 1 are λ = 2^g, g = 1, 2; substituting
λ = 2^g turns s(λ) = 1 into 3·4^g = 3 + 3^g(1 + 2^g)). The reappearing root at λ = 4 is a
property of the annealed relaxation only: numerically ρ_k(F_λ) < 1 throughout
λ ∈ [2.2, 12] (checked k = 4,5,6; e.g. ρ ≈ 0.52 at λ = 4, k = 5), decreasing in λ, so the
quenched system shows no feasibility beyond 2; and KL's Theorem 2.2 requires λ ≤ 2 anyway.

**Corollary 1.5 (the limit exists).** λ∞ := lim_{k→∞} λ_k exists, and
λ∞ ∈ (1.8307718, 2], i.e. γ∞ := log₂ λ∞ ∈ (0.8724520, 1]. (Monotone by Lemma 1.2, bounded
by Proposition 1.4; the lower end is the certified λ_14 = 2^{0.8724520} = 1.8307718….) ∎

λ∞ is determined by the tower of finite systems, which by §1.1 is the canonical
inverse-limit discretization of the weighted system (Y; S, R₂, R₈; weights
−2, α−2, α−1). In this sense λ∞ is an invariant of the pair (×4 isometry, ÷3 refinement)
on ℤ₃, with the Collatz exponent α = log₂3 entering only through the weights.

---

## 2. The log/Bellman transformation: a zero-sum ergodic control problem at precision k

### 2.1 Variables

Set **v := log₂ c ∈ [0,∞)^{Y_k}** and **β := log₂ λ ∈ [0,1]**. Feasibility c ≤ F_λ(c),
c ≥ 1 becomes: v ≥ 0 and

- m ≡ 5 (9): v^m ≤ v^{4m} − 2β;
- m ≡ 2 (9): v^m ≤ log₂( 2^{v^{4m} − 2β} + 2^{(α−2)β + min_j v^{r₂(m)+j·3^{k−1}}} );
- m ≡ 8 (9): v^m ≤ log₂( 2^{v^{4m} − 2β} + 2^{(α−1)β + min_j v^{r₈(m)+j·3^{k−1}}} ).

So v is a bounded **subsolution of an ergodic Isaacs-type equation** whose Bellman
operator combines (i) an inner minimization (the adversary), and (ii) a log-sum-exp — not
a max — across the two branches: the "maximizing player" is not a controller selecting one
branch but the *branching itself* (the difference inequalities count two disjoint families
of predecessors, so the counts add; log-sum-exp is the free-energy/risk-sensitive form of
max). λ_k = sup{λ : a subsolution exists} is precisely a Mañé-critical-value definition.

### 2.2 The pieces of the game, precisely

(i) **State space**: Y_k = Y/3^kℤ₃ (3^{k−1} states), the precision-k quotient of the fixed
compact space Y ⊂ ℤ₃.

(ii) **Controlled transition**: from state m the system branches to
  - 4m (always; the isometry step), with **reward −2β**;
  - additionally, if m ≡ 2 (mod 9): to a lift of r₂(m) ∈ Y_{k−1}, with **reward (α−2)β**;
  - additionally, if m ≡ 8 (mod 9): to a lift of r₈(m) ∈ Y_{k−1}, with **reward (α−1)β**.
  The **adversary picks the lift**, i.e. the 3-adic digit at scale 3^{−(k−1)} that the
  division map lost — this is the min in F. The rewards are the shifts of the KL time
  variable y = log₂(x/a): the (D1)–(D3) inequalities relate φ^m(y) to φ^{4m}(y−2),
  φ^{r₂(m)}(y+α−2), φ^{r₈(m)}(y+α−1) (THEOREM.md §1). Signs: passing to the 4m-class costs
  two doublings of size (reward −2β < 0); the (4m−2)/3-class is larger by 4/3 = 2^{2−α}
  (reward (α−2)β ≈ −0.415β, retarded); the (2m−1)/3-class is *smaller* by 3/2 = 2^{α−1}
  — its members have more predecessors below the same x — an advanced term with strictly
  positive reward (α−1)β ≈ +0.585β. The positive-reward edges are exactly why the KL paper
  exists (advanced terms broke the earlier machinery) and why ρ_k(λ) is not trivially
  monotone in λ.

(iii) **Precision structure**: at level k the adversary's action is one ternary digit per
division step, located at 3-adic scale 3^{−(k−1)}: the three lifts of r(m) are mutually at
distance 3^{−(k−1)} in Y. A *policy* is a digit table σ: Y_{k−1} → {0,1,2} (the LP's min
is stationary: one choice per fiber, not per path). As k → ∞ the adversary's action moves
to asymptotically fine scales; Lemma 1.2 says each refinement transfers one digit from the
adversary to the dynamics, so the adversary's value can only shrink: β_k nondecreasing.

**Proposition 2.1 (policy collapse).** For each policy σ let A_λ^σ be the nonnegative
linear operator obtained from F_λ^{(k)} by replacing each min over the fiber of r by
evaluation at the lift σ(r). Then:
(a) ρ_k(λ) ≤ min_σ ρ(A_λ^σ) always;
(b) if F_λ^{(k)} has an eigenvector c* > 0 (strictly positive), then
ρ_k(λ) = min_σ ρ(A_λ^σ), and a minimizing σ* is read off from c* by selecting, in each
fiber, a lift attaining the min.

*Proof.* (a) F_λ(c) ≤ A_λ^σ c for all c ≥ 0 and all σ; iterate and take n-th roots.
(b) Let F(c*) = ρ c*, c* > 0, and let σ* select minimizers of c* in each fiber. Then
A^{σ*} c* = F(c*) = ρ c*; a nonnegative matrix with a strictly positive eigenvector has
that eigenvalue as its spectral radius (proof as in Lemma 1.3(ii)), so ρ(A^{σ*}) = ρ. Also
ρ = ρ_k(λ) because (min c*)·1 ≤ c* ≤ (max c*)·1 pinches the growth of F^n(1) to ρ. With
(a), the min is attained at σ*. ∎

There are 3^{3^{k−2}} policies; the concave Perron problem (one power iteration) collapses
this doubly-exponential min. Strict positivity of the extremal eigenvector is **verified
numerically for k ≤ 12** (power iteration converges with Collatz–Wielandt bounds pinched
to 7+ digits and min c > 0; the normalized spread max c/min c reproduces KL's C^max_k
column: 1.832 at k = 2, 98.401 at k = 11, 146.97 at k = 12) but not proved in general;
this is hypothesis (H_k) below. (Pinch at threshold: ≤ 4×10⁻¹³ for k ≤ 9, ≤ 10⁻⁷ for
k ≤ 12.)

**Lemma 2.2 (threshold = eigenvalue 1).** ρ_k(λ) is continuous in λ on [1,2] (for
λ′ = tλ, t ≥ 1: t^{−2} F_λ ≤ F_{λ′} ≤ t^{α−1} F_λ pointwise, hence
t^{−2}ρ_k(λ) ≤ ρ_k(λ′) ≤ t^{α−1}ρ_k(λ)), and ρ_k(λ_k) ≥ 1. If moreover λ_k < 2 and
F_{λ_k} has a strictly positive eigenvector c* with F(c*) = ρ c*, then ρ = ρ_k(λ_k) = 1.

*Proof.* Continuity: the sandwich. ρ_k(λ_k) ≥ 1: feasibility gives ρ_k ≥ 1 at feasible λ
(§1.2), take feasible λ_j ↑ λ_k and use continuity. Last claim: if ρ > 1, rescale c* ≥ 1;
for t ∈ (1, min(√ρ, 2/λ_k)] we get F_{tλ_k}(c*) ≥ t^{−2} F_{λ_k}(c*) = t^{−2}ρ c* ≥ c*,
so tλ_k ∈ (λ_k, 2] is feasible — contradicting the supremum. ∎

### 2.3 Variational (pressure) form: the ergodic value

Fix a policy σ and let G_σ be the finite directed graph on Y_k with edges
m → 4m (label g = −2) for all m; m → σ-lift of r₂(m) (label g = α−2) for m ≡ 2 (9);
m → σ-lift of r₈(m) (label g = α−1) for m ≡ 8 (9). Every vertex has out-degree ≥ 1. By the
standard identity "log Perron root = topological pressure" for subshifts of finite type
with locally constant potential (Parry; Walters), with entropy h measured in bits:

  log₂ ρ(A_λ^σ) = P_σ(β) := max_{μ} [ h(μ) + β ∫ g dμ ],

the max over shift-invariant probability measures μ on the edge shift of G_σ. Combining
with Proposition 2.1 and Lemma 2.2:

**Proposition 2.3 (β_k is a zero-sum ergodic value).** Under (H_k) (λ_k < 2 attained with
a strictly positive eigenvector),

  **min_σ max_μ [ h(μ) + β_k ∫ g dμ ] = 0,  β_k = log₂ λ_k,**

where σ ranges over digit tables Y_{k−1} → {0,1,2} and μ over invariant path statistics on
G_σ. The maximizing player earns entropy (the branching rate of the certified predecessor
tree) plus β times the mean size-drift ∫g dμ ∈ [−2, α−1]; the adversary suppresses this by
choosing lost digits. λ_k is the point where the adversarially suppressed pressure hits
zero — "**optimal ergodic reward = 0**". Equivalently, whenever the optimal μ has
E_μ[−g] > 0 (empirically true: ρ_k(λ) is strictly decreasing in λ on [1,2] on numerical
grids), β_k = min_σ max_μ h(μ)/E_μ[−g]: an **adversarial entropy-over-drift critical
exponent** — an adversarial Bowen equation. ∎ (given Prop 2.1, Lemma 2.2, and the cited
pressure identity)

### 2.4 Where this sits (weak KAM / max-plus / nonlinear Perron)

Conceptual placement, with pointers rather than verified quotations. The threshold
definition λ_k = sup{λ : a bounded subsolution v of the ergodic inequality exists} is the
discrete analogue of the **Mañé critical value**, and v = log₂ c is a **subaction**
(discrete corrector / weak-KAM subsolution): Conze–Guivarc'h (1993), Mañé (1996), Fathi's
weak KAM theorem, Bousch ("Le poisson n'a pas d'arêtes", 2000; Walters condition, 2001),
Contreras–Iturriaga. The min-of-linear eigenproblem and its Collatz–Wielandt theory is
nonlinear Perron–Frobenius: Nussbaum (1986), Gaubert–Gunawardena (2004) — monotone
homogeneous maps, policy iteration, and the cone spectral radius used throughout §2. The
λ → limit/tropicalization of such spectral problems (not taken here — β stays finite; but
the min-plus component of our hybrid operator is their object) is the max-plus spectral
theory of Cohen–Dubois–Quadrat–Viot (1983–85) and Baccelli–Cohen–Olsder–Quadrat (1992),
where the ergodic eigenvalue is the maximal cycle mean and eigenfunctions are max-plus
superpositions. The log-sum-exp branch combination is risk-sensitive control
(Whittle; Fleming–McEneaney), i.e. our game is "risk-sensitive for the counting player,
robust (worst-case) for the digit player". In ergodic-optimization language, the dichotomy
of §3 is a question about **stability of an ergodic value under vanishing discretization**
and **equicontinuity of the correctors c_k**: precisely the mechanism by which
zero-temperature / fine-precision limits fail or hold in weak KAM theory.

---

## 3. The dichotomy

### 3.1 KL's conditional statement, verbatim

The statement is in §6 of the paper (pp. 16–17 of arXiv:math/0205002v1). It carries **no
theorem number**; both sentences credit [2] = D. Applegate and J. C. Lagarias, *Density
bounds for the 3x+1 problem. II. Krasikov inequalities*, Math. Comp. 64 (1995), 427–438.
Quoting kl_paper.txt (lines 1019–1023 and 1042–1044; "ǫ" rendered ε):

> "In [2] it was noted that a necessary and sufficient condition for a bound like
> π₁(x) > x^{1−ε} to hold for each ε > 0 and all sufficiently large x is that λ_k → 2 as
> k → ∞, and this in turn would follow from the existence of feasible solutions with
> c̄_{k−1,k}/c̄_{k,k} → 1 as k → ∞."

> "As already noted in [2], showing that λ_k → 2 as k → ∞ would imply a lower bound
> π_a(x) ≥ x^{1−ε} holds for each positive ε, for each a ≢ 0 (mod 3) and all sufficiently
> large x ≥ x₀(a)."

The sufficiency direction is conditional on a corrected proof of their Theorem
2.2 and the actual predecessor-count instantiation (current audit in
`experiments/kl/TERMINATION_AUDIT.md`), and we record the intended statement
precisely:

**Proposition 3.1 (conditional sufficiency).** If λ_k → 2 and the repaired KL
trust chain holds, then for every ε > 0 and every positive
a ≢ 0 (mod 3): π_a(x) ≥ x^{1−ε} for all x ≥ x₀(a, ε).

*Proof.* Given ε, pick k with λ_k > 2^{1−ε/2}, then (definition of the supremum) a
feasible λ ∈ (2^{1−ε/2}, λ_k] with solution {c^m}. KL Theorem 2.2 gives
φ^m_k(y) ≥ Δ₁ c^m λ^y (all y ≥ 0, Δ₁ = 1/(4 max c)); the corrected transfer
chain in `THEOREM.md` §4 gives π_a(x) ≥ C(a) x^{γ}, with `C(a)>0` and
γ = log₂ λ > 1 − ε/2, for all sufficiently large x (for a direct non-cycle
target in class 2 this starts at x≥a; doubled targets start at their chosen
predecessor). For x large, C(a) x^{γ} ≥ x^{1−ε}. ∎

On the *necessity* direction of the first quote: as stated it is exactly true **within the
method** — the set of exponents certifiable by the family {L^NT_k(λ)} is
{log₂ λ : λ feasible for some k}, whose supremum is γ∞; so the method delivers x^{1−ε} for
every ε iff γ∞ = 1 iff λ_k → 2. It is *not* a claim that π₁(x) ≥ x^{1−ε} unconditionally
forces λ_k → 2: that converse would require the lower bound of Theorem 2.2 to be optimal
against the truth and not merely against the difference system I_k. (KL's own optimality
discussion — their conditions (1), (2), lines 1067–1086 — is optimality relative to I_k.)

### 3.2 The oscillation law

We now make the second half of KL's first quote ("would follow from
c̄_{k−1,k}/c̄_{k,k} → 1") into an exact equivalence. This is the sharpest form of the
"equicontinuity criterion" we know how to prove.

**Hypothesis (H_k).** λ_k < 2, the supremum is attained, and F_{λ_k}^{(k)} has an
eigenvector c_k > 0 with eigenvalue 1 (by Lemma 2.2 the eigenvalue is then forced). This
is KL's §6 conditions (1)+(2) plus strict positivity; KL: "Experimentally this is the case
for k ≤ 11" (line 1078) and "We think it likely that properties (1), (2) hold for all
k ≥ 2, but this may be difficult to prove" (lines 1085–1086). We verified (H_k)
numerically for 2 ≤ k ≤ 12 (Collatz–Wielandt pinch ≤ 4×10⁻¹³ for k ≤ 9, ≤ 10⁻⁷ for
k ≤ 12; eigenvector positive; its normalized spread reproduces KL's C^max_k column).

For a positive vector c on Y_k define the **fiber oscillation** at r ∈ Y_{k−1}:

  D_r(c) := (1/3)Σ_{j=0}^2 c^{r+j·3^{k−1}} − min_{j} c^{r+j·3^{k−1}} ≥ 0,

and the **mean relative oscillation**  δ(c) := Σ_{r∈Y_{k−1}} D_r(c) / Σ_{m∈Y_k} c^m.
Write δ_k := δ(c_k), w₂ := λ_k^{α−2}, w₈ := λ_k^{α−1}.

**Theorem 3.2 (oscillation law).** Assume (H_k). Then:

(i) **Identity:**  s(λ_k) − 1 = (λ_k^{α−2} + λ_k^{α−1}) · δ_k.
 Equivalently, in KL's Table-2 notation, c̄_{k−1,k}/c̄_{k,k} = 1 − 3δ_k and
 1 = λ_k^{−2} + (1/3)(λ_k^{α−2}+λ_k^{α−1}) · (c̄_{k−1,k}/c̄_{k,k}).

(ii) **Two-sided comparison:** for λ_k ∈ [λ₂, 2] = [1.3534, 2],
 ((2−α)/6)(2−λ_k) ≤ δ_k ≤ 0.3493·(2−λ_k), with (2−α)/6 = 0.069173…; and if λ_k → 2 then
 δ_k = ((2−α)/6 + o(1))(2−λ_k).

(iii) **Equivalence:**  λ_k → 2 ⟺ δ_k → 0.

(iv) **Sup-oscillation is sufficient (but not necessary):** if
 ε_k := max_{r∈Y_{k−1}} (1 − min_j c_k / max_j c_k over the fiber) → 0, then
 δ_k ≤ ε_k/(3(1−ε_k)) → 0, hence λ_k → 2. No summability of ε_k is needed — plain
 convergence to 0 suffices.

*Proof.* (i) Sum the eigen-equalities c^m = (F_{λ_k} c)^m over m ∈ [3^k]. The isometry
part contributes λ_k^{−2} Σ c (bijectivity of m ↦ 4m); by the bijections (2), (3) of
Lemma 1.3's proof, the division parts contribute w₂ Σ_r min-fiber(r) + w₈ Σ_r
min-fiber(r) = (w₂+w₈) Σ_r [avg-fiber(r) − D_r]. Since the fibers partition Y_k,
Σ_r avg-fiber(r) = (1/3)Σ_m c^m. Hence Σc = λ_k^{−2}Σc + (w₂+w₈)((1/3)Σc − Σ_r D_r)
= s(λ_k)Σc − (w₂+w₈)Σ_r D_r. Rearrange and divide by Σc. The Table-2 form: with
c̄_{k,k} = Σc/3^{k−1}, c̄_{k−1,k} = Σ_r min/3^{k−2}, one computes
δ_k = 1/3 − (1/3)(c̄_{k−1,k}/c̄_{k,k}).
(ii) s(λ_k) − 1 = ∫_{λ_k}^2 |s′(t)| dt and |s′| is decreasing on [1,2] (the proof of
Lemma 1.3(iii) shows 3λ^{3−α}s′ is increasing and negative there), so
|s′(2)|(2−λ_k) ≤ s(λ_k)−1 ≤ |s′(λ_k)|(2−λ_k); also w₂+w₈ is increasing in λ with value
9/4 at 2 and 2.0756 at λ₂, and |s′(λ₂)| = 0.72495. Lower constant: |s′(2)|/(9/4)
= (3(2−α)/8)/(9/4) = (2−α)/6; upper constant: 0.72495/2.0756 = 0.34927.
(iii) Immediate from (i)–(ii) and continuity/monotonicity of s: s(λ_k) → 1 ⟺ λ_k → 2
(within [1,2]), and s(λ_k) − 1 ≍ δ_k with the constants of (ii).
(iv) In each fiber, max ≤ min/(1−ε_k) ≤ avg/(1−ε_k), so D_r ≤ max − min ≤ ε_k max
≤ (ε_k/(1−ε_k))·avg; summing, Σ D_r ≤ (ε_k/(1−ε_k))·(1/3)Σc. ∎

**Corollary 3.3 (unconditional inequality version).** Without (H_k): every feasible pair
(λ, c) satisfies s(λ) ≥ 1 + (λ^{α−2}+λ^{α−1})·δ(c), i.e.
λ ≤ s^{−1}(1 + (w₂+w₈)δ(c)) < 2 whenever δ(c) > 0. (Same summation with "≤".) So
*any* certificate's oscillation caps the λ it can certify. ∎

**Corollary 3.4 (persistent oscillation under (B)).** If λ∞ < 2 then, under (H_k) for all
large k, δ_k ≥ (s(λ∞) − 1)/(9/4) > 0 for all k: the extremal eigenvectors keep a fixed
positive amount of mean oscillation over fibers at *every* precision — no continuous
corrector on Y exists in the limit. (From (i), λ_k ≤ λ∞, s decreasing, w₂+w₈ ≤ 9/4.) ∎

**Numerical verification** (float solver, thresholds re-solved and eigenvectors computed;
k ≤ 12; script §"limit_object_checks"): the identity (i) holds to all computed digits
(≤ 10^{−6} relative, limited by the threshold solve), e.g.:

| k | λ_k (float) | δ_k directly | (s(λ_k)−ρ)/(w₂+w₈) | c̄_{k−1,k}/c̄_{k,k} = 1−3δ_k |
|---|------------|--------------|---------------------|------------------------------|
| 2 | 1.3534001 | 0.114577 | 0.114577 | 0.65627 |
| 6 | 1.6944520 | 0.032283 | 0.032283 | 0.90315 |
| 11 | 1.7922310 | 0.019115 | 0.019115 | 0.94266 |
| 12 | 1.8064236 | 0.017459 | 0.017459 | 0.94762 |

(KL's Table 2 lists c̄_{k,k}, c̄_{k−1,k} for their LP solutions at feasible λ slightly
below threshold; our threshold eigenvector values agree with their columns to ~10^{−3},
and max c/min c reproduces their C^max_k.) Two further empirical facts worth recording:
**the sup-oscillation of (iv) does NOT vanish** — ε_k ≈ 0.45–0.47, flat, for k = 2…12,
while the *median* fiber oscillation decays (0.140 at k = 3 → 0.080 at k = 12) — so (iv)
is true but empirically vacuous, and the mean criterion (iii) is the live one; and KL's
Table-2 difference c̄_{k,k} − c̄_{k−1,k} ≈ 0.39–0.41 stays roughly constant while c̄_{k,k}
grows, which is exactly "δ_k → 0 by growth of the mean, not by flattening of the
difference" — weak structural evidence for (A).

### 3.3 The open problem

**Problem 3.5 (dichotomy).** Determine which of the following holds for
λ∞ = lim λ_k ∈ (1.8307, 2]:

**(A) λ∞ = 2** ("the adversary's ergodic value vanishes at fine precision").
Equivalent, under (H_k), to δ_k → 0 (Theorem 3.2(iii)). Conditional consequence
through Proposition 3.1 and the repaired KL trust chain:
π_a(x) ≥ x^{1−ε} for every ε > 0 and every a ≢ 0 (mod 3), x ≥ x₀(a,ε) —
the full heuristic exponent, up to ε.

**(B) λ∞ < 2** ("adversarial digit control retains positive value at all scales").
Then:
 (i) λ∞ is a well-defined **new invariant** of the weighted system (Y; S = ×4 isometry;
 R₂, R₈ = ÷3 refinements; weights −2, α−2, α−1 with α = log₂3): the asymptotic value of
 the zero-sum digit-control game of §2, strictly between the trivial value (no adversary
 sees only weights) and the annealed value 2. By Corollary 3.4 it is *realized* as
 persistent mean oscillation of the extremal eigenvectors: liminf δ_k ≥ (s(λ∞)−1)/(9/4) > 0,
 i.e. the correctors v_k = log₂ c_k develop non-vanishing fine-scale oscillation and have
 no continuous limit on Y — the finite-precision games do not converge to the continuum
 game (whose value is annealed, = 2, by Lemma 1.3's Haar computation, *if* correctors were
 continuous).
 (ii) **Ceiling of the method:** every certificate in the family {L^NT_k(λ) : k ≥ 2}
 certifies an exponent log₂ λ ≤ γ_k ≤ γ∞, with γ_k < γ∞ for all k if the λ_k increase
 strictly (empirically true for k ≤ 14); so **no difference-inequality argument of KL type
 ever certifies an exponent ≥ γ∞ = log₂ λ∞ < 1**. Under KL's optimality conditions
 (1),(2) (their §6 discussion), log₂ λ_k is the best exponent extractable from the
 difference system I_k at level k by *any* positive monotone exponential solution, so the
 ceiling applies to the method as such, not merely to the LP relaxation.
 (iii) What (B) would **not** mean: no upper bound on π_a follows; the truth could still
 be π_a(x) ≥ x^{1−ε}. (B) measures the information content of the I_k inequalities, i.e.
 the price of replacing the lost digit by its worst case.

Adjacent open questions, distinct from Problem 3.5: (a) kernel-check the later
research proofs of `(H_k)` and qualitative strict growth; (b) prove a
quantitative adjacent gain strong enough for endpoint convergence; (c) does
ρ_k(2) → 1 ⟺ λ∞ = 2? (plausible transfer
between the two monotone families; we use ρ_k(2) only as a secondary empirical observable
in §4); (d) identify λ∞ (if < 2) with the value of an explicitly-defined game on Y — the
exchange-of-limits question that makes "limit object" precise.

---

## 4. Pre-registered predictions for k = 15–18

Written 2026-07-20, before any k ≥ 15 computation exists. Data used: γ₂…γ₁₀ from KL
Table 2's λ-column (γ_k := log₂ λ_k, 7 significant digits; our solver reproduces the
column to 10^{−6}), γ₁₁…γ₁₄ from the certified values (header table). Increments
γ_{k+1} − γ_k for k = 10…13: 0.0122098, 0.0113792, 0.0098695, 0.0094467. Gap ratios
(1−γ_{k+1})/(1−γ_k) for k = 10…13: 0.9284, 0.9281, 0.9328, 0.9310 — stable near 0.93.

**Model A (λ_k → 2 geometrically).** If the adversary's value decays geometrically in
precision — the natural guess if each extra digit multiplies the adversary's residual
advantage by a fixed contraction factor, and consistent with Theorem 3.2's
δ_k ≍ (2−λ_k) ≍ (1−γ_k) — then 1 − γ_k = C_A·q_A^k. Fit on k = 8…14 (the transient
k ≤ 7 is excluded; on the full range the 3-parameter fits are transient-dominated — the
best full-range Model-B fit even predicts γ₁₅ < γ₁₄, i.e. is invalid):

  q_A = 0.93003, C_A = 0.351652, rms residual 1.9×10⁻⁴
  (window k = 9…14 gives q = 0.93001 and shifts predictions by < 2×10⁻⁵ — stable).

**Model B (λ_k → λ∞ < 2).** γ_k = γ∞ − C·q^k with γ∞ < 1. The free-γ∞ fit on k = 8…14
has monotonically decreasing SSE as γ∞ → 1 (profile: SSE(γ∞ = 0.90) = 6.1×10⁻⁵,
(0.92) = 1.8×10⁻⁵, (0.96) = 1.7×10⁻⁶, (→1) = 2.5×10⁻⁷): **the current 13 points contain
no evidence for any finite γ∞ < 1**, and already mildly disfavor γ∞ ≤ 0.95 (rms 3.5× worse
than A). Model B is therefore pre-registered as a grid of representatives, each with
(C, q) fit to k = 8…14:

| model | q | rms on 8–14 | γ₁₅ | γ₁₆ | γ₁₇ | γ₁₈ |
|---|---|---|---|---|---|---|
| **A: γ∞ = 1** | 0.93003 | 1.9e−4 | **0.88154** | **0.88983** | **0.89754** | **0.90470** |
| B: γ∞ = 0.95 | 0.89891 | 6.7e−4 | 0.87977 | 0.88687 | 0.89325 | 0.89899 |
| B: γ∞ = 0.92 | 0.86116 | 1.6e−3 | 0.87788 | 0.88373 | 0.88876 | 0.89310 |
| B: γ∞ = 0.90 | 0.81296 | 2.9e−3 | 0.87585 | 0.88037 | 0.88404 | 0.88703 |

Predicted increments γ_{k}−γ_{k−1}, k = 15…18:
A: 0.00909, 0.00829, 0.00771, 0.00717 (ratio stays ≈ 0.93);
B(0.95): 0.00732, 0.00710, 0.00638, 0.00574;
B(0.92): 0.00543, 0.00585, 0.00504, 0.00434;
B(0.90): 0.00340, 0.00452, 0.00367, 0.00298.

**Discriminators.**
1. *Levels:* A vs B(0.95) differ by 1.8×10⁻³ at k = 15 (≈ 9× the A-fit rms) and 5.7×10⁻³
at k = 18 (≈ 30×). Decision rule: observed γ₁₅ above 0.8807 favors A over every B with
γ∞ ≤ 0.95; γ₁₅ below 0.8807 rejects A at ≈ 9 rms.
2. *Gap ratios:* under A, (1−γ_{k+1})/(1−γ_k) stays ≈ 0.930 through k = 18; under B it
must **drift upward toward 1** (the gap 1−γ_k → 1−γ∞ > 0): B(0.95) implies 0.941, 0.944,
0.946 at k = 15, 16, 17. Conversely the *increment* ratios stay ≈ 0.93 under A but sink
toward q_B < 0.93 under B.
3. *Nonparametric consistency check:* the measured increment ratio q̄ ≈ 0.9292 (mean of
the last four) extrapolates the total remaining sum to γ∞ ≈ γ₁₄ + inc₁₄·q̄/(1−q̄)
= 0.9964, within 0.4% of the annealed value 1 — suggestive of (A), not probative. (γ∞ ≤ 1
forces the asymptotic increment ratio ≤ 0.9310; the data sit exactly at that edge.)
4. *Secondary observable (cheap for the same run):* ρ_k(2), the quenched Perron value at
λ = 2. Data (this note, k = 13, 14 computed fresh): 0.6064972 (k=2), …, 0.9103342 (8),
0.9193913 (9), 0.9267254 (10), 0.9334900 (11), 0.9398400 (12), 0.9450493 (13),
0.9499767 (14). Geometric fit 1 − ρ_k(2) = 0.19352·(0.90761)^k on k = 8…14 (rms 2.8×10⁻⁴)
predicts ρ(2) at k = 15…18: **0.95479, 0.95897, 0.96276, 0.96620**. Under (A)-type
behavior ρ_k(2) ↑ 1 geometrically; under (B) it should level off below 1. (The implication
ρ_k(2) → 1 ⟺ λ∞ = 2 is heuristic — §3.3(c) — so this is a consistency check, not a test.)

Bug guards for the incoming data: any γ_{k+1} < γ_k contradicts Lemma 1.2; any γ_k ≥ 1
contradicts Proposition 1.4; both would indicate computation error, not mathematics.

---

## 5. Status ledger

**Proved in this note** (self-contained, modulo standard facts cited inline):
- Lemma 1.1 (3-adic structure of S, R₂, R₈; digit loss; tower coherence).
- Lemma 1.2 (λ_k nondecreasing; the lift direction works, pushforward provably fails).
  [Statement is KL §6; proof written out here.]
- Lemma 1.3 (annealed operator: all column sums s(λ); ρ(A_λ^{(k)}) = s(λ) ∀k; s(2) = 1 =
  s(4) exactly; Haar eigenmeasure of the limit operator L_λ).
- Proposition 1.4 (λ_k ≤ 2), Corollary 1.5 (λ∞ ∈ (1.8307, 2]).
- Proposition 2.1 (policy collapse; equality under strictly positive eigenvector).
- Lemma 2.2 (continuity of ρ_k in λ; ρ_k(λ_k) = 1 under positivity when λ_k < 2).
- Proposition 2.3 (β_k = value of zero-sum ergodic pressure game; adversarial Bowen
  equation form), given (H_k) and the standard Perron-root/pressure identity.
- Proposition 3.1 (λ_k → 2 ⟹ π_a(x) ≥ x^{1−ε}), conditional on the
  repaired KL Theorem 2.2/counting trust chain.
- Theorem 3.2 (oscillation law: exact identity, two-sided comparison, equivalence
  λ_k → 2 ⟺ δ_k → 0, sup-oscillation sufficiency), under (H_k).
- Corollaries 3.3 (unconditional inequality version), 3.4 (persistent oscillation under (B)).

**Original numerical ledger (superseded for `(H_k)` by the later research
proof):** (H_k) for k ≤ 12 (KL assert conditions (1),(2)
experimentally for k ≤ 11); the finite values increase through the reported
levels; strict
decrease of ρ_k(λ) on [1,2]; infeasibility for all λ ∈ (2,12] (k ≤ 6); identity residuals
≤ 10⁻⁶; ε_k (sup fiber oscillation) flat ≈ 0.46 while median fiber oscillation decays.

**Conjectured / open after the successor update:** Problem 3.5 (the dichotomy)
— the point of the note; kernel formalization of the research proofs of
`(H_k)` and qualitative strict growth; a quantitative adjacent gain;
ρ_k(2) → 1 ⟺ λ∞ = 2; an intrinsic
game on Y whose value is λ∞ (exchange of limits).

**Honest failure report.** We did not prove the criterion in the form first attempted
("sup-oscillation ε_k → 0 with Σε_k < ∞"): summability turned out to be unnecessary
(Theorem 3.2(iv) needs only ε_k → 0), but sup-oscillation itself is the wrong quantity —
numerically ε_k does **not** decay (≈ 0.46 flat, k ≤ 12) even though everything is
consistent with λ_k → 2; the correct, and provably equivalent, quantity is the mean
oscillation δ_k. We also did not prove: eigenvector existence/positivity for all k (used
as (H_k)); equality in Proposition 2.1(a) without positivity; and any relation between
ρ_k(2) and λ∞ beyond heuristics.

## References

- I. Krasikov, J. C. Lagarias, *Bounds for the 3x+1 problem using difference
  inequalities*, Acta Arith. 109 (2003) 237–258; arXiv:math/0205002. [Quotes: §6,
  kl_paper.txt lines 1005–1023, 1031–1044, 1067–1086.]
- D. Applegate, J. C. Lagarias, *Density bounds for the 3x+1 problem. II. Krasikov
  inequalities*, Math. Comp. 64 (1995) 427–438. [KL's "[2]".]
- I. Krasikov, *How many numbers satisfy the 3x+1 conjecture?*, Internat. J. Math. Math.
  Sci. 12 (1989) 791–796. [Origin of the difference inequalities.]
- G. Cohen, D. Dubois, J.-P. Quadrat, M. Viot, *A linear-system-theoretic view of
  discrete-event processes and its use for performance evaluation in manufacturing*,
  IEEE Trans. Automat. Control 30 (1985) 210–220; F. Baccelli, G. Cohen, G. J. Olsder,
  J.-P. Quadrat, *Synchronization and Linearity*, Wiley 1992. [Max-plus spectral theory.]
- S. Gaubert, J. Gunawardena, *The Perron–Frobenius theorem for homogeneous monotone
  functions*, Trans. AMS 356 (2004) 4931–4950; R. D. Nussbaum, *Convexity and log-convexity
  for the spectral radius*, Linear Algebra Appl. 73 (1986) 59–122. [Nonlinear Perron;
  Collatz–Wielandt; policy iteration.]
- J.-P. Conze, Y. Guivarc'h, *Croissance des sommes ergodiques et principe variationnel*,
  manuscript 1993; R. Mañé, *Generic properties and problems of minimizing measures*,
  Nonlinearity 9 (1996) 273–310; A. Fathi, *Weak KAM Theorem in Lagrangian Dynamics*;
  T. Bousch, *Le poisson n'a pas d'arêtes*, Ann. IHP Prob. Stat. 36 (2000) 489–508.
  [Subactions, Mañé critical value, ergodic optimization.]
- W. Parry, *Intrinsic Markov chains*, Trans. AMS 112 (1964) 55–66; P. Walters, *An
  Introduction to Ergodic Theory*, Springer 1982, ch. 9. [Perron root = pressure.]
- P. Whittle, *Risk-sensitive Optimal Control*, Wiley 1990; W. H. Fleming, W. M.
  McEneaney, *Risk-sensitive control on an infinite time horizon*, SIAM J. Control Optim.
  33 (1995) 1881–1915. [Log-sum-exp Bellman operators.]

Reproduction: `experiments/kl/limit_object_checks.py` (float; regenerates every table and
fit in this note; §1 tables ≈ 3 min on a laptop). Certified values: `experiments/kl/certify.py`,
`cert_k12.json`–`cert_k14.json` (exact rational arithmetic; see THEOREM.md §5).

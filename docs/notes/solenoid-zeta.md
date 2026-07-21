# The Collatz solenoid zeta: functional equation, confluence at q=3, and why it is hollow

**Date:** 2026-07-20 · **Status:** exact computations + literature audit +
audited handwritten arguments; universal analytic claims await formalization.
**Tags:** **[P]** machine-checked or elementary proof already accepted in the
repo · **[PL]** written proof pending formal check · **[L]** literature ·
**[C]** conjectural (= open arithmetic) · **[S]** speculative.
**Parents:** `deninger-solenoid.md` (Traceless Theorem, Linearization Lemma, arithmetic dictionary), `cycle-finite-places.md` (exp-sum `S_{K,L}`, Q2 equidistribution). Consulted gpt-5.6-sol (verified/corrected the framing; corrections folded in below).

---

## 0. Verdict first (honest calibration)

Pushing the Traceless Theorem to a zeta produces **three genuine, provable statements** and **one clean no-go**, but **no new engine**:

1. **[P] Functional equation + confluence.** The graded `(2,q)`-solenoid zeta satisfies a Weil-shaped functional equation with a self-dual eigenvalue pair `{2,(1+q)/2}`; `q=3` is the *unique confluence* where the pair collides to a double value on the self-dual circle and the zeta trivialises (`Z_3≡1`). This is **real but shallow** — one linear equation in a one-parameter family; it *repackages* first-moment criticality `E_Haar[T']=1`, it does not touch cycle arithmetic. "RH-type / Weil number" is a **metaphor**, not a theorem (after cancellation there is no zero, no pole, no genuine Frobenius/weight theory).
2. **[P/L] Bost–Connes / Connes no-go (qualified).** The `⟨2,3⟩`-semigroup partition function is `(1−2^{-β})^{-1}(1−3^{-β})^{-1}` — two Euler factors of `ζ`, no Collatz content. Any *constant-coefficient* Connes/BC/adele-class zeta on `S` is **blind to the `+1`** (Linearization Lemma) hence to cycles. Same information loss as `Z_3≡1`.
3. **[P] Weil positivity is vacuous here.** `Z_3≡1` has **empty** zero/pole distribution, so the Weil–Guinand positivity mechanism has nothing to act on. No constant-coefficient positivity/vanishing can express "no positive cycle."
4. **[C/S] The real object is the twisted zeta** at *moving* coefficients — and it **relocates the Baker/exp-sum wall**, it does not break it (with a correction to the naive statement: class-0 detection is *additive-character orthogonality over all frequencies*, not a single trivial character).

**Successor-audit candidate theorem (§6, [PL] + exact finite checks):** the
proposed natural boundary at `|u|=1/4` is **false** for the unsigned zeta defined
here. Its fixed-point coefficients are `2·4^K` minus a positive exponentially
smaller term, so the zeta factors as a double pole at `u=1/4` times a
holomorphic nonzero function on a strictly larger disk. The written argument
also makes the residual non-rational and singular at a larger positive radius;
whether its whole circle is a natural boundary is open. Under the repository's
verification rule these general conclusions remain provisional until
formalized; the checker covers the exact finite scope stated below.

---

## 1. Three zetas

`C = g_0 + g_1` on `S`, `g_0 = ×½`, `g_1 = ×(q/2)` (Collatz `q=3`); `λ_v = q^{L}/2^{K}` for a word `v∈{0,1}^K` with `L` ones; `m_v = 2^K−3^L`; `#Fix(g_v|S) =` prime-to-6 part of `|m_v|` (CEW / product formula, `deninger-solenoid.md §2`).

- **Cohomological (graded/Lefschetz) zeta** `Z_q(u) = det(1−uC|H̄^1)/det(1−uC|H̄^0)`. `C` acts on `H̄^0=R` by `2` (branch count) and on `H̄^1=R·[ds]` by `½+q/2=(1+q)/2` (pullback of `ds` by `×λ` scales by `λ`). So
  `Z_q(u) = (1 − (1+q)/2·u)/(1 − 2u)`.  **[P]**
- **Unsigned Artin–Mazur zeta** `ζ_S(u) = exp Σ_K (u^K/K)·a_K`, `a_K = Σ_v #Fix(g_v|S)`. **[P]**
- **Twisted / moving-coefficient zeta** `L(u,·)` — §5.

The supertrace is `Str(C^K) = Tr(C^K|H̄^0) − Tr(C^K|H̄^1) = 2^K − ((1+q)/2)^K`, `= 0 ∀K ⟺ q=3`. (Note: *supertrace*, not trace — each individual trace is `2^K`; the Traceless Theorem is the vanishing of the *difference*.)

---

## 2. Functional equation and the confluence theorem **[P]**

**Prop 2.1 (functional equation).** With `μ = (1+q)/2`,
`Z_q(u)·Z_q(1/((1+q)u)) = μ/2 = (1+q)/4.`
The involution `u ↦ 1/((1+q)u)` fixes the circle `|u| = 1/√(1+q)`; the two "Frobenius eigenvalues" `{2, μ}` form a **self-dual pair** under `x ↦ (1+q)/x`, geometric mean `√(1+q)`. *(Verified symbolically, `scratchpad/zeta.py §2`; also the `×3/2` subsystem's CEW zeta `(1−2u)/(1−3u)` obeys `ζ(u)ζ(1/(6u))=2/3`, eigenvalues `{2,3}` about `√6`.)*

**Prop 2.2 (confluence = criticality).** The pair `{2, μ}` collides (`μ=2`, double eigenvalue *on* the self-dual circle `|x|=√(1+q)=2`) **iff q=3**, and there `Z_3(u) ≡ 1`. The collision condition `μ=2` is identically the first-moment criticality
`E_Haar[T'] = ½·½ + ½·(q/2) = (1+q)/4 = 1.`
So: **`3x+1` is the unique `qx+1` at which a zero–pole pair of the graded solenoid zeta collides on the functional-equation's self-dual circle and the zeta trivialises.** **[P]**

**Honest reading (gpt-5.6-sol, endorsed).** This is *algebraically correct but tautological as "rigidity"*: it solves one linear equation `μ=2` in a one-parameter family. It is a faithful geometric *repackaging* of criticality, valuable as a slogan and as a sanity check on the cohomology normalisation, but it carries **no arithmetic information about cycles**. Calling `{2,2}` a "double Weil number of weight `log 4` on the critical line" is a **metaphor**: once numerator and denominator cancel there is no spectrum, no `Frobenius`, no weight filtration, no critical-line theorem. Tag the slogan **[P]**, the RH-analogy **[S]**.

---

## 3. Bost–Connes / Connes semilocal for (2,3): the constant-coefficient no-go **[P/L]**

- **BC partition function.** For the multiplicative semigroup `⟨2,3⟩` (the natural "semilocal Bost–Connes" datum of the two ramified places of `S`) the partition function is `Σ_{a,b≥0}(2^a3^b)^{-β} = (1−2^{-β})^{-1}(1−3^{-β})^{-1}` — literally the `p=2,3` Euler factors of `ζ(β)`. It knows the *entropy* `log 2`, `log 3` of `×½`, `×3/2` (= the CEW zeta data) and **nothing else**. [L: Bost–Connes phase transition; Connes–Consani semilocal; Morishita 2025 relates Deninger systems ↔ Connes–Consani adelic spaces.]
- **The no-go.** By the **Linearization Lemma** the affine `+1` dies in `S` (it is a diagonal `½∈Z[1/6]`). Hence any zeta/`L`-function built from the *descended constant-coefficient* automorphisms of `S` — BC partition function, adele-class trace, Connes–Consani semilocal `ζ` — is **structurally blind to the `+1`**, therefore to cycles and divergence. This is the *same* information loss that makes `Z_3≡1`.
- **Caveat (do not overclaim).** "*Any* BC/Connes construction" is too strong: one may **retain the affine cocycle** (a lift to the cover `R×Z_2×Z_3`, a groupoid, or twisted coefficients). The no-go is exactly: *constant-coefficient* theories on `S` cannot see Collatz; the arithmetic sits in the deck/cocycle data — which is §5.

---

## 4. Ruelle/dynamical zeta and its two faces **[P/PL]**

- **Signed (cohomological).** `Z_3(u) ≡ 1`: the signed dynamical zeta of the correspondence is the constant `1`. Rational, entire, no zeros/poles. This is the exact statement "the Collatz solenoid correspondence is cohomologically acyclic (Fredholm-determinant `1`)."
- **Unsigned.** `ζ_S(u) = exp Σ_K (u^K/K) a_K`, where `a_K` sums the
  prime-to-6 parts of `|2^K−3^L|` over words. The exact asymptotic is
  `a_K=2·4^K−Θ(R^K/√K)`, with
  `R=2 exp(h(log_3 2))≈3.863626<4`; hence the radius is `1/4`. Data:
  `experiments/solenoid_zeta_growth.csv`; exact checker:
  `experiments/solenoid_zeta_leading_pole.py`. **[PL + exact finite checks]**
- More strongly (§6),
  `ζ_S(u)=(1−4u)^{-2} exp(G(u))`, where `G` is holomorphic for
  `|u|<1/R>1/4`. Thus the first circle contains one double pole, not a
  natural boundary.

**Interpretation.** The signed zeta is the trivial object (`≡1`); *all* of the "size" `~4^K` of the correspondence's fixed-point set is invisible to it (perfect `+`/`−` cancellation across the `2^K>3^L` vs `2^K<3^L` sectors). The unsigned zeta keeps that size but discards the cycle-selecting torsion class — it counts the full pseudo-cycle group `Z/|m_v|` per necklace, blind to *which* class is arithmetic (`deninger-solenoid.md §2.2`).

---

## 5. The twisted zeta is the real object — and it relocates the wall **[C/S]**

To see cycles one must restore the moving coefficients (isogeny tower `×m : S→S`). The honest object is **not** a single Dirichlet twist. Grouping by shape `(K,L)`, `N = 2^K−3^L`, the class-0 (= integer-cycle) count is **additive-character orthogonality over all frequencies**:
`A_{K,L} = (1/N) Σ_{a mod N} Σ_{#1(v)=L} e(a·W(v)/N)`  — a cycle of shape `(K,L)` exists `⟺ A_{K,L} ≥ 1`.
(Correction to a tempting shortcut: it is **not** `Σ_v e(W(v)/N)` — that is the single frequency `a=1`; one needs *every* `a`, and equidistribution/square-root cancellation gives exclusion only when the resulting integer count is `<1`. Admissibility and cyclic rotations must be handled.)

**So the Weil-positivity dream, made precise, is:** *for every contracting shape `2^K>3^L` and every primitive necklace `v∉{0,10}`, `A_{K,L}` restricted to that necklace class vanishes.* This is **exactly** the exp-sum equidistribution Q2 of `dynamical-hasse.md` / `cycle-finite-places.md §8` — the same object whose uniform square-root cancellation is open and whose collapse to Baker was shown on the `m=1` stratum. **No known functional equation or Reidemeister-zeta positivity produces the required Diophantine lower bounds** (gpt-5.6-sol, endorsed). The twisted theory *restores* the arithmetic the constant-coefficient theory erased, but only by *reintroducing the original hard problem*.

- Weil positivity (Q3): with `Z_3≡1` the zero/pole distribution is **empty**, so Weil–Guinand positivity is vacuous. One can tautologically write a positive counting operator whose trace vanishes iff no cycle exists, but it yields no estimate. Positivity needs zeros to be positive *about*; the traceless collapse removed them. **Constant coefficients are the wrong home; the affine cocycle must be restored — and then there is no positivity engine known.**

---

## 6. Candidate leading-pole theorem: the proposed first natural boundary is absent **[PL + exact finite checks]**

Let `β=log_3 2`, `r_K=floor(βK)`, and first omit the prime-to-6
correction:

`A_K = Σ_{L=0}^K binom(K,L)|2^K−3^L|`.

The signed binomial sum is exactly zero. Since `2^K=3^L` has no positive
solutions,

`A_K = 2 Σ_{L≤r_K} binom(K,L)(2^K−3^L)`.

Writing

`T_K=2^K Σ_{L>r_K}binom(K,L)` and
`U_K=Σ_{L≤r_K}binom(K,L)3^L`

gives `A_K=2·4^K−2(T_K+U_K)`. For `L≥1`, `|2^K−3^L|`
is already prime to `6`; only the all-even word changes. If

`D_K=(2^K−1)−(2^K−1)/3^{v_3(2^K−1)}`,

then the actual coefficient is

`a_K=2·4^K−e_K`,  with  `e_K=2(T_K+U_K)+D_K`.

Standard boundary-term estimates (or Stirling plus geometric tail ratios) give

`T_K,U_K = Θ(R^K/√K)`,  `R=2 exp(h(β))≈3.8636262129<4`,

where `h(x)=−x log x−(1−x)log(1−x)` is binary entropy with natural logarithms,

while `D_K=O(2^K)`. An elementary gap proof needs no asymptotic machinery:
`3/5<β<2/3` follows from `3^3<2^5` and `2^3<3^2`; exponential tilting
then bounds the two tails by bases

`ρ_T=5(2/3)^{3/5}<4`,  `ρ_U=3(3/2)^{2/3}<4`,

with the strict inequalities certified after taking fifth and third powers.
Consequently

`log ζ_S(u) = −2 log(1−4u) + G(u)`,

where `G(u)=−Σ_{K≥1}e_Ku^K/K` has exact radius `1/R`. Therefore

`ζ_S(u)=(1−4u)^{-2}exp(G(u))`

extends meromorphically to `|u|<1/R≈0.258824`, and its only singularity on
`|u|=1/4` is the double pole at `u=1/4`. This disproves the inherited
natural-boundary conjecture at the first circle, conditional only on the
written all-`K` tail argument being accepted.

The same `Θ(R^K/√K)` asymptotic proves `ζ_S` is non-rational: rationality
would make `uζ'_S/ζ_S=Σa_Ku^K` rational, hence make `(e_K)` an eventual
constant-coefficient recurrence sequence, whose dominant terms are
polynomials in `K` times exponentials and cannot have a `K^{-1/2}` factor.
At `u=1/R`, `G` converges but `G'` diverges, so the residual factor has a
genuine positive-real singularity there. A natural boundary on the *larger*
circle `|u|=1/R` remains open; the previous claim that cycle arithmetic lives
on `|u|=1/4` is retracted.

**Verification scope.** `experiments/solenoid_zeta_leading_pole.py` checks the
coefficient decomposition exactly through a requested finite `K` (80 in the
documented run), brute-enumerates words through `K=16`, verifies the zeta-series
factorization through degree 80, and checks the powered rational inequalities
for `ρ_T,ρ_U`. It does not prove the all-`K` boundary-tail estimates, the
`Θ(R^K/√K)` asymptotic, exact residual radius, non-rationality, or analytic
continuation. Those are independently audited handwritten arguments awaiting
a proof-assistant trust path.

---

## 7. Next steps (ranked)

1. **[OPEN, low priority]** Determine the singular set of the residual factor on
   `|u|=1/R`. The written proof gives a positive-real singularity; a full
   natural boundary is open, and the claim is provisional under repo policy.
   Do not present it as a Collatz cycle engine without a new bridge.
2. **[OPEN]** Reidemeister/Nielsen twisted-zeta computation for `g_v` on `S`
   (classes `=Z/m_v`). This restores the cycle-selecting class but also restores
   the original exponential-sum/Baker wall.
3. **[days]** Append §2's functional-equation/confluence lemma to
   `deninger-solenoid.md`, explicitly labelled as repackaging rather than rigidity.
4. **Do not pursue** the former `|u|=1/4` natural-boundary program or a
   constant-coefficient Weil-positivity route; both are now closed.

---

## Files
- `experiments/solenoid_zeta_growth.csv` — unsigned-count growth (radius `1/4`).
- `experiments/solenoid_zeta_leading_pole.py` — exact identities, word-level
  cross-checks, zeta-coefficient recurrence, and rational exponential-gap checks.
- Literature: `papers/deninger-2005-arithmetic-foliated-aws.pdf`, `chothi-everest-ward-1997-sinteger-periodic-points.pdf`, `bell-lagarias-natural-boundaries-1408.6884.pdf`; Fel'shtyn–Bondarewicz–Ziętek `arXiv:2202.09776`; Morishita `arXiv:2508.15971`; Bost–Connes / Connes–Consani (semilocal partition function).

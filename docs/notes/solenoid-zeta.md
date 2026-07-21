# The Collatz solenoid zeta: functional equation, confluence at q=3, and why it is hollow

**Date:** 2026-07-20 · **Status:** proved computations + literature audit + blunt verdict.
**Tags:** **[P]** proved here · **[PL]** provable-looking · **[L]** literature · **[C]** conjectural (= open arithmetic) · **[S]** speculative.
**Parents:** `deninger-solenoid.md` (Traceless Theorem, Linearization Lemma, arithmetic dictionary), `cycle-finite-places.md` (exp-sum `S_{K,L}`, Q2 equidistribution). Consulted gpt-5.6-sol (verified/corrected the framing; corrections folded in below).

---

## 0. Verdict first (honest calibration)

Pushing the Traceless Theorem to a zeta produces **three genuine, provable statements** and **one clean no-go**, but **no new engine**:

1. **[P] Functional equation + confluence.** The graded `(2,q)`-solenoid zeta satisfies a Weil-shaped functional equation with a self-dual eigenvalue pair `{2,(1+q)/2}`; `q=3` is the *unique confluence* where the pair collides to a double value on the self-dual circle and the zeta trivialises (`Z_3≡1`). This is **real but shallow** — one linear equation in a one-parameter family; it *repackages* first-moment criticality `E_Haar[T']=1`, it does not touch cycle arithmetic. "RH-type / Weil number" is a **metaphor**, not a theorem (after cancellation there is no zero, no pole, no genuine Frobenius/weight theory).
2. **[P/L] Bost–Connes / Connes no-go (qualified).** The `⟨2,3⟩`-semigroup partition function is `(1−2^{-β})^{-1}(1−3^{-β})^{-1}` — two Euler factors of `ζ`, no Collatz content. Any *constant-coefficient* Connes/BC/adele-class zeta on `S` is **blind to the `+1`** (Linearization Lemma) hence to cycles. Same information loss as `Z_3≡1`.
3. **[P] Weil positivity is vacuous here.** `Z_3≡1` has **empty** zero/pole distribution, so the Weil–Guinand positivity mechanism has nothing to act on. No constant-coefficient positivity/vanishing can express "no positive cycle."
4. **[C/S] The real object is the twisted zeta** at *moving* coefficients — and it **relocates the Baker/exp-sum wall**, it does not break it (with a correction to the naive statement: class-0 detection is *additive-character orthogonality over all frequencies*, not a single trivial character).

**One genuinely-new open lead (§6):** the signed zeta is *rational* (`≡1`) while the unsigned zeta has a *natural boundary* at `|u|=1/4`. This places Collatz exactly on the two sides of the **Pólya–Carlson dichotomy** of Fel'shtyn–Bondarewicz–Ziętek — a well-defined, active, and unexploited framing: **the cycle arithmetic lives in the natural boundary of the unsigned Reidemeister-type solenoid zeta.**

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

## 4. Ruelle/dynamical zeta and its two faces **[P]**

- **Signed (cohomological).** `Z_3(u) ≡ 1`: the signed dynamical zeta of the correspondence is the constant `1`. Rational, entire, no zeros/poles. This is the exact statement "the Collatz solenoid correspondence is cohomologically acyclic (Fredholm-determinant `1`)."
- **Unsigned.** `ζ_S(u) = exp Σ_K (u^K/K) a_K`, `a_K = Σ_v (\text{prime-to-6 part of }|2^K−3^L|)`. Numerically `a_K^{1/K}→4` (so **radius of convergence `=1/4`**), with a slowly growing sub-exponential factor `a_K/4^K` (`0.5→1.63` over `K≤25`); the prime-to-6 correction is negligible (`b_K/a_K≈1`). Data: `experiments/solenoid_zeta_growth.csv`; full sweep `scratchpad/zeta.py §5`. **[P]**
- Why `1/4`: `Σ_v(2^K−3^L)=0` (Traceless), so `a_K = 2Σ_{3^L<2^K}C(K,L)(2^K−3^L) ~ c·4^K`. The *fluctuating* arithmetic of `|2^K−3^L|` about this mean is exactly the CEW/Everest–Ward regime that produces natural boundaries (§6).

**Interpretation.** The signed zeta is the trivial object (`≡1`); *all* of the "size" `~4^K` of the correspondence's fixed-point set is invisible to it (perfect `+`/`−` cancellation across the `2^K>3^L` vs `2^K<3^L` sectors). The unsigned zeta keeps that size but discards the cycle-selecting torsion class — it counts the full pseudo-cycle group `Z/|m_v|` per necklace, blind to *which* class is arithmetic (`deninger-solenoid.md §2.2`).

---

## 5. The twisted zeta is the real object — and it relocates the wall **[C/S]**

To see cycles one must restore the moving coefficients (isogeny tower `×m : S→S`). The honest object is **not** a single Dirichlet twist. Grouping by shape `(K,L)`, `N = 2^K−3^L`, the class-0 (= integer-cycle) count is **additive-character orthogonality over all frequencies**:
`A_{K,L} = (1/N) Σ_{a mod N} Σ_{#1(v)=L} e(a·W(v)/N)`  — a cycle of shape `(K,L)` exists `⟺ A_{K,L} ≥ 1`.
(Correction to a tempting shortcut: it is **not** `Σ_v e(W(v)/N)` — that is the single frequency `a=1`; one needs *every* `a`, and equidistribution/square-root cancellation gives exclusion only when the resulting integer count is `<1`. Admissibility and cyclic rotations must be handled.)

**So the Weil-positivity dream, made precise, is:** *for every contracting shape `2^K>3^L` and every primitive necklace `v∉{0,10}`, `A_{K,L}` restricted to that necklace class vanishes.* This is **exactly** the exp-sum equidistribution Q2 of `dynamical-hasse.md` / `cycle-finite-places.md §8` — the same object whose uniform square-root cancellation is open and whose collapse to Baker was shown on the `m=1` stratum. **No known functional equation or Reidemeister-zeta positivity produces the required Diophantine lower bounds** (gpt-5.6-sol, endorsed). The twisted theory *restores* the arithmetic the constant-coefficient theory erased, but only by *reintroducing the original hard problem*.

- Weil positivity (Q3): with `Z_3≡1` the zero/pole distribution is **empty**, so Weil–Guinand positivity is vacuous. One can tautologically write a positive counting operator whose trace vanishes iff no cycle exists, but it yields no estimate. Positivity needs zeros to be positive *about*; the traceless collapse removed them. **Constant coefficients are the wrong home; the affine cocycle must be restored — and then there is no positivity engine known.**

---

## 6. The one new lead: the Pólya–Carlson dichotomy placement **[C, worth pursuing]**

Fel'shtyn–Bondarewicz–Ziętek (`arXiv:2202.09776`, *Towards a dichotomy for the Reidemeister zeta function*) prove a **Pólya–Carlson dichotomy** — *rational* vs *natural boundary* on the circle of convergence — for Reidemeister/dynamical zetas of endomorphisms of `p`-adic groups and torsion abelian groups; R. Miles gives necessary-and-sufficient rationality conditions for solenoid-endomorphism zetas. The Collatz solenoid lands on **both sides simultaneously**:

| zeta | analytic type | side of dichotomy | sees cycles? |
|---|---|---|---|
| signed `Z_3(u)` | `≡1` (rational, trivial) | rational | no (hollow) |
| unsigned `ζ_S(u)` | radius `1/4`, expected **natural boundary** on `|u|=1/4` | wild | in the boundary |

**Claim/conjecture [C]:** `ζ_S` has `|u|=1/4` as a natural boundary (CEW/Everest–Ward mechanism for `S`-integer zetas with two ramified places), and *the Collatz cycle/divergence arithmetic is precisely the boundary behaviour there* — inaccessible to any rational (constant-coefficient) zeta by construction. This is well-posed, connects to an active program, and is unexploited. It reframes "why has no zeta ever decided Collatz" as a **theorem-shaped statement**: the deciding zeta is provably non-rational, and its natural boundary is the singular locus where `L/K→log_2 3` convergent statistics live.

---

## 7. Next steps (ranked)

1. **[PL, weeks]** Prove the natural boundary of `ζ_S` on `|u|=1/4` via Everest–Ward / Bell–Lagarias technology (`papers/bell-lagarias-natural-boundaries-1408.6884.pdf`); locate the `log_2 3`-convergent singularities. First rigorous non-rationality statement for the Collatz solenoid; genuinely new, publishable, Collatz-agnostic to the hard conjecture.
2. **[PL, weeks]** Reidemeister/Nielsen twisted-zeta computation for `g_v` on `S` (classes `= Z/m_v`); check whether Fel'shtyn rationality survives *word-mixing* — likely a proved no-go that *is* the natural-boundary phenomenon of (1).
3. **[days]** Write §2 (functional equation + confluence) as a clean lemma appended to `deninger-solenoid.md`'s Theorem A — labelled as repackaging, not rigidity.
4. **Do not pursue** a constant-coefficient Weil-positivity route: §3, §5(Q3) show it is provably empty.

---

## Files
- `experiments/solenoid_zeta_growth.csv` — unsigned-count growth (radius `1/4`).
- `scratchpad/zeta.py` — functional equation, confluence, CEW check, growth sweep (all reproducible).
- Literature: `papers/deninger-2005-arithmetic-foliated-aws.pdf`, `chothi-everest-ward-1997-sinteger-periodic-points.pdf`, `bell-lagarias-natural-boundaries-1408.6884.pdf`; Fel'shtyn–Bondarewicz–Ziętek `arXiv:2202.09776`; Morishita `arXiv:2508.15971`; Bost–Connes / Connes–Consani (semilocal partition function).

# THEOREM.md — Exact hypotheses of Krasikov–Lagarias (2002/2003) and correspondence to our solver

Source: I. Krasikov, J. C. Lagarias, *Bounds for the 3x+1 problem using difference
inequalities*, arXiv:math/0205002v1 (30 Apr 2002); published Acta Arith. 109 (2003) 237–258.
Local file: `/Users/simon/Desktop/COLLATZ/papers/krasikov-lagarias-2002-bounds-3x1-difference-inequalities.pdf`
(text extraction: `/Users/simon/Desktop/COLLATZ/experiments/kl/kl_paper.txt`, produced by `pdftotext -layout`).
All line references below are to `kl_paper.txt`.

---

## 0. Objects

- `T(n) = n/2` (n even), `(3n+1)/2` (n odd) — the 3x+1 function.
- For `a ≢ 0 (mod 3)`, `x ≥ 1`:
  - `π_a(x) := #{n : 1 ≤ n ≤ x, some T^(j)(n) = a}` (paper §2, lines 104–105).
  - `π*_a(x) := #{n ≤ x : some T^(j)(n) = a, and all T^(i)(n) ≤ x for 0 ≤ i ≤ j}` (line 107).
    Note `π*_a(x) ≤ π_a(x)`.
- For each residue class `m (mod 3^k)` with `m ≢ 0 (mod 3)` and `y ≥ 0`:
  - `φ^m_k(y) := inf{ π*_a(2^y a) : a ≡ m (mod 3^k), a not in a cycle }` (lines 110–112).
    Well defined because some `a ≡ m (mod 3^k)` is not in a cycle (line 114).
- Properties (immediate from the definition, lines 115–127):
  - (P1) Positivity: `φ^m_k(y) ≥ 1` for all `y ≥ 0`.
  - (P2) Monotonicity: `φ^m_k(y)` nondecreasing in `y`.
  - (P3) Minimization: `φ^m_{k-1}(y) = min[φ^m_k(y), φ^{m+3^{k-1}}_k(y), φ^{m+2·3^{k-1}}_k(y)]`.
- **Audit correction to printed equation (2.1).** The claimed equality
  `φ^m_k(y) = φ^{2m}_k(y−1)` for `m ≡ 1 (mod 3)` is false under the
  definitions above. Writing `P*_a(x)` for the bounded-predecessor set counted
  by `π*_a(x)`, each nonperiodic target `a ≡ 1 (mod 3)` and `x ≥ 2a`
  satisfies the exact targetwise identity

      `P*_a(x) = {a} ⊔ P*_{2a}(x)`,

  because `2a` is the only positive immediate predecessor of `a`. This
  elementary all-`k` identity is kernel-checked in Lean commit `58f0ef8`. Taking
  infima over residue classes loses equality—the doubled targets form only a
  subset of the targets in class `2m`—but gives the valid and stronger useful
  direction

      `φ^m_k(y) ≥ 1 + φ^{2m}_k(y−1)` for `y ≥ 1`.

  The exact `k=2, m=7, y=1` obstruction is
  `φ^7_2(1)=3` versus `φ^{14}_2(0)=φ^5_2(0)=2`; it is checked by independent
  forward and reverse enumeration algorithms in
  `verify_equation_2_1_obstruction.py`. Thus it still suffices
  to work with classes `m ≡ 2 (mod 3)` for lower-bound transfer, but not by
  the printed equality. Notation (eq. (2.2), line 134):
  `[3^k] := {m (mod 3^k) : m ≡ 2 (mod 3)}` — exactly `3^{k-1}` classes.
- `α := log₂ 3 ≈ 1.585` (Proposition 2.1, line 136). This is where the irrational exponent
  enters: it comes from the odd step `n → (3n+1)/2`, which multiplies size by `3/2`, i.e.
  shifts the "time" variable `y = log₂(x/a)` by `α − 1` (and the `(4m−2)/3` branch by `α − 2`).

## 1. The difference inequalities I_k (Proposition 2.1, lines 136–158)

For each `k ≥ 2`, the functions `{φ^m_k : m ∈ [3^k]}` satisfy, **for all y ≥ 2**:

- (D1) if `m ≡ 2 (mod 9)`:  `φ^m_k(y) ≥ φ^{4m}_k(y−2) + φ^{(4m−2)/3}_{k−1}(y+α−2)`   (2.3)
- (D2) if `m ≡ 5 (mod 9)`:  `φ^m_k(y) ≥ φ^{4m}_k(y−2)`                                 (2.4)
- (D3) if `m ≡ 8 (mod 9)`:  `φ^m_k(y) ≥ φ^{4m}_k(y−2) + φ^{(2m−1)/3}_{k−1}(y+α−1)`   (2.5)

where `φ^m_{k−1}(y) := min[φ^m_k(y), φ^{m+3^{k−1}}_k(y), φ^{m+2·3^{k−1}}_k(y)]` (2.6).
(Provenance: [Krasikov 1989, Lemma 4]; also [Applegate–Lagarias 1995 II, Prop. 2.1].)

**Independent successor audit.** These three inequalities do not depend on the
false equality (2.1). For a positive nonperiodic target `a ≡ 2 (mod 3)`, put
`b=4a`, `c=(2a−1)/3`, `X=2^y a`, and
`X'=2^{y−1}(2a−1)`. Uniqueness of the hit on a nonperiodic target gives, for
`y≥2`, the exact disjoint partition

    `P*_a(X) = {a,2a} ⊔ P*_b(X) ⊔ P*_c(X)`.

In the three classes modulo 9, the corrected targetwise doubling identity,
discarding the unusable `c` branch, or retaining it directly gives D1, D2, or
D3 respectively. In fact the right sides may be strengthened by additive
constants `+3,+3,+2`. The scale identities are exact:
`X=2^{y−2}(4a)`,
`X'=2^{y+α−2}(4a−2)/3`, and
`X'=2^{y+α−1}(2a−1)/3`. Taking infima has the favorable inequality direction
even though the child targets cover only subsets of their residue pools. An
exact reverse-tree checker `verify_predecessor_base_inequalities.py` passed
these inclusions and disjointness claims for all nonperiodic `a<500` and
integer `2≤y≤5`; the targetwise doubling lemma is
kernel-checked, and commit `729f5fa` kernel-checks the all-`k` D1--D3
residue-infimum theorem. The nonperiodicity hypothesis is essential for
disjointness.

Arithmetic sanity (used by our indexing): if `m ≡ 2 (mod 9)` then `4m−2 ≡ 0 (mod 3)` and
`(4m−2)/3 ≡ 2 (mod 3)`; if `m ≡ 8 (mod 9)` then `2m−1 ≡ 0 (mod 3)` and `(2m−1)/3 ≡ 2 (mod 3)`;
`4m ≡ 2 (mod 3)` always. The classes `(4m−2)/3`, `(2m−1)/3` are taken `mod 3^{k−1}`, and the
result is independent of which lift of `m (mod 3^k)` is used.

Terms `φ^m_k(y+β)` with `β ≥ 0` are called **advanced**, with `β < 0` **retarded** (lines 163–165).
(D3) contains the advanced term (α−1 > 0); (D1) is purely retarded (α−2 < 0) (`α−2 ≈ −0.415 < 0` is retarded, but after expanding the
min (2.6) and iterating, `α−1 ≈ 0.585 > 0` in (D3) is advanced). This is why the earlier
Applegate–Lagarias machinery did not apply directly and why this paper exists.

## 2. The linear program family L^NT_k(λ) (§2, eqs. (2.7)–(2.14), lines 180–224)

**Naming.** The superscript "NT" is a *tag* meaning "No Truncation" — it refers to the linear
program denoted `L^NT_λ` in Applegate–Lagarias [2], associated *directly* to I_k without the
truncation operation used in [2]. **There are no parameters N and T**; nothing in the LP family
grows with k except the number of residue classes (`3^{k-1}` principal variables). We checked
this reading against every occurrence of "NT" and "truncat-" in the paper (lines 69–79, 83–87,
170–181, 995: "Table 2: NLP Lower Bounds: No truncation of advanced terms").

Variables:
- **principal**: `c^m_k` for `m ∈ [3^k]` (that is, `3^{k−1}` variables);
- **auxiliary**: `c^m_{k−1}` for `m ∈ [3^{k−1}]`;
- **objective**: `C^max_k` (plays no role in feasibility, lines 233–235).

`L^NT_k(λ)`: Minimize `C^max_k` subject to:

- (L0) for all `m ∈ [3^k]`:  `1 ≤ c^m_k ≤ C^max_k`                                    (2.8)
- (L1) for all `m ∈ [3^k]`, `m ≡ 2 (mod 9)`:
        `c^m_k ≤ c^{4m}_k λ^{−2} + c^{(4m−2)/3}_{k−1} λ^{α−2}`                        (2.9)
- (L2) for all `m ∈ [3^k]`, `m ≡ 5 (mod 9)`:
        `c^m_k ≤ c^{4m}_k λ^{−2}`                                                     (2.10)
- (L3) for all `m ∈ [3^k]`, `m ≡ 8 (mod 9)`:
        `c^m_k ≤ c^{4m}_k λ^{−2} + c^{(2m−1)/3}_{k−1} λ^{α−1}`                        (2.11)
- (L4) for all `m ∈ [3^{k−1}]`:
        `c^m_{k−1} ≤ c^m_k`,  `c^m_{k−1} ≤ c^{m+3^{k−1}}_k`,  `c^m_{k−1} ≤ c^{m+2·3^{k−1}}_k`
        (2.12)–(2.14); cf. (2.15): `c̄^m_{k−1} := min{c^m_k, c^{m+3^{k−1}}_k, c^{m+2·3^{k−1}}_k}`.

  (In the raw pdftotext output the superscripts `3^{k−1}` in (2.12)–(2.14) are mangled to
  "3k"; that they are `3^{k−1}` is unambiguous from (2.6), (2.15) (line 240), (4.6)–(4.7)
  (lines 777–784, `m(v)+j·3^{k−1}`), and the k=2 appendix.)

Inequality directions (L1)–(L3) are *opposite* to (D1)–(D3); (L4) matches (2.6) (lines 225–226).

**Auxiliary-variable elimination** (lines 243–253): auxiliaries have no lower bound; given any
feasible solution one may raise each auxiliary to its maximal value `c^m_{k−1} = c̄^m_{k−1} ≥ 1`
(this keeps (L4) tight and only weakens (L1),(L3), whose RHS coefficients `λ^{α−2}, λ^{α−1} > 0`).
Hence:

> **Reduced feasibility criterion.** `L^NT_k(λ)` is feasible iff there is a vector
> `c = (c^m)_{m ∈ [3^k]}` with `c^m ≥ 1` and, for all `m ∈ [3^k]` (all classes mod `3^k`, taken
> as integer representatives; `4m`, `r` reduced mod `3^k`, `mod 3^{k−1}` resp.):
>
> - `m ≡ 2 (mod 9)`:  `c^m ≤ λ^{−2} c^{4m mod 3^k} + λ^{α−2} · min_{j=0,1,2} c^{r + j·3^{k−1}}`,
>   `r = (4m−2)/3 mod 3^{k−1}`;
> - `m ≡ 5 (mod 9)`:  `c^m ≤ λ^{−2} c^{4m mod 3^k}`;
> - `m ≡ 8 (mod 9)`:  `c^m ≤ λ^{−2} c^{4m mod 3^k} + λ^{α−1} · min_{j=0,1,2} c^{r + j·3^{k−1}}`,
>   `r = (2m−1)/3 mod 3^{k−1}`.

This is a componentwise condition `c ≤ F_λ(c)` for the monotone, degree-1-homogeneous,
concave (min-of-linear) operator `F_λ`; feasibility for a given λ is equivalent to the
nonlinear Perron eigenvalue of `F_λ` being **≥ 1** (Collatz–Wielandt: for any `c > 0`,
`min_m F_λ(c)_m/c_m ≤ ρ(F_λ) ≤ max_m F_λ(c)_m/c_m`).

**Orientation.** The inequality direction to be certified is exactly (2.9)–(2.14) of the
paper: `c^m` on the small side, `F_λ(c)^m` on the large side. The feasible region in λ lies
*below* the threshold: §6 (lines 1028–1031) defines λ_k as "the supremum of values of λ for
which L^NT_k(λ) has a feasible solution", and (lines 1031–1041) any feasible solution at level
k lifts to level k+1 at the same λ, so λ_k is nondecreasing in k. Our certificates take
λ_cert strictly below the numerically computed threshold and then verify `c ≤ F_λcert(c)`
**directly and exactly** — no monotonicity-in-λ or spectral argument is part of the proof
chain; the LP inequalities themselves are checked one by one.

### Correspondence with `kl_perron_solver.py` `build()` / `eigval()`

| paper object | solver object | check |
|---|---|---|
| `[3^k]` = {m mod 3^k : m ≡ 2 mod 3} | `ms = np.arange(2, 3**k, 3)` (n = 3^{k−1} entries) | ✓ same set, ascending |
| `c^{4m mod 3^k}` | `c[i4m]`, `i4m[i] = idx[(4*m) % 3**k]` | ✓ |
| branch `m ≡ 2 (mod 9)` (L1) | `mask2 = (ms % 9 == 2)` | ✓ |
| branch `m ≡ 5 (mod 9)` (L2) | neither mask (only the `4m` term) | ✓ |
| branch `m ≡ 8 (mod 9)` (L3) | `mask8 = (ms % 9 == 8)` | ✓ |
| `min_j c^{(4m−2)/3 + j·3^{k−1}}` | `ref2[i] = [idx[(r + j*3^{k−1}) % 3^k]]`, `r = ((4m−2)//3) % 3^{k−1}` | ✓ = c̄ of (2.15) |
| `min_j c^{(2m−1)/3 + j·3^{k−1}}` | `ref8[i]`, `r = ((2m−1)//3) % 3^{k−1}` | ✓ |
| coefficient `λ^{−2}` (all of L1–L3) | `w4 = lam**-2.0` | ✓ |
| coefficient `λ^{α−2}` (L1 only) | `w2 = lam**(ALPHA-2)`, `ALPHA = log₂3` | ✓ |
| coefficient `λ^{α−1}` (L3 only) | `w8 = lam**(ALPHA-1)` | ✓ |
| feasibility `c ≤ F_λ(c)`, `c ≥ 1` | fixed point of `f = w4·c[i4m] + mask2·w2·min + mask8·w8·min`; `λ_k` = λ where Perron value = 1 | ✓ |

(Independently re-derived and cross-checked machine-side in `certify.py`
(`build_exact()` vs solver `build()`, exact match for k = 2..7).)

## 3. Main theorem

> **Theorem 2.2** (lines 263–275, verbatim modulo typography). *Let `1 ≤ λ ≤ 2` be such that
> the linear program `L^NT_k(λ)` has a feasible solution with principal variables
> `{c^m_k : m ∈ [3^k]}`. Then for all `m ∈ [3^k]` and all `y ≥ 0`,*
>
>   `φ^m_k(y) ≥ Δ₁ · c^m_k · λ^y`,   where  `Δ₁ := 1 / (4 · max{c^m_k : m ∈ [3^k]})`.  (2.16)–(2.17)

Supporting chain (all stated for **every** `k ≥ 2`, no upper bound on k in the
statements). **Successor-audit caveat:** the exact certificate in
`TERMINATION_AUDIT.md` invalidates the derivation of equation (3.2) and directly
falsifies the following identical-subtree step in the printed proof of Theorem
3.1. A second exact path makes all three leaves of a new minimum
deletion-eligible, contradicting the construction's claimed nonempty-minimum
invariant. A generic four-value countermodel also refutes the split-invariant
induction from the hypotheses it uses. CLEAN_LEAN independently checks both
newer obstructions and proves the abstract branch-arrival compactness theorem.
Commit `3d6a186` also checks an all-`k` replacement construction: a
well-founded raw-history producer, root-level occurrence provenance, live
deterministic pruning, a common positive lag, and the complete comparison from
finite feasibility to the `1/(4C)` exponential lower bound. Thus the abstract
advanced-elimination seam is kernel-checked without the printed construction.
Commit `331ff48` defines the literal statewise predecessor family and proves
target-pool nonemptiness, normalization, and monotonicity. Commit `729f5fa`
proves that family satisfies D1--D3. Commit `76ec861` proves the final fixed-
target/all-target exponent transfer, so the mathematical chain to the literal
`π_a` statement is complete. The large `k=19` data remain externally exact-
verified rather than Lean-ingested.

- **Theorem 3.1** (lines 428–433): for `m ∈ [3^k]`, `m ≡ 8 (mod 9)`, the back-substitution
  process (with the deletion rule) halts in finitely many steps at an inequality `I^m_k(EL)`
  containing no advanced terms; the result is order-independent.
- **Theorem 3.2** (lines 468–473): any set `Φ_k = {φ^m_k}` of strictly positive, nondecreasing
  functions on `R≥0` satisfying I_k for all `y ≥ 2` also satisfies `I_k(EL)` for all `y ≥ 2`.
  (This is where positivity (P1) and monotonicity (P2) are used, to justify the deletion rule.)
- **Theorem 4.1** (lines 717–722): if `L^NT_k(λ)` has a feasible solution with principal
  variables `{c^m_k}`, `1 ≤ λ ≤ 2`, then `L^EL_k(λ)` has a *positive* feasible solution with the
  same principal variables. (Purely LP-side; auxiliaries are assigned by (4.7),
  `a_v = c̄^{m(v)}_{k−1}`.)
- **Theorem 5.1** (lines 815–833): if `Φ_k` positive, nondecreasing satisfies a difference
  system D with *no advanced variables* and `L^D_k(λ)`, `λ > 1`, has a positive feasible
  solution `{c^m_k}`, then `φ^m_k(y) ≥ Δ c^m_k λ^y` for all `y ≥ 0`, with
  `Δ = λ^{−ν} · min{φ^m_k(0)}/max{c^m_k}`, ν = largest backward time-shift in D.
- **Proof of Theorem 2.2** (lines 912–946): combine the above with D = I_k(EL); every retarded
  shift produced by the construction satisfies `β_j ≥ −2` (line 346), so `ν ≤ 2`; with (P1)
  (`φ^m_k(0) ≥ 1`) and `λ ≤ 2`: `Δ ≥ λ^{−2}·1/max{c} ≥ (1/4)/max{c} = Δ₁`. This is the only
  place the hypothesis `λ ≤ 2` is used, and the only role of `C^max_k`: it controls the
  *constant* `Δ₁`, never the exponent.

## 4. From Theorem 2.2 to π_a(x) (Theorem 6.1, lines 965–977)

> **Theorem 6.1.** *For each positive `a ≢ 0 (mod 3)`,
> `π_a(x) ≥ x^{0.84}` for all sufficiently large `x ≥ x₀(a)`.*
> Proof: "by finding a positive feasible solution by computer to the linear program family
> `L^NT_k(λ)` for k = 11, for λ = 1.7922310 … This yields the exponent γ = log₂λ ≈ 0.84175."

Transfer mechanism (making the constants explicit): if `a ≡ m (mod 3^k)`, `m ≡ 2 (mod 3)`, and
`a` is not in a cycle, then for `x = 2^y a`, `y ≥ 0`:
`π_a(x) ≥ π*_a(2^y a) ≥ φ^m_k(y) ≥ Δ₁ c^m_k λ^y ≥ Δ₁ (x/a)^{γ}` with `γ = log₂ λ`,
i.e. `π_a(x) ≥ (Δ₁ a^{−γ}) · x^{γ}` for all `x ≥ a`. If
`a ≡ 1 (mod 3)` is nonperiodic, apply the same bound to `2a ≡ 2 (mod 3)`
and use `π_a(x) ≥ π_{2a}(x)`; equivalently, use the corrected one-sided
version of (2.1) above. This costs the same factor `λ^{−1}`. If `a` lies in
an arbitrary positive cycle, choose a sufficiently large `b=2^r a` with
`b ≡ 2 (mod 3)`. Only finitely many such distinct powers can lie in that
cycle, so `b` can be chosen nonperiodic, while `T^[r](b)=a` gives
`π_a(x) ≥ π_b(x)`. No classification of positive cycles is needed. Because of the
`a`-dependent constant, the clean stated form rounds the exponent *down* (0.84175… → 0.84) and
holds "for all sufficiently large x ≥ x₀(a)". The bound is **asymptotic, not effective in a
uniform sense**: x₀(a) depends on the chosen doubled predecessor `b` and its
residue coefficient (the direct class-2 constant is `Δ₁ c^m_k b^{−γ}`),
but for fixed a it is effective — the constant `Δ₁ = 1/(4 max c^m_k)` is explicit from the
certificate, e.g. `π_a(x) ≥ Δ₁ (x/a)^γ` for every non-cycle `a ≡ 2 (mod 3)` and all `x ≥ a`.

## 5. Hypotheses checklist for a new k (what a certificate must establish)

To invoke Theorem 2.2 at level k with parameter λ we need **exactly**:

1. `k ≥ 2` (integer); the residue system, branch classes, and min-triples built as in §2 above.
2. `1 ≤ λ ≤ 2` (for the Δ₁ form; `λ > 1` for a nontrivial bound).
3. A vector `{c^m : m ∈ [3^k]}` with `c^m ≥ 1` satisfying the reduced feasibility criterion of
   §2 (equivalently, together with auxiliaries `c̄^m_{k−1}` and `C^max = max c^m`, a feasible
   point of (L0)–(L4)).

Nothing else. In particular:

- **No hypothesis limits k.** Theorems 3.1, 3.2, 4.1, 5.1 and 2.2 are stated for all `k ≥ 2`.
  The derived system I_k(EL) is finite but astronomically large for k ≥ 5 (Table 1, line 597:
  depth > 226, > 10^9 literals already at k = 5) — but I_k(EL) is *never constructed* in
  applying Theorem 2.2; only feasibility of the small system L^NT_k(λ) must be exhibited.
  The paper's k ≤ 11 is a computational budget of 2002, not a hypothesis. §6 (lines 1030–1041)
  proves `λ_k ≤ λ_{k+1}` (lifting a feasible solution by `c^{m+j·3^k}_{k+1} := c^m_k`), and
  poses `λ_k → 2` as the open problem.
- **No x-range hypothesis** enters Theorem 2.2 (conclusion holds for all `y ≥ 0`); the
  `x ≥ x₀(a)` in Theorem 6.1 only absorbs the explicit constant `Δ₁ a^{−γ}` and the rounding
  of the exponent.
- **Certificate-format scope.** The finite JSON/sidecar certifies solely LP
  feasibility; it does not certify that the literal predecessor functions
  satisfy `I_k`. Proposition 2.1 supplies that paper-side step. Its targetwise
  D1--D3 derivation has now been independently re-audited, and bounded cases
  have an exact checker; commit `729f5fa` proves that the concrete `klPhi` of
  commit `331ff48` satisfies the base system. Commit `76ec861` closes the final
  exponent wrapper for arbitrary admissible targets.
- **Conditions "(1)", "(2)" at the end of §6** (lines 1067–1086: λ_k attained; principal
  inequalities tight at the optimum) concern only whether Theorem 2.2's bound is *best
  possible* for I_k — the converse direction. They are not hypotheses of Theorem 2.2 and
  play no role in the lower bound.
- The paper does **not** document how Applegate's 1995/2002 computations handled the
  irrational exponents `λ^{α−1}, λ^{α−2}` (α = log₂3) in verifying feasibility — Theorem 6.1
  just says "by finding a positive feasible solution by computer … for λ = 1.7922310", λ given
  as an exact 8-digit rational. No exact-arithmetic device appears in the paper. Our
  certification therefore *strengthens* the requirement instead of copying a device: we verify
  in exact rational arithmetic the **tighter** system in which the coefficients `λ^{α−2}` and
  `λ^{α−1}` are replaced by certified rational lower bounds `W2 ≤ λ^{α−2}`, `W8 ≤ λ^{α−1}`
  (`λ^{−2}` is exactly rational for rational λ). Since these coefficients multiply nonnegative
  quantities on the ≤-side, feasibility of the tightened system implies feasibility of
  `L^NT_k(λ)` with the true irrational coefficients. The bounds W2, W8 are certified by pure
  integer inequalities: with `p/q = 50508/31867` (a continued-fraction convergent of α from
  below), `2^p < 3^q` certifies `p/q < α`, and since `λ > 1`, `λ^{α−2} > λ^{p/q−2}` and
  `λ^{α−1} > λ^{p/q−1}`; then `W2 ≤ λ^{p/q−2} ⇔ W2^q · λ^{2q−p} ≤ 1` and
  `W8 ≤ λ^{p/q−1} ⇔ W8^q ≤ λ^{p−q}`, which for rational W2, W8, λ are finite integer
  comparisons. See `certify.py`, function `certified_weight_bounds()`.

## 6. Discrepancy notes (paper-internal)

- Table 2's γ-column is log₂(λ-column) truncated (not rounded) at the 7th decimal; e.g.
  log₂(1.7922310) = 0.84175658…, table prints 0.8417560. The "record exponent" is thus
  γ₁₁ = log₂ 1.7922310 = 0.8417566 (7 s.f.), consistent with our solver's output.
- Theorem 6.1's exponent 0.84 is a deliberate round-down of 0.84175…, absorbing constants.
- Our independently written float solver reproduces the full Table 2 λ-column to within
  1e-6 (their published precision) for k = 2..11 — strong evidence the constraint system
  transcribed above is the one they solved.

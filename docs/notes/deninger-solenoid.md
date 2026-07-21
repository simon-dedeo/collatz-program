# The Collatz correspondence on the (2,3)-solenoid: a Deninger-style Lefschetz linkage

**Date:** 2026-07-20 · **Status:** structural note with proved computations, a literature audit, and a precisely stated dream.
**Claim tags:** **[P]** proved here (short argument included and/or machine-checked), **[L]** literature theorem (source cited, hypotheses quoted), **[PL]** provable-looking (routine but not written out), **[C]** conjectural (equivalent to open arithmetic), **[S]** speculative (formalism does not yet exist).
**Prior context:** LANDSCAPE.md (2-adic conjugacy, cycle equation, Hercher/Baker bounds), SMELL.md item 9 / CRACKS.md crack #6, and `docs/cracks/MSC-11K16--11K06-distribution-mod-1-Mahler-32-prob.json` (the solenoid bridge file; cut-and-project dictionary). Novelty check 2026-07-20: web search for Collatz + Deninger/foliated/Lefschetz returns nothing — this bridge is unclaimed.

---

## 0. Summary — the sharpest statements

Let `S = (R × Q_2 × Q_3)/Z[1/6]` (diagonal embedding; compact connected abelian group, laminated by dense R-leaves, Cantor transversal `Q_2 × Q_3`). For a parity word `v ∈ {0,1}^K` with `L` ones write `λ_v = 3^L/2^K`, `m_v = 2^K − 3^L`, and `W(v) = Σ_j 3^{L−j} 2^{t_j}` (Böhm–Sontacchi weight; odd steps at times `t_1 < … < t_L`).

1. **[P] Linearization Lemma.** The affine Collatz branches `x/2` and `(3x+1)/2` descend to S as the *linear* automorphisms `×(1/2)` and `×(3/2)`: every translation the Collatz map ever produces (`1/2`, and `W(v)/2^K` for any word) lies in `Z[1/6]` and dies in the quotient. The (2,3)-solenoid sees only `(K, L)`; the additive `+1` — the entire arithmetic of the problem — lives on the cover `R × Q_2 × Q_3` (equivalently `(R×Z_2×Z_3)/Z`), not on S.

2. **[P] Per-word fixed points (product formula).** `g_v := g_{v_{K−1}} ∘ … ∘ g_{v_0}` acts on S as `×λ_v`, with
   `#Fix(g_v|S) = Π_{w∈{∞,2,3}} |1−λ_v|_w = ` prime-to-6 part of `|2^K − 3^L|` (= `|2^K−3^L|` whenever `L ≥ 1`),
   and `Fix(g_v|S) ≅ Z[1/6]/m_v Z[1/6]` canonically. This is the Chothi–Everest–Ward S-integer periodic-point formula (Lemma 5.2 of CEW) applied word by word; the count is an Artin–Whaples product-formula computation.

3. **[P] Traceless Theorem (the balanced identity).** The Collatz correspondence `C = graph(g_0) ∪ graph(g_1)` acts on the reduced leafwise cohomology of S (`H̄^0 ≅ R`, `H̄^1 ≅ R·[ds]`, Fourier computation) with
   `Tr(C^K | H̄^0) = 2^K` and `Tr(C^K | H̄^1) = Σ_v λ_v = (1+3)^K/2^K = 2^K`,
   so the graded (Atiyah–Bott–Guillemin-normalized) Lefschetz trace **vanishes identically for every K**: `Σ_v (1 − λ_v) = 2^K − 4^K/2^K = 0`. The associated cohomological zeta function is `det(1−u·C|H̄^1)/det(1−u·C|H̄^0) = (1−2u)/(1−2u) ≡ 1`.
   **Uniqueness of 3:** for the `qx+1` correspondence on the (2,q)-solenoid the graded trace is `2^K − ((1+q)/2)^K`, which vanishes **iff q = 3**. Equivalently: `3x+1` is the unique `qx+1` problem whose branch multipliers satisfy `(1/2)·(1/2) + (1/2)·(q/2) = 1` — Haar-expected leafwise derivative exactly 1, the first-moment martingale criticality of the Collatz walk (the multiplicative twin of the known log-drift `½log(3/4) < 0`).

4. **[P] Defect Theorem (test of Deninger's solenoid working hypothesis).** The suspension flow on `X_C := (Ω̂ × S) ×_Z R` (Ω̂ = two-sided 2-shift; return map `F(ω,x) = (σω, g_{ω_0}x)` — an honest homeomorphism, so the branching correspondence *is* a flow on a compact laminated space, matching Deninger's 7.5 setting: 2-dim leaves, codim-1 subfoliation F, flow transverse, no fixed points, all closed orbits non-degenerate) has orbit side
   `Σ_v sign(m_v)·#Fix(g_v|S) = −( (2^K−1) − (2^K−1)/3^{v_3(2^K−1)} )`,
   which is `0` for K odd and **nonzero for every even K** (`v_3(2^K−1) = 1 + v_3(K)` by LTE), while the cohomological side is 0 by (3). So Deninger's working hypothesis 7.5 (formula (32) of the Arizona lectures), taken with its stated ±1 orbit coefficients, **fails on X_C at even K by exactly the 3-part of 2^K − 1**, a defect supported entirely on the all-even necklace (the 0-cycle). Numerically verified K ≤ 10 (e.g. K=2: −2; K=6: −56; K=10: −682).

5. **[P] Corrected local terms.** The formula is restored exactly, for all K, by weighting each closed orbit with the **p-adic modules of its transverse holonomy**:
   `local term at (v,x) := sign(1−λ_v) · |1−λ_v|_2^{-1} · |1−λ_v|_3^{-1}` (per fixed point; note `|1−λ_v|_2 = 2^K` uniformly — a global 2-adic Tate twist — and `|1−λ_v|_3 = 1` except on all-even words).
   With these local factors, LHS = RHS = 0 for every K, by the product formula. This reduces to Deninger's ±1 coefficients precisely when the transverse holonomy is isometric — which covers every previously proved case (Deninger–Singhof suspensions Thm 7.8, Álvarez López–Kordyukov Riemannian foliations, Leichtnam's p-adic laminations) — and X_C is, to my knowledge, **the first explicit adelic example showing the non-isometric correction is forced**. *Proposed general form* **[PL→C]**: in the laminated trace formula the coefficient of `δ_{kl(γ)}` should be `ε_γ(k)/|det(1 − hol_γ^k)|_{transversal}` with the module taken over the totally disconnected transversal directions.

6. **[P] The arithmetic dictionary (exact relation to Collatz cycles, trivial and negative included).** Closed orbits of combinatorial length K of the flow on X_C ↔ pairs (necklace `v`, torsion class `j ∈ Z[1/6]/m_v ≅ Z/N_v`). Each necklace carries exactly one **arithmetic class** `j = [W(v)]`, the image of the unique 2-adic T-cycle `n_v = W(v)/m_v ∈ Q ∩ Z_2` through the word `v`. Then:
   - `n_v ∈ Z` (integer cycle) ⟺ `[W(v)] = 0` ⟺ the arithmetic orbit passes through the basepoint fiber `0 ∈ S` ⟺ **integrality at the moving places** `p | 2^K − 3^L`;
   - `n_v > 0` ⟺ `2^K > 3^L` ⟺ `λ_v < 1` ⟺ the closed orbit is **leafwise contracting** (`ε_γ = +1`).
   The five known integral necklaces:

   | necklace | (K,L) | m = 2^K−3^L | W | n | leafwise sector |
   |---|---|---|---|---|---|
   | `0` | (1,0) | 1 | 0 | 0 | contracting |
   | `10` | (2,1) | 1 | 1 | **1** (trivial cycle {1,2}) | contracting |
   | `1` | (1,1) | −1 | 1 | **−1** | expanding |
   | `110` | (3,2) | −1 | 5 | **−5** ({−5,−7,−10}) | expanding |
   | `11110111000` | (11,7) | −139 | 2363 = 17·139 | **−17** (11-step cycle) | expanding |

   The first four are **unit necklaces**: `|2^K − 3^L| = 1`, so `Fix(g_v|S) = {0}` and integrality is *forced* — no arithmetic coincidence at all; the complete list of unit solutions is `(K,L) ∈ {(1,0),(2,1),(1,1),(3,2)}` (elementary + Mihailescu). The −17 cycle is the only known **sporadic** integral necklace: a genuine finite-place coincidence `139 | 2363`. The negative cycles are exactly as the mandate predicted: integral at every finite place, distinguished only by the archimedean/leafwise datum — they sit in the *expanding* sector, where the "Frobenius weight" `log λ_v > 0`. A K ≤ 16 exhaustive sweep finds precisely the members of these five orbits and nothing else **[P]**.

7. **[C→S] The dream, stated precisely** (§7): "no nontrivial positive cycle" ⟺ *in the leafwise-contracting sector, no primitive necklace other than `0`, `10` has vanishing arithmetic class* `[W(v)] ∈ Z/|2^K−3^L|`. The cohomological upgrade would be a positivity/vanishing statement for the correspondence acting on a **moving-coefficient** cohomology (`Z/m_v`-towers = the isogeny covers `×m_v : S → S`); constant coefficients provably cannot see it, because by (3) the constant-coefficient theory is *exactly hollow* (zeta ≡ 1, no spectral sector at all — no room for a Weil positivity). This locates the precise point where the Weil/Deninger pipeline must be extended rather than applied.

---

## 1. Objects

### 1.1 The solenoid

`A := R × Q_2 × Q_3` with the diagonal embedding of `Λ := Z[1/6]`; Λ is discrete and cocompact (fundamental domain `[0,1) × Z_2 × Z_3`), `S := A/Λ`. Facts, all standard **[L]**:
- S is a compact connected abelian group; `Ŝ ≅ Λ` (self-orthogonality of the S-integers under the S-adelic pairing; this is the duality CEW use, §2 of [CEW]).
- Path components ("leaves") are the images of `R × {pt}`; each is dense (strong approximation: Z[1/6] dense in `Q_2 × Q_3`); transversal `Q_2 × Q_3` totally disconnected. S is a *generalized solenoid / laminated space* exactly in the sense of Deninger's §7 (AWS lectures) and of Leichtnam.
- Equivalent presentations: `S ≅ (R × Z_2 × Z_3)/Z ≅ lim← (R/Z, ×2, ×3)` — the (2,3)-adic solenoid; the cut-and-project scheme with internal space `Z_2 × Z_3` and window `Z_2 × Z_3` reproduces Z ⊂ Λ (crack-file dictionary).
- Every `2^a 3^b ∈ Λ^×` acts as an automorphism of S. `×(3/2)` has entropy `log 3` and CEW-periodic points `#Fix((3/2)^k) = Π_{w∈{∞,2,3}} |(3/2)^k − 1|_w = 3^k − 2^k` — this is verbatim **Example 8.1 of [CEW]** with zeta `exp Σ (3^k−2^k)u^k/k = (1−2u)/(1−3u)`, a rational, "curve-like" zeta with Frobenius eigenvalues {2,3}.

### 1.2 Linearization Lemma **[P]**

The Collatz branches on A are `f_0(x) = x/2`, `f_1(x) = (3x+1)/2` (componentwise; both bijections of A since 2, 3 ∈ Λ^×). The translation part of `f_1` is the *diagonal* element `1/2 ∈ Λ`, hence trivial on S: `f_1 ≡ ×(3/2) mod Λ`. Inductively `g_v = f_{v_{K−1}}∘…∘f_{v_0}` has linear part `λ_v = 3^L/2^K` and translation `W(v)/2^K ∈ Λ` (W(v) an integer, 2^K a unit of Λ), so **on S, `g_v = ×λ_v` exactly**. ∎

Consequences: (i) the fixed-point sets on S depend only on (K,L); (ii) all arithmetic content (the `+1`) is *deck-transformation data* of the covering `A → S` (equivalently of `(R×Z_2×Z_3) → S` with deck group Z); (iii) the integer/rational cycle structure reappears downstairs only through *which torsion class* the canonical fixed point occupies — §2.

### 1.3 The Collatz suspension flow (the "right construction")

The mandate asked: suspension of T on Z_2, or the ×3/2 flow? **Answer: neither alone; the correct object is the common refinement.** Define
- `Ω̂ := {0,1}^Z` with shift σ (= the natural extension of T on Z_2, via Lagarias's conjugacy **[L]**),
- `F : Ω̂ × S → Ω̂ × S`, `F(ω, x) = (σω, g_{ω_0} x)` — a **homeomorphism** (branching absorbed into the symbolic coordinate),
- `X_C := (Ω̂ × S) ×_Z R` (mapping torus), with suspension flow φ.

Then `(X_C, L, F, φ)` is a compact laminated space with 2-dimensional leaves (R-leaf of S × flow direction), the codim-1 subfoliation `F` by the S-leaf direction, flow everywhere transverse to F, no fixed points, and every closed orbit non-degenerate (`λ_v ≠ 1` always since `2^K ≠ 3^L`). This is *exactly* the shape of Deninger's working hypotheses 7.5 (and of his proved suspension Theorem 7.8, except our fiber map is not an unramified self-cover of a manifold and our transverse holonomy is not isometric — §4, §6). **[P]** (construction; verifications elementary)

Its two degenerate collapses:
- forgetting S: the suspension of the 2-shift = suspension of the natural extension of `T` on `Z_2` — symbolically trivial, zeta `1/(1−2u)`, *no* arithmetic (LANDSCAPE: "ergodic theory sees only noise") — one closed orbit per necklace = the rational T-cycles `n_v`, all counted 1;
- restricting to the all-odd sector: the `×(3/2)` suspension with CEW zeta `(1−2u)/(1−3u)`.

Closed orbits of φ **[P]**: length-K periodic points of F = pairs `(v, x)`, `v ∈ Fix(σ^K)`, `x ∈ Fix(g_v|S)`; grouped into F-orbits = (necklace, torsion-class-orbit). Lengths: K (unit time per symbol; `ℓ = K log 2` if one prefers `e^{ℓ} = 2^K` normalization — the uniform 2-adic factor in §4 then reads as a Tate twist).

---

## 2. Closed orbits vs. Collatz cycles: the arithmetic dictionary

### 2.1 Fixed points per word **[P]**

`Fix(×λ_v | S) = ker(×(1−λ_v))`; since `2^K ∈ Λ^×`, this is `ker(×m_v) = (m_v^{-1}Λ)/Λ ≅ Λ/m_vΛ ≅ Z/N_v`, `N_v :=` prime-to-6 part of `|m_v|` (for `L ≥ 1`, `m_v` is odd and prime to 3, so `N_v = |m_v| = |2^K − 3^L|`; for the all-even word, `N = (2^K−1)/3^{v_3(2^K−1)}`). Equivalently `#Fix = Π_{w∈{∞,2,3}}|1−λ_v|_w` — CEW Lemma 5.1/5.2 **[L]**, or directly the Artin–Whaples product formula: `Π_{all w}|1−λ_v|_w = 1`, so the S-places count = inverse of the outside-places content = prime-to-6 part of the numerator. All fixed points are images of rationals `μ/m_v` (μ ∈ Λ).

### 2.2 The arithmetic class **[P]**

Upstairs in `Z_2`, each word v has a *unique* T-periodic point with itinerary v: the rational `n_v = W(v)/m_v` (the affine fixed-point equation `g̃_v(x) = x` solved in `Z_2`, `m_v` odd hence a 2-adic unit; this is the Böhm–Sontacchi cycle equation `n(2^K − 3^L) = W(v)` **[L]**). Its image in S is the torsion point of class `[W(v)] ∈ Λ/m_vΛ`. Hence:

- **Integrality.** `n_v ∈ Z ⟺ m_v | W(v) in Z ⟺ [W(v)] = 0 ⟺` the arithmetic orbit passes through `0 ∈ S`. Note the divisibility is a condition at the **moving places** `p | 2^K − 3^L` — always coprime to 6, hence *invisible to the three fixed places of S*. The window `Z_2 × Z_3` cannot detect integrality of `n_v` (all `n_v` already lie in `Z_2 ∩ Z_3`); only the position relative to the deck lattice Λ does.
- **Positivity.** For `L ≥ 1`, `W(v) > 0`, so `n_v > 0 ⟺ m_v > 0 ⟺ 2^K > 3^L ⟺ λ_v < 1`: positive cycles inhabit the **leafwise-contracting** sector, negative cycles the expanding one. The three negative cycles are not anomalies to explain away; they are the expanding-sector integral classes, and the formalism *must* (and does) produce them.
- **Unit vs. sporadic.** `|2^K−3^L| = 1` forces integrality outright (trivially zero class group `Z/1`): complete solution list `(1,0), (2,1), (1,1), (3,2)` — i.e. cycles 0, 1, −1, −5 **[P/L** via Mihailescu for the general statement; these small cases elementary**]**. The −17 cycle `(K,L) = (11,7)`, word `11110111000`, `139 | 2363 = 17·139`, is the unique known non-unit integral necklace. (Machine-verified; also an exhaustive K ≤ 16 word sweep finds exactly the five orbits' members and nothing else.)
- **Known exclusions [L].** Hercher 2023 (+ Barina's 2^71 verification): no nontrivial positive m-cycle with m ≤ 91; any nontrivial positive cycle has > 1.375×10^11 odd terms and ≥ 2.2×10^11 T-steps. Mechanism: continued fractions of `log_2 3` + Baker–Rhin linear forms in logarithms, i.e. *archimedean lower bounds on `|2^K − 3^L|`* — in our language: lower bounds on the leafwise holonomy defect `|1 − λ_v|_∞`, the archimedean local factor of the trace formula. The completeness of {−1, −5, −17} on the negative side is **open [C]** (same genre).

**Summary picture:** the solenoid Lefschetz theory counts, for each necklace, the full class group `Z/N_v` of "pseudo-cycles" (cycles of Collatz-with-Λ-fuzz: `g_v(x) = x + λ`, λ ∈ Λ); the honest rational cycle is one distinguished class; integer cycles are the class-0 stratum; positivity is the leafwise contraction sign. Grothendieck-style: *the correspondence has a canonical cycle class in every fiber; Collatz asks when it hits the identity section, and Baker theory is the current archimedean handle on that question.*

---

## 3. Literature: the exact trace formulas (task 1)

All sources saved to `/Users/simon/Desktop/COLLATZ/papers/`.

### 3.1 Deninger's program **[L]**

`deninger-2005-arithmetic-foliated-aws.pdf` (Arizona Winter School lectures, 2005; the canonical technical survey — also arXiv:math/0505354). Key items, quoted:

- **Explicit formula** (his (4)–(6)): for `Φ(s) = ∫ φ(t)e^{ts}dt`, φ ∈ D(R):
  `Φ(0) − Σ_ρ Φ(ρ) + Φ(1) = −log|d_{K/Q}|φ(0) + Σ_{p∤∞} log Np (Σ_{k≥1} φ(k log Np) + Σ_{k≤−1} Np^k φ(k log Np)) + Σ_{p|∞} W_p(φ)`
  — the target shape: `H^0` contributes 1, `H^1` the zeros `e^{tρ}`, `H^2` the pole `e^t`; primes = closed orbits of lengths `log Np`; archimedean places = fixed points.
- **Conjecture 5.1** (dynamical Lefschetz trace formula; his (22)): X compact manifold, `F` codim-1 foliation, `F`-compatible flow φ with non-degenerate fixed points and closed orbits; then there should be a natural `D'(R^{>0})`-valued trace on reduced leafwise cohomology `H̄^•(X, R)` with
  `Σ_n (−1)^n Tr(φ*|H̄^n) = Σ_γ ℓ(γ) Σ_{k≥1} ε_γ(k) δ_{kℓ(γ)} + Σ_x ε_x |1 − e^{κ_x t}|^{-1}`,
  `ε_γ(k) = sgn det(1 − T_xφ^{kℓ(γ)} | T_xX/RY_φ)`, `ε_x = sgn det(1 − T_xφ^t | T_xF)`. Open in general, "not known (except dim X = 1) if φ has fixed points."
- **Theorem 5.3 = Álvarez López–Kordyukov** (his (23)): X compact **oriented manifold**, codim-1 foliation, flow **everywhere transverse** to F (forcing F Riemannian), bundle-like metric, all orbits non-degenerate. Then `A_φ = ∫φ(t)φ^{t*}dt` is trace class on the Hilbert completions `Ĥ^n` and, in `D'(R)`:
  `Σ_n (−1)^n Tr(φ*|H̄^n) = χ_Co(F,μ)·δ_0 + Σ_γ ℓ(γ) Σ_{k∈Z∖0} ε_γ(k) δ_{kℓ(γ)}`
  (χ_Co = Connes' Euler characteristic w.r.t. the transverse measure from the trace). The underlying leafwise Hodge theorem (`Ker Δ_F ≅ H̄^n`, a deep result since Δ_F is only leafwise elliptic) is **Álvarez López–Kordyukov, Compositio 125 (2001)**; the Lefschetz-distribution version for Lie foliations is [arXiv:math/0703753](https://arxiv.org/abs/math/0703753) (`alvarezlopez-kordyukov-2007-lefschetz-lie-foliations.pdf`): Lie foliation with structural Lie group G, transverse G-action, Lefschetz distribution on G via leafwise Hodge theory, distributional Gauss–Bonnet + local Lefschetz formula. State of the art for **fixed points**: the 2025 Springer book *A Trace Formula for Foliated Flows* (Álvarez López–Kordyukov–Leichtnam, [link](https://link.springer.com/book/9783032154125)): codim-1 foliations on closed manifolds, "transversely simple" preserved leaves — still manifolds, still not correspondences.
- **Counterexample warning:** Deninger–Singhof, Ann. Inst. Fourier 51 (2001) 209–219 (`deninger-singhof-2001-counterexample-hodge.pdf`): for **non-Riemannian** foliations, smooth leafwise Hodge decomposition *fails* and with it the naive trace formulas. This is the direct ancestor of our §4 defect.
- **Working Hypotheses 7.5** (laminated/solenoid version; his (32), on `D'(R^*)`): same shape with `k ≤ −1` coefficients `ε_γ(|k|)det(−T_xφ^{kℓ(γ)}|T_xF)` and fixed-point distributions `W_x`; for solenoids `TX := TL` — tangent along leaves only (his 7.1), so all determinants are **leafwise**; the totally disconnected transversal contributes nothing in his normalization. *This is precisely what our example corrects* (§4–5).
- **Theorem 7.8** (proved case): suspensions `X = M̄ ×_Λ R`, `M̄ = lim←(M, f)` of an unramified self-covering f of a **compact manifold** M, all orbits non-degenerate: formula holds in `D'(R)` with `χ_Co(F,μ)δ_0 = χ(M)·l·δ_0`; closed orbits ↔ finite f-orbits on M. (For f = ×p on R/Z this is the p-adic solenoid; the elliptic-curve example in §7.7/`deninger-2001-explicit-formulas-simple-example.pdf` (arXiv:math/0204194) realizes the explicit formula of `ζ_E(s)` for ordinary E/F_p on `(C ×_Γ T_πΓ) ×_Λ R` — with the conformal factor `e^t`, α = 1, possible *only* on solenoids, not manifolds.)
- **Deninger, Dynamical systems for arithmetic schemes**, arXiv:1807.10380 (`deninger-2018-dynamical-systems-arithmetic-schemes.pdf`): constructs actual (infinite-dimensional) dynamical systems for Spec Z with periodic orbits ↔ primes; the finite-dimensional realization remains open. Recent related: Kim, [arXiv:1912.02159](https://arxiv.org/abs/1912.02159) (leafwise cohomological zeta expression on 3-dim Riemannian foliated systems); Morishita, [arXiv:2508.15971](https://arxiv.org/abs/2508.15971) (Deninger systems ↔ Connes–Consani adelic spaces, 2025 — the analogy S ↔ adele class space is active).

### 3.2 Leichtnam's p-adic laminations **[L]**

`leichtnam-2006-lefschetz-padic-transversal.pdf` = [arXiv:math/0603576](https://arxiv.org/abs/math/0603576), Bull. Sci. Math. 131 (2007): laminated spaces locally (complex disk) × Z_p, **Riemannian lamination** with scaling-group flow; proves a Lefschetz trace formula for the flow on leafwise Hodge cohomology matching the explicit formula of `ζ_Y(s)` for curves Y/F_q, with `Re(spec Θ|H^1) = 1/2`. Closest existing theorem-class to our object; hypotheses still include the Riemannian/isometric transverse structure that X_C violates.

### 3.3 S-integer dynamics **[L]**

Chothi–Everest–Ward, *S-integer dynamical systems: periodic points*, Crelle 489 (1997) (`chothi-everest-ward-1997-sinteger-periodic-points.pdf`, [UEA copy](https://ueaeprints.uea.ac.uk/id/eprint/18601/1/sintdynsys.pdf)): duality-defined systems `(X^{(k,S)}, α_ξ)`; **Lemma 5.2**: `|F_n(α)| = Π_{ν∈S∪P_∞} |ξ^n − 1|_ν`; **Example 8.1**: ξ = 3/2, S = {2,3}: `3^n − 2^n` periodic points; zeta functions "in general irrational" for S finite — the analytic wildness expected of our unsigned zeta (cf. also Everest–Stangoe–Ward on natural boundaries). Our §2.1 is CEW applied to the word-indexed family `ξ = 3^L/2^K`.

### 3.4 Correspondence-Lefschetz **[L]**

The étale-world results for correspondences: Lefschetz–Verdier (SGA 5), and **Deligne's conjecture** — after twisting a correspondence by a high power of Frobenius (making it *contracting* near fixed points) the local terms become naive multiplicities: proved by Pink (1992, special cases), **Fujiwara** (Invent. Math. 127 (1997)), **Varshavsky** ([arXiv:math/0505564](https://arxiv.org/abs/math/0505564), "Lefschetz–Verdier trace formula and a conjecture of Deligne"). (The mandate's "Migliorini/..." pointer resolves to this family; no Migliorini result on correspondence trace formulas applies here.) **No laminated/foliated analogue of any of these exists.** Note the suggestive match: "twist until contracting" ↔ compose with extra halving steps; the contracting regime `λ_v < 1` is *exactly the positive-cycle sector* — Fujiwara-style local-term control would be available precisely where the Collatz cycle conjecture lives **[S]**.

---

## 4. The candidate Lefschetz identity for X_C (task 2)

### 4.1 Leafwise cohomology **[P]** (Fourier; standard technique, stated for our lamination)

Along the S-leaf foliation F of X_C, decompose functions over `Ŝ = Z[1/6]`: `d_F` acts on the χ_λ-sector by `2πiλ_∞`. Nonzero sectors have dense image (`|λ|_∞` accumulates at 0, so the image is not closed — reduced cohomology kills them); the λ = 0 sector survives with free dependence on the symbolic and flow coordinates:
`H̄^0_F(X_C) ≅ C(Y)`, `H̄^1_F(X_C) ≅ C(Y)·[ds]`, where `Y := Ω̂ ×_Z R` is the suspension of the 2-shift.
The flow acts on the `H̄^0` sector by the Koopman operator of the suspension flow of σ, and on `H̄^1` by the same twisted by the leafwise-derivative cocycle (`λ_v` over a K-step return through word v). Both spaces are infinite-dimensional with continuous Koopman spectrum: **no trace-class trace exists** (AK's Hilbert-space mechanism is unavailable); the natural regularization is the flat/transfer-operator trace, under which the K-step traces are `Σ_v 1 = 2^K` on `H̄^0` and `Σ_v λ_v = 2^K` on `H̄^1`. **[P** for the identities; the *choice* of flat trace as "the" natural D'-trace is exactly the unresolved definitional freedom Deninger flags — tag **[PL]** for the identification.**]**

### 4.2 The identity, both normalizations

Written as distributions on `R^{>0}` (unit orbit length per symbol; primitive-orbit bookkeeping standard):

**(a) Cohomological / Atiyah–Bott normalization [P]:**
`Σ_{n=0}^{1} (−1)^n Tr^♭(φ*|H̄^n_F(X_C)) = Σ_K [ Σ_{v∈{0,1}^K} (1 − λ_v) ] δ_K = Σ_K [2^K − 2^K] δ_K = 0`,
and per word this equals the honest fixed-point sum with adelic determinants: `Σ_{x∈Fix(g_v)} (1−λ_v)/Π_{w∈{∞,2,3}}|1−λ_v|_w = (1−λ_v)` (product formula). **Both sides vanish identically. The Collatz solenoid zeta is ≡ 1.**

**(b) Deninger-7.5 normalization (±1 per orbit) [P]:**
RHS coefficient at K = `Σ_v sign(1−λ_v)·#Fix(g_v|S) = Σ_v sign(m_v)N_v = −((2^K−1) − (2^K−1)_{3'})` — zero iff K odd; the even-K defect is the 3-part of `2^K−1`, supported on the all-even necklace, with Iwasawa-type growth `v_3(2^K−1) = 1 + v_3(K)`. **So (32) as stated fails for X_C**; the failure mode is exactly Deninger–Singhof's (non-Riemannian transverse structure), here computed in closed form: the transverse holonomy of the orbit (v) acts on `Q_2 × Q_3` by ×λ_v with modules `|λ_v|_2 = 2^K ≠ 1` (never isometric) and `|1−λ_v|_3 < 1` exactly on all-even words at even K (where `3 | 2^K−1`, a *transversal 3-adic tangency* of the holonomy to the identity).

**(c) Corrected identity [P for X_C; proposed generally]:** with orbit local terms
`ε_γ(k) · |det(1 − hol_γ^k)|_2^{-1} · |det(1 − hol_γ^k)|_3^{-1}` per fixed point (equivalently: Guillemin's `1/|det(1−P_γ)|` with the determinant-module taken over leaf ⊕ p-adic transversal),
LHS(a) = RHS for all K, reducing to Deninger's coefficients whenever the transverse holonomy is isometric (all proved cases: 7.8 suspensions, AK, Leichtnam). The uniform 2-adic factor `2^{-K}` is a global Tate-type twist (`u ↦ u/2` in the zeta variable); the 3-adic factor is the interesting, orbit-dependent one.

### 4.3 What each side computes in Collatz terms

- `Tr on H̄^0 = 2^K`: the count of admissible parity words — the full-shift/entropy-log-2 level; in arithmetic terms, the size of the candidate cycle combinatorics (Terras: all words admissible).
- `Tr on H̄^1 = Σ_v 3^L/2^K = 2^K`: the same words weighted by leafwise expansion — the 3-adic mass of the backward tree (Applegate–Lagarias / Wirsching-flavored weighting; `Σ_L C(K,L)3^L = 4^K` is the first-moment count).
- **Their equality = first-moment criticality** `E_Haar[T'] = 1` (the Collatz multiplicative walk is a martingale in n, not merely negatively drifted in log n), unique to q = 3 among qx+1. The trace formula is *balanced-by-construction*: cohomology cannot distinguish the two lines.
- RHS orbit terms: pseudo-cycle classes `Z/|2^K−3^L|` per necklace — the *full residue count of the cycle equation mod `2^K−3^L`*; the arithmetic stratum (integer cycles) is the class-0 slice; positivity is `ε_γ`. The trace formula sees `Σ_classes 1` but is blind to *which* class is arithmetic: **the Collatz content is strictly finer than any constant-coefficient trace identity on S.** The three-tier place structure: places {2,3} (branching/window), place ∞ (positivity/contraction), moving places `p | 2^K−3^L` (integrality) — the solenoid geometrizes the first two tiers; the third has no fixed-place home, which is the structural discovery/obstruction of this note.

---

## 5. Honest assessment: hypothesis audit (task 3)

| Hypothesis (source) | Status for X_C |
|---|---|
| Phase space compact manifold (Conj. 5.1, AK Thm 5.3, ALKL book) | **fails** — laminated with Cantor transversals; Deninger 7.5/Leichtnam allow this |
| Flow (one-parameter group), not correspondence | **repaired** — branching absorbed into the symbolic factor: F is a homeomorphism, φ an honest flow **[P]**; cost: H̄^0 becomes C(suspension of shift) with continuous spectrum |
| Riemannian foliation / bundle-like metric / leafwise Hodge (AK Compositio 2001; needed for trace-class LHS) | **fails** — transverse holonomy ×λ_v on Q_2×Q_3 is never isometric (`|λ_v|_2 = 2^K`); this is the Deninger–Singhof failure mode, and §4(b) computes its exact toll |
| Non-degenerate closed orbits (all sources) | holds (`λ_v ≠ 1`) |
| No fixed points of the flow (AK; 7.8) | holds for X_C; note Deninger *needs* fixed points for archimedean places — in our picture the archimedean datum appears instead as the contraction/expansion sign ε_γ, which is where positivity lives |
| Isometric/trivial transverse holonomy (implicit in 7.5's ±1 coefficients; true in 7.8, Leichtnam) | **fails**, and the corrected p-adic local factors of §4(c) are forced — the transferable lesson of this note |
| Conformal flow metric `e^{αt}`, α = 1 (Deninger's (31), RH mechanism) | **fails as stated** — the leafwise conformal factor is the *cocycle* `λ_v`, not `e^{αt}`; its logarithm per unit time ("weight of the orbit") spreads over `[−log 2, log(3/2)]` instead of being the constant 1. Collatz is "mixed-weight" where Spec Z is pure. Positive cycles = negative-weight orbits. **[P** computation, **S** gloss**]** |
| Correspondence-Lefschetz with controlled local terms (Fujiwara/Varshavsky) | **not available** — étale schemes only; no laminated analogue. Suggestive: their contraction-twist mechanism matches our positive-cycle sector exactly **[S]** |

**Bottom line.** Every proven trace formula in this literature has hypotheses that X_C violates in an essential (not technical) way, *and* the violation is quantifiable: the constant-coefficient theory balances to zero (Theorem A), the ±1-normalized theory has a computable 3-adic anomaly (Theorem B), and the corrected formula (Prop. C) is consistent but *hollow* — it counts pseudo-cycles perfectly and integer cycles not at all. The Deninger pipeline, run honestly on Collatz, terminates in a precise statement of *where new structure is required*: coefficients at the moving places.

---

## 6. Relation to the ×3/2 flow and the rest of the program

- The `×(3/2)` suspension is the all-odd-word subsystem; its CEW zeta `(1−2u)/(1−3u)` is rational with "Frobenius eigenvalues" 2 and 3 — a genuine (and known) Weil-like toy. The full Collatz object mixes the multipliers 1/2 and 3/2 word-by-word; its *signed* zeta collapses to 1 (Theorem A). A successor audit gives an independently reviewed handwritten argument that the corresponding unsigned zeta is non-rational but **does not** have a natural boundary on its first circle: it factors as `(1−4u)^{-2}` times a holomorphic nonzero residual on a larger disk. The finite identities have an exact checker; the universal analytic argument awaits formalization. See `solenoid-zeta.md §6`.
- `|2^K − 3^L|`-weighted counts are exactly the quantities Baker/Rhin/Hercher bound from below along `L/K ≈ log_2 3` convergents **[L]** — the archimedean local data of our trace formula is the *same* quantity the cycle-exclusion literature squeezes; Hercher's theorem is, in this dictionary, an effective archimedean-place statement about closed orbits near the critical slope.
- Siegel's numen `χ: Z_2 → Z_3` (papers/siegel-2024-pq-adic-collatz.pdf) is the a.e.-defined arithmetic section of the fibration `X_C → Y` (the S-coordinate of the natural extension; the backward 3-adic contraction rate `3^{−#odd}` is `|λ|_3` of the holonomy) — the crack-file unification, now with the holonomy-module language making it precise **[PL]**.
- The weak-model-set exclusion lemma (crack #6 first move) is complementary: it excludes positive-density *divergence certificates* via windows; this note concerns *cycles* via classes. Same solenoid, orthogonal payloads.

---

## 7. The dream, precisely (and its current price)

**(D1) Arithmetic form [C — equivalent to the Collatz cycle conjecture, positive side].**
For every primitive necklace `v ∉ {0, 10}` with `2^K > 3^L`: `W(v) ≢ 0 (mod 2^K − 3^L)`.
Equivalently: *the only leafwise-contracting closed orbits of φ on X_C whose arithmetic class vanishes are the 0-orbit and the trivial orbit.* (Negative-side analogue: in the expanding sector, only `1`, `110`, `11110111000`.) Known: true for the Hercher range **[L]**.

**(D2) Cohomological form [S — formalism does not exist].**
Sought: a cohomology of the pair (S, C) with coefficients in the isogeny tower `{S →^{×m} S}` (equivalently étale-like `Z/m`-local systems, m running over the *moving* moduli `m_v`), on which the correspondence acts so that (i) the trace localizes fixed points **by torsion class** (a Reidemeister/Nielsen-type refinement: the class-group `Λ/m_vΛ` is exactly the Nielsen datum of `g_v` on S), and (ii) an archimedean positivity — Deninger's Hodge-star conformality `Θ = ½ + skew` (his (11)), which on X_C must be replaced by a *cocycle-weighted* positivity because the weight is mixed — forces the vanishing of the class-0 multiplicity in the contracting sector away from the unit necklaces.
**Requirements any such theory must meet (computed in this note):**
1. reproduce Theorem A's global cancellation (the theory must be an *extension* of, not a replacement for, constant coefficients);
2. carry the 3-adic anomaly of Theorem B as a boundary/χ_Co-type term at the 0-orbit (the `v_3(2^K−1) = 1 + v_3(K)` growth is Iwasawa-shaped: the 0-orbit carries a nontrivial 3-adic L-invariant **[S]**);
3. beat Baker quantitatively: any positivity strong enough for (D1) must dominate `|2^K−3^L| > 2^K·K^{−13.3}`-type bounds in the convergent range — nothing in the Deninger formalism currently *produces* Diophantine inequalities (the analogy has always run explicit-formula ↔ trace-formula as consistency, not as engine). This is the honest wall, and it is the same wall as ever, relocated — but now *located*: the missing object is finite-place equidistribution of `W(v) mod (2^K−3^L)` as v ranges over a necklace class, i.e. a weight/monodromy theory at the moving places.

**Odds assessment.** (D2) as stated: no current technology; I estimate the probability that a constant-coefficient-style trace formula ever decides (D1) at ~0 (Theorem A is a *proof of hollowness*, which is itself the useful rigidity statement). The moving-coefficient refinement is mathematically well-posed (Nielsen classes, isogeny towers, twisted Burnside/Reidemeister traces are all standard objects) and unexplored in this configuration — that is where the next real theorem lives (§8), even though the full dream would additionally need the positivity engine that nobody has.

---

## 8. Concrete next steps (ranked, with provability estimates)

1. **Write up Theorems A/B/Prop C** (§4) as a standalone result: "A dynamical Lefschetz trace formula on the (2,3)-adic solenoid: exact validity and exact failure of Deninger's working hypotheses, with p-adic holonomy corrections." All computations complete in this note; only exposition remains. Also a clean test-case contribution to the foliated-trace-formula literature independent of Collatz. (~90% a paper-grade note in weeks.)
2. **Moving-coefficient pilot:** compute the correspondence action on `H^•(S, Z/m)` (= functions on `ker(×m) ≅ Z/m` with C permuting classes) for m = 5, 7, 139: the class-refined counting matrix is the induced action of {×½, ×3/2, +translation data on classes} on `Z/m` — a finite computation; determine whether the arithmetic class `[W(v)]` admits a transfer-operator expression (i.e., whether the class-0 stratum is cut out by a finite-dimensional twist). This is the precise finite test of (D2)(i). (~Weeks; outcome either a genuine refinement or a proved no-go — both valuable.)
3. **Reidemeister/Nielsen literature pass:** twisted Burnside–Frobenius for solenoid automorphisms (Fel'shtyn school) — the Nielsen classes of `g_v` on S are exactly `Λ/m_vΛ`; check whether any twisted-zeta rationality statement survives word-mixing. (~Days to scope.)
4. **Residual unsigned-zeta singularities after removing the leading pole.** The audited handwritten argument says the former proposed boundary on the first circle is false: `ζ_S=(1−4u)^{-2}exp(G(u))`, with `G` analytic past `|u|=1/4` and a positive-real singularity at radius `1/(2exp(h(log_3 2)))≈0.258824`. Formal verification is pending. Whether the full larger circle is a natural boundary is open and currently has no cycle-arithmetic bridge. (`solenoid-zeta.md §6`.)
5. **Negative-time side + fixed-point W_x terms** of the corrected formula (32) on X_C **[PL]** — routine but should be pinned before (1) is submitted.
6. Cross-feed to crack #6: the corrected p-adic local factors suggest the right weighting for window-certificate obstructions; keep the two threads in one Lean-able framework ("certificate = post-fixpoint" file).

---

## References (all verified 2026-07-20; local copies in `/Users/simon/Desktop/COLLATZ/papers/`)

- C. Deninger, *Arithmetic geometry and analysis on foliated spaces*, AWS lectures 2005, [PDF](https://swc-math.github.io/dls/DLSDeninger.pdf) · local: `deninger-2005-arithmetic-foliated-aws.pdf`. (Conjecture 5.1/(22); Thm 5.3/(23); 7.5/(32); Thm 7.8; explicit formulas (4)–(6).)
- C. Deninger, *On the nature of the "explicit formulas" in analytic number theory — a simple example*, [arXiv:math/0204194](https://arxiv.org/abs/math/0204194) · local: `deninger-2001-explicit-formulas-simple-example.pdf`.
- C. Deninger, *Dynamical systems for arithmetic schemes*, [arXiv:1807.10380](https://arxiv.org/abs/1807.10380) · local: `deninger-2018-dynamical-systems-arithmetic-schemes.pdf`.
- C. Deninger, W. Singhof, *A counterexample to smooth leafwise Hodge decomposition… and to a type of dynamical trace formulas*, Ann. Inst. Fourier 51 (2001), [numdam](http://www.numdam.org/item/AIF_2001__51_1_209_0/) · local: `deninger-singhof-2001-counterexample-hodge.pdf`.
- J. Álvarez López, Y. Kordyukov, *Long time behavior of leafwise heat flow for Riemannian foliations*, Compositio 125 (2001) (leafwise Hodge); *Lefschetz distribution of Lie foliations*, [arXiv:math/0703753](https://arxiv.org/abs/math/0703753) · local: `alvarezlopez-kordyukov-2007-lefschetz-lie-foliations.pdf`.
- J. Álvarez López, Y. Kordyukov, E. Leichtnam, *A Trace Formula for Foliated Flows*, Springer 2025, [link](https://link.springer.com/book/9783032154125).
- E. Leichtnam, *Scaling group flow and Lefschetz trace formula for laminated spaces with p-adic transversal*, [arXiv:math/0603576](https://arxiv.org/abs/math/0603576) · local: `leichtnam-2006-lefschetz-padic-transversal.pdf`.
- V. Chothi, G. Everest, T. Ward, *S-integer dynamical systems: periodic points*, Crelle 489 (1997), [PDF](https://ueaeprints.uea.ac.uk/id/eprint/18601/1/sintdynsys.pdf) · local: `chothi-everest-ward-1997-sinteger-periodic-points.pdf`. (Lemma 5.2; Example 8.1.)
- J. Kim, *Leafwise cohomological expression of dynamical zeta functions on foliated dynamical systems*, [arXiv:1912.02159](https://arxiv.org/abs/1912.02159) · local: `kim-2019-leafwise-zeta-rfds.pdf`.
- M. Morishita, *On a relation between Deninger's foliated dynamical systems and Connes–Consani's adelic spaces*, [arXiv:2508.15971](https://arxiv.org/abs/2508.15971).
- Y. Varshavsky, *Lefschetz–Verdier trace formula and a conjecture of Deligne*, [arXiv:math/0505564](https://arxiv.org/abs/math/0505564); K. Fujiwara, Invent. Math. 127 (1997).
- M. C. Siegel, *(p,q)-adic analysis and the Collatz conjecture*, [arXiv:2412.02902](https://arxiv.org/abs/2412.02902) · local: `siegel-2024-pq-adic-collatz.pdf`.
- C. Hercher, [arXiv:2201.00406](https://arxiv.org/abs/2201.00406) (m ≤ 91; cycle-length bounds); Lagarias 1985/1990 and Bernstein–Lagarias 1996 as in LANDSCAPE.md.
- Numerical verifications: `/private/tmp/claude-503/-Users-simon-Desktop-COLLATZ/9f856e7c-a0ad-44ae-bdf4-ecc5f1403748/scratchpad/check.py` (identities K ≤ 10; five-orbit table; K ≤ 16 integral-necklace sweep).

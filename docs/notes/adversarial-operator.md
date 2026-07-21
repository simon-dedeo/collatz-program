# Adversarial transfer operators over the 3-adic odometer: theory hunt, the equicontinuity criterion, and the shape of the defect

2026-07-20. Status: **theory-hunt report + proofs + one structural surprise**.
Companion to `docs/notes/kl-limit-object.md` (cited below as [LIM]; its numbering
Lemma 1.1–Corollary 3.4 is reused). Object under study: the operator family

  (F_λ^{(k)} c)^m = λ^{−2} c^{4m} + 1_{m≡2(9)} λ^{α−2} min_j c^{r₂(m)+j·3^{k−1}}
                                + 1_{m≡8(9)} λ^{α−1} min_j c^{r₈(m)+j·3^{k−1}}

on Y_k = (2+3ℤ₃)/3^kℤ₃, α = log₂3, with thresholds λ_k ↑ λ∞ ∈ (1.8703, 2]
(k = 18 certified, `experiments/kl/RESULT.md`), and the dichotomy λ∞ = 2 vs λ∞ < 2
([LIM] Problem 3.5).

**Ledger.**
*Proved here*: Lemma 1.1 (the base isometry is the 3-adic odometer; single-cycle
quotients), Lemma 1.2 (period-3 branch driving), Proposition 1.3 (normal forms:
topical/Shapley operator, Protasov product family, interval-MDP abstraction),
**Theorem 2.1 ((H_k) holds unconditionally whenever λ_k < 2** — via
Gaubert–Gunawardena; discharges the standing hypothesis of [LIM] §2–3 and KL's §6
conditions (1),(2)**)**, Theorem 3.1 (equicontinuity criterion hierarchy, exact
constants), Proposition 3.2 (uniform equicontinuity is *impossible* if C^max_k → ∞;
the sup-criteria are dead), Lemma 3.3 (oscillation-transport inequality; the factor-2
obstruction), Proposition 4.1 (the limit path space supports pressure ≥ α−1 > 0 at
λ = 2: **the adversary does not evaporate in the limit**).
*Provable-looking*: Prop 4.2 (limit points of optimal measures live on the path
space X); the entropy bookkeeping h(μ) = h(word marginal).
*Conjectural*: Conjecture 4.3 (defect identification: adversarial Mather measure with
Haar-singular marginal).
*Speculative*: the Barles–Souganidis reading of the dichotomy (§3.5), the
concentration numerics as evidence of a forming hierarchical exceptional set (§5).

---

## 1. What the object is, exactly (three proved normal forms)

### 1.1 The base dynamics is *the* 3-adic odometer

**Lemma 1.1.** Let Y = 2+3ℤ₃ and S(x) = 4x. Then:
(a) (Y, S) is topologically conjugate to the 3-adic odometer (ℤ₃, t ↦ t+1). In
particular S is minimal, uniquely ergodic (invariant measure = normalized Haar),
equicontinuous (an isometry), and has zero topological entropy.
(b) For every k ≥ 1 the induced map m ↦ 4m on [3^k] = {m mod 3^k : m ≡ 2 (3)} is a
single cycle of length 3^{k−1}.

*Proof.* (a) Y = 2·U₁ with U₁ = 1+3ℤ₃ (2·(1+3ℤ₃) = 2+6ℤ₃ = 2+3ℤ₃ since 2 is a
unit), and S(2u) = 2·(4u), so S is conjugate to multiplication by 4 on the group U₁.
U₁ is procyclic ≅ (ℤ₃, +), and 4 = 1+3 ∈ U₁ \ U₂ (U₂ = 1+9ℤ₃) is a topological
generator; the continuous isomorphism e: ℤ₃ → U₁, e(t) = 4^t (well defined since
|4^{3^n} − 1|₃ = 3^{−(n+1)} → 0) conjugates u ↦ 4u to t ↦ t+1. Explicitly
Φ(t) = 2·4^t satisfies Φ(t+1) = S(Φ(t)). The odometer's standard properties
(minimality, unique ergodicity, zero entropy) transfer; S is visibly a 3-adic
isometry. (b) By lifting-the-exponent, v₃(4^n − 1) = v₃(3) + v₃(n) = 1 + v₃(n), so
ord(4 mod 3^k) = 3^{k−1}; the orbit m·⟨4⟩ = 2u₀·U₁ = 2·U₁ = [3^k] mod 3^k has full
cardinality 3^{k−1}. ∎

So the task's framing is exact and not merely metaphorical: F_λ^{(k)} is a transfer
operator whose deterministic branch is the level-k section of an odometer — the
canonical zero-entropy, isometric, uniquely ergodic dynamics — while the two
expanding branches R₂, R₈ ([LIM] Lemma 1.1) each burn one 3-adic digit, and the min
is an adversary re-supplying that digit at the worst value.

**Lemma 1.2 (periodic driving).** Along the S-orbit the branch class is exactly
periodic with period 3: m ↦ 4m maps class 2 (mod 9) → 8 → 5 → 2 → ⋯ (4·2 = 8,
4·8 ≡ 5, 4·5 ≡ 2 mod 9). Hence every third odometer step carries the R₂ chord, every
third the R₈ chord, every third no chord; the "driving sequence" of the transfer
operator over the odometer is *periodic* (not Sturmian, not random). ∎

(Immediate but structurally important: the level-k policy digraphs are one
3^{k−1}-cycle — the odometer — decorated with chords in a rigid period-3 pattern;
all entropy in the system is injected by the chords.)

### 1.2 Normal forms

**Proposition 1.3.** Fix k ≥ 3 and λ ∈ [1,2]. Write n = 3^{k−1}, v = log₂ c,
β = log₂ λ.

(i) **Topical/Shapley form.** B(v) := log₂ F_λ^{(k)}(2^v) is order-preserving and
additively homogeneous (B(v + t·1) = B(v) + t·1), i.e. a *topical map* (in the sense
of Gunawardena–Keane; the class of Shapley/dynamic-programming operators of zero-sum
games). It is the minimum over finitely many policies σ of the risk-sensitive
(log-sum-exp) Bellman operators B^σ. λ_k is the parameter where the "escape rate"
lim_n max_m B^n(0)_m/n of this topical family crosses 0.

(ii) **Product-family form.** {A_λ^σ : σ} ([LIM] Prop 2.1) is a *product family* of
nonnegative matrices in Protasov's sense: row m has an independent finite row set
(3 choices for m ≡ 2, 8 mod 9; 1 choice for m ≡ 5). The quantity min_σ ρ(A_λ^σ) is
the minimal spectral radius over a product family — the object of the
Nesterov–Protasov spectral-optimization theory and Protasov's spectral simplex
method; [LIM] Prop 2.1(b) (policy collapse) is their attainment theorem in this
special case, and greedy policy iteration is exactly the spectral simplex method.

(iii) **Abstraction form.** F_λ^{(k)} is the *pessimistic (adversarial) abstraction*
of the level-∞ linear operator L_λ on C(Y) ([LIM] §1.4) induced by aggregating Y
into 3^{k−1} cells: the transition "R-image of the cell" is known only up to the
3 refinements, and an abstraction adversary resolves it — the exact scheme of
bounded-parameter/interval MDPs (Givan–Leach–Dean) and of game-based
abstraction-refinement (Kattenbelt–Kwiatkowska–Norman–Parker), in risk-sensitive
(multiplicative/Perron) rather than additive form. Refinement monotonicity λ_k ≤
λ_{k+1} ([LIM] Lemma 1.2) is the standard abstraction-refinement monotonicity.

*Proof.* (i) Monotonicity and additive homogeneity are direct computations
(log-sum-exp of shifted arguments shifts; min of topical is topical). (ii)–(iii) are
verbatim matchings of definitions; no content beyond [LIM] Prop 2.1 and Lemma 1.2. ∎

---

## 2. Theory hunt

Method: targeted web search (July 2026) across ergodic optimization, nonlinear
Perron–Frobenius/games, spectral optimization, robust control/verification,
low-temperature statistical mechanics, p-adic dynamics, weighted composition
operators. Key PDFs saved to `papers/` (filenames below). Negative results are
reported as "no direct hit found", not as proofs of absence.

### 2.1 What exists (nearest neighbors, by layer)

| layer of our object | literature home | what it gives us | where it stops |
|---|---|---|---|
| min-of-linear Perron eigenproblem, fixed k | nonlinear Perron–Frobenius: **Gaubert–Gunawardena** TAMS 356 (2004) [`papers/gaubert-gunawardena-2004-perron-homogeneous-monotone.pdf`]; Nussbaum; Akian–Gaubert–Nussbaum | **existence of positive eigenvectors — see Theorem 2.1 below**; Collatz–Wielandt; policy iteration | says nothing about the k → ∞ tower |
| ergodic eigenproblem of zero-sum games (Shapley operators) | **Akian–Gaubert–Hochart**, Ergodicity conditions for zero-sum games, arXiv:1405.4658 [saved]; Hochart hypergraph conditions arXiv:1510.05396; accretive-operator approach arXiv:1605.04520 | solvability/uniqueness theory of B(v) = χ+v; mean-payoff interpretation of β_k | finite state space; no refinement-tower asymptotics |
| min of Perron roots over row-independent choices | **Protasov / Nesterov–Protasov** spectral optimization of product families; spectral simplex; antinorms & lower spectral radius (Guglielmi–Protasov LAA 2020) | our policy collapse = their attainment; algorithms; certifies the finite-k object is *standard* | again no tower; their families are k-fixed |
| min/max growth of compositions of topical maps | **Bousch–Mairesse**, JAMS 15 (2002) 77–111 [`papers/bousch-mairesse-2002-tetris-finiteness.pdf`] | height optimization for topical IFS ≡ ergodic optimization on a compact measure space; **finiteness conjecture is false** — optimal switching need not be periodic | their IFS is over the full shift (free switching); ours is policy-constrained over a fixed odometer tower |
| ergodic optimization proper | **Jenkinson survey** ETDS 39 (2019), arXiv:1712.02307 [saved]; **Bousch, "Le poisson n'a pas d'arêtes"**, Ann. IHP 36 (2000) 489–508 [`papers/bousch-2000-le-poisson.pdf`]; Bousch "La condition de Walters" (2001); Contreras (Invent. Math. 205 (2016)); subaction regularity for circle expanding maps arXiv:2105.10767 | the *converse* template: maximizing measures, subactions, Mañé critical values; Sturmian solutions of E.O. over rotation-like constraints | all regularity theory for subactions **assumes expanding/hyperbolic dynamics**; nothing for isometric branches |
| E.O./Mather theory for matrix products | **Morris**, Mather sets for sequences of matrices, Proc. LMS 107 (2013), arXiv:1109.4615 [`papers/morris-2011-mather-sets-matrices-jsr.pdf`] | the defect object for extremal-growth matrix products is an invariant measure (Mather set) — the right template for §4 | maximal growth (JSR); our min side is the lower spectral radius, less developed |
| zero-temperature / fine-scale limits of Gibbs states | **Chazottes–Hochman** CMP 297 (2010), arXiv:0907.0081 [saved]; Coronel–Rivera-Letelier JSP 160 (2015); van Enter–Ruszel JSP 127 (2007); Baraviera–Leplaideur–Lopes minicourse, arXiv:1305.2396 [saved] | the *mechanism library* for non-convergence along a tower of scales: hierarchical alternation between competing configurations — exactly the shape a (B)-scenario would take | their parameter is temperature, ours is precision; no adversary |
| transfer/weighted-shift operators over *arbitrary* (incl. equicontinuous) base | **Antonevich–Bakhtin–Lebedev** t-entropy variational principle, ETDS 31 (2011); **Latushkin–Stepin**, Russ. Math. Surveys 46 (1991) | spectral radius of a weighted composition operator over any base = variational principle; over a uniquely ergodic isometry it degenerates to ∫log w dHaar — the "annealed" answer | linear, single-branch, no adversary; our sum-of-branches + min is outside |
| robust / interval MDPs, adversarial aggregation | Givan–Leach–Dean AIJ 122 (2000); Iyengar (2005); Nilim–El Ghaoui (2005); robust *average-reward* MDPs arXiv:2301.00858 (AAAI 2023); game-based abstraction Kattenbelt et al. FMSD 36 (2010) | our F is a pessimistic-abstraction Bellman operator; s-rectangularity = per-fiber independence; refinement monotonicity | all finite-state; convergence of refinements is studied to the value of a *finite* concrete model, never to a continuum limit; average-reward robust theory is itself recent and incomplete |
| risk-sensitive control | Whittle; Fleming–McEneaney; risk-sensitive MDP surveys | the log-sum-exp branch combination = risk-sensitive aggregation; "risk-sensitive for the counter, robust for the digit player" | no ultrametric/tower structure |
| base dynamics itself | Anashin; Anashin–Khrennikov (p-adic ergodic theory: 1-Lipschitz maps, ergodicity ⟺ single cycle mod p^k) | Lemma 1.1(b) is their single-cycle criterion in action; the odometer identification is standard there | no transfer-operator / thermodynamic layer exists in p-adic dynamics literature |

### 2.2 What does not exist (as far as this hunt reached)

No literature was found that treats any of:
**(i)** "minimax/robust/adversarial Ruelle or transfer operators" as such (searches
land either in robust MDPs or in game theory, never in thermodynamic formalism);
**(ii)** ergodic control / thermodynamic formalism on ultrametric state spaces *as
ultrametric* (the Cantor structure is always immediately recoded as a shift — which
destroys our specific tower-of-fibers adversary);
**(iii)** zero-temperature or fine-precision Gibbs theory *over odometers / group
rotations as the dynamics* (over rotations E.O. is trivial by unique ergodicity —
which is exactly why our object had to put the optimization in the adversary, not in
the measure);
**(iv)** the composite: a transfer operator whose deterministic branch is an
isometry, whose expanding branches descend a refinement tower, with worst-case
resolution of the lost digit, and the question of the profinite limit of its Perron
values. **Verdict: the object appears to be new as a composite; every layer
separately has a named home** (Prop 1.3), which fixes vocabulary and imports tools.

### 2.3 Is it "ergodic optimization over an odometer in disguise"?

Three-part answer, now precise:
- **At fixed k: no.** It is a mean-payoff / risk-sensitive zero-sum game (a
pressure min-max, [LIM] Prop 2.3), equivalently minimization of a Perron root over a
Protasov product family. E.O. would be the β → ∞ tropicalization, which we never
take (β_k ≤ 1).
- **Bousch's poisson is the right cousin, on the converse side.** In Bousch's
problem the dynamics is expanding (doubling) and the *solution* turns out to be
supported on rotation-like (Sturmian) sets. In ours the rotation (odometer) is
*installed in the operator from the start*, and the open question is whether the
adversarial value converges to the annealed one. The structural analogue of "the
maximizing measure is Sturmian" is Conjecture 4.3 below: "the defect measure is an
adversarial Mather measure over the odometer".
- **The genuinely missing theory** is a priori regularity of extremal
eigenvectors/subactions when the deterministic branch is an *isometry*. All known
subaction regularity (Bousch's Walters condition, Hölder subactions for expanding
maps, arXiv:2105.10767) uses expansion to contract oscillation backwards. Lemma 3.3
shows exactly where that fails here (a factor ~2 per level in the wrong direction).
This is the sharpest formulation of why the dichotomy is open.

### 2.4 One imported theorem with immediate payoff

**Theorem 2.1 ((H_k) is a theorem).** For every k ≥ 2 and every λ > 0, F_λ^{(k)} has
a strictly positive eigenvector; its eigenvalue is unique among positive
eigenvectors and equals the cone spectral radius ρ_k(λ). Consequently, whenever
λ_k < 2: the supremum λ_k is attained, ρ_k(λ_k) = 1, and F_{λ_k}^{(k)} has a
strictly positive eigenvector with eigenvalue exactly 1 — i.e. hypothesis (H_k) of
[LIM] §3.2 (= Krasikov–Lagarias §6 conditions (1)+(2) plus positivity) holds
unconditionally. All conclusions of [LIM] conditioned on (H_k) — policy collapse
equality (Prop 2.1(b)), the game value (Prop 2.3), the oscillation law (Theorem 3.2)
— are now unconditional (for λ_k < 2; if instead λ_k = 2 for some k, the dichotomy
is resolved as (A) outright).

*Proof.* F = F_λ^{(k)} maps the open cone into itself (the λ^{−2}c^{4m} term is
positive), is degree-1 homogeneous and monotone. Apply Gaubert–Gunawardena
[TAMS 356 (2004), Theorem 2]: if the digraph G(F) — edge (m, m′) iff
F_m(u_{\{m′\}}) → ∞ as u → ∞, where u_{\{m′\}} has coordinate u at m′ and 1
elsewhere — is strongly connected, then F has an eigenvector in the open cone.
Here F_m(u_{\{4m\}}) ≥ λ^{−2}u → ∞, so G(F) contains every edge m → 4m; by
Lemma 1.1(b) these edges alone form a single cycle through all of [3^k], hence G(F)
is strongly connected. (The min-terms contribute no edges — min(u, 1, 1) stays
bounded — but none are needed.) Uniqueness of the eigenvalue and its Collatz–Wielandt
characterization is [GG04, Prop 1]. Attainment and ρ_k(λ_k) = 1 then follow from
[LIM] Lemma 2.2 exactly as written (its hypothesis "F_{λ_k} has a strictly positive
eigenvector" is now supplied); rescaling the eigenvector to min = 1 exhibits a
feasible point at λ = λ_k. ∎

Remarks. (1) This discharges the item KL called "may be difficult to prove"
(their §6, on conditions (1),(2)) in the form needed for the limit analysis; what it
does *not* give is uniqueness of the eigenvector (GG04's example (6) shows
non-uniqueness can happen for topical maps; irrelevant to the oscillation law, which
holds at any positive unit-eigenvector). (2) The proof is stable under any
modification of the chord structure: only the odometer cycle is used. This is a
small, reusable principle: **transfer operators over odometer sections always have
positive Perron eigenvectors, whatever adversarial decoration is added**, because
the equicontinuous branch already supplies strong connectivity.

---

## 3. The equicontinuity criterion (proof section)

Setting: c_k > 0 the extremal eigenvector at λ_k (< 2), F_{λ_k}(c_k) = c_k
(Theorem 2.1), lifted to a locally constant function on Y; v_k := log₂ c_k. For a
level-(k−1) point r, the fiber is {r + j·3^{k−1}}, of 3-adic diameter 3^{−(k−1)}.
Define

- D_r := (fiber average of c_k) − (fiber min of c_k) ≥ 0,
- **mean oscillation** δ_k := Σ_r D_r / Σ_m c_k^m,
- **sup oscillation** ε_k := max_r (1 − fiber-min/fiber-max),
- **spread** C^max_k := max c_k / min c_k.

Recall the **oscillation law** ([LIM] Theorem 3.2, now unconditional by Theorem 2.1):
s(λ_k) − 1 = (λ_k^{α−2} + λ_k^{α−1})·δ_k exactly, where
s(λ) = λ^{−2} + (λ^{α−2}+λ^{α−1})/3, s(2) = 1. The identity is the "coupling of the
adversarial min to the average": summing the eigen-equation over Y_k, the min terms
equal the average terms minus D_r, the average terms produce s(λ_k) by exact
counting, and the defect is the oscillation.

**Theorem 3.1 (criterion hierarchy — what decay suffices).** With the above:

(E1 ⟹ E2) If the family {v_k} admits *any* common modulus of continuity ω on Y
(ω(0+) = 0, no rate required), then ε_k ≤ 1 − 2^{−ω(3^{−(k−1)})} → 0.

(E2 ⟹ E3) If ε_k → 0 (no rate, no summability required), then
δ_k ≤ ε_k/(3(1−ε_k)) → 0.

(E3 ⟺ conclusion) δ_k → 0 ⟺ λ_k → 2, with the exact two-sided rate
  ((2−α)/6)·(2−λ_k) ≤ δ_k ≤ 0.34927·(2−λ_k),
i.e. 2.8631·δ_k ≤ 2−λ_k ≤ 14.458·δ_k. In particular **no decay rate of any
oscillation quantity is needed anywhere: plain o(1) suffices at every rung, and at
the mean rung the criterion is not merely sufficient but equivalent, with δ_k forced
to decay at exactly the rate (2−λ_k).**

*Proof.* (E1 ⟹ E2): fiber points are at distance 3^{−(k−1)}, so the oscillation of
v_k on a fiber is ≤ ω(3^{−(k−1)}); hence fiber-min/fiber-max = 2^{−osc(v_k)} ≥
2^{−ω(3^{−(k−1)})}. (E2 ⟹ E3): in each fiber, avg − min ≤ max − min ≤ ε_k·max ≤
(ε_k/(1−ε_k))·avg; sum over fibers (fiber averages sum to (1/3)Σc). (E3): the
oscillation law plus s strictly decreasing with s(2) = 1 and the elementary bounds
|s′(2)| = 3(2−α)/8, |s′(λ₂)| = 0.72495, 2.0756 ≤ w₂+w₈ ≤ 9/4 on [λ₂, 2]
([LIM] Theorem 3.2(ii)(iii), proof unchanged). ∎

**Proposition 3.2 (the sup-criteria are provably not the mechanism).** If
C^max_k → ∞ (observed: 98.4, 147, 224, 339, 516, 793, 1207, 1835 at k = 11…18,
stable growth factor ≈ 1.52 per level), then no common modulus of continuity for
{v_k} exists: (E1) is *false* for the actual eigenvectors regardless of the truth of
the dichotomy.

*Proof.* Y has 3-adic diameter 1/3, so a common modulus ω would force
sup v_k − inf v_k = log₂ C^max_k ≤ ω(1/3) < ∞ uniformly in k. ∎

Moreover the new data (§5) show ε_k does not decay either — it *rises* slowly
(0.4566 → 0.4703 for k = 14 → 18). So among the rungs of Theorem 3.1 the only one
that can carry a proof of (A) is the mean rung (E3) — and (E3) is *equivalent* to
the conclusion, so it has no independent leverage. **The exact missing lemma is an
a priori mean-oscillation bound**: some structural estimate δ_k ≤ o(1) derived from
the operator (not from λ_k itself). Candidate routes, all currently blocked:
transportation/coupling estimates for the optimal policy chain (blocked by the
isometric branch: no Doeblin condition at fiber scale); symmetrization over fibers
(blocked: fiber-averaging is exactly the pushforward direction that provably fails,
[LIM] §1.3); backward-contraction of oscillation (blocked quantitatively by
Lemma 3.3).

**Lemma 3.3 (oscillation transport; the factor-2 obstruction).** For k ≥ 3 let
O_k(m̄) := fiber-max − fiber-min of c_k over the fiber of m̄ ∈ Y_{k−1}, and let
Ō_{k−1}(t) denote the oscillation of the fiber-min vector c̄ (level k−1) over the
fiber of t ∈ Y_{k−2}. Then, S denoting the induced odometer on Y_{k−1}:

  O_k(m̄) ≤ λ^{−2} O_k(S m̄) + w(m̄) Ō_{k−1}(π r(m̄)),

where w(m̄) ∈ {0, λ^{α−2}, λ^{α−1}} by branch class, and consequently
sup O_k ≤ (w₈/(1−λ^{−2}))·sup Ō_{k−1}, with w₈/(1−λ^{−2}) → 2 as λ → 2.

*Proof.* Since k ≥ 3, all lifts of m̄ share m̄'s branch class. Subtract the
eigen-equations of two lifts m, m′: the S-terms differ by λ^{−2}(c^{4m} − c^{4m′}),
and ×4 maps the fiber of m̄ bijectively onto the fiber of Sm̄ (4(m + j3^{k−1}) =
4m + (4j mod 3)·3^{k−1}); the chord terms are fiber-mins at r(m), r(m′), which lie
in the same level-(k−2) class but different level-(k−1) classes
(r₂(m + j3^{k−1}) = r₂(m) + (4j)·3^{k−2}), hence differ by at most Ō_{k−1}(π r(m̄)).
Iterate the pointwise inequality along the S-cycle and sum the geometric series. ∎

Interpretation (this explains the data, and the failure of the naive proof): the
isometry branch *transports* fiber oscillation without contracting it (coefficient
λ^{−2} per step, but the cycle returns), and each chord *injects* the coarser-scale
oscillation of the min-vector with weight w/(1−λ^{−2}) ≈ 2 > 1 near λ = 2. An
expanding branch in place of S would have given a coefficient < 1 and the classical
Lasota–Yorke/Walters bootstrap — precisely the regularity theory that does not exist
over isometric bases (§2.3). The empirical flat-to-rising ε_k ≈ 0.46 is this
non-contraction made visible.

**Remark 3.4 (qualitative strictness is now checked; a uniform gain still
resists).** At the extremal eigenvector the
class-5 rows (no chord) are *tight and slackless*: c^m = λ^{−2}c^{4m} exactly, with
no min-term to gain from refinement. The refinement slack of [LIM] Lemma 1.2 lives
only on chord rows, and converting it into a strictly larger feasible λ requires
re-solving the eigenvector globally (any λ-increase breaks the slackless rows
first). So no local/greedy argument gives λ_{k+1} > λ_k. A 2026-07-21
successor argument does spread the nonzero lifted slack globally: iterate the
superadditive operator around the full transport cycle and average its orbit.
Under an attained positive critical eigenvector at `lambda_k in (1,2)`, this
produces a vector with strict slack in every coordinate and hence proves
`lambda_(k+1)>lambda_k` by continuity. The propagated margin can be
exponentially small in the state count, so the quantitative endpoint problem
described here is unchanged. Lean commits `d4c08a2`/`5fecf65` check this
fixed-vector argument. Commit `78602d4` proves the stronger result that any
positive feasible vector below two lifts to a strictly larger feasible
parameter at the next level, and constructs an infinite strict ladder without
critical attainment. See `annealed-critical-coding.md §5.3`.

**Remark 3.5 (scheme-theoretic reading — pointer, not a claim).** F^{(k)} is a
monotone, stable, adversarially one-sided discretization of the linear eigenproblem
for L_λ on C(Y); the dichotomy is a Barles–Souganidis-type convergence question in
which consistency holds only up to the fiber-oscillation of the discrete solutions —
and §4 shows the "continuum equation" it should converge *to* is itself not the
naive one (the adversary leaves a trace in the limit). The nearest control-theory
analogues (interval-MDP abstraction refinement; robust average-reward MDPs) have no
continuum-refinement convergence theory to import.

---

## 4. The converse structure: what is the defect if λ∞ < 2?

### 4.1 The limit path space, and a surprise

Define the **limit path space** with move labels

  X := {((y_n), (w_n)) ∈ (Y × {s,d})^ℕ : y_{n+1} = 4y_n if w_n = s;
        y_n ∈ Y₂∪Y₈ and y_{n+1} = R(y_n) if w_n = d},

R = R₂ on Y₂, R₈ on Y₈. X is compact (clopen conditions coordinatewise) and
shift-invariant; the reward g(w_n = s) = −2, g(d at Y₂) = α−2, g(d at Y₈) = α−1.
Every finite-level policy graph G_σ is a precision-k shadow of X in which the d-moves
are re-targeted by the adversary within a 3-adic ball of radius 3^{−(k−1)}.

**Proposition 4.1 (the adversary does not evaporate; proved).** The unconstrained
pressure of the limit system at β = 1 (λ = 2) is strictly positive:
P(1) := sup{h(μ) + ∫g dμ : μ shift-invariant on X} ≥ α−1 = 0.585 > 0. Consequently
λ∞ ≤ 2 < 2^{P(1)}: **the value of the finite adversarial systems does not converge
to the unconstrained value of the limit system**; the adversary's scale-by-scale
digit vetoes survive the limit as a nontrivial constraint on which invariant
measures are attainable.

*Proof.* The sets V_n := {y ∈ Y₈ : R₈^j y ∈ Y₈ for j = 1..n} are nonempty
(R₈: Y₈ → Y is a homeomorphism onto Y ⊇ Y₈, so V_{n+1} = Y₈ ∩ R₈^{−1}(V_n) is a
nonempty clopen set) and nested; pick y* ∈ ∩V_n. The path (R₈^n y*, all labels d)
lies in X with g ≡ α−1; its orbit closure is compact shift-invariant with g ≡ α−1
on it (labels are preserved in the limit in the labeled space), and any invariant
measure on it (Krylov–Bogolyubov) has h ≥ 0, ∫g = α−1. ∎

This corrects a natural first guess (present in [LIM] §3.3(i)) that "the continuum
game's value is the annealed value 2". The honest statement: on X, *typical* (Haar)
digit streams give the annealed pressure 0 at β = 1, but *exceptional* 3-adic points
support greedy orbits of strictly positive reward — e.g. y* above, whose entire
division itinerary stays in the advanced class Y₈. The finite-k min is exactly what
prevents the counting functions from exploiting such orbits: **the adversarial min
is the arithmetic** — it is the operator-theoretic residue of the fact that
φ^m_k = inf over an integer congruence class, i.e. that the true object lives on ℤ,
whose elements cannot follow an exceptional 3-adic itinerary forever.

### 4.2 The admissible class and the defect object

For a coherent adversary tower σ⃗ = (σ_k)_{k≥2} (one digit table per level;
Π_k(finite sets) is compact), call μ ∈ M_shift(X) **σ⃗-admissible** if μ is a
weak-* limit of invariant measures of the level-k policy graphs G_{σ_k} (lifted to
(Y × {s,d})^ℕ by putting, say, Haar on each level-k cell); write M(σ⃗) for the set
of such limits — nonempty, compact, convex. [Provable-looking, standard weak-*
arguments: limits are supported on X, since the adversarial re-targeting moves points
by ≤ 3^{−(k−1)} → 0 and X is defined by closed conditions; and level-k invariance
passes to shift-invariance.]

**Conjecture 4.3 (defect identification).** λ∞ = 2^{β∞} where
β∞ = min_{σ⃗} max_{μ ∈ M(σ⃗)} critical β of [h(μ) + β∫g dμ = 0], and:
(a) under (A), the optimum is the annealed object: optimal μ has Y-marginal = Haar
(the measures of maximal entropy of the policy graphs flatten over fibers);
(b) under (B), any optimal pair (σ⃗*, μ*) has μ* with **Y-marginal singular with
respect to Haar** — an "adversarial Mather measure": the exact analogue for the
lower-spectral-radius game of Morris's Mather sets for maximal matrix products, and
the analogue of Bousch's Sturmian maximizing measures with the odometer in the base.
Its support would be carried by the hierarchical set where the eigenvectors keep
oscillating (Corollary 3.4 of [LIM] guarantees persistent mean oscillation under
(B)); the singular-marginal claim is the precise content of "the finite-precision
games do not converge to the Haar/annealed game".
Two cautions from the literature: Bousch–Mairesse's disproof of the finiteness
conjecture warns that σ⃗*/μ* need not be periodic or otherwise finitely describable;
Chazottes–Hochman's zero-temperature non-convergence shows that towers of
optimizations at refining scales can oscillate forever between competing hierarchical
structures — a (B)-like mechanism, and also a warning that even under (B) the *pair*
(σ⃗_k, μ_k) may fail to converge while the value λ_k does.

Status: the *definitions* above are sound (compactness statements are routine); the
*identification* λ∞ = value of the limit game is open (it is [LIM] §3.3(d), the
exchange-of-limits question, now with the correct limit game — Prop 4.1 shows the
naive limit game without the admissibility constraint has the wrong value).

---

## 5. New numerics (k = 14–18 eigenvectors; script `experiments/kl/osc_stats.py`)

GPU candidate eigenvectors (`eigvec_k{14..18}.npy`, float thresholds λ̂_k). The
oscillation-law identity δ_k = (s(λ̂_k)−1)/(λ̂^{α−2}+λ̂^{α−1}) holds to all printed
digits at every k (extends [LIM]'s verification from k ≤ 12):

| k | δ_k | ε_k (sup) | ε (median) | argmin j = 0/1/2 | top 1% share of ΣD | top 10% share | C^max |
|---|------|------|------|------|------|------|------|
| 14 | 0.014755 | 0.4566 | 0.0655 | .3330/.3338/.3332 | 0.149 | 0.487 | 339 |
| 15 | 0.013566 | 0.4588 | 0.0591 | .3332/.3339/.3329 | 0.158 | 0.499 | 516 |
| 16 | 0.012506 | 0.4655 | 0.0534 | .3332/.3332/.3336 | 0.166 | 0.511 | 793 |
| 17 | 0.011554 | 0.4694 | 0.0485 | .3335/.3332/.3334 | 0.175 | 0.522 | 1207 |
| 18 | 0.010705 | 0.4703 | 0.0442 | .3333/.3333/.3334 | 0.183 | 0.532 | 1835 |

Readings (interpretive, not proofs):
- **δ decays, ε_sup rises**: mean flattening with persistent worst fibers — exactly
the Lemma 3.3 transport picture. δ-ratios (0.9194 → 0.9265) track the (2−λ)-ratios
(0.9338 → 0.9376) as the identity requires.
- **The adversary's optimal digit is exactly equidistributed** (argmin ⅓/⅓/⅓ to 4
decimals): no digit bias for the defect to latch onto; whatever structure the
would-be defect measure has, it is not a first-digit bias.
- **Concentration is slowly increasing**: the top 1% of fibers carry a growing share
(14.9% → 18.3%) of the total oscillation. Under (A) this is a vanishing-mass
hierarchical exceptional set (the residue of Prop 4.1's greedy orbits); under (B) it
is the skeleton of the defect measure's support. This is the observable to track:
if λ∞ < 2, the Lorenz curve of D_r should converge to a nondegenerate limit; if
λ∞ = 2, total mass → 0 while concentration may still sharpen.
- Class-8 fibers (feeding the advanced chord) oscillate ≈ 8% more than class-2/5
fibers at every k — consistent with the advanced term being the operative
difficulty, as in KL's own account of why their method needed the min.
- **Model check against [LIM] §4's pre-registered predictions** (certified
γ_15..18 = 0.8812479, 0.8892666, 0.8966115, 0.9032886): the k = 15 value matches
Model A (γ∞ = 1, geometric) to 3×10⁻⁵, but a systematic downward bend grows to
8.4×10⁻⁴ by k = 18; gap ratios drift up 0.9310 → 0.9354 (the (B)-signature
direction). Refitting on k = 8–18: the pre-registered discriminator rejects every
Model B with γ∞ ≤ 0.95 (γ₁₅ = 0.88125 > 0.8807); free-γ∞ fits now weakly prefer
γ∞ ≈ 0.99–1.00 with essentially flat SSE on [0.99, 1]. Calibrated summary: **data
constrain γ∞ to [0.97, 1] and cannot separate 1 from 0.99; the drift direction has
flipped from pro-(A) to mildly pro-(B), at ~4σ of fit rms but well within model
mis-specification risk.**

---

## 6. Status ledger and sharpest findings

**Proved in this note.** Lemma 1.1 (odometer conjugacy; single-cycle sections);
Lemma 1.2 (period-3 driving); Prop 1.3 (normal forms); **Theorem 2.1 ((H_k)
unconditional via Gaubert–Gunawardena — KL §6 conditions (1),(2) hold at every k
with λ_k < 2, and the oscillation law/game value of [LIM] are now unconditional)**;
Theorem 3.1 (criterion hierarchy with exact constants; answer to "what decay
suffices": *any* o(1), and at the mean rung the criterion is an equivalence with
rate δ_k ≍ 2−λ_k); Prop 3.2 ((E1) impossible given C^max_k → ∞); Lemma 3.3
(oscillation transport, factor-2 obstruction); Prop 4.1 (P(1) ≥ α−1 > 0 on the limit
path space; the adversary survives the limit).

**Provable-looking (stated, not fully written).** Prop 4.2-type compactness (limit
measures land on X; M(σ⃗) compact convex); h(μ) = h(word marginal) on X.

**Conjectural.** Conjecture 4.3 (λ∞ = value of the constrained limit game; defect =
adversarial Mather measure with Haar-singular marginal under (B)).

**Open after the 2026-07-21 successor update.** The dichotomy itself; a
dimension-free quantitative adjacent gain (qualitative strict feasible lifting
is kernel-checked in `78602d4`); an a priori mean-oscillation bound (the exact
missing lemma, §3.2); and nonlinear eigenvector uniqueness at fixed `k` (which
is not needed for the strict feasible ladder and need not hold for a general
topical map).

**Sharpest findings of this session.**
1. **(H_k) is a theorem** (Theorem 2.1): the odometer cycle makes G(F) strongly
connected, so Gaubert–Gunawardena's generalized Perron–Frobenius theorem applies at
every level and every λ. One standing numerical hypothesis of the program is
discharged; KL's "may be difficult to prove" item falls to a 2004 theorem plus
Lemma 1.1(b).
2. **The adversary is the arithmetic** (Prop 4.1): the limit system without the
adversary has pressure ≥ α−1 > 0 at λ = 2 (greedy all-Y₈ orbits), so λ∞ is *not*
the value of the naive continuum system; the min encodes precisely that counting
functions live on ℤ. Any correct limit object must carry an admissibility
constraint; Conjecture 4.3 states it.
3. **The criterion, sharpened and closed off** (Theorem 3.1 + Prop 3.2): uniform
equicontinuity along the tower suffices with *no rate* — but is provably false for
the actual eigenvectors (spread → ∞), sup-oscillation is empirically rising, and the
mean criterion is an exact equivalence, hence powerless without a new structural
input. The missing regularity theory (subactions over isometric branches) does not
exist in the literature; Lemma 3.3 quantifies the obstruction (factor w₈/(1−λ^{−2})
→ 2 > 1).
4. Theory-hunt verdict (§2): the composite object is new; its layers live in
nonlinear Perron–Frobenius/Shapley theory, Protasov product families, topical IFS
(Bousch–Mairesse), interval-MDP abstraction, and E.O./zero-temperature theory — with
the profinite-tower limit question absent from all of them.

## References (beyond [LIM]'s list; saved PDFs noted)

- S. Gaubert, J. Gunawardena, *The Perron–Frobenius theorem for homogeneous,
  monotone functions*, Trans. AMS 356 (2004) 4931–4950. arXiv:math/0105091.
  [`papers/gaubert-gunawardena-2004-perron-homogeneous-monotone.pdf`]
- M. Akian, S. Gaubert, A. Hochart, *Ergodicity conditions for zero-sum games*,
  Discrete Contin. Dyn. Syst. 35 (2015) 3901–3931. arXiv:1405.4658.
  [`papers/akian-gaubert-hochart-2014-ergodicity-zero-sum-games.pdf`]
- T. Bousch, *Le poisson n'a pas d'arêtes*, Ann. IHP Probab. Stat. 36 (2000)
  489–508. [`papers/bousch-2000-le-poisson.pdf`]
- T. Bousch, J. Mairesse, *Asymptotic height optimization for topical IFS, Tetris
  heaps, and the finiteness conjecture*, J. Amer. Math. Soc. 15 (2002) 77–111.
  [`papers/bousch-mairesse-2002-tetris-finiteness.pdf`]
- O. Jenkinson, *Ergodic optimization in dynamical systems*, Ergodic Theory Dynam.
  Systems 39 (2019) 2593–2618. arXiv:1712.02307.
  [`papers/jenkinson-2017-ergodic-optimization-survey.pdf`]
- I. D. Morris, *Mather sets for sequences of matrices and applications to the study
  of joint spectral radii*, Proc. London Math. Soc. 107 (2013) 121–150.
  arXiv:1109.4615. [`papers/morris-2011-mather-sets-matrices-jsr.pdf`]
- J.-R. Chazottes, M. Hochman, *On the zero-temperature limit of Gibbs states*,
  Comm. Math. Phys. 297 (2010) 265–281. arXiv:0907.0081.
  [`papers/chazottes-hochman-2009-zero-temperature-limit.pdf`]
- A. Baraviera, R. Leplaideur, A. O. Lopes, *Ergodic optimization, zero temperature
  limits and the max-plus algebra*, IMPA minicourse (2013). arXiv:1305.2396.
  [`papers/baraviera-leplaideur-lopes-2013-maxplus-zero-temp.pdf`]
- V. Yu. Protasov, *Spectral simplex method*, Math. Program. 156 (2016) 485–511;
  Yu. Nesterov, V. Yu. Protasov, *Optimizing the spectral radius*, SIAM J. Matrix
  Anal. Appl. 34 (2013) 999–1013; N. Guglielmi, V. Protasov, *An antinorm theory for
  sets of matrices: bounds and approximations to the lower spectral radius*, Linear
  Algebra Appl. 607 (2020) 89–117.
- R. Givan, S. Leach, T. Dean, *Bounded-parameter Markov decision processes*,
  Artificial Intelligence 122 (2000) 71–109. G. Iyengar, *Robust dynamic
  programming*, Math. Oper. Res. 30 (2005) 257–280. A. Nilim, L. El Ghaoui, Oper.
  Res. 53 (2005) 780–798. Y. Wang et al., *Robust average-reward Markov decision
  processes*, AAAI 2023, arXiv:2301.00858.
- M. Kattenbelt, M. Kwiatkowska, G. Norman, D. Parker, *A game-based
  abstraction-refinement framework for Markov decision processes*, Form. Methods
  Syst. Des. 36 (2010) 246–280.
- A. Antonevich, V. Bakhtin, A. Lebedev, *On t-entropy and variational principle for
  the spectral radii of transfer and weighted shift operators*, Ergodic Theory
  Dynam. Systems 31 (2011) 995–1042. Yu. Latushkin, A. Stepin, *Weighted translation
  operators and linear extensions of dynamical systems*, Russian Math. Surveys 46
  (1991) 95–165.
- V. Anashin, A. Khrennikov, *Applied Algebraic Dynamics*, de Gruyter 2009 (p-adic
  1-Lipschitz ergodic theory; single-cycle criterion).
- *Regularity of calibrated sub-actions for circle expanding maps and Sturmian
  optimization*, Ergodic Theory Dynam. Systems (2022), arXiv:2105.10767. G.
  Contreras, *Ground states are generically a periodic orbit*, Invent. Math. 205
  (2016) 383–412.
- G. Barles, P. E. Souganidis, *Convergence of approximation schemes for fully
  nonlinear second order equations*, Asymptotic Anal. 4 (1991) 271–283 (pointer only,
  §3.5).

Reproduction: Theorem 2.1's graph condition is Lemma 1.1(b) (one-line check:
`{(4*m)%3**k for m in range(2,3**k,3)}` has full size and the orbit of 2 under
m ↦ 4m mod 3^k has length 3^{k−1}); §5 table: `python3 experiments/kl/osc_stats.py`
(~2 min, needs `eigvec_k{14..18}.npy`); model refits: fit 1−γ_k = C q^k and
γ_k = γ∞ − C q^k on k = 8–18 with the certified values in `RESULT.md`.

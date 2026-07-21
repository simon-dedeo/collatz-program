# The KL tower as tropicalized Iwasawa theory: an exact dictionary, a control theorem that holds on the nose, and a tropical main conjecture

2026-07-20. Status: **structural note with one new theorem** (the complete Λ-spectral
resolution of the annealed KL tower, §2), a precise Iwasawa dictionary (§1, §3), fresh
k = 15–18 data confronted with the pre-registered predictions of
`docs/notes/kl-limit-object.md` §4 (§4), and a main-conjecture-format statement of the
dichotomy with one divisibility proved (§5). Literature verified §6.
Prerequisites: `docs/notes/kl-limit-object.md` (cited below as [LO]; its Lemmas 1.1–1.3,
Prop. 1.4, Thm 3.2 are used freely), `experiments/kl/THEOREM.md` (exact KL hypotheses).
Every numerical claim is reproduced by `experiments/kl/tropical_iwasawa_checks.py`.

**Claim ledger.** PROVED: Lemma 1.1 (torsor dictionary), Lemma 1.2 (branch classes =
Γ-cosets, min = tropical norm), Lemma 1.3 (multiplier–weight law), Theorem 2.1 (annealed
spectral resolution; verified to machine precision for k ≤ 6 at three values of λ),
Corollaries 2.2–2.4, Proposition 3.1 (tropical defect kills old vectors), Proposition 3.2
(= [LO] Thm 3.2 restated as an exact control theorem). PROVABLE-LOOKING: extension of
(H_k)-conditional statements to all k. CONJECTURAL: Conjecture 5.2 (μ_trop = 0),
Conjecture 5.3 (geometric increments), the dichotomy itself; the empirical lean toward
λ∞ < 2 in §4. SPECULATIVE: the (φ,Γ)/U_p shape remarks (§2.5), the β = 1, 2 "critical
weights" reading (§2.4), all numerology in §4.5.

Throughout p := 3, α := log₂3, β := log₂λ; k ≥ 2 indexes the KL tower;
n := 3^{k−1} = number of level-k states.

---

## 0. Summary

The Krasikov–Lagarias difference-inequality systems live on the residues ≡ 2 (mod 3)
modulo 3^k with base isometry x ↦ 4x [LO §1]. We make exact the observation that this is
the standard Iwasawa setting at p = 3:

- Γ := 1 + 3ℤ₃ is the standard Iwasawa group for p = 3, with **canonical topological
  generator γ₀ := 1 + p = 4**; Λ := ℤ₃[[Γ]] ≅ ℤ₃[[T]] via γ₀ ↦ 1 + T (Serre).
- The KL state space Y = 2 + 3ℤ₃ is the **nontrivial coset 2Γ of Γ in ℤ₃^×** — a
  Γ-torsor — and the KL isometry branch is translation by γ₀. The level-k state set is
  Γ/Γ_{k−1}; level-k functions form Λ_ℝ/(ω_{k−1}(T)), ω_m(T) := (1+T)^{3^m} − 1 — the
  standard control-theorem quotients (Lemma 1.1).
- The adversary's min is a min over one orbit of the layer Galois group
  Γ_{k−2}/Γ_{k−1} ≅ ℤ/3: **the KL min is the min-plus (tropical) norm of the layer; the
  annealed average is the ordinary norm** (Lemma 1.2).
- **Theorem 2.1**: the annealed (linear) tower is trace-compatible
  (π_! ∘ A^{(k)} = A^{(k−1)} ∘ π_!, exactly), and its full spectrum in closed form is
  {s(λ)} ∪ {λ^{−2}ζ : ζ^{3^{k−1}} = 1, ζ ≠ 1}: one **Eisenstein eigenvalue** s(λ) on the
  trivial-character tower and the pure unit λ^{−2}γ₀ = λ^{−2}(1+T) everywhere else. The
  characteristic polynomial is (x − s(λ)) · λ^{−2(n−1)} · ω_{k−1}(T)/T under
  x = λ^{−2}(1+T). "Annealed value exactly 2" is the statement **s(2) = 1: the
  trivial-character (T = 0, Euler-characteristic-slot) eigenvalue equals 1 at λ = 2.**
- The tropical deformation F = A − Def perturbs this exactly-solved Λ-diagonal object by
  a defect operator supported on "new vectors" (functions not pulled back from level
  k−1); [LO] Theorem 3.2 becomes an **exact control theorem**: the control failure at
  level k is the mean fiber oscillation δ_k, with s(λ_k) − 1 = (w₂+w₈)δ_k, and Mazur-type
  asymptotic control ⟺ λ_k → 2 (§3).
- New data (k = 15–17 extracted here from the PSC eigenvectors; k = 18 preliminary):
  γ₁₅ = 0.8812483, γ₁₆ = 0.8892670, γ₁₇ = 0.8966119, γ₁₈ ≈ 0.9033. Increments decay
  geometrically with ratio ≈ 0.913; **the pre-registered discriminators of [LO] §4 now
  lean mildly but consistently toward dichotomy (B): λ∞ < 2, with a fitted
  γ∞ ≈ 0.974 ± 0.01** — while a sub-geometric approach to 1 remains unexcluded (§4).
- Main-conjecture format (§5): analytic side = the annealed L-function s(β) with its zero
  at β = 1; algebraic side = the tropical spectral limit λ∞. One divisibility is a
  theorem (λ∞ ≤ 2, [LO] Prop. 1.4). Equality is the tropical main conjecture;
  conditional on the repaired KL Theorem 2.2/counting chain, it would imply the
  predecessor-count bound π_a(x) ≥ x^{1−ε}. The converse is only an equivalence
  within the difference-inequality method.
- Literature (§6, searched 2026-07-20): **"tropical Iwasawa theory" does not exist** in
  the literature; the nearest developed neighbor is the Iwasawa theory of ℤ_ℓ-towers of
  graphs (Vallières et al.), whose growth law and zeta factorization our Theorem 2.1
  parallels exactly on the annealed side; no Collatz–Iwasawa linkage appears anywhere.

---

## 1. The dictionary, precisely

### 1.1 Torsor, tower, Iwasawa algebra

Standard facts, p = 3: ℤ₃^× ≅ μ₂ × Γ with Γ := 1 + 3ℤ₃; Γ is procyclic with topological
generator γ₀ := 1 + p = 4; Γ_j := Γ^{3^j} = 1 + 3^{j+1}ℤ₃ are its closed subgroups;
Λ := ℤ₃[[Γ]] = lim← ℤ₃[Γ/Γ_j] ≅ ℤ₃[[T]] via γ₀ ↦ 1 + T (Serre); Γ/Γ_{k−1} is cyclic of
order 3^{k−1} generated by γ₀. Since the KL eigenvectors are real, we use the
real-coefficient tower Λ_ℝ-quotients ℝ[Γ/Γ_{k−1}] ≅ ℝ[T]/(ω_{k−1}(T)),
ω_m(T) := (1+T)^{3^m} − 1; every statement below is at finite level, so no completion
issues arise.

**Lemma 1.1 (the KL space is the Γ-torsor tower). [PROVED]**
(a) Y := 2 + 3ℤ₃ = 2Γ = the nontrivial coset of Γ in ℤ₃^×; multiplication makes Y a
principal homogeneous Γ-space, and the KL isometry S(x) = 4x is **translation by the
canonical generator γ₀**.
(b) For x = 2u, x′ = 2u′ ∈ Y: x ≡ x′ (mod 3^k) ⟺ u′u^{−1} ∈ Γ_{k−1}. Hence the KL
level-k state set Y_k = [3^k] is canonically Γ/Γ_{k−1} (a Γ-torsor quotient), of order
3^{k−1}, on which S induces the generating 3^{k−1}-cycle m ↦ 4m.
(c) The fibers of Y_k → Y_{k−1} (the triples {r + j·3^{k−1}} over which KL takes the
min) are exactly the **orbits of the layer group Γ_{k−2}/Γ_{k−1} ≅ ℤ/3**:
r + 3^{k−1}ℤ₃ = r·Γ_{k−2} for every r ∈ Y.

*Proof.* (a) 2Γ = 2 + 6ℤ₃ = 2 + 3ℤ₃ (2 is a unit); Γ has index 2 in ℤ₃^× and Y is the
complement of Γ = 1 + 3ℤ₃; multiplication by γ₀ = 4 sends 2u ↦ 2(γ₀u).
(b) 2u ≡ 2u′ (3^k) ⟺ u − u′ ∈ 3^kℤ₃ ⟺ u′u^{−1} ∈ 1 + 3^k u^{−1}ℤ₃ = 1 + 3^kℤ₃ = Γ_{k−1}.
The quotient Γ/Γ_{k−1} of the procyclic Γ is cyclic with generator γ₀; since |Y_k| =
3^{k−1} equals the order of 4 mod 3^k on units ≡ 1 mod 3, S is a single cycle.
(c) r + 3^{k−1}ℤ₃ = r(1 + 3^{k−1}r^{−1}ℤ₃) = r(1 + 3^{k−1}ℤ₃) = rΓ_{k−2}, r a unit. ∎

So the KL tower {Y_k} **is** the canonical Γ-tower {Γ/Γ_{k−1}}, the same tower that
indexes the layers of a ℤ₃-extension, and the base map x ↦ 4x is the canonical generator
1 + p. This is the verified kernel of the linkage, now with proofs.

### 1.2 Branch structure and the tropical norm

**Lemma 1.2 (branch classes are Γ-cosets; the KL min is a min-plus norm). [PROVED]**
(a) The KL branch decomposition Y = B₂ ⊔ B₅ ⊔ B₈, B_i := i + 9ℤ₃, is the coset
decomposition of Γ₁ in the torsor: B₂ = 2Γ₁, B₈ = 2γ₀Γ₁, B₅ = 2γ₀²Γ₁. The two division
branches sit on the cosets γ₀⁰ (R₂, retarded weight λ^{α−2}) and γ₀¹ (R₈, advanced
weight λ^{α−1}); the coset γ₀² carries no division.
(b) In the KL operator [LO §1.2], the quantity min_{j} c^{r+j·3^{k−1}} is the min of c
over one Γ_{k−2}/Γ_{k−1}-orbit — the min-plus (tropical) analogue of the layer norm
N = Σ_{σ ∈ Γ_{k−2}/Γ_{k−1}} σ; the annealed operator [LO §1.4] replaces it by the
ordinary normalized norm (1/3)N.

*Proof.* (a) 2Γ₁ = 2 + 18ℤ₃ = 2 + 9ℤ₃; 2γ₀Γ₁ = 8 + 72ℤ₃ = 8 + 9ℤ₃;
2γ₀²Γ₁ = 32 + 9ℤ₃ = 5 + 9ℤ₃. The branch assignment is KL's (their (2.3)–(2.5), see
THEOREM.md §1). (b) is Lemma 1.1(c) plus the definitions: in log variables v = log₂c the
average becomes a log-sum-exp and the min becomes the tropical sum
min_σ (v ∘ σ) — the (min,+)-degeneration of the norm. ∎

Dictionary so far: *adversary's digit = layer Galois orbit; quenched KL = tropical norm;
annealed KL = ordinary norm.* Refinement k → k+1 transfers one layer from the adversary
to the dynamics ([LO] Lemma 1.2) — in tower language, **restriction along the tower can
only shrink the tropical value, exactly as corestriction-compatibility constrains Iwasawa
modules**.

### 1.3 The multiplier–weight law

**Lemma 1.3 (weights are multiplier powers). [PROVED, immediate]** Each KL branch map
g ∈ {S, R₂, R₈} is affine on Y with linear part (multiplier)
a_g ∈ {4, 4/3, 2/3}, and the KL weight of g at parameter λ = 2^β is exactly a_g^{−β}:
4^{−β} = λ^{−2}, (4/3)^{−β} = λ^{α−2}, (2/3)^{−β} = λ^{α−1}. The annealed Perron value
[LO Lemma 1.3] is the weighted multiplier sum

  **s(β) = 4^{−β} + (1/3)(4/3)^{−β} + (1/3)(2/3)^{−β}**,

the coefficients 1, 1/3, 1/3 being the relative Haar measures of the branch domains. Its
only real zeros of s − 1 are β = 1 and β = 2 ([LO] Lemma 1.3(iii) and the monotonicity
argument there). ∎

Remarks (tagged): (i) The multiplier group generated is ⟨4, 4/3, 2/3⟩ = 2^ℤ3^ℤ ⊂ ℚ₊^× —
the full (2,3)-lattice; its v₃-grading (0 for S, −1 for R₂, R₈) is the tower-level shift
("digits spent"), its v₂-grading is KL's time shift. The KL operator is thus a weight-β
element of a (2,3)-affine groupoid algebra over ℤ₃, with the Iwasawa Γ as its isometric
(v₃ = 0) part. [PROVED as bookkeeping; the groupoid framing is organizational.]
(ii) That the second zero sits at λ = 4 = γ₀, i.e. that s(γ₀) = 1, and that the two
zeros are at consecutive integer weights β = 1, 2, is noted as a curiosity.
[SPECULATIVE — no interpretation is claimed.]

---

## 2. The annealed system resolved as a Λ-tower (new theorem)

Notation from [LO §1.4]: A_λ^{(k)} is the annealed (linear) operator on C(Y_k),
w₂ := λ^{α−2}, w₈ := λ^{α−1}, s(λ) = λ^{−2} + (w₂+w₈)/3. Let
π_! : C(Y_k) → C(Y_{k−1}) be the **fiber-sum (trace/corestriction)** map
(π_!c)(m̄) := Σ_{π(m)=m̄} c(m), and U := U_{γ₀}, (Uc)(m) := c(4m).

**Theorem 2.1 (spectral resolution of the annealed tower). [PROVED; verified numerically
to ≤ 3·10^{−13} for k ≤ 6 at λ ∈ {1.5, 1.83, 2}]** For every k ≥ 2 and λ > 0, with
n = 3^{k−1}:

(i) **Trace compatibility:** π_! ∘ A_λ^{(k)} = A_λ^{(k−1)} ∘ π_! (k ≥ 3). The annealed
tower is an inverse system of operators under the norm maps — the corestriction-
compatible structure of an Iwasawa module — even though it is *not* compatible with the
pullbacks π* and *not* Γ-equivariant (see 2.3).

(ii) **The kernel of the trace is pure cyclotomic:** Z_k := ker π_! is A_λ^{(k)}-invariant
and A_λ^{(k)}|_{Z_k} = λ^{−2}·U|_{Z_k}: on Z_k the division/branching terms vanish
identically and the operator is multiplication by the **unit** λ^{−2}γ₀ of the group
algebra.

(iii) **Spectrum in closed form:**
spec A_λ^{(k)} = {s(λ)} ⊔ {λ^{−2}ζ : ζ^n = 1, ζ ≠ 1}, all eigenvalues simple (note
s(λ) = λ^{−2} + (w₂+w₈)/3 > λ^{−2} for every λ > 0), and

  det(xI − A_λ^{(k)}) = (x − s(λ)) · (x^n − λ^{−2n})/(x − λ^{−2}).

(iv) **Characteristic ideal form:** substituting x = λ^{−2}(1 + T) (the spectral
variable of the unit λ^{−2}γ₀),

  det(xI − A_λ^{(k)}) = (x − s(λ)) · λ^{−2(n−1)} · ω_{k−1}(T)/T,

the standard Iwasawa control polynomial ω_{k−1}, unit-twisted, times the linear
**Eisenstein factor** (x − s(λ)).

*Proof.* (ii) Fibers of π are the triples {r + j·3^{k−1}} (Lemma 1.1(c)). For c ∈ Z_k
every division term of (A c)(m) is w · (1/3)Σ_j c(r(m) + j·3^{k−1}) =
w·(1/3)(π_!c)(r(m)) = 0, so Ac = λ^{−2}Uc pointwise on Z_k. U maps Z_k to Z_k:
Σ_i (Uc)(m + i·3^{k−1}) = Σ_i c(4m + 4i·3^{k−1}) = (π_!c)(4m mod 3^{k−1}) = 0, using
that 4i·3^{k−1} mod 3^k runs over the fiber offsets (4 ≡ 1 mod 3).

(i) Fix m̄ ∈ Y_{k−1} and a lift m. Since k ≥ 3, all three lifts share the mod-9 branch
class of m̄. Isometry part: as just computed, fiber-sums intertwine with U. Division part
(branch R₂; R₈ is identical with 2 in place of 4): r₂(m + i·3^{k−1}) =
r₂(m) + 4i·3^{k−2} (mod 3^{k−1}), and {4i·3^{k−2} mod 3^{k−1} : i = 0,1,2} =
{0, 3^{k−2}, 2·3^{k−2}} since gcd(4,3) = 1; so as i runs over the fiber of m̄, the
targets r₂(m + i·3^{k−1}) run over the full fiber of r̄ := r₂(m) mod 3^{k−2} in Y_{k−1},
and Σ_i (1/3)Σ_j c(r₂(m+i·3^{k−1}) + j·3^{k−1}) = (1/3)·(sum of c over the 9-element
π_{k,k−2}-fiber over r̄) = (1/3)Σ_{j} (π_!c)(r̄ + j·3^{k−2}). By the tower coherence of
the division maps ([LO] Lemma 1.1(d)), r̄ = r₂^{(k−1)}(m̄); so the fiber-sum of the
division term of A^{(k)}c at m̄ equals the division term of A^{(k−1)}(π_!c) at m̄.

(iii) Induction on k via the exact sequence 0 → Z_k → C(Y_k) →^{π_!} C(Y_{k−1}) → 0,
which is A-triangular by (i)–(ii): spec A^{(k)} = spec(λ^{−2}U|_{Z_k}) ⊔ spec A^{(k−1)}.
Base k = 2: C(Y_2) is 3-dimensional; column sums give the eigenvalue s(λ) on the
quotient ([LO] Lemma 1.3), and A|_{Z_2} = λ^{−2}·(3-cycle) with eigenvalues
λ^{−2}e^{±2πi/3}. Step: U is the regular 3^{k−1}-cycle (Lemma 1.1(b)); its
eigenfunctions are the characters χ of Γ/Γ_{k−1} with Uχ = χ(γ₀)χ; χ ∈ Z_k iff χ is
nontrivial on the layer group Γ_{k−2}/Γ_{k−1}, i.e. iff χ is **primitive** (exact
conductor 3^{k−1}); those χ(γ₀) are exactly the primitive 3^{k−1}-th roots of unity,
each once. The union over the induction is all nontrivial 3^{k−1}-th roots of unity.
(iv) Substitute; ω_{k−1}(T)/T = Π_{ζ≠1}((1+T) − ζ) up to sign conventions. ∎

Machine check (`spectrum_theorem_check`): matched spectra agree to ≤ 3·10^{−13}
(k ≤ 6, λ ∈ {1.5, 1.83, 2}); ‖π_!A − A′π_!‖ = 0.0 exactly (k = 3..6, λ = 2, 1.83).

### 2.2 Answers to the structure questions

**"What Λ-module is the annealed system?"** The underlying module tower is the free
rank-one tower ℝ[Γ/Γ_{k−1}] = Λ_ℝ/(ω_{k−1}); the arithmetic sits in the operator, which
is triangular with respect to the norm-compatible filtration: associated graded =
(cyclotomic part: the unit λ^{−2}(1+T) acting on ker-of-trace at every level) ⊕
(Eisenstein line: the scalar s(λ)). As a "Λ-module with operator", the semisimplification
is completely explicit — Theorem 2.1(iii)–(iv).

**"Does the averaged operator commute with the Γ-action?"** **No** — and this is a
finding, not a defect: ‖[A, U_{γ₀}]‖_max = 0.5 at λ = 2 (k ≤ 5), and even
Γ₁-translations fail to commute for k ≥ 3 (the division maps are additive-affine, not
multiplicative; their affinity intertwines *additive* translations δ ↦ a_g δ with the
multipliers of Lemma 1.3). The annealed tower is instead **trace-compatible**
(Theorem 2.1(i)) and **spectrally of character type** (Theorem 2.1(iii)): equivariance
fails on the nose but holds on the level of spectral data. [PROVED/verified]

**"Where does 'value exactly 2' sit? Is it an Euler-characteristic-like invariant?"**
Yes, in the following precise sense. The trivial-character direction (the tower of
augmentation quotients, i.e. the T = 0 slot where Euler characteristics of Λ-modules are
computed: χ(Γ, M) is f_M(0) up to units) carries the eigenvalue s(λ), independent of k;
all other spectral data is the fixed unit λ^{−2}(1+T). So the entire k-independent
content of the annealed tower is the single number s(λ) sitting in the T = 0 slot, and

  **"annealed value = 2" ⟺ s(2) = 1 ⟺ the Euler-characteristic slot of the annealed
  tower is trivial (eigenvalue 1) exactly at λ = 2** ⟺ Haar measure on Y is invariant
  under the λ = 2 annealed transfer operator ([LO] Lemma 1.3) — the density heuristic
  π_a(x) ≍ x in tower form. [PROVED]

### 2.3 Control on the annealed side is exact

**Corollary 2.2 (perfect control). [PROVED]** char_k(x)/char_{k−1}(x) =
(x^n − λ^{−2n})/(x^{n/3} − λ^{−2n/3}), i.e. level k adds exactly the primitive-conductor
cyclotomic factor ω_{k−1}/ω_{k−2} (unit-twisted) and nothing else; the Eisenstein factor
(x − s(λ)) is common to all levels. In Mazur's language the annealed tower satisfies a
control theorem **with zero error term**: level-k spectral data = level-(k−1) data plus
the forced new-character contribution. ∎

**Corollary 2.3 (Artin-type factorization). [PROVED]** det(xI − A_λ^{(k)}) factors over
the characters of Γ/Γ_{k−1} with L-factor (x − s(λ)) at χ = 1 and (x − λ^{−2}χ(γ₀)) at
χ ≠ 1. The branching (division maps) contributes to the trivial character only: **the
annealed L-data is concentrated at the trivial character.** ∎

This is exactly the shape of the Ihara-zeta factorization along abelian covers in the
Iwasawa theory of graph towers (§6, refs [V21], [DLRV], [branched]): our annealed tower
is a weighted-digraph ℤ₃-tower whose zeta factors along the character tower, with a
single "special value" factor carrying all the arithmetic.

**Corollary 2.4 (spectral gap). [PROVED]** The annealed Perron gap is
s(λ) − λ^{−2} = (w₂+w₈)/3 — k-independent and large (= 3/4 at λ = 2: eigenvalue 1
against a cyclotomic shell of radius 1/4). Whatever makes λ_k creep upward is invisible
in the annealed spectrum; it lives entirely in the tropical deformation. ∎

### 2.4–2.5 Two tagged remarks

(2.4) [SPECULATIVE] s(β) is a three-term Dirichlet polynomial with real zeros exactly at
the integer weights β = 1, 2 (Lemma 1.3). In the main-conjecture format of §5, β = 1 is
the "central" zero (the counting exponent), and the second zero at β = 2 (λ = 4 = γ₀) is
outside the KL range λ ≤ 2 and is annihilated by the quenched system (ρ_k < 1 on (2,12],
[LO] §1.4 remark (2)) — an "extra zero of the annealed relaxation only".

(2.5) [SPECULATIVE, shape only] The operator A = λ^{−2}γ₀ + w₂·(branch)∘tr + w₈·(branch)∘tr
has the algebraic shape "unit·γ + weights·ψ" familiar from two places: the ψ-operator
(normalized trace, left inverse of Frobenius) acting with Γ on modules over the Iwasawa
algebra in (φ,Γ)-module theory (Perrin-Riou, Colmez), and Atkin's U_p =
(1/p)Σ_{fiber} acting on towers of modular curves together with diamond operators. No
descent data is claimed; what is exact is: Γ-generator translation + normalized
layer-trace, which is precisely the generating pair of those theories.

---

## 3. Tropicalization as a deformation of the resolved tower

**Proposition 3.1 (the tropical defect kills old vectors). [PROVED]** Write the quenched
KL operator as F_λ^{(k)} = A_λ^{(k)} − Def_λ^{(k)}, where

  (Def c)(m) := 1_{B₂}(m)·w₂·D_{r₂(m)}(c) + 1_{B₈}(m)·w₈·D_{r₈(m)}(c),
  D_r(c) := (1/3)Σ_j c(r + j·3^{k−1}) − min_j c(r + j·3^{k−1}) ≥ 0.

Then Def(c + π*h) = Def(c) for every h ∈ C(Y_{k−1}): the defect operator vanishes on
(and is insensitive to) the "old" subspace V_{k−1} := π*C(Y_{k−1}) and factors through
the new-vector quotient C(Y_k)/V_{k−1}.

*Proof.* π*h is constant on fibers, and D_r(c + const-on-fiber) = D_r(c) since both the
average and the min shift by that constant. ∎

So the tropical deformation couples the exactly-resolved annealed tower (Theorem 2.1) to
the k-th level **only through the new-conductor components** of the argument. The
extremal eigenvector's mean defect is exactly the δ_k of [LO]:

**Proposition 3.2 (oscillation law = exact tropical control theorem). [PROVED = [LO]
Thm 3.2, restated]** Under (H_k), the extremal pair (λ_k, c_k) satisfies the exact
identity s(λ_k) − 1 = (w₂ + w₈)·δ_k with δ_k = Σ_r D_r(c_k)/Σ_m c_k(m), two-sided
comparable to (2 − λ_k); hence:

- *Annealed tower:* control exact, defect ≡ 0, value pinned at s(λ) with s(2) = 1.
- *Tropical tower:* control fails by exactly δ_k at level k; **Mazur-type asymptotic
  control (δ_k → 0) ⟺ λ_k → 2 ⟺ the tropical main conjecture of §5.** ∎

Dictionary table (statements above; correspondences [PROVED] unless marked):

| Iwasawa theory (p = 3) | KL tower |
|---|---|
| Γ = 1+3ℤ₃, canonical generator γ₀ = 1+p = 4 | base isometry x ↦ 4x on Y = 2Γ (torsor) |
| layers Γ/Γ_{k−1} of the ℤ₃-tower | KL residue classes [3^k], n = 3^{k−1} |
| Λ = ℤ₃[[Γ]] ≅ ℤ₃[[T]], γ₀ = 1+T | level-k functions = Λ_ℝ/(ω_{k−1}(T)) |
| layer Galois group ≅ ℤ/p | adversary's lost digit: fiber = Γ_{k−2}-orbit |
| norm/corestriction maps | annealed: (1/3)·trace π_!; **tropical: min-plus norm** |
| control polynomial ω_k | annealed char-poly factor (Thm 2.1(iv)) |
| Euler characteristic = char series at T = 0 | Eisenstein eigenvalue s(λ); s(2) = 1 |
| control theorem (Mazur 1972) | annealed: exact (Cor 2.2); tropical: defect δ_k (Prop 3.2) |
| growth law ℓ^{μℓ^n+λn+ν} (Iwasawa) | defect ansatz 3^{−(μ3^k+λk+ν)}: fits §4 |
| μ = 0 (Ferrero–Washington) | Conjecture 5.2: μ_trop = 0 (fitted |μ| < 10^{−9}) |
| λ-invariant ∈ ℤ≥0 (Weierstrass) | fitted λ_trop ≈ 0.06–0.08 ∉ ℤ: **no Λ-module realizes the tropical defect** (§4.4) |
| main conjecture: analytic = algebraic | λ∞ =? 2 = zero of s(β) at β = 1 (§5) |

---

## 4. Growth laws against the new k = 15–18 data

### 4.1 Data

Sources: k ≤ 11 KL 2003 (float thresholds); k = 12–14 certified
(`cert_k1*.json`, RESULT.md); **k = 15–17 extracted in this note** from the PSC-run
eigenvectors (`experiments/kl/eigvecs/eigvec_k{15,16,17}.npy`, job 42443512) via the
class-5 fixed-point ratios λ = (c^{4m}/c^m)^{1/2} — interquartile spread ≤ 10^{−13},
i.e. fully converged eigenvectors; absolute accuracy limited by the run's threshold
solve (est. ~10^{−6}), and these are *float estimates, not certificates*;
**k = 18 preliminary** (reported value from the run; eigenvector file incomplete
locally at time of writing — treat with caution).

| k | λ_k | γ_k | δ_k | ε_k (sup-osc) | median fiber osc |
|---|------|------|------|------|------|
| 12 | 1.8064236 | 0.8531363 | 0.017459 | 0.4652 | 0.0799 |
| 13 | 1.8188238 | 0.8630058 | 0.016061 | 0.4604 | 0.0725 |
| 14 | 1.8307724 | 0.8724524 | 0.014755 | 0.4566 | 0.0655 |
| 15 | 1.8419684 | 0.8812483 | 0.013566 | 0.4588 | 0.0591 |
| 16 | 1.8522348 | 0.8892670 | 0.012506 | 0.4655 | 0.0534 |
| 17 | 1.8616888 | 0.8966119 | 0.011554 | 0.4694 | 0.0485 |
| 18 | ≈1.870 | ≈0.9033 (prelim.) | — | — | — |

The oscillation identity s(λ_k) − 1 = (w₂+w₈)δ_k holds at k = 15–17 to ≤ 2·10^{−13}
(new verification levels for [LO] Thm 3.2). The sup-oscillation ε_k remains flat ≈ 0.46
(now through k = 17): the mean criterion, not the sup, remains the live one — as [LO]
recorded.

Increments γ_{k+1} − γ_k (k = 11..17): 0.011380, 0.009870, 0.009447, 0.008796, 0.008019,
0.007345, 0.006688(prelim). Increment ratios: 0.867, 0.957, 0.931, 0.912, 0.916,
0.911 — **stable at ≈ 0.913 over the last three**. Gap ratios (1−γ_{k+1})/(1−γ_k):
0.9281, 0.9328, 0.9310, 0.9310, 0.9325, 0.9337, 0.9353 — **drifting upward**.

### 4.2 Verdict on the pre-registered test ([LO] §4)

- Levels: observed γ₁₅ = 0.88125 vs Model A (γ∞ = 1, fit k = 8–14) 0.88154 and
  B(γ∞ = 0.95) 0.87977. The decision rule "γ₁₅ above 0.8807 favors A over every B with
  γ∞ ≤ 0.95" fires: **B with γ∞ ≤ 0.95 is rejected.** But the data run *systematically
  below Model A*, with deviation growing monotonically: −2.9·10^{−4} (1.5× fit-rms) at
  k = 15, −5.6·10^{−4} (3×) at 16, −9.3·10^{−4} (5×) at 17, −1.4·10^{−3} (7×, prelim.)
  at 18. **Fixed-ratio Model A is also being rejected.**
- Ratio diagnostics point the same way: increment ratio (≈ 0.913) sits below the gap
  ratio (≈ 0.933), and the gap ratio drifts upward — both are signatures of a finite
  limit γ∞ < 1 (under a true geometric-gap law the two ratios coincide and are flat).
- Free-limit fits (γ_k = γ∞ − Cq^k), sliding windows: γ∞ = 0.994 (k = 8–14),
  0.985 (11–17), 0.983 (11–18), 0.986 (12–18), **0.974 (14–18, rms 4·10^{−6} — 30×
  better than Model A's 1.4·10^{−4} on the same window)**. The fitted limit *decreases*
  as the window slides late — consistent with convergence of the fit toward a true
  γ∞ < 1 (early-k transient inflates it), and inconsistent with plain Model A.

**Honest empirical verdict [CONJECTURAL-EMPIRICAL]: the new data lean mildly but
coherently toward dichotomy (B) — a stall at γ∞ ≈ 0.974 ± 0.010, λ∞ ≈ 1.964 — while a
sub-geometric approach to 1 (gap ratios creeping to 1 with γ∞ = 1) remains unexcluded.
The 2026-07-20 morning position "no evidence for any finite γ∞ < 1" ([LO] §4 Model B
discussion) is now outdated: the evidence exists, at the 5–7σ_fit level against fixed-q
Model A, though not yet against all γ∞ = 1 models.**

Coherence check (two independent extrapolations): from the γ-tower, γ∞ = 0.974 gives
λ∞ = 1.9640 and, via the oscillation law, predicts δ∞ = (s(λ∞)−1)/(w₂+w₈) ≈ 0.0026;
direct geometric extrapolation of the δ-tower gives δ∞ ≈ 0.0021. Agreement to ~20%
with no shared fitting — the (B)-reading is internally consistent. Under (A) both would
have to drift to 0 together; present decay rates do not suggest it, but cannot rule
it out.

### 4.3 The Iwasawa growth-law ansatz

Translate Iwasawa's h_ℓ(K_n) = ℓ^{μℓ^n + λn + ν} by taking the level-k "order" to be the
defect exponent e_k := −log₃(defect_k):

- Ansatz on the gap (defect = 1 − γ_k): e_k = μ3^k + λk + ν. Fit (any window):
  **μ = O(10^{−10}) ≈ 0**, λ = 0.063–0.067, ν ≈ 0.97.
- Ansatz on the increments (defect = γ_{k+1} − γ_k): **μ ≈ 0**, λ = 0.074–0.083
  (λ = 0.083 on the late window 14–18, rms 10^{−3}), ν ≈ 3.2.

What the ansatz *predicts*: μ > 0 would force doubly-exponential defect collapse
(increment ratios → 0 fast) — decisively absent; μ = 0, λ > 0 predicts exactly geometric
increments with ratio 3^{−λ} — this is what the data show, with 3^{−λ} ≈ 0.913, i.e.
**λ_trop ≈ 0.083**.

### 4.4 Non-integrality: a no-go for naive Λ-module models [standard implication +
empirical premise]

If the defect tower were of Λ-module type — i.e. 3^{e_k} = |X/ω_{k−1}X| for some
finitely generated torsion Λ-module X — then Iwasawa's structure theorem would force
e_k = μ3^k + λk + ν *exactly* for large k with **integers** μ, λ ≥ 0 (Weierstrass
preparation is where integrality comes from). The fits give μ = 0 and λ ≈ 0.06–0.08,
robustly non-integer. Conclusion (conditional on the fitted asymptotics being real):
**no finitely generated Λ-module realizes the tropical defect tower.** The min-plus
deformation leaves the category in which characteristic ideals exist; whatever "tropical
characteristic ideal" means, it must allow irrational slopes. This is the sharpest
structural disanalogy found, and it is a *finding about the tropicalization*, not a
failure of the dictionary: the annealed side is exactly of Λ-type (Theorem 2.1), the
tropical side provably close to it (Prop 3.1–3.2) yet outside it.

### 4.5 Numerology [SPECULATIVE, recorded to be dismissed]

Candidates matching the increment ratio q ≈ 0.913 ± 0.003: 3^{−1/12} = 0.9125,
(4/3)^{−1/3} = 0.9086, 2^{−1/8} = 0.9170, e/3 = 0.9061; matching the gap ratio
q ≈ 0.933: 3^{−1/16} = 0.9337. That *both* ratios can be "matched" by some 3^{−1/n} is
exactly why none of this is evidence; no principled derivation exists for any candidate;
we record them only to mark them as unclaimed. The honest statement is: q is measured to
3 significant figures, drifting, and unidentified.

---

## 5. The main-conjecture format

**Analytic side.** The annealed L-function of the tower: s(β) − 1, with
s(β) = 4^{−β} + (1/3)(4/3)^{−β} + (1/3)(2/3)^{−β} — k-independent (Theorem 2.1: it is
the entire k-independent spectral content of the annealed tower, sitting in the
Euler-characteristic slot), with central zero β = 1 (λ = 2), simple, with explicit
leading coefficient s′(2) = 3(α−2)/8 = −0.15564 ([LO] Lemma 1.3(iii)).

**Algebraic side.** The tropical spectral limit λ∞ := lim λ_k ∈ (1.8616, 2] (exists:
[LO] Cor. 1.5 with the new floor λ₁₇), equivalently γ∞ = log₂λ∞; realized under (H_k) by
the persistent mean oscillation δ∞ (via the exact identity, Prop 3.2). Alternative
formulations of the same invariant: the value of the limiting adversarial digit game
([LO] §2); 3^{−λ_trop} as the asymptotic decay rate of the corrector's new-conductor
content (Prop 3.1 + §4.3).

**Theorem (one divisibility). [PROVED]** λ∞ ≤ 2: the algebraic invariant is bounded by
the analytic zero. (= [LO] Prop. 1.4; in this note's language: min-plus norm ≤ averaged
norm, summed against the exact left-eigenmeasure of the resolved annealed tower.) ∎

**Conjecture 5.1 (tropical main conjecture, TMC). [CONJECTURAL]** λ∞ = 2: the tropical
algebraic invariant equals the central zero of the annealed L-function. Equivalently
(under (H_k), [LO] Thm 3.2(iii)) δ_k → 0; conditional on the repaired KL
Theorem 2.2/counting chain it implies
π_a(x) ≥ x^{1−ε} for all ε > 0, a ≢ 0 (3), x ≥ x₀(a, ε) — and conversely within the
method ([LO] §3.1). *Status: the §4 data now mildly disfavor TMC* (fitted γ∞ ≈ 0.974);
if TMC fails, λ∞ itself is the new invariant and log₂(2/λ∞) ≈ 0.026 is the "tropical
defect of the main conjecture" — an analogue of a nonzero algebraic-vs-analytic
discrepancy, measuring exactly the information the difference-inequality method loses to
the adversary at all scales.

**Conjecture 5.2 (μ_trop = 0; Ferrero–Washington analogue). [CONJECTURAL, strong
numerical support]** The defect tower has no doubly-exponential component: fitted
|μ| < 10^{−9} across all windows; equivalently, increments decay no faster than
geometrically.

**Conjecture 5.3 (geometric increments; the sharpest quantitative claim we defend).
[CONJECTURAL]** There exist q ∈ (0.90, 0.94) and C > 0 with
γ_{k+1} − γ_k = (C + o(1))·q^k. Equivalently e′_k = λ_trop·k + ν + o(k) with
λ_trop = −log₃ q ∈ (0.053, 0.088), μ_trop = 0. This holds in every fit window with
stable parameters and is the precise "μ = 0, λ > 0 Iwasawa growth law" for the tropical
tower — with the caveat of §4.4 that λ_trop is not an integer, so the law is
Iwasawa-*shaped* but not Λ-module-*sourced*. Under 5.3, λ∞ < 2 ⟺ TMC fails; the current
point estimate is γ∞ = 0.974 ± 0.010.

**What the two sides would be if TMC fails (the task's payoff question).** Analytic:
unchanged — s(β) with its zero at β = 1 (the annealed/Eisenstein prediction of exponent
1). Algebraic candidates for an *identification* of λ∞, in decreasing order of our
confidence that they are even well-posed: (i) the value of the intrinsic zero-sum digit
game on Y (exchange-of-limits object, [LO] §3.3(d)) — well-posed modulo an
exchange-of-limits lemma; (ii) δ∞ via the exact self-consistency
s(λ∞) − 1 = (λ∞^{α−2} + λ∞^{α−1})·δ∞, with δ∞ the mass of the limiting oscillation
measure — the "measure of a subset of ℤ₃" candidate: the oscillation measures
ν_k(r) := D_r(c_k)/Σc_k on Y_{k−1} should converge weak-* to a measure on Y whose total
mass is δ∞; whether ν∞ is Haar-absolutely-continuous, singular, or supported on a
characterizable subset of Y is a concrete, currently open question — the natural next
computation on the stored eigenvectors; (iii) a 3-adic L-value: **no candidate
identification found** — we searched (§6) and decline to invent one. [SPECULATIVE
beyond (i)–(ii) being well-posed.]

**Pre-registered predictions for k = 19, 20** (fits frozen 2026-07-20, window 14–18,
before any k ≥ 19 computation exists):

| model | γ₁₉ | γ₂₀ | inc₁₉ | inc₂₀ | gap-ratio₁₉ | gap-ratio₂₀ |
|---|---|---|---|---|---|---|
| A (γ∞ = 1, q = 0.9331) | 0.90991 | 0.91593 | 0.00661 | 0.00603 | 0.9317 | 0.9331 |
| B (γ∞ = 0.9738, q = 0.9133) | 0.90942 | 0.91500 | 0.00612 | 0.00558 | 0.9367 | 0.9383 |

Levels separate by only 5·10^{−4} (k = 19) and 9·10^{−4} (k = 20) — near the run's
resolution; **the increments and the gap-ratio drift are the discriminators** (A: flat
≈ 0.932; B: continuing drift up through 0.937, 0.938). A k = 19 increment below 0.0063
or a gap ratio above 0.936 is (B)-evidence at the same strength that killed fixed-q A.

---

## 6. Literature (verified 2026-07-20)

**Tropical/min-plus deformations of Iwasawa modules: no hits.** Web searches for
"tropical Iwasawa", "min-plus Iwasawa", "tropicalized Iwasawa theory" return only
unrelated tropical-integrable-systems papers and standard Iwasawa expositions; a search
for Collatz + Iwasawa + 3-adic towers returns nothing connecting them. As far as we can
determine **the linkage in this note is new**. (Searched via web; see also the two
Lagarias annotated bibliographies in `papers/` — no Iwasawa-theoretic entry.)

**Nearest developed neighbor: Iwasawa theory of ℤ_ℓ-towers of graphs.** Verified:
Dion–Lei–Ray–Vallières, *On the distribution of Iwasawa invariants associated to
multigraphs*, arXiv:2207.07213 (saved:
`papers/dion-lei-ray-vallieres-2022-iwasawa-invariants-multigraphs.pdf`); it states
Iwasawa's growth law h_ℓ(K_n) = ℓ^{μℓ^n+λn+ν} [their (1.1), citing Iwasawa 1973] and
develops the multigraph analogue (spanning-tree counts in abelian ℓ-towers of covering
graphs; earlier: Vallières, *On abelian ℓ-towers of multigraphs* I–III, with McGown;
Gonet). More recent strands include Ihara zeta/L-functions for branched ℤ_p-towers and
"Iwasawa theory of graphs and their duals" (e.g. arXiv:2410.11704 — authorship not
independently verified here). The parallel to §2 is exact on the annealed side: a
ℤ₃-tower of weighted digraphs, determinant factoring over the character tower
(Cor. 2.3), one special-value factor carrying the arithmetic. **The tropical (min-plus)
deformation of such a graph tower appears in none of this literature** — our λ_k tower
is, as far as we know, the first example of a "min-plus Iwasawa tower" with measured
(and Iwasawa-shaped, μ = 0) growth data.

**Standard Iwasawa references** for the dictionary entries: Iwasawa (growth law, 1959
announcement / *On ℤ_ℓ-extensions of algebraic number fields*, Ann. of Math. 98 (1973));
Serre (Λ ≅ ℤ_p[[T]], Bourbaki 1958/59); Mazur, *Rational points of abelian varieties
with values in towers of number fields*, Invent. Math. 18 (1972) — the control theorem;
Ferrero–Washington, Ann. of Math. 109 (1979) — μ = 0 for abelian fields; Washington,
*Introduction to Cyclotomic Fields*, ch. 13 — the structure-theorem source of the
integrality used in §4.4. [Standard; cited from memory — statements used are textbook.]

**Shape-analogies (§2.5)**: Colmez / Perrin-Riou for (φ/ψ, Γ)-structures; Atkin U_p.
[Cited as shape only; no claim verified against these texts.]

**Solenoid context.** The pair (×2-isometry-free part, ×3-structure) on ℤ₃ here is the
3-adic leaf of the (2,3)-solenoid circle of ideas already on our board (CRACKS #6, weak
model sets; `papers/einsiedler-lindenstrauss-2021-tori-solenoids.pdf`;
Lind–Schmidt–Ward-style entropy of Λ-module actions is where "Iwasawa algebra meets
dynamics" classically — but there the module is the variable and the dynamics linear;
here the module tower is trivial and the operator tropical. The two setups intersect
only at the annealed level.) [Context, no new claim.]

---

## 7. Status ledger, failures, next moves

**Proved here:** Lemmas 1.1–1.3; Theorem 2.1 (i)–(iv) with complete proof and machine
verification; Corollaries 2.2–2.4; Proposition 3.1. **Restated from [LO] (proved
there):** Prop 3.2 = oscillation law as exact control; one-divisibility λ∞ ≤ 2.
**New data:** γ, δ, ε at k = 15–17 (float, converged; not certified); k = 18
preliminary; oscillation identity verified at k = 15–17.
**Conjectural:** 5.1 (TMC — now *disfavored* by our own data, honestly recorded),
5.2 (μ_trop = 0), 5.3 (geometric increments, γ∞ = 0.974 ± 0.010 point estimate);
the §4.4 no-go (standard implication, empirical premise).
**Speculative, tagged:** §1.3(ii), §2.4, §2.5, §4.5, §5 candidate (iii).

**Honest failures.** (1) We did not construct a "tropical characteristic ideal": §4.4
suggests any such object needs irrational slopes, i.e. lives outside f.g. Λ-modules, and
we have no candidate category. (2) We did not prove Γ-equivariance in any twisted sense
that would let character-by-character analysis apply to the *tropical* operator — the
min does not act diagonally in the character basis, and we found no substitute. (3) No
3-adic L-value identification for λ∞ (searched, none found, none invented). (4) The
(φ,Γ)/U_p shape remains a shape: we exhibit no cyclotomic descent datum. (5) γ₁₈ used at
4-decimal precision from the run report; the local eigenvector file is incomplete and
the value is not independently extracted — all k = 18-dependent fits were therefore also
run without k = 18 (§4, window 11–17: same conclusions, slightly weaker).

**Next moves.** (i) k = 19–20 on PSC: the §5 pre-registered discriminators; (ii) compute
the oscillation measures ν_k from the stored eigenvectors and test weak-* convergence /
absolute continuity (the algebraic-side candidate (ii)); (iii) attempt the
exchange-of-limits lemma making the limit game value well-posed ([LO] §3.3(d)) — under
(B) this is the definition of the new invariant; (iv) certify k = 15 (extend
`certify.py`; eigenvector in hand) so the record theorem advances to x^{0.8812};
(v) Fourier-analyze c_k in the character basis of Γ/Γ_{k−1}: Prop 3.1 predicts the
conductor-3^j mass profile decays like q^j — a direct, currently untested, sharpening
of Conjecture 5.3.

**Reproduction.** `experiments/kl/tropical_iwasawa_checks.py`
(A/B: extraction + oscillation identity at k = 12..17 — needs the eigenvector files;
C: all fits/windows; D + `spectrum_theorem_check`: Theorem 2.1 verification, no large
files needed). Eigenvectors: `experiments/kl/eigvecs/eigvec_k{12..17}.npy`.
Saved paper: `papers/dion-lei-ray-vallieres-2022-iwasawa-invariants-multigraphs.pdf`.

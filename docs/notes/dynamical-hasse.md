# Collatz cycles as a dynamical local–global problem

2026-07-20. Status: **structural note — foundations proved, framing precise, program
speculative at the top.** Every claim below is tagged one of **[PROVED]** (proof
in this note or verified citation), **[PROVABLE-LOOKING]** (sketch given, no gap
expected), **[CONJECTURAL]** (precise statement, open), **[SPECULATIVE]**
(directional). Literature verified by direct fetch; PDFs saved under `papers/`
(paths in §9). Core identities verified by brute force (parity consistency and
periodicity for all words K ≤ 10; the translation lemma for all words K ≤ 12; the
(11,7)/139 hit is exactly one necklace among 330 words; unit stratum exhaustive to
K, L ≤ 200): `experiments/dynamical-hasse/verify_dynamical_hasse.py`. Context:
docs/LANDSCAPE.md (cycle bounds, 2-adic rigidity), docs/SMELL.md item on the
(2,3)-solenoid, docs/CRACKS.md #6 (solenoid windows).

**One-line summary.** A nontrivial Collatz cycle is an integral-and-positive point
in a family of zero-dimensional Q-schemes indexed by binary necklaces; every local
test passes at every place individually **[PROVED]**, all known exclusions
(Steiner → Simons–de Weger → Hercher) are computations at the archimedean place
alone **[PROVED]**, and the "obstruction group" the mandate asks for exists in a
degenerate canonical form: the cycle class `W(v) mod (2^K − 3^L)` viewed as a
torsion point on the (2,3)-solenoid, whose vanishing *is* integrality. The real
question — made precise in §6 — is whether nonvanishing admits *structured
certificates* (Skolem-type moduli / spectral gaps of a finite affine monodromy),
and that is where this problem separates from all existing dynamical local–global
frameworks, none of which handles correspondences or integrality.

---

## 1. Foundations, corrected: periodic points of T on ℤ₂

T: ℤ₂ → ℤ₂, T(x) = x/2 (x even), (3x+1)/2 (x odd). Parity-vector map Q_∞
conjugates T to the full one-sided 2-shift; its inverse Φ is a homeomorphism of
ℤ₂ (Lagarias 1985, Theorem L: "Φ is continuous, one-one, onto, and
measure-preserving on ℤ₂" — verified against the paper) **[PROVED, cited]**.

**Notation (fixed for the whole note).** A *word* is v = (v₀,…,v_{K−1}) ∈ {0,1}^K,
K ≥ 1; L := Σᵢ vᵢ; the *Pillai form* Λ(v) := 2^K − 3^L (never 0 for K ≥ 1);
c_i(v) := #{j > i : v_j = 1}; the *Böhm–Sontacchi weight*

  W(v) := Σ_{i=0}^{K−1} vᵢ · 2^i · 3^{c_i(v)}  ∈ ℤ_{≥0}.

The branch composite along v is the affine map T_v(x) = (3^L x + W(v)) / 2^K,
with unique fixed point in ℚ (hence in every ℚ_p and ℝ):

  **x_v := W(v) / Λ(v).**   (cycle equation; Böhm–Sontacchi 1978, ccchallenge-audited)

**Lemma 1 (parity consistency is automatic). [PROVED]**
For every word v: x_v ∈ ℤ₂, the T-parity of x_v is v₀, T(x_v) = x_{σv} (σ = left
rotation), and hence T^K(x_v) = x_v with parity word exactly v^∞.
*Proof.* Λ(v) is odd, so x_v ∈ ℤ₂. Mod 2, W(v) ≡ v₀·3^{c₀} ≡ v₀ (only the i = 0
term is odd) and Λ(v) ≡ 1, so parity(x_v) = v₀: the branch T_{v₀} is the one T
actually applies. T_{v₀}(x_v) is fixed by T_{σv} (conjugation identity
T_{σv}∘T_{v₀} = T_{v₀}∘T_v), and affine fixed points are unique, so
T(x_v) = x_{σv}. Induct. ∎

**Theorem 1 (what the periodic points actually are). [PROVED]**
(a) Per(T) := {x ∈ ℤ₂ : T^K x = x, some K ≥ 1} = {x_v : v a word}. The map
v ↦ x_v induces a bijection {primitive necklaces} ↔ {T-cycles in ℤ₂}.
(b) Per(T) ⊂ ℚ_odd := ℚ ∩ ℤ₂ (odd-denominator rationals), and Per(T) is a
countable dense subset of ℤ₂ (density: conjugacy to the shift).
(c) EvPer(T) (eventually periodic points) ⊆ ℚ_odd: an eventually periodic point
maps into Per(T) ⊂ ℚ under some T^m, and both branches of T are invertible affine
maps with coefficients in ℤ[1/6], so preimages of rationals are rational, with
denominators staying odd.
(d) The reverse inclusion ℚ_odd ⊆ EvPer(T) is **open**: it is Lagarias's
Periodicity Conjecture (every x ∈ ℚ_odd has eventually periodic parity vector),
which restricted to ℤ_{≥1} is exactly the no-divergent-orbits half of Collatz.

**Correction to the mandate.** The tasking stated "T-periodic points in ℤ₂ are
exactly rationals with odd denominator (Lagarias 1985)". That is **false as an
equality** in both readings: 7 ∈ ℚ_odd is eventually periodic but not periodic,
and whether *every* element of ℚ_odd is even eventually periodic is the open
Periodicity Conjecture. The true statements are Theorem 1(a)–(d). What survives,
and is what the linkage needs: **a nontrivial integer cycle = a point x_v of the
countable explicit family {W(v)/Λ(v)} that is integral at every finite place and
lands in the positive archimedean window.**

Known rational integer cycles of T on ℤ (Lagarias's finite-cycles conjecture:
this list is complete) — all five verified against the formulas above:

| cycle | word v | K | L | Λ = 2^K − 3^L | W(v) | x_v = W/Λ |
|---|---|---|---|---|---|---|
| {0} | 0 | 1 | 0 | 1 | 0 | 0 |
| {−1} | 1 | 1 | 1 | −1 | 1 | −1 |
| {1, 2} | 10 | 2 | 1 | 1 | 1 | 1 |
| {−5, −7, −10} | 110 | 3 | 2 | −1 | 5 | −5 |
| {−17, …, −34} (11 elts) | 11110111000 | 11 | 7 | −139 | 2363 = 17·139 | −17 |

(W(11110111000) = 3⁶ + 2·3⁵ + 4·3⁴ + 8·3³ + 32·3² + 64·3 + 128 = 2363, checked.)

## 2. The algebraic avatar is a correspondence, not a morphism

T is **not** a morphism of any ℚ-variety: the parity branch choice is a 2-adic
clopen condition, not algebraic. The algebraic object is the correspondence

  **C ⊂ 𝔸¹ × 𝔸¹, C : (2y − x)(2y − 3x − 1) = 0,**

union of two graphs Γ₀: y = x/2 and Γ₁: y = (3x+1)/2, each an affine automorphism
over ℤ[1/6]. Two structural facts:

**Lemma 2 (integrality forces determinism at p = 2). [PROVED]**
On ℤ₂ (equivalently, on ℤ), from each point exactly one branch of C stays in ℤ₂:
from odd n, n/2 ∉ ℤ₂; from even n, (3n+1)/2 ∉ ℤ₂. The unique ℤ₂-integral forward
selection of C is T. On ℤ_p (p odd) both branches preserve ℤ_p and the
correspondence is a full binary tree — no canonical dynamics. *So the dynamical
selection itself is the local condition at 2, and the Diophantine content of
cycles lives at the other places.*

**Consequence.** Every existing dynamical local–global framework (§5) takes a
*morphism* φ: X → X over a global field as input. Collatz does not provide one;
it provides a correspondence plus a 2-adic selection rule. This is not a cosmetic
mismatch — it relocates the problem from "rationality of orbit intersections"
(where Brauer–Manin lives) to "integrality and positivity within an explicit
rational family" (where, at present, only counting and Baker bounds live).

For K ≥ 1 define the **cycle scheme** 𝒞_K := the closed subscheme of 𝔸^K over ℤ
cut out by the K cyclic step conditions (2n_{i+1} − n_i)(2n_{i+1} − 3n_i − 1) = 0
(indices mod K). Over ℚ, 𝒞_K is zero-dimensional and *every point is rational*:
its points are exactly the orbit tuples (x_v, x_{σv}, …, x_{σ^{K−1}v}) for words
v ∈ {0,1}^K **[PROVED** — branch-resolve into 2^K affine linear systems, each with
unique solution by Lemma 1; branch-degeneracies (both factors vanish) occur only
at overlapping solutions and do not add points**]**. So the classical Hasse
principle for rational points on 𝒞_K holds trivially and carries no content.
The content is integral and signed.

## 3. The cycle problem, place by place

**Theorem 2 (the local dictionary). [PROVED]** Let v be a word, K ≥ 1, L ≥ 1
(L = 0 forces x_v = 0). Then:

- **(p = 2)** x_v ∈ ℤ₂ always (Λ odd), and by Lemma 1 the T-orbit of x_v in ℤ₂ is
  a genuine K-cycle realizing v. *The local condition at 2 is void: every word is
  2-adically realized.*
- **(p = 3)** x_v ∈ ℤ₃ always (Λ ≡ 2^K ≢ 0 mod 3, W ∈ ℤ). *Void.* (T itself does
  not act on ℤ₃; the branch composite does.)
- **(p ≥ 5)** x_v ∈ ℤ_p ⟺ v_p(W(v)) ≥ v_p(Λ(v)); nontrivial only for the finitely
  many p | Λ(v), a sporadic, (K,L)-dependent set of primes. Jointly over all
  finite p: x_v ∈ ℤ ⟺ **Λ(v) | W(v)** (the necklace congruence).
- **(∞, sign)** W(v) > 0, so x_v > 0 ⟺ Λ(v) > 0 ⟺ 2^K > 3^L.
- **(∞, size)** If x_v ∈ ℤ_{>0} with cycle minimum x_min, then multiplying
  n_{i+1} = (3nᵢ+1)/2 resp. nᵢ/2 around the cycle gives 2^K = Π_{odd steps}(3 + 1/nᵢ),
  hence
    0 < K·log 2 − L·log 3 ≤ L·log(1 + 1/(3·x_min)) < L/(3·x_min).
  With Barina's verification (all n < 2^71 reach 1; LANDSCAPE.md), any nontrivial
  positive cycle has x_min > 2^71, so **0 < K log 2 − L log 3 < L·2^{−71}/3**:
  K/L must approximate log 3/log 2 from above to convergent-beating quality.
- **(∞, transcendence counter-bound)** Linear forms in logarithms (Rhin, as used
  in Simons–de Weger Lemma 12, their normalization): the same quantity
  K log 2 − L log 3 is bounded *below* by exp(−13.3(0.46057 + ln L)). The pincer
  of the last two bullets, refined by continued fractions of log 3/log 2 and the
  m-block structure of words, is *the entire content* of the exclusion literature:
  Steiner 1977 (m = 1), Simons 2005 (m = 2), Simons–de Weger 2010 (m ≤ 75),
  Hercher 2023 (m ≤ 91, and L > 1.375×10^11, K ≥ 2.18×10^11 for any nontrivial
  cycle).

**Proposition 3 (the exclusion literature is archimedean). [PROVED, by audit]**
The Steiner/Simons–de Weger/Hercher proofs use, besides x ∈ ℤ only through
"x ≥ verified bound", *no* condition at any finite place: their announced method
is (1) cycle system → linear form in two logs, (2) Baker-type lower bound,
(3) continued-fraction / lattice reduction, (4) computation. Verified directly in
the Simons–de Weger paper (papers/simons-deweger-2010-m-cycles-v144.pdf: the
four-step method at their §"Conditions on K and m from a linear form in
logarithms" and §"…from continued fractions"; the only congruence in the paper is
an index convention). The sporadic primes p | Λ — the only finite places with
content by Theorem 2 — are **unused in the entire exclusion literature**.

**Worked closed form (Steiner's stratum).** For the 1-block word v = 1^L 0^{K−L}:
W(v) = 3^L − 2^L (telescoping), so a 1-cycle exists iff
(3^L − 2^L)/(2^K − 3^L) ∈ ℤ_{>0}. Steiner's theorem ("only {1,2}") is thus the
statement that a specific two-term S-unit divisibility never happens nontrivially
— proved, then and since, only through the archimedean place.

## 4. The dynamical Hasse principle for C, stated precisely

Let 𝒞_K° := 𝒞_K minus the components of the five known cycles and their
rotations/repetitions. Call a component (word) v *windowed-integral at p* if
x_v ∈ ℤ_p (finite p), and *at ∞* if x_v > 2^71. Note (Theorem 2 + Barina) a
nontrivial positive integer cycle = a component of some 𝒞_K° windowed-integral
at every place — and conversely, since Λ | W with Λ > 0 makes x_v a positive
integer cycle, which verification forces above 2^71.

**Proposition 4 (every place passes separately). [PROVED]**
For every K ≥ 194 and every place p of ℚ, 𝒞_K° has a component windowed-integral
at p.
*Proof.* p = 2, 3: Theorem 2, any nontrivial word. p ≥ 5: p | Λ(K,L) forces
3^L ≡ 2^K (mod p), which pins L to a single residue class mod ord_p(3), and
ord_p(3) ≥ 2 for p ≥ 5 (ord = 1 ⟺ p | 2); so the bad L form a progression of
density ≤ 1/2 in {1,…,K−1} and a good nontrivial weight L exists; every word of
that weight is p-integral. ∞: take the Steiner
necklace at weight L = 122 ≤ K·log2/log3 (exists for K ≥ 194, and 3^122 < 2^K
gives Λ > 0): its maximal element is 2^{K−L}(3^L−2^L)/Λ ≈ (3/2)^L > 2^71. ∎

**Proposition 5 (no finite set of places obstructs). [PROVABLE-LOOKING]**
For every finite set S of places there are infinitely many K and nontrivial words
v windowed-integral at *all* places in S simultaneously.
*Sketch.* Choose (K,L) with 0 < K log2 − L log3 small (near-convergents; infinitely
many by equidistribution of K·log₂3 mod 1) subject to the finitely many congruence
conditions "p ∤ Λ(K,L)" for p ∈ S-finite; these are conditions on (K mod ord_p(2),
L mod ord_p(3)) and are compatible with the Diophantine condition by Weyl
equidistribution of (K log₂3 mod 1, K mod M). Then every word of weight L is
integral at S-finite, and the Steiner necklace passes at ∞ as in Prop. 4. The
only gap to [PROVED] is the routine joint-equidistribution bookkeeping. ∎

**The Hasse-principle question (the precise deliverable).**

> **DHP(C).** For which K does 𝒞_K° have components windowed-integral at every
> place separately (true for all K ≥ 194, Prop. 4) — indeed adelically, i.e. one
> choice of component per place — while **no single component** is
> windowed-integral at all places simultaneously?
>
> The Collatz cycle conjecture ⟺ DHP-failure for **every** K (equivalently: the
> necklace congruence Λ(v) | W(v) has no solution with Λ(v) > 1 and Λ(v) > 0).

Three structural remarks, each precise:

1. **The unit stratum trivializes the principle. [PROVED]** |Λ| = 1 makes
   integrality automatic at all finite places (H90-degenerate case: unit modulus).
   |2^K − 3^L| = 1 ⟺ (K,L) ∈ {(1,0),(1,1),(2,1),(3,2)} — classical (Levi ben
   Gerson 1342; two-line proof: for K ≥ 3 reduce mod 8, forcing 3^L ≡ 1 (8), L = 2M,
   then 2^K = (3^M−1)(3^M+1) forces M = 1; K ≤ 2 by inspection). At these four
   (K,L), *every* word yields an integer cycle, and these are exactly the first
   four known cycles. **Four of the five known integer cycles exist because the
   Pillai form is a unit — the Hasse question is vacuous there.**
2. **The fifth cycle is a genuine congruence hit, on the negative side. [PROVED]**
   (K,L) = (11,7): Λ = −139, and the necklace 11110111000 satisfies 139 | W = 2363.
   K/L = 11/7 is only a *semiconvergent* of log 3/log 2 (mediant of 3/2 and 8/5) —
   enough on the negative side because the negative window is weak (|x| ≥ 1-ish,
   little verification), while the positive window demands the extreme
   approximation quality of Theorem 2(∞, size). **Any obstruction-theoretic
   explanation of "no positive cycles" must be signed: it must permit the (11,7)
   negative hit.** Positivity — an archimedean open condition invisible to any
   finite-place cohomology — is irreducibly part of the problem.
3. **No confirmed DHP failure is known anywhere.** On the negative side at (11,7)
   locals pass and a global exists (principle *holds* non-vacuously). Heuristics
   (§7) predict failures abound in both signs; proving even one instance "locals
   pass adelically, no global word" appears to be exactly as hard as producing
   cycle exclusions beyond the archimedean method.

## 5. Literature audit (task 1): what exists, what applies

All fetched/verified 2026-07-20; PDFs in `papers/` (§9).

- **Hsia–Silverman 2009**, *On a dynamical Brauer–Manin obstruction* (J. Théor.
  Nombres Bordeaux 21, arXiv:0801.3045). Defines, for a **morphism** φ: X → X of
  a projective variety over a number field and V ⊂ X: "V(K) Brauer–Manin
  unobstructed for φ" iff O_φ(P) ∩ V(K) = C(O_φ(P)) ∩ V(𝔸_K) (adelic orbit
  closure), following Scharaschkin. Proves unobstructedness for power maps on ℙ²
  (V a torus translate, or a line with preperiodic-coordinate P) and for
  multiplication maps on abelian varieties, via Bang–Zsigmondy primitive divisors.
  **Does not apply:** needs a morphism; detects rationality, not integrality; our
  candidate points are all rational already.
- **Silverman–Voloch 2009**, *A local-global criterion for dynamics on ℙ¹* (Acta
  Arith. 137, arXiv:0806.2580). For rational maps of degree ≥ 2 on ℙ¹ and finite
  V: orbit meets V globally iff it does adelically (a "finite-descent" flavor of
  the above). Same two mismatches.
- **Krumm 2016**, *A local–global principle in the dynamics of quadratic
  polynomials* (Int. J. Number Theory 12, arXiv:1508.03830). The model theorem
  shape for *periodic points*: for quadratic f/K, "period-n point in every K_p ⟹
  period-n point in K" holds for n ≤ 3; at most finitely many failures for
  n ∈ {4,5}; over ℚ, for n = 4 the local hypothesis fails at infinitely many p
  for every f. **Instructive inversion:** for x²+c the local–global tension sits
  already at *rationality* of periodic points, and local solvability often fails;
  for Collatz, Theorem 2 shows local solvability holds at every single place —
  the opposite extreme — and the whole question migrates to simultaneous
  integrality. No correspondence version exists.
- **Benedetto–Ghioca–Hutz–Kurlberg–Scanlon–Tucker 2013**, *Periods of rational
  maps modulo primes* (Math. Ann. 355, arXiv:1107.2816). If α ∉ O_φ(β) globally,
  a positive density of primes detects this mod p. The "local detection of global
  non-membership" paradigm; proofs via p-adic uniformization of *morphisms*. A
  Collatz analogue ("if v never yields an integer cycle, a positive density of
  p | Λ-type moduli certifies it") would be precisely a Skolem-type certificate
  (§6); nothing of the sort is known for correspondences.
- **Sun 2015**, *The Brauer–Manin–Scharaschkin obstruction for subvarieties of a
  semi-abelian variety and its dynamical analog* (J. Number Theory,
  sciencedirect.com/science/article/pii/S0022314X14002546). Closest ambient
  geometry: our problem is multiplicative — (2^K, 3^L) ranges over a rank-2
  sub-semigroup of 𝔾_m²(ℚ) — and Sun's zero-dimensional-subvariety setting is the
  semiabelian home of such questions. Still: endomorphisms of semiabelian
  varieties, rational points. (No arXiv version located; PDF not saved — flagged.)
- **Ingram**, *Canonical heights for correspondences* (arXiv:1411.1041). Height
  machinery (Call–Silverman) extends to polarized correspondences — so the
  *height* half of arithmetic dynamics survives the morphism→correspondence
  generalization. **Verified gap:** no local–global / obstruction theory for
  correspondences was found in any search performed (dynamical Brauer–Manin +
  correspondences, local-global + correspondences, 2023–2026 arXiv sweeps).
  Together with the Collatz novelty check (searches for Collatz × {Hasse
  principle, Brauer–Manin, adelic} return nothing relevant), the framing of this
  note appears to be unoccupied ground. [Verified-absence caveat: absence of
  evidence in keyword search.]
- **Skolem's conjecture / Bertók–Hajdu 2016**, *A Hasse-type principle for
  exponential Diophantine equations and its applications* (arXiv:1407.6499,
  Acta Arith. lineage with parts II, III). Skolem's conjecture: an unsolvable
  purely exponential equation a₁b₁^{α} + … = c is already unsolvable modulo some
  single modulus m. Bertók–Hajdu prove a density version ("almost all" such
  equations obstructed by a finite modulus, via Carmichael-λ constructions) and
  give an effective modulus-search algorithm. **This — not Brauer–Manin — is the
  correct local–global family for Collatz cycles:** the cycle condition for a
  fixed block shape (m-cycle profile) is a polynomial–exponential equation in the
  block exponents, e.g. Steiner's stratum x·(2^K − 3^L) = 3^L − 2^L. (Ours has
  the variable coefficient x, one step outside the proven Bertók–Hajdu classes —
  honest gap.)
- **Kontorovich 2013**, *From Apollonius to Zaremba: local-global phenomena in
  thin orbits* (arXiv:1208.5460). The thin-orbit local–global philosophy
  (Apollonian curvatures, Zaremba): exponentially thin orbit sets, family of
  moduli, "congruence obstructions + almost-local-global via expansion/circle
  method". §6 shows Collatz cycles fit this template exactly — with the necklace
  set as the thin set and Aff(ℤ/Λ) as the congruence quotients.

**Verdict on task 1.** Obstruction frameworks exist for *orbits of morphisms
meeting subvarieties* (Hsia–Silverman; Silverman–Voloch; Sun) and for *existence
of periodic points of polynomials* (Krumm), and mod-p detection theorems exist
for morphisms (BGKST). **None applies to correspondences, and none sees
integrality-plus-positivity of an already-rational family** — the two defining
features of the Collatz cycle problem. The adjacent frameworks that *do* fit are
non-cohomological: Skolem-type moduli certificates and thin-orbit
expansion/counting.

## 6. The obstruction object (task 3): monodromy mod Λ and the solenoid

The sharpest structure found. Fix (K, L), Λ = Λ(K,L), |Λ| > 1, and work in
ℤ/Λ := ℤ/|Λ|ℤ. Since 2, 3 are units mod Λ, both branches are *bijections* of ℤ/Λ:

  t₀(x) = x/2,  t₁(x) = (3x+1)/2  ∈ Aff(ℤ/Λ).

**Theorem 3 (translation lemma and trace formula). [PROVED]**
For any word v of shape (K,L), using 3^L ≡ 2^K (mod Λ):

  t_v := t_{v_{K−1}} ∘ ⋯ ∘ t_{v₀} = ( x ↦ x + W(v)·2^{−K} )  on ℤ/Λ —

a *translation*. Hence:
(a) x_v ∈ ℤ ⟺ Λ | W(v) ⟺ **t_v = id on ℤ/Λ** ⟺ t_v has a fixed point mod Λ
   (translations act freely otherwise);
(b) with C₀, C₁ the permutation operators of t₀, t₁ on ℓ²(ℤ/Λ),

   **N(K,L) := #{v of shape (K,L) : Λ | W(v)} = |Λ|^{−1} · [u^L] tr( (C₀ + u·C₁)^K ).**

*Proof.* T_v(x) = (3^L x + W)/2^K ≡ (2^K x + W)/2^K = x + W·2^{−K} (mod Λ). Each
word contributes tr(perm matrix of t_v) = |Λ| if t_v = id, else 0; expanding
(C₀ + uC₁)^K collects words by weight. ∎

So the *entire* finite-place content of the cycle problem is the word problem
("which words evaluate to the identity") in the finite **monodromy group**
G_Λ := ⟨t₀, t₁⟩ ≤ Aff(ℤ/Λ) — the mod-Λ shadow of the global affine group
⟨x/2, (3x+1)/2⟩ ≅ ℤ[1/6] ⋊ ⟨2,3⟩ ≤ Aff(ℚ). And:

- **Spectral decomposition. [PROVED, elementary]** ℓ²(ℤ/Λ) splits under
  (C₀ + uC₁) into blocks indexed by orbits of the unit subgroup ⟨2,3⟩ ≤ (ℤ/Λ)^×
  acting on the dual group. The trivial-character block contributes the main term
  C(K,L)/|Λ| to N(K,L); all deviation lives in the nontrivial blocks, whose sizes
  are the multiplicative orders |⟨2,3⟩ mod d| over divisors d | Λ. (Same
  order-of-2-and-3 data that governs the determinants in Karras–de Weger 2026,
  arXiv:2601.15463 — the closest existing mod-N study; they analyze the graph of
  T mod N, not the word-trace over ℤ/Λ(K,L), and state they see no route to the
  conjecture from it.)
- **The obstruction group, in the only precise sense found.** Rotation acts by
  W(σv) ≡ 2^{−1}3^{v₀}·W(v) (mod Λ) [PROVED: from T(x_v) = x_{σv}], so the
  **cycle class**
    obs(v) := [ W(v) mod Λ(v) ] ∈ (ℤ/Λ)/⟨2,3⟩
  is a well-defined invariant of the T-cycle of x_v in ℤ₂, and **obs(v) = 0 ⟺
  the cycle is integral**. Equivalently (solenoid form): with
  S := (ℝ × ℚ₂ × ℚ₃)/Δ(ℤ[1/6]) the (2,3)-solenoid (SMELL #9, CRACKS #6), the point
  ξ_v := [x_v·(1,1,1)] lies in the Λ-torsion S[Λ] ≅ ℤ[1/6]/Λ ≅ ℤ/Λ, corresponds
  to W(v) mod Λ, and **ξ_v = 0 ⟺ x_v ∈ ℤ[1/6] ⟺ x_v ∈ ℤ** [PROVED — the
  denominator of x_v divides Λ, coprime to 6]. Candidate cycles are canonical
  torsion points on the solenoid; integer cycles are their vanishing locus; the
  five known cycles are the classes forced to vanish by |Λ| = 1, plus one
  sporadic vanishing at Λ = −139.
- **Honesty about degeneracy.** This obstruction class is *canonical and
  computable but tautological per word*: its vanishing is the definition of
  integrality, not an explanation. The non-tautological question — the real task-3
  question — is **uniformity**: what structure forces obs(v) ≠ 0 for *all*
  nontrivial words in the positive window? Two precise candidate mechanisms:

**Q1 (Skolem-type certificates). [CONJECTURAL, computable]** For a fixed block
shape (say 1-cycles), does there exist a *single modulus* M with: the system
"x·(2^K − 3^L) = 3^L − 2^L mod M, with (K, L) mod (ord_M(2), ord_M(3))" having no
solutions beyond the images of the known ones? Skolem's conjecture (and the
Bertók–Hajdu density theorem, for the purely exponential class) predicts yes when
no global solutions exist. **Concrete experiment proposed:** run the Bertók–Hajdu
modulus search on Steiner's stratum — a certificate would be the first
*non-archimedean* proof of "no nontrivial 1-cycles", i.e. the first exclusion in
the literature located at finite places. This is the cheapest sharp test of
whether the local–global reformulation buys anything.

**Q2 (spectral gap / equidistribution). [CONJECTURAL]** The character-sum decay
  | tr of nontrivial blocks in Theorem 3(b) | = o(C(K,L)/|Λ|)
uniformly over near-convergent (K,L), would give N(K,L) = C(K,L)/|Λ|·(1+o(1)) and
— combined with the archimedean pincer of Theorem 2 — "expected zero" nontrivial
positive cycles (§7). This is exactly a *twisted transfer-operator gap* for the
two-generator affine walk mod Λ: the same object Tao's Syracuse analysis controls
when the modulus is 3^n (Fourier decay of Syracuse random variables,
arXiv:1909.03562) — there conductor 3^n, here conductor Λ(K,L) = 2^K − 3^L.
The **obstruction characters** — where decay can fail — are computable: divisors
d | Λ with |⟨2,3⟩ mod d| anomalously small (short dual orbits ⇒ large blocks with
no mixing). Their absence for a given (K,L) is a finite computation. This is the
precise sense in which "the vanishing of a computable obstruction would explain
why W(v)/Λ is a positive integer only for the trivial word": vanishing of
low-order divisors ⇒ square-root cancellation heuristics ⇒ empty window.
**Q3 (thin-orbit packaging). [SPECULATIVE]** Necklace words of shape (K,L) form
an exponentially thin set (2^{0.95K} of 2^K) mapping to Aff(ℤ/Λ); "no positive
cycles" is an empty-intersection statement between this thin set's
identity-fiber and the archimedean window — structurally an
Apollonius/Zaremba-type local–global problem (Kontorovich), suggesting
expansion/circle-method technology rather than cohomology. The S-adelic
equidistribution of ⟨2,3⟩-orbits (arXiv:1303.1661, already in papers/) is the
zero-th input of this program.

**Reformulating the known exclusions (task 3 wording).** In this packaging:
Steiner/Simons–de Weger/Hercher prove ξ_v ≠ 0 for all structured v (m ≤ 91
blocks) by *archimedean* means: the linear-forms-in-logs lower bound is a
quantitative statement that the real coordinate of (a lift of) ξ_v stays far from
the lattice ℤ[1/6] relative to the window — a lower bound on an archimedean
distance-to-zero of the obstruction class. They are local computations at ∞ of a
global class; what global structure they are shadows of is exactly Q1/Q2: the
finite-place components of the same class, which no one has made do any work.
That asymmetry — a century of archimedean-only certificates for a class that has
components at every place — is the cleanest formulation of what this linkage
proposes to change.

## 7. The heuristic backdrop (why an obstruction may not exist)

**[HEURISTIC/CONJECTURAL, stated for discipline.]** Under equidistribution
(Q2 holding), the expected number of nontrivial positive cycle words of shape
(K,L) is ≈ C(K,L)/|Λ|, supported on the near-convergent strip of Theorem 2:
with L/K ≈ log 2/log 3 = 0.63093, C(K,L) ≈ 2^{H(0.63093)·K} = 2^{0.94992·K},
while |Λ| ≥ 2^K·exp(−13.3(0.46 + ln L)) (Rhin), giving

  E(K) ≲ K^{13.3} · 2^{−0.05008·K},

summable, with the sum over the Hercher-admissible range K ≥ 2.18×10^11 smaller
than 2^{−10^10}. Two honest consequences: (i) heuristics predict *scarcity
without structure* — the truth of the cycle conjecture needs no conspiracy and
hence possibly no obstruction group at all, unlike classical Brauer–Manin
failures which are structured events; (ii) precisely for that reason the
realistic mathematical products of this linkage are the *certificate* questions
Q1/Q2 (finite, falsifiable, new-place-content), not a Ш-analogue. A genuine
obstruction group would have to break equidistribution on the positive window
while sparing the (11,7) negative hit — no candidate mechanism is known, and §7's
convergence is evidence against its existence.

## 8. Claim ledger

| # | Claim | Tag |
|---|---|---|
| 1 | Lagarias 1985 Thm L (Φ homeo of ℤ₂); parity conjugacy | PROVED (cited, fetched) |
| 2 | Mandate's "periodic pts = ℚ_odd" corrected: Thm 1(a)–(d); converse = open Periodicity Conj. | PROVED / OPEN as stated |
| 3 | Lemma 1 (parity consistency automatic), Lemma 2 (integrality forces determinism at 2) | PROVED |
| 4 | Theorem 2 local dictionary; places 2, 3 void; finite content only at p | Λ; ∞ = window | PROVED |
| 5 | Baker/Rhin bounds = quantitative archimedean condition; exclusion literature purely archimedean | PROVED (audit of SdW; Hercher same scheme) |
| 6 | 𝒞_K zero-dim, all points rational; rational HP trivial | PROVED |
| 7 | Prop 4 (every place passes separately, K ≥ 194) | PROVED |
| 8 | Prop 5 (no finite set of places obstructs) | PROVABLE-LOOKING |
| 9 | Unit stratum = Gersonides |2^K−3^L| = 1 ⟺ 4 of 5 known cycles; fifth = Λ = −139 hit | PROVED |
| 10 | DHP(C) statement; cycle conjecture ⟺ DHP fails for every K | PROVED (equivalence) |
| 11 | Theorem 3: t_v = translation by W·2^{−K}; trace formula for N(K,L) | PROVED |
| 12 | obs(v) ∈ (ℤ/Λ)/⟨2,3⟩ ≅ solenoid torsion class ξ_v; vanishing ⟺ integrality | PROVED |
| 13 | Q1 Skolem certificate for Steiner stratum exists | CONJECTURAL (computable experiment) |
| 14 | Q2 spectral gap / character decay mod Λ(K,L); obstruction characters = low-order divisors | CONJECTURAL |
| 15 | Q3 thin-orbit circle-method program | SPECULATIVE |
| 16 | E(K) ≲ K^{13.3}2^{−0.05K}; no obstruction needed heuristically | HEURISTIC |
| 17 | No existing framework handles correspondences or integrality; no prior Collatz×Hasse work | VERIFIED-ABSENCE (search) |

## 9. References (fetched 2026-07-20; local paths)

- Lagarias 1985, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92, 3–23. HTML: cecm.sfu.ca/organics/papers/lagarias (Thm L verified at node10). Bibliographic entry verified in papers/lagarias-2003-annotated-bibliography-I.pdf.
- Böhm–Sontacchi 1978 cycle equation: ccchallenge-audited (github.com/tcosmo/BohmSontacchi1978_lean; see LANDSCAPE.md).
- Hsia–Silverman 2009, arXiv:0801.3045 → papers/hsia-silverman-2009-dynamical-brauer-manin-0801.3045.pdf
- Silverman–Voloch 2009, arXiv:0806.2580 → papers/silverman-voloch-2009-local-global-p1-0806.2580.pdf
- Krumm 2016, arXiv:1508.03830 → papers/krumm-2016-local-global-quadratic-dynamics-1508.03830.pdf
- Benedetto–Ghioca–Hutz–Kurlberg–Scanlon–Tucker 2013, arXiv:1107.2816 → papers/benedetto-ghioca-hutz-kurlberg-scanlon-tucker-2013-periods-mod-primes-1107.2816.pdf
- Benedetto et al. 2019 survey, arXiv:1806.04980 → papers/benedetto-etal-2019-current-trends-arithmetic-dynamics-1806.04980.pdf
- Sun 2015, J. Number Theory (S0022314X14002546) — no arXiv found, PDF not saved (flagged).
- Ingram, arXiv:1411.1041 → papers/ingram-2019-canonical-heights-correspondences-1411.1041.pdf
- Bertók–Hajdu, arXiv:1407.6499 → papers/bertok-hajdu-2016-hasse-principle-exponential-diophantine-1407.6499.pdf (parts II: arXiv:2105.00415; III: S0022314X21000500)
- Kontorovich 2013, arXiv:1208.5460 → papers/kontorovich-2013-apollonius-zaremba-thin-orbits-1208.5460.pdf
- Simons–de Weger 2010 → papers/simons-deweger-2010-m-cycles-v144.pdf; Hercher 2023 → papers/hercher-2023-no-collatz-m-cycles-91-2201.00406.pdf
- Karras–de Weger 2026, arXiv:2601.15463 → papers/karras-deweger-2026-modular-collatz-graph-determinants.pdf
- Tao 2019, arXiv:1909.03562 (Fourier decay of Syracuse random variables — Q2's 3^n-conductor case).
- Adelic ⟨2,3⟩ orbit density: arXiv:1303.1661 → papers/adele-semigroup-orbit-density-2013.pdf
- Harari–Voloch, *The Brauer–Manin obstruction for integral points on curves* (imo.universite-paris-saclay.fr/~david.harari/articles/dhvol.pdf) — integral-BM vocabulary anchor, not used quantitatively.

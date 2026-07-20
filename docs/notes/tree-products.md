# Collatz on the (2,3) tree product: the affine lattice Λ, its arithmetic quotient, and the operator a spectral gap would have to live on

2026-07-20. Status: geometry made precise and mostly **proved** (elementary/standard,
proofs or sketches included); the spectral question sharpened to a named conjecture
(Conjecture A) plus two proved no-go lemmas that kill the naive versions. Companion
to `two-bases.md` (base-2/base-3 certificate disjointness), SMELL.md #1 (KL/Perron),
SMELL.md bubble (Potapov–Semukhin), CRACKS.md crack 6 (solenoid).

**Tag legend:** [PROVED] = proof included or standard-with-citation; [PROVABLE]
= we see the proof route, not written; [CONJ] = precise open statement; [SPEC] =
speculative framing. Literature: [VER] = verified this session (PDF saved to
`/Users/simon/Desktop/COLLATZ/papers/`), [CLASSICAL] = standard, cited from
memory, low risk, not re-fetched.

---

## 0. Executive summary

1. [PROVED] The group Λ = Z[1/6]^* ⋉ Z[1/6] of affine maps x ↦ ±2^a 3^b x + c
   contains both Collatz branch maps. It acts properly discontinuously and
   cocompactly on a *weighted horospherical product* W ⊂ 𝒯₂ × 𝒯₃ × H², where
   𝒯₂, 𝒯₃ are the Bruhat–Tits trees of Q₂ (3-regular) and Q₃ (4-regular) and the
   weights are (log 2, log 3, 1). The archimedean factor is *forced*: on 𝒯₂ × 𝒯₃
   alone the action is non-proper (Lemma 1.3).
2. [PROVED — sketch included, bookkeeping routine] The compact quotient Y = Λ⁺\W
   is canonically the **suspension of the ×2, ×3 automorphism Z²-action on the
   6-adic solenoid Σ₆** (Proposition 2). So
   the arithmetic quotient of the (2,3) tree-product geometry *is* the classical
   linear ×2×3 system — Furstenberg/Rudolph–Johnson/BLMV live exactly here.
3. [PROVED] **Collapse Lemma.** Every Collatz orbit projects to a *single point*
   of Y (the walk generators lie in the lattice). The +1 shear is a deck
   transformation of the quotient; all arithmetic content lives in the choice of
   section Z₊ ↪ W. This is the geometric face of "T on Z₂ ≅ full shift, ergodic
   theory sees noise", and of the 5x+1 / negative-cycle sanity tests.
4. [PROVED] The natural orbit path in W ascends the 2-tree along a *deterministic
   ray* (parity data is consumed choosing the word), descends the 3-tree recording
   n_k mod 3^L, and carries drift + Böhm–Sontacchi data in the H² factor. Cycles =
   elements of the Collatz semigroup with integral fixed point c_γ/(1−u_γ); the
   cycle equation n(2^K−3^L) = W(v) is that fixed-point equation verbatim, and
   Baker/Rhin lower bounds say exactly "no element of the semigroup is too close
   to unipotent at the archimedean place".
5. [PROVED] **No-gap Lemma.** The averaging operator ½(U₂+U₃) of the ×2,×3 action
   has spectral radius 1 on L²₀(Σ₆) and on L²₀(R/Z): the dual frequency walk is a
   walk on amenable Z²-orbits. There is *no* L² spectral gap at the level of the
   abelian quotient; BLMV's effective ×2×3 theorems (statements quoted exactly in
   §4.2) are entropy-rigidity results with iterated-logarithm rates, **not** a
   spectral gap — the prompt's premise needed this correction.
6. [CONJ] The operator for which a gap would matter is identified precisely:
   the **character-twisted transfer operators of the parity-shift skew product**
   (fiber = Σ₆, equivalently conductor-3^m characters), Conjecture A = uniform
   exponential decay, which is a strong form of Tao's fine-scale mixing (proved
   polynomially by Tao) and of his equidistribution conjecture. Consequences and
   the exact wall (a.e.-vs-every, exponential adaptive sparsity) are itemized.
7. [PROVED/VER] Placement results: DL(2,3) — indices checked: the horospherical
   product of the 3-regular and 4-regular trees — is not quasi-isometric to *any*
   finitely generated group (Eskin–Fisher–Whyte), so the "congruence-only" home
   of Collatz has no lattice; the arithmetic home needs the irrational weights
   (log 2, log 3) and the real place. ⟨×3/2, +1⟩ is finitely generated but not
   finitely presented (Bieri–Strebel), while the full Λ is — the (2,3) syntax
   wall appears again at the level of group presentations.

---

## 1. The stage

### 1.1 Trees, ends, heights [PROVED — standard]

For p prime, the Bruhat–Tits tree 𝒯_p of PGL₂(Q_p) is (p+1)-regular. Fixing the
end ∞_p (the line spanned by e₁), vertices are parametrized by closed balls of
Q_p: vertex ↔ B(c, p^m) = {x : |x−c|_p ≤ p^m}, c ∈ Q_p, m ∈ Z; two balls are
adjacent iff one contains the other with index p. The boundary is ∂𝒯_p =
Q_p ∪ {∞_p}. (Serre, *Trees*; Casselman's notes [CLASSICAL],
https://ncatlab.org/nlab/files/CasselmanOnBruhatTitsTree2014.pdf.)

The affine group Aff(Q_p) = Q_p^* ⋉ Q_p, acting by x ↦ ux + c, is the stabilizer
of ∞_p (mod center) and acts on balls by γ·B(c, r) = B(uc + c′, |u|_p r).
Define the **height** ht_p(B(c, p^m)) = m·log p. Then

    ht_p(γ·B) = ht_p(B) + log|u|_p.

Horospheres centered at ∞_p are the level sets of ht_p; moving toward ∞_p means
increasing height (bigger balls = coarser congruence information).

**Dictionary.** A vertex of 𝒯₂ at height −m·log 2 (m ≥ 0) containing an integer
is exactly a congruence class mod 2^m. Terras stopping-time classes, the DFA/
regular certificates of LANDSCAPE §4, and Monks sufficiency all speak about
finite unions of 𝒯₂-vertices; Tao's Syracuse characters speak about 𝒯₃-vertices.

### 1.2 The archimedean factor

H² = {x + iy : y > 0} with Aff(R)⁺ = {x ↦ ux + c, u > 0} acting simply
transitively by z ↦ uz + c; ht_∞(x+iy) = log y, boundary horocoordinate x ∈ R,
distinguished end i∞. This is the "tree at the archimedean place"; its
horocoordinate is where size and positivity live.

### 1.3 The weighted horospherical product W, and why the real place is forced

Let X = 𝒯₂ × 𝒯₃ × H² and

    W := { (B₂, B₃, z) ∈ X : ht₂(B₂) + ht₃(B₃) + ht_∞(z) = 0 }.

For u ∈ Z[1/6]^* = {±2^a 3^b} the product formula gives |u|₂|u|₃|u|_∞ = 1, so W
is invariant under Λ := Z[1/6]^* ⋉ Z[1/6] ⊂ Aff(Q₂) × Aff(Q₃) × Aff(R)
(diagonal embedding). [PROVED]

**Lemma 1.3 (the real place is forced).** The Λ-action on 𝒯₂ × 𝒯₃ alone is not
properly discontinuous: translation by 6^N fixes every vertex B(c, r) with
r ≥ |6^N|₂ = 2^{−N} in 𝒯₂ and every vertex with r ≥ 3^{−N} in 𝒯₃ — i.e. it
fixes pointwise the radius-N neighborhood of the base pair — while being
nontrivial; so as N → ∞ these elements violate properness. Adding the H²
factor restores properness: translation by 6^N moves x + iy to x + 6^N + iy,
displacement → ∞. ∎ [PROVED]

This is the geometric product formula: congruence data at 2 and 3 alone cannot
separate the translations; the archimedean coordinate must be carried. Compare
`two-bases.md`: certificates cannot live in two bases; here, *lattices* cannot
live on two trees.

### 1.4 Proposition 1 (the lattice) [PROVED — standard S-arithmetic]

Λ is a discrete subgroup of G¹ := {(u, c) ∈ Q_S^* ⋉ Q_S : Π_v |u_v|_v = 1}
(Q_S = R × Q₂ × Q₃), and Λ\G¹ is compact; consequently Λ acts properly
discontinuously and cocompactly on W ≅ G¹/K¹, K¹ = (Z₂^*⋉Z₂) × (Z₃^*⋉Z₃) × {1}.

*Sketch.* Z[1/6] is a discrete cocompact lattice in Q_S (S-integers in the
S-adeles; geometry of numbers), and Z[1/6]^* is discrete cocompact in the
norm-one unit group {u : Π|u_v|_v = 1} (Dirichlet S-unit theorem: log-image is a
rank-2 lattice in the plane Σ log|u_v| = 0, kernel {±1} compact). The extension
assembles, and the basepoint o = (B(0,1), B(0,1), i) has compact-open stabilizer
K¹ in G¹, with G¹·o = W. ∎

Heights give a fibration W → P := {(h₂, h₃, h_∞) ∈ (log2)Z × (log3)Z × R :
Σ = 0} ≅ R-thickened Z², and Λ's unit part acts on P as the rank-2 lattice
generated by (−log2, 0, log2) and (0, −log3, log3).

### 1.5 Proposition 2 (the quotient is the ×2×3 solenoid suspension) [PROVED]

Let Λ⁺ = ⟨2,3⟩ ⋉ Z[1/6] (index 2, dropping −1) and Σ₆ := Q_S / Z[1/6]
(diagonal), the **(2,3)-adelic solenoid**: compact connected abelian group with
dual Ẑ₆^ = Z[1/6]; equivalently lim← R/6^k Z. Multiplication by 2 and by 3 are
*automorphisms* of Σ₆. Then

    Y := Λ⁺\W ≅ ( Σ₆ × R² ) / Z²,

the suspension of the Z²-action (×2, ×3) on Σ₆ (Z² acts on R² by the log-lattice
translations, on Σ₆ by 2^a3^b).

*Proof.* Y = Λ⁺\G¹/K¹. Quotient first by translations: Z[1/6]\Q_S = Σ₆. Then by
units: (Q_S^×)¹/(Z₂^* × Z₃^* × R₊-part of K) ≅ R² via logs of |·|₂, |·|₃, and
⟨2,3⟩ ≅ Z² acts by the log-lattice on R² and by multiplication on Σ₆. ∎

So: **the arithmetic quotient of the (2,3) tree-product geometry is canonically
the natural extension / suspension of the classical ×2, ×3 system.** The
linkage between the Bruhat–Tits picture and the Furstenberg–Rudolph–Johnson–BLMV
picture is exact, not an analogy. Y is a compact 3-dimensional solenoidal
lamination fibering over T² = R²/(log-lattice) with fiber Σ₆.

### 1.6 Stabilizers, the +1 shear, positivity [PROVED]

- **Stabilizers.** Stab_Λ(pair of base vertices) = {(u,c) : u = ±1, c ∈
  Z₂ ∩ Z₃ ∩ Z[1/6] = Z} = {±1} ⋉ Z ≅ D_∞ — *the integer translations*. The full
  basepoint stabilizer (including i ∈ H²) is Z/2 (the reflection), trivial in
  Λ⁺. That the integers form exactly the residual vertex-stabilizer is the group
  fact behind the Collapse Lemma (§2.4).
- **The +1 shear** γ = (1,1): fixes pointwise every tree vertex of height ≥ 0 at
  both 2 and 3 (all balls of radius ≥ 1); below a fixed unit ball it permutes the
  2^m (resp. 3^m) depth-m sub-balls as the **+1 odometer** on Z/2^m (resp.
  Z/3^m), acting on the boundary fibers Z₂, Z₃ as the adding machine; at ∞ it is
  parabolic (z ↦ z+1). So the shear is elliptic at the finite places, parabolic
  at the archimedean place, and "odometric at infinity". (Cross-ref: the
  AFS/odometer thread, SMELL cross-connection (d).)
- **Positivity.** The semigroup S = ⟨γ₀, γ₁⟩ (below) preserves both half-lines
  (0,∞) and (−∞,−1] of the real horocoordinate ∂H² ⊃ R; positivity is a purely
  archimedean-boundary condition, invisible in 𝒯₂ × 𝒯₃. The classical negative
  cycles {−1}, {−5,−7,−10}, {−17,…} [CLASSICAL, Lagarias 1985] are S-words with
  negative integral fixed points and satisfy the same cycle equation with
  2^K < 3^L; the sign of n equals the sign of 2^K − 3^L, so positivity couples
  to the drift line from one side. Any framework that forgets the archimedean
  coordinate *must* admit the negative cycles — a hard test it is healthy to
  keep failing loudly.

---

## 2. Collatz inside Λ

### 2.1 Generators and self-enforcing admissibility [PROVED]

With T(n) = n/2 (n even), (3n+1)/2 (n odd), the branch maps are

    γ₀ = (1/2, 0),   γ₁ = (3/2, 1/2)   ∈ Λ,

with height steps (per §1.1 conventions)

    γ₀: (+log2, 0, −log2),      γ₁: (+log2, −log3, +log(3/2)).

**Lemma (valuation self-enforcement).** For x ∈ Q₂: if v₂(x) < 0 then both
γ₀x and γ₁x have strictly smaller v₂ (for γ₁: v₂(3x+1) = v₂(x) by the
ultrametric inequality since v₂(x) < 0 = v₂(1)); if v₂(x) = 0 then v₂(γ₀x) < 0.
Hence a word in {γ₀, γ₁} applied to n ∈ Z stays in Z iff at every step the
branch matches the parity — misapplication is never repaired. ∎

**Consequence.** Collatz ⟺ *unrestricted* vector reachability: for every n > 0
there is a word w in the free monoid {γ₀, γ₁}^* with w·(n,1)ᵀ = (1,1)ᵀ, where
γ_i are the upper-triangular matrices [[u, c],[0,1]] ∈ GL₂(Q). No admissibility
side-condition is needed. This places Collatz in the reachability landscape of
Diekert–Potapov–Semukhin [VER, arXiv:1910.02302, PDF:
`papers/diekert-potapov-semukhin-2020-flat-rational-GL2Q.pdf`]: their dichotomy
says a f.g. group G with GL₂(Z) < G < GL₂(Q) is either GL₂(Z) × Z^k (membership
decidable via flat rational subsets) or contains an extension of BS(1,q) at
infinite index, where membership is **open**. Λ contains BS(1,2) = ⟨(2,0),(1,1)⟩
and BS(1,3) = ⟨(3,0),(1,1)⟩ at infinite index: Collatz reachability sits squarely
in the open cell, as recorded in SMELL (bubble item), now with the exact citation.

### 2.2 The orbit path in W: three shadows [PROVED]

Let n_k = T^k(n), γ_(k) = the word taking n to n_k (so n_k = u_k n + c_k,
u_k = 3^L/2^k after k steps with L odd steps), and mark integers by
w(n) := (n + Z₂, n + Z₃, n + i) ∈ W. The orbit path is x_k := γ_(k)·w(n), with:

- **𝒯₂-shadow:** vertex B(n_k, 2^k) = B(0, 2^k) — the *deterministic ray*
  toward ∞₂, independent of n. All 2-adic information is consumed choosing the
  word (Terras: parity word of length k ↔ n mod 2^k, a bijection). The forward
  dynamics *ascends* the 2-tree and learns nothing there.
- **𝒯₃-shadow:** vertex n_k + 3^L Z₃ — genuine descent into the 3-tree,
  recording n_k mod 3^L. Nothing consumes it: 3-adic data *accumulates*. This is
  precisely the data of Tao's Syracuse random variables.
- **H²-shadow:** point n_k + i·3^L 2^{−k}. Writing n_k/u_k = n + r_k with
  r_k = Σ_{odd steps i} 2^{k_i} 3^{−L_i−1} ∈ Z[1/6], the archimedean coordinate
  carries exactly the pair (drift walk L log3 − k log2, Böhm–Sontacchi series
  r_k). Descent to 1 is the statement that this shadow returns to a bounded
  region of the horoball.

The **backward** walk (predecessors m ↦ 2m and m ↦ (2m−1)/3) is the mirror:
ascends 𝒯₃, descends 𝒯₂ (accumulating the mod-2^j data of Terras layers), every
step descends at 2. Krasikov–Lagarias difference inequalities live on the
𝒯₃-shadow of the backward tree at fixed depth (residues mod 3^k); the SMELL #1
identification "KL exponents = min-plus Perron roots on mod-3^k states" is the
tropicalization of the backward transfer operator on this shadow. The forward/
backward asymmetry of the two trees is the geometric face of the base-2 vs
base-3 certificate disjointness of `two-bases.md`.

### 2.3 Cycles as integral fixed points; Baker as anti-unipotency [PROVED — restatement]

γ = (u, c) with u ≠ 1 has unique fixed point c/(1−u) ∈ Q. For a Collatz word
with K halvings and L odd steps, u = 3^L/2^K and 2^K c = W(v) (the cycle-equation
weight), so the fixed point is n = W(v)/(2^K − 3^L): the classical cycle
equation n(2^K − 3^L) = W(v) *is* the fixed-point equation of the semigroup
element. Nontrivial cycles ⟺ elements of S with fixed point in Z_{>0} ⟺
"integral torsion" of the section. Baker/Rhin linear-forms bounds
(LANDSCAPE §2: Λ > exp(−13.3(0.46057 + log K))) say: no element of S is too
close to unipotent at the archimedean place, i.e. |1 − u_γ|_∞ cannot be
super-exponentially small in the word length — which caps the height of the
would-be integral fixed point. Steiner/Simons–de Weger/Hercher's m-cycle
exclusions are quantitative anti-torsion theorems for S ⊂ Λ. [SPEC framing;
content proved elsewhere.]

### 2.4 The Collapse Lemma [PROVED]

**Lemma.** Let Γ be any group with γ₀, γ₁ ∈ Γ ≤ Λ (e.g. Λ itself, or
PGL₂(Z[1/6]) in the §4.4 picture). Then the image of the orbit path {x_k} in
Γ\W is the single point [w(n)] = [w(1)] (all integer markings are in one
Λ-orbit: w(n) = (1,n)·w(0), and γ_(k) ∈ Γ).

*Moral.* The Collatz walk cannot be a walk *on* an arithmetic quotient of this
geometry: the walk's generators are deck transformations. Equivalently: on Σ₆
the +1 of the shear is invisible (translation by 1 ∈ Z[1/6] is trivial), so the
"linearized Collatz" on the quotient is x ↦ x/2, x ↦ 3x/2 — the full ⟨2,3⟩
system — and every integer sits at the point 0 ∈ Σ₆. All content is in the
*section* Z₊ ↪ W of the quotient map, where +1 acts as the double odometer of
§1.6. Partial quotients Γ′ < Λ of finite index retain exactly coset data =
congruence information (the tame Terras layer, LANDSCAPE §4); quotients missing
the generators lose compactness. This is the geometric form of "T ≅ full shift
on Z₂, strongly mixing, conjecture invisible to Haar" (Lagarias 1985), and it
*proves* that the naive "orbits = geodesics on the quotient" slogan is empty for
this problem. [The lemma is trivial; its value is that it is a permanent no-go
for a family of proposals.]

### 2.5 What Collatz is, then: a piecewise-Λ section map [PROVED — definition]

T is the self-map of the marked horosphere-section {w(n) : n ∈ Z₊} ⊂ W given on
the 𝒯₂-children of each vertex by different elements of Λ (γ₀ on the even child,
γ₁ on the odd child). The algebraic home of such objects is Kohl's
residue-class-wise affine (rcwa) framework [CLASSICAL, S. Kohl, "The Collatz
conjecture in a group theoretic context"]; the geometry adds: the pieces are
indexed by tree-children, the map is height-preserving on W only in the weighted
sense, and its linear part generates the full deck group. [SPEC: the right
"quotient object" is therefore not a space but the groupoid/crossed product of
the section — the Exel–Pardo/Katsura lane of SMELL bubble; K-theoretic
invariants of C(Σ₆-with-section) ⋊ S are computable and uncomputed.]

### 2.6 Unrestricted reachability is solved: the wild semigroup [VER]

Applegate–Lagarias, *The 3x+1 semigroup* [VER, arXiv:math/0411140, PDF:
`papers/applegate-lagarias-2006-3x1-semigroup.pdf`]: the multiplicative
semigroup generated by {(2k+1)/(3k+2) : k ≥ 0} ∪ {2} (backward Collatz ratios)
equals *all* positive rationals a/b with 3 ∤ b; in particular it contains every
positive integer (Farkas's Weak 3x+1 Conjecture, proved). Read in our frame:
once the *order* of moves is freed (multiplicative closure instead of orbit
composition), the (2,3) obstruction evaporates. The conjecture is irreducibly
about the *directed* path structure of S, not about the group or semigroup
closure — consistent with the Collapse Lemma: closures live on the quotient,
paths live on the section.

---

## 3. Naive homes and their obstructions

### 3.1 Diestel–Leader: indices checked, and a no-lattice theorem [VER]

Convention check (as requested): DL(q, r) is the horocyclic product of the
trees T_{q+1} and T_{r+1} (degrees q+1, r+1) [VER — Woess, *Lamplighters,
Diestel–Leader graphs, random walks, and harmonic functions*, Comb. Probab.
Comput. 14 (2005); Bartholdi–Neuhauser–Woess, *Horocyclic products of trees*,
JEMS 10 (2008) 771–816]. So the Collatz-relevant graph is **DL(2,3)** — the
horospherical product of the 3-regular tree (𝒯₂) and the 4-regular tree (𝒯₃),
with *unweighted* integer heights h₂ + h₃ = 0. DL(q,q) is a Cayley graph of the
lamplighter Z_q ≀ Z; and:

**Theorem (Eskin–Fisher–Whyte)** [VER, Ann. of Math. 176 (2012) 221–260,
arXiv:math/0607207, PDF: `papers/eskin-fisher-whyte-2012-coarse-differentiation-I.pdf`]:
for m ≠ n, DL(m,n) is not quasi-isometric to any finitely generated group.

So no group acts properly cocompactly on DL(2,3) (Milnor–Švarc): **the
congruence-only (two-tree, equal-weight) home of the (2,3) problem admits no
lattice at all.** The arithmetic home W repairs this in exactly two ways: the
height weights become (log 2, log 3) — irrational ratio, the Collatz constant —
and the archimedean factor is appended (Lemma 1.3). [Interpretation SPEC: the
distance between DL(2,3) and W is a geometric measure of what automata/congruence
methods miss; the two repairs are "log₂3 is irrational" and "size exists".]

### 3.2 Finite presentability: the (2,3) wall in group syntax [PROVED — classical]

F := ⟨x ↦ (3/2)x, x ↦ x+1⟩ = Z[1/6] ⋊_{3/2} Z is the metabelianization of
BS(2,3); by the Bieri–Strebel criterion [CLASSICAL, Bieri–Strebel, Proc. LMS 41
(1980)] it is finitely generated but **not finitely presented** (Z[1/6] is not
finitely generated over Z[t] or over Z[t⁻¹] alone: t = 3/2 gives only Z[1/2],
t⁻¹ only Z[1/3]). The full Λ⁺ = Z[1/6] ⋊ Z² *is* finitely presented (the two
valuation directions in the character sphere are not antipodal — tame). The
one-parameter (3/2)-dynamics is syntactically infinite; only the two-parameter
(2,3)-ambient is finite. [SPEC: resonates with "no finite certificate in one
base"; F is the group-theoretic Antihydra.]

### 3.3 Precedents for the geometry [VER/CLASSICAL]

BS(1,n) = Z[1/n] ⋊ Z acts properly cocompactly on the treebolic space
T_{n+1} ×_h H² (Farb–Mosher, Invent. Math. 131 (1998), rigidity; analysis on
treebolic spaces: Bendikov–Saloff-Coste–Salvatori–Woess, e.g. arXiv:1212.6151)
[CLASSICAL, cross-checked in search results]. W is the natural two-prime
sibling: 𝒯₂ ×_h 𝒯₃ ×_h H² with weights (log2, log3, 1). We found **no prior
occurrence of this specific triple product, nor any Collatz linkage to tree
products, in the literature** (searches: "Collatz Bruhat–Tits", "Collatz product
of trees", "Collatz Baumslag–Solitar", "Collatz adelic/solenoid"; closest are
Siegel's (p,q)-adic analysis arXiv:2412.02902 — analysis on Z₂×Z₃ without the
geometry — and Kohl's rcwa framework). Modern S-arithmetic lattices acting on
products of two trees (the simple/quaternionic, spectral-gap-bearing kind):
arXiv:2305.04448 [VER, PDF: `papers/stix-etal-2023-sarithmetic-products-of-trees.pdf`];
Burger–Mozes lattices (Publ. IHÉS 92, 2000) are the wild non-arithmetic cousins
[CLASSICAL]. These live in the *full* Aut(𝒯)×Aut(𝒯), are non-amenable, and are
where gaps are theorems — see §4.4 for why Collatz does not currently reach them.

---

## 4. The spectral question, sharpened

### 4.1 Two proved no-gaps [PROVED]

**Lemma (no abelian-quotient gap).** Let M = ½(U₂ + U₃) on L²(Σ₆), U_a f(σ) =
f(a·σ). Then ‖M‖ = 1 on L²₀ and the spectral radius is 1. *Proof.* The dual
walk on Σ₆^ = Z[1/6]∖{0} sends ξ ↦ 2ξ, 3ξ; since 2,3 are units of Z[1/6], each
⟨2,3⟩-orbit is a free Z²-orbit, so M is unitarily a direct sum of copies of
½(λ(e₁)+λ(e₂)) on ℓ²(Z²), which has norm sup_{T²}|½(z+w)| = 1 (Z² amenable). ∎
Same conclusion on L²₀(R/Z) with N²-orbits (Følner vectors in the quadrant).

So "spectral gap on the quotient" is *false* in the naive L² sense — for the
torus just as for our Y. Any descent mechanism phrased as an L²-gap of a
group-average on the abelian quotient is dead on arrival.

**Lemma (no expansion route through Λ).** Λ is solvable, hence amenable, hence
has no property (T)/(τ)-type gap; and the super-approximation machinery
(Bourgain–Gamburd; Salehi Golsefidy–Varjú, *Expansion in perfect groups*, GAFA
2012 [CLASSICAL]) requires perfect/semisimple Zariski closure — the closure of
Λ is the Borel B ⊂ GL₂, on the excluded side. The geometry (Lemma 1.3, EFW) and
the group theory say the same thing: the affine (2,3) world is structurally
gapless at the group level. [PROVED modulo standard citations]

### 4.2 What is true at the linear level: exact BLMV statements [VER]

PDF saved: `papers/bourgain-lindenstrauss-michel-venkatesh-2009-effective-xa-xb.pdf`
(Erg. Th. Dynam. Sys. 29 (2009) 1705–1722). Quoting their numbering:

- **Thm 1.3 (Rudolph–Johnson).** μ a ×a,×b-invariant probability on R/Z with
  h_μ(t_a) = η log a ⟹ μ ≥ η·Leb. (Sharp; rationals show sharpness.)
- **Thm 1.4 (effective R–J).** If H_μ(𝒫_N) ≥ ρ log N (entropy at scale N) then
  some m = a^s b^t < N has [m.μ](f) ≥ (ρ − 3δ)λ(f) − κ₁ (log N)^{−κ₂δ}‖f′‖₂.
- **Thm 1.8 (effective Furstenberg).** α irrational with |α − p/q| ≥ q^{−k}
  (Diophantine-generic): {a^s b^t α : s,t ≤ N} is (log log N)^{−κ₅}-dense,
  N ≥ N₀(k,a,b).
- **Thm 1.10 (rational points).** (ab, N) = 1, m ∈ (Z/N)^×: {a^k b^l m/N :
  0 < k,l < 3 log N} is κ₇(log log log N)^{−κ₂/100}-dense.

Mechanism: entropy + Host-style arguments, ℓ^p-flattening — **not** a spectral
gap; rates are iterated logarithms, consistent with §4.1 (no gap exists to give
better). This corrects the task premise: BLMV is a proven (2,3) *effective
rigidity* theorem, not a proven (2,3) *spectral gap*.

Transport to our quotient: the ×2,×3 system on Σ₆ is an invertible extension of
×2,×3 on R/Z (dual: Z ⊂ Z[1/6]); Furstenberg/R–J/BLMV statements lift with the
same entropy hypotheses [PROVABLE — routine lift, worth writing]. But on Σ₆ the
integers sit at the single point 0 (Collapse Lemma), which is exactly the
excluded (rational/zero-entropy) case of every one of these theorems. Thm 1.10
is the one statement that touches Collatz-relevant points *unconditionally*: the
odd-denominator rationals m/N are the periodic layer of T (periodic points =
odd-denominator rationals, LANDSCAPE §4), and their ⟨2,3⟩-orbits are the
linearized cycle shadows. No Collatz consequence derived yet [honest]; the
triple-log rate calibrates how weak "proven and unconditional" currently is
exactly where the section meets the quotient.

### 4.3 The operator that matters, and Conjecture A [CONJ + PROVABLE consequences]

The non-collapsing dynamical object is the **skew product over the parity
shift**: base (Z₂, T, Haar) ≅ full 2-shift; fiber M = Z₃ (equivalently, the
conductor-filtered part of Σ₆ that survives the section); fiber maps z ↦ z/2
(even), z ↦ (3z+1)/2 (odd) — isometry resp. 3-adic contraction. The invariant
object is Tao's Syracuse structure: driving the odd steps by iid Geometric(1/2)
halving-counts, the fiber marginal is the Syracuse law Syrac(Z₃), and
equidistribution of orbit segments mod 3^m is controlled by the
**character-twisted transfer operators**: for ξ a character of Z₃ of conductor
3^m, L_ξ acts on observables of the base and its n-th power norm is the decay of
E[e(ξ·X_n)], X_n the Syracuse sum after n odd steps.

- **Proved (Tao 2019, arXiv:1909.03562, §1.3 and §7):** |E e(ξ X_n)| ≪_A n^{−A}
  for all A, uniformly over primitive ξ of conductor 3^m in the relevant range —
  super-polynomial but sub-exponential twisted decay. [VER via LANDSCAPE §4 +
  paper]
- **Conjecture A (uniform twisted gap; strong form of Tao's exponential-mixing
  expectation).** ∃ C, c > 0: for every m ≥ 1, every primitive character ξ of
  conductor 3^m, and every n ≥ Cm: |E e(ξ X_n)| ≤ e^{−cn}.

This is *the* precise answer to "what operator on which quotient": the gap is
not for a group average on L²(Y) (dead by §4.1) but for the family {L_ξ}
uniformly over the fiber conductor — a Dolgopyat-type twisted gap for a solvable
skew product, the exact p-adic mirror of "exponential Fourier decay for
Bernoulli convolutions at good parameters". The entropy heuristic (LANDSCAPE §4)
predicts it; nothing known contradicts it; no current technique proves it
(BLMV's entropy method gives iterated logs; Tao's renewal/black-triangle method
tops out at n^{−A}).

**What Conjecture A buys** (all conditional):
1. [PROVABLE given A] Exponential-rate equidistribution mod 3^m of length-n
   orbit segments for all but a e^{−c′n}-fraction of seed residues mod 2^n —
   note: over the *exact* Terras ensemble (parity words of length n are
   equidistributed over Z/2^n exactly), so no measure-transfer loss.
2. [PROVABLE given A, following Tao's own conditional chain] The β = 1 Syracuse
   equidistribution conjecture and hence #{N ≤ x : Col_min(N) = 1} ≫ x^{1−o(1)}
   (LANDSCAPE §4) — nearly closing predecessor density; cross-ref SMELL #1,
   where the same limit appears as "does λ_k → 2": Conjecture A is the annealed
   mechanism that would make the KL adversarial exponents climb.
3. [PROVED wall, unchanged] No individual-orbit conclusion: the fraction of bad
   residues at window length n ~ C log(seed) is polynomial in 1/seed, and Tao's
   Remark 1.4 / Dolgopyat–Sarig (SMELL dead ends 3, 8) show the a.e.→every chasm
   is not crossable by rate improvements alone. A gap sharpens *density*
   statements; it does not touch *divergence* without a new coupling idea.

### 4.4 The GL₂ upgrade: real gaps, out of reach [PROVED facts, SPEC bridge]

Embedding Λ ⊂ B ⊂ PGL₂ and passing to the full group restores everything §4.1
forbids: PGL₂(Z[1/6])\(H² × 𝒯₂ × 𝒯₃) is a finite-volume S-arithmetic quotient
on which the tree adjacency operators *are* the Hecke operators T₂, T₃, and
their spectral gap is a **theorem** (Selberg 3/16 → Kim–Sarnak 7/64 at ∞;
property (τ): Clozel; Ramanujan-quality at the finite places for the compact
quaternionic cousins: Jordan–Livné, *The Ramanujan property for regular cubical
complexes*, Duke 2000 [VER, arXiv:math/9907214, PDF:
`papers/jordan-livne-2000-ramanujan-cubical-complexes.pdf`] — quotients of
products of BT trees, Ramanujan via Ramanujan–Petersson for Hilbert modular
forms). [CLASSICAL/VER]

But the Collapse Lemma persists verbatim (γ₀, γ₁ ∈ PGL₂(Z[1/6])): Collatz
orbits are again a single point of this quotient. What survives is a *sampling*
formulation: orbit segments are N adaptively-chosen points on exponentially
expanding horospherical pieces (the B-orbits) of a quotient whose full-horosphere
equidistribution has proven exponential rates. The known sparse-equidistribution
technology (Venkatesh, Ann. Math. 172 (2010): polynomially sparse times on
horocycles; Sarnak–Ubis: primes on horocycles [CLASSICAL]) tolerates polynomial
sparsity with non-adaptive sampling; Collatz sampling is exponentially sparse
(N points against e^{cN} volume) and adaptive (each point's position determines
the next branch). **Verdict:** the automorphic gap is real but currently buys
nothing for Collatz; today it yields strictly less than Tao's bespoke renewal
argument. Any bridge would need an "exponentially sparse adaptive horosphere
sampling" theorem — no instance of which exists in the literature we checked.
[Honest negative assessment; the precise reformulation is retained as a
dictionary entry: π_a(x) = #{γ ∈ S⁻¹-words : γ·w(a) ∈ integer horoball,
ht_∞ ≤ log x}.]

### 4.5 Ledger

| Object | Gap status | Sees the +1 / section? |
|---|---|---|
| ½(U₂+U₃) on L²₀(Σ₆) or L²₀(T) | **No gap** (proved, §4.1) | No (deck) |
| Effective ×2×3 (BLMV) | No gap; entropy rigidity, log-log rates (proved) | No (integers = point 0; Thm 1.10 touches periodic layer) |
| Hecke T₂,T₃ on PGL₂(Z[1/6])-quotient | **Gap proved** (τ, Ramanujan-type) | No (collapse); bridge = exp-sparse adaptive sampling, nonexistent tech |
| Twisted transfer {L_ξ}, conductor 3^m, n ≥ Cm | n^{−A} proved (Tao); **exponential = Conjecture A, open** | **Yes** — this is the section's own operator |
| KL min-plus Perron on mod-3^k (SMELL #1) | adversarial 0.87 vs annealed 2 | Yes (backward tree; tropical shadow of L_ξ) |

The unique entry that is both open and section-aware is Conjecture A. That is
the sharp content of "spectral gap as the descent mechanism".

---

## 5. Deliverables and next actions

1. **Write up Propositions 1–2 + Lemmas (1.3, Collapse, No-gap, valuation)**
   as a self-contained 6–8 page note; everything is elementary given standard
   S-arithmetic facts; Lean-ability: high for the lemmas, medium for Prop 2.
   [~1 week]
2. **BLMV-on-Σ₆ lift** (Thms 1.4/1.8/1.10 to the solenoid) — routine but
   citable; establishes the "linear theory complete on the quotient" plank.
   [PROVABLE, ~half week]
3. **Register Conjecture A** as the program's named spectral target; reconcile
   with Tao's §7 renewal structure and with SMELL #1's λ_k → 2 (same limit
   object from the min-plus side). A first computation: numerically estimate
   the twisted decay rate ĉ(m) = −(1/n) log|E e(ξX_n)| at conductors 3, 9, 27
   from the existing expsum atlas (CRACKS crack 3 infrastructure). [days]
4. **Anti-torsion reformulation of cycles** (§2.3) as a short section in the
   cycles file: no new theorem, but it puts Baker, Hercher, and the semigroup
   S in one sentence, and makes "positivity = archimedean boundary" checkable
   against any proposed certificate class (must fail on −5, −7, −10).
5. **Crossed-product invariants** of the section groupoid (Exel–Pardo lane,
   SMELL bubble): the geometry now specifies *which* groupoid: Σ₆ ⋊ S with the
   D_∞ vertex stabilizer as isotropy. [SPEC, unpriced]

## 6. Sources

Verified this session (PDFs in `/Users/simon/Desktop/COLLATZ/papers/`):
- Bourgain–Lindenstrauss–Michel–Venkatesh, *Some effective results for ×a×b*,
  ETDS 29 (2009) — `bourgain-lindenstrauss-michel-venkatesh-2009-effective-xa-xb.pdf`
  (source: https://www.epfl.ch/labs/tan/wp-content/uploads/2018/10/blmv.pdf)
- Eskin–Fisher–Whyte, Ann. Math. 176 (2012) 221–260 —
  `eskin-fisher-whyte-2012-coarse-differentiation-I.pdf` (arXiv:math/0607207)
- Diekert–Potapov–Semukhin (ISSAC 2020) — `diekert-potapov-semukhin-2020-flat-rational-GL2Q.pdf`
  (arXiv:1910.02302)
- Applegate–Lagarias, *The 3x+1 semigroup*, J. Number Theory 117 (2006) —
  `applegate-lagarias-2006-3x1-semigroup.pdf` (arXiv:math/0411140); Farkas 2005
  via https://en.wikipedia.org/wiki/3x_%2B_1_semigroup
- Jordan–Livné, Duke 2000 — `jordan-livne-2000-ramanujan-cubical-complexes.pdf`
  (arXiv:math/9907214)
- S-arithmetic groups simply transitive on products of trees —
  `stix-etal-2023-sarithmetic-products-of-trees.pdf` (arXiv:2305.04448)
- Bartholdi–Neuhauser–Woess, JEMS 10 (2008) 771–816; Woess, CPC 14 (2005)
  [statements verified via search, PDFs not saved: paywalled/EPFL infoscience]

Classical, cited from memory (low risk): Serre *Trees*; Casselman notes (URL in
§1.1); Farb–Mosher Invent. Math. 131 (1998); Bendikov–Saloff-Coste–Salvatori–
Woess (arXiv:1212.6151); Bieri–Strebel Proc. LMS 41 (1980); Burger–Mozes Publ.
IHÉS 92 (2000); Selberg; Kim–Sarnak (JAMS 16, 2003); Clozel (Invent. 151,
2003); Salehi Golsefidy–Varjú (GAFA 22, 2012); Venkatesh (Ann. Math. 172,
2010); Sarnak–Ubis (JMPA 103, 2015); Lagarias 1985; Kohl rcwa.

Program-internal: LANDSCAPE.md §§2,4; SMELL.md #1, bubble items (Potapov–
Semukhin, Exel–Pardo), cross-connections (c)–(e); CRACKS.md crack 6;
notes/two-bases.md; Tao arXiv:1909.03562.

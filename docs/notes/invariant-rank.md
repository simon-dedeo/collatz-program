# The invariant-rank functional

2026-07-20 (audited + extended same day: citations verified against papers/
and the web, three PDFs added, one citation corrected (V₁ᵖ), one closure
axiom repaired (H2/L4a), one provenance gap flagged (M(d,e) exhaustion
logs), three theory-hunt items added (§4.10–4.12)). Status: definitions +
easy lemmas PROVED here (elementary, Lean-able); theory hunt complete with
verdicts; central conjectures stated with an explicit proved/open split. Companion to REVERSE-MINING.md §2A.2
(the bbchallenge occupancy census), notes/two-bases.md, and the dfacert
exhaustions. Calibration labels used throughout:
**[PROVED]** (proof in this note or a cited theorem applied verbatim),
**[CITED]** (external theorem, not re-proved), **[PROVABLE-LOOKING]**,
**[CONJECTURAL]**, **[SPECULATIVE]**.

The object in one sentence: for a dynamical/rewriting system S and a safety
behavior φ, `rank_H(S, φ)` is the least tier of a fixed hierarchy H of
certificate classes admitting a sound inductive invariant witnessing φ —
provability itself, treated as a graded, measurable invariant of the system.
The bbchallenge BB(5) pipeline measured its distribution over an exhaustive
program population (175,373,810 → 6,005,142 → 6,577 → 23 → 17 → 13); our
dfacert/dfacert3 exhaustions, the Monks corollary, the de Bruijn fullness
argument, YAH's matrix no-go, and the bi-Mahler exclusion are lower-bound
measurements of the same functional at the Collatz point.

---

## 1. Formal definitions

### 1.1 Presented systems, charts

A **presented transition system** is S = (Σ, X, R): finite alphabet Σ, a
regular set X ⊆ Σ* of configurations, and a relation R ⊆ X × X realized by a
finite (synchronized or sequential) transducer. Post(L) := R(L),
Pre(L) := R⁻¹(L), Reach(I) := ⋃ₖ Rᵏ(I).

The same abstract dynamics has many presentations. A **chart** for a map
T: ℤ⁺ → ℤ⁺ is a pair (X, ν) with ν: X → ℤ⁺ a bijection (a numeration system)
such that ν ∘ T ∘ ν⁻¹ ... more precisely such that the relation
{(w, w′) : T(ν(w)) = ν(w′)} is realized by a finite transducer. Working
charts for Collatz: **chart₂** (LSB-first binary; T is a 3-state sequential
transducer — experiments/dfacert) and **chart₃** (MSD-first base 3; odd step
= append digit, halving = 2-state division transducer — experiments/dfacert3).
An **atlas** is a set of charts; ours currently {chart₂, chart₃}, with
rational-base 3/2 (Akiyama–Frougny–Sakarovitch) and Zeckendorf-type charts
queued. Chart-change maps (base conversion) are **not** rational
(Stérin–Woods 2020 measure exactly how non-local); this failure is
load-bearing below (§2, L5).

### 1.2 Safety behaviors and semantic certificates

A **behavior** is a pair φ = (I, B) of regular subsets of X ("initial",
"bad"). φ **holds** iff Reach(I) ∩ B = ∅. A **(semantic) certificate** for
(S, φ) is L ⊆ X with

  (C1) I ⊆ L;  (C2) Post(L) ⊆ L;  (C3) L ∩ B = ∅.

For Collatz disproof-search the instance is degenerate but legitimate: a
**divergence certificate** is L ≠ ∅ with T(L) ⊆ L and 1 ∉ L (the certificate
is its own initial set; B = {1}); its existence refutes the conjecture
(Lean: `Collatz.not_conjecture_of_invariant_set`).

**Lemma L0 (adequacy; certificate lattice).** [PROVED] A certificate exists
iff φ holds. Moreover every certificate L satisfies
Reach(I) ⊆ L ⊆ X ∖ Pre*(B), and both endpoints are themselves certificates
(when φ holds): Reach(I) is the least, X ∖ Pre*(B) the greatest.

*Proof.* If L is a certificate, induction on (C1)+(C2) gives Reach(I) ⊆ L,
so by (C3) φ holds. If x ∈ L ∩ Pre*(B), its forward orbit stays in L (C2)
and meets B, contradicting (C3); so L ⊆ X ∖ Pre*(B). Conversely if φ holds,
Reach(I) satisfies (C1)–(C3); and X ∖ Pre*(B) is Post-closed (complement of
a Pre-closed set), contains I (else φ fails), avoids B (as B ⊆ Pre*(B)). ∎

Note the two endpoints' recursion-theoretic types: Reach(I) is Σ⁰₁,
X ∖ Pre*(B) is Π⁰₁. Rank (below) asks how far *below* Σ⁰₁ some certificate
can be pushed.

### 1.3 Certificate schemes, soundness relation, admissible hierarchies

The bbchallenge lesson (REVERSE-MINING 2B.1: "the shipped certificate is the
DFA alone") is that a tier is not a class of sets but a class of *finite
codes plus a checker plus a soundness theorem*. Accordingly:

A **certificate scheme** for a transducer class 𝒯 is C = (D, check, γ):
a decidable set D ⊆ ℕ of codes; a total computable
check: D × 𝒯-presentations → {0,1}; and a semantics γ: D → 𝒫(Σ*), such that

  (S1) **Soundness relation**: check(d, S, φ) = 1 ⟹ γ(d) is a semantic
       certificate for (S, φ). (Required to be a theorem; ideally
       machine-checked — this is the FAR/WFAR verifier discipline.)
  (S2) **Effectiveness**: γ(d) has decidable membership, uniformly in d.

The scheme is **complete for its class** if conversely, whenever some
L ∈ γ(D) is a semantic certificate, some d with γ(d) = L passes check. (Our
regular scheme is complete: conditions (C1)–(C3) are decidable for regular L
against rational R — product constructions, as implemented in dfacert. A
scheme may be sound but incomplete, e.g. widening-based closure checks;
rank is then defined w.r.t. the scheme, and scheme-completeness is what
makes exhaustion results clean lower bounds.)

An **admissible hierarchy** is a countable family H = {C_i}_{i∈P} of
certificate schemes, indexed by a poset P, with:

  (H1) **Effective monotonicity**: i ≤ j gives a computable translation of
       C_i-codes to C_j-codes preserving γ.
  (H2) **Effective lattice closure**: each γ(D_i) effectively closed under
       finite unions, and under intersections *with regular sets*. (Closure
       under intersections of two tier sets with each other is deliberately
       NOT part of (H2): it holds for W₃, for V₀/V₁/V₁ᵖ, and for W₄ at
       variable counter dimension — the product construction preserves
       determinism and concatenates counters — but at *fixed* dimension the
       blind-counter hierarchy is strict (Greibach 1978), and for the Mahler
       class W₆ intersection closure is the open Hadamard-product question.
       Lemmas that intersect two tier certificates carry the hypothesis
       explicitly — see L4.)
  (H3) **Recoding closure**: each γ(D_i) effectively closed under images and
       preimages of synchronized-rational bijections Σ* → Σ′* (letter
       permutations, higher-block codes, padding).

Deliberately **not** required: complementation (the deterministic-Parikh
tier is not complement-closed as a nondeterministic class; determinism is
what restores checkability — this is *why* WFAR uses deterministic weighted
automata, a fact the theory forces rather than the engineers choosing it);
infinite unions (tiers are not σ-complete; that is why least fixpoints
escape them).

### 1.4 Spectrum and rank

For an admissible hierarchy H, system S, behavior φ:

  **Spec_H(S, φ)** := {i ∈ P : some d ∈ D_i has γ(d) a certificate for
  (S, φ) and (for complete schemes equivalently) check(d, S, φ) = 1}.

  **rank_H(S, φ)** := the set of minimal elements of Spec_H (along a chain:
  the least tier), with rank = ∞ iff Spec_H = ∅.

**Lemma L1 (spectrum is an up-set).** [PROVED] i ∈ Spec_H and i ≤ j imply
j ∈ Spec_H. *Proof.* (H1). ∎ So rank is well-defined as the boundary of a
filter; on a chain it is an element of P ∪ {∞}.

### 1.5 The reference hierarchy H_auto (value tiers, chart tiers)

Two interleaved towers, one chart-free (value sets ⊆ ℤ⁺), one per chart.

Chart-free value tiers:
- **V₀** finite sets.
- **V₁** semilinear = ultimately periodic = Presburger-definable sets.
  (Chart-independent: recognizable in *every* base — the easy direction of
  Cobham.)
- **V₁ᵖ** Semenov tier: definable in Presburger + the function n ↦ 2ⁿ —
  decidable by **Semenov 1984** (not by the 2024 paper previously cited
  here; corrected on audit). The Collatz-natural *two-power* refinement
  **V₁ᵖ(2,3)**: sets defined by *existential* formulas over
  ⟨ℤ; 0, 1, <, +, 2^ℕ, 3^ℕ⟩ (both power predicates at once — the class
  where 3^a vs 2^b comparisons are native). The ∃-fragment is decidable
  (Karimov–Luca–Nieuwveld–Ouaknine–Worrell, arXiv:2407.05191,
  papers/karimov-luca-nieuwveld-ouaknine-worrell-2024-presburger-powers.pdf),
  while already 3 alternating quantifier blocks are undecidable
  (Hieronymi–Schulz, sharpened ibid.) — so certificate *checkability*
  (which needs (C1)–(C3), a ∀∃ condition, discharged for the specific
  transducer) sits exactly at today's decidability frontier: a scheme here
  must ship auxiliary witnesses making the inductiveness check ∃-only.
- **V_ce** (top) c.e. sets.

Per-chart word tiers (chart b, encoding convention fixed):
- **W₁(b)** lasso languages (finite ∪ finite unions of xy*z) — the
  translated-cycler tier.
- **W₂(b, n)** locally-testable/n-gram tier; its "prefix-window" fragment =
  unions of residue classes mod bⁿ (which sit inside V₁).
- **W₃(b, q)** regular, ≤ q DFA states — the FAR tier, parameterized.
- **W₄(b)** deterministic Parikh / regular + blind ℤ-counters — the WFAR
  tier (Greibach 1978; Klaedtke–Rueß 2003).
- **W₅(b)** weighted/path-complete: ordered-semiring matrix interpretations
  (ℕ-matrix, arctic), safety orientation (FAR ladder of REVERSE-MINING
  2B.1–2B.2); includes polyhedral/Farkas accept sets.
- **W₆(b)** b-Mahler-supported: L whose generating series Σ_{n∈L} zⁿ
  satisfies a linear b-Mahler equation (⊋ b-automatic, via Becker 1994).

This is a **poset, not a chain**: W₆(2) and W₃(3) are incomparable; V₁ embeds
in every W₃(b); V₁ᵖ ⊄ W₃(2) ∪ W₃(3) etc. Rank statements below always name
the chain or antichain they live on.

**Caveat (W₆ is a semantic exclusion class, not a certified scheme).** W₆
has no known checker: deciding (C2) for a set given only by a Mahler
equation for its generating series is not known to be effective, and even
(H2) would require the Mahler class to be closed under Hadamard product
with automatic sequences, which is open in general. We keep W₆ in the
hierarchy because our results *exclude semantic certificates* there
(Theorem M(f)) — an exclusion at a non-effective tier is strictly stronger
than at its effective subtiers (it kills every b-automatic and b-regular
certificate a fortiori, via Becker 1994). Rank *upper* bounds at W₆ would
be meaningless until a scheme (D, check, γ) is exhibited; rank *lower*
bounds are not affected. The termination-certificate hierarchy
(for the *proof* side of Collatz, which is liveness, not safety) is the
matching tower of ranking-function schemes: ℕ-matrix interpretations of
dimension d < arctic < ...; soundness relations are the standard
monotone-algebra theorems (Endrullis–Waldmann–Zantema 2008;
Koprowski–Waldmann 2008).

---

## 2. Basic properties: the easy lemmas

Throughout: H admissible, S presented, φ = (I, B) regular.

**L2 (soundness of finite rank).** [PROVED] rank_H(S, φ) ≠ ∞ ⟹ φ holds.
*Proof.* (S1) + L0. ∎ (Converse fails by design: φ may hold with all its
certificates transcending H — that is the content of rank = ∞, L8.)

**L3 (monotonicity in the behavior).** [PROVED] If I′ ⊆ I and B′ ⊆ B then
Spec_H(S, (I,B)) ⊆ Spec_H(S, (I′,B′)); hence rank(S,(I′,B′)) ≤ rank(S,(I,B)).
*Proof.* A certificate for (I,B) verifies (C1)–(C3) for (I′,B′) verbatim. ∎

**L4 (lattice laws).** [PROVED] With (H2), and for (a) and (c) the extra
hypothesis that the target tier is effectively closed under finite
intersections *of its own sets* (true for W₃, V₀, V₁, V₁ᵖ, and W₄ at
variable counter dimension; see the (H2) remark — this hypothesis is not
free, and (a) genuinely fails as a schema for fixed-dimension counter
tiers):
(a) rank(S, (I, B₁ ∪ B₂)) ≤ max(rank(S,(I,B₁)), rank(S,(I,B₂)));
(b) rank(S, (I₁ ∪ I₂, B)) ≤ max(rank(S,(I₁,B)), rank(S,(I₂,B)));
(c) synchronous products: if tiers are closed under cylinders and finite
intersections, rank(S₁ × S₂, φ₁ × φ₂) ≤ max(rank(S₁,φ₁), rank(S₂,φ₂)).
*Proof.* (a) L := L₁ ∩ L₂: Post(L) ⊆ Post(L₁) ∩ Post(L₂) ⊆ L (Post is
monotone), I ⊆ L, L ∩ (B₁∪B₂) ⊆ (L₁∩B₁) ∪ (L₂∩B₂) = ∅.
(b) L := L₁ ∪ L₂: Post(L) = Post(L₁) ∪ Post(L₂) ⊆ L; the rest is clear.
(c) L := π₁⁻¹(L₁) ∩ π₂⁻¹(L₂). ∎
No matching lower bounds hold in general (a product can admit accidental
low-tier certificates through one factor alone when B = B₁ × X₂); the census
question "is rank superadditive on natural ensembles?" is open and
empirical. [CONJECTURAL]

**L5 (rational-recoding invariance; chart dependence).** [PROVED]
Let h: X → Y be a bijection realized, together with h⁻¹, by synchronized-
rational transducers, and let S^h = (Σ′, Y, h∘R∘h⁻¹), φ^h = (h(I), h(B)).
With (H3): Spec_H(S, φ) = Spec_H(S^h, φ^h); rank is invariant.
*Proof.* L ↦ h(L) is a bijection between certificate families preserving
(C1)–(C3), and (H3) preserves tiers in both directions. ∎

**Failure beyond rational recodings — the chart phenomenon.** [PROVED,
via cited theorems] Base conversion ℤ⁺-value-preserving maps between chart₂
and chart₃ are not rational, and rank is *not* invariant under them: by
Cobham 1969, a value set recognizable in both charts is semilinear, and by
the Monks 2006 corollary (notes/two-bases.md) no infinite semilinear
divergence certificate exists. Restated rank-theoretically:

> **Bi-chart collapse (two-bases theorem, recast).** On the atlas
> {chart₂, chart₃}, the intersection of the two regular tiers, as classes of
> certificate value-sets for Collatz divergence, collapses to V₀, and V₀
> membership forces a nontrivial cycle (elements > 2⁷¹, ≥ 2.18×10¹¹
> T-steps). Equivalently: geometric rank — min over charts — cannot be
> attained at "regular" in two multiplicatively independent charts
> simultaneously, except through a cycle.

This makes precise both the Skelet-10 lesson ("regular after a change of
numeration" — recoding can lower presented rank) and its Collatz limit
(Cobham rigidity: it cannot do so in two independent bases at once). Define
**geometric rank** := min over an atlas of presented ranks; it is the
chart-free invariant, and Cobham–Semenov theory is exactly the (only known)
tool that controls quantification over charts.

**L6 (simulation/factor monotonicity — hardness transport).** [PROVED]
Let h: X → Y be computable with h∘R ⊆ R′∘h (one step maps to one step;
the R′* version is identical), h(I) ⊆ I′, B ⊆ h⁻¹(B′). If every tier is
effectively closed under h-preimages, then
rank_H(S, (I,B)) ≤ rank_H(S′, (I′,B′)).
*Proof.* L′ a certificate for (S′,(I′,B′)); put L := h⁻¹(L′). (C2): x ∈ L,
x → x′ ⟹ h(x) ∈ L′ and h(x) →′ h(x′), so h(x′) ∈ L′, x′ ∈ L. (C1):
h(I) ⊆ I′ ⊆ L′. (C3): x ∈ L ∩ B ⟹ h(x) ∈ L′ ∩ B′ = ∅. ∎
Contrapositive: **lower bounds on the simulating system's pulled-back
behavior are lower bounds on the simulated system's behavior.** This is the
formal license for reading bbchallenge data as Collatz-family measurement:
Michel's TM ⇄ Collatz-like translations (Michel 1993, 2015) are rational at
the configuration level, so decider failures (rank lower bounds on the TM
side, e.g. the Cryptids resisting every implemented tier) transport to the
arithmetic maps, and conversely — *provided* the simulation is
tier-compatible; each transport must check (H3) for its h. Caveat recorded:
the constant-factor tier shifts (h's own automaton states) must be tracked
for quantitative statements.

**L7 (computability trichotomy).** [PROVED (a),(b); CITED (c)]
(a) If tier C_i is a parameterized family of *finite* abstract domains with
computable best transformers (n-gram/SLT_n at fixed n; threshold+modulus
RepWL; unions of residue classes mod bⁿ), then "rank ≤ i" is **decidable**:
the least tier-invariant containing I exists (finite Moore family) and is
reached by Kleene iteration in finitely many steps; compare with B.
This is Cousot–Cousot 1977 specialized to finite domains, and is the
NGramCPS Algorithm-2 situation.
(b) If C_i is merely an R-checkable scheme with c.e. codes, "rank ≤ i" is
**Σ⁰₁** (enumerate codes, check). Exhaustion-by-code-size — dfacert,
bbchallenge FAR — is the canonical algorithm, and per-tier the negative
results it produces ("no certificate with ≤ q states") are the strongest
statements available at this generality.
(c) For expressive tiers the fixed-tier existence problem is genuinely
undecidable in general: the **Monniaux problem** — given program, safety
property, abstract domain, decide existence of an inductive invariant in the
domain — is undecidable for semilinear invariants of affine programs, with
decidability recovered for restricted subclasses (Fijalkow–Lefaucheux–
Ohlmann–Ouaknine–Pouly–Worrell, SAS 2019, arXiv:1907.08257, JACM 2024;
Monniaux 2019 for polyhedra). So no uniform improvement on (b) exists; but
(open, interesting) the *Collatz-Monniaux problem* — decidability of
"∃ regular divergence certificate" for the specific transducer T in chart₂
— inherits no known undecidability proof and is a well-posed new question.

**L8 (incompleteness: rank-∞ instances exist for every H).** [PROVED]
For any admissible hierarchy H: {(S, φ) presented instances : rank_H < ∞}
is Σ⁰₁ (by L7(b), uniformly). True safety of presented systems is
Π⁰₁-complete (encode Turing nonhalting; e.g. via string rewriting). A
Π⁰₁-complete set is not Σ⁰₁; hence for every admissible H there are true
instances with rank_H = ∞. Moreover such instances exist *within the
generalized-Collatz class*: Conway 1972 (generalized Collatz maps simulate
arbitrary computation, even with zero offsets) and Kurtz–Simon 2007
(Π⁰₂-completeness of total convergence; the safety fragment is
Π⁰₁-complete) put nonhalting-hard instances inside residue-affine maps, and
L6 transports rank-∞ along the (rational) simulations. ∎
Also class-level: Blondel–Tsitsiklis 2000 (boundedness of piecewise-affine
maps undecidable) gives rank-∞ instances among PAMs for every H.
**No admissible hierarchy is complete for true safety** — the certificate
analogue of Gödel incompleteness, and the reason "rank" does not collapse.

**L9 (window/de Bruijn blindness — the SFT tier at the Collatz point).**
[PROVED] For every n ≥ 1, the only union of residue classes mod 2ⁿ that is a
T-closed set avoiding 1 is ∅.
*Proof.* Let L ≠ ∅ be a union of classes mod 2ⁿ with T(L) ⊆ L. Consider the
class graph on ℤ/2ⁿℤ with an edge c → c′ iff some x ≡ c has T(x) ≡ c′. If
class c ⊆ L and c → c′, pick the witness x ∈ c ⊆ L; then T(x) ∈ L ∩ c′, and
L is a union of classes, so c′ ⊆ L. The class graph is the binary de Bruijn
graph B(2, n) (Laarhoven–de Weger 2013, arXiv:1209.3495), which is strongly
connected; so every class, in particular the class of 1, is contained in L,
giving 1 ∈ L. ∎
(Map convention: Laarhoven–de Weger prove de Bruijn isomorphism for the
*shortcut* map T(x) = (3x+1)/2. For the full map C (odd x ↦ 3x+1) the
argument transfers: odd classes have the single successor 3c+1, and the two
mod-2ⁿ successors of the even class 3c+1 are exactly the two shortcut
successors of c, so every shortcut class path lifts to a C class path;
strong connectivity is inherited, and forward closure under C implies
forward closure of the class set under the lifted edges.)
Mod-3 analogue [PROVED, direct check]: class edges mod 3 are
0→{0,1}, 1→{1,2}, 2→{1}; any T-closed union of classes avoiding the class
of 1 must avoid 2 (edge 2→1 with full-class image: n ≡ 2 (6) halves into
1 (3), n ≡ 5 (6) maps to 16+18m ≡ 1 (3)) and avoid 0 (witness 3 → 10); so ∅.
Extension of L9 from prefix-windows to the full SLT_n/n-gram word tier over
chart₂ (factors constrained anywhere in the word): [PROVABLE-LOOKING] via
the same fullness — the 2-adic extension of T is conjugate to the full
2-shift (Lagarias 1985; Bernstein–Lagarias 1996), so the order-n SFT cover
of any T-closed set's orbit closure is the full shift; a complete proof
must handle the carry-boundary and MSB-end effects and is not written down.
Note L9 is *also* a special case of the Monks corollary (residue-class
unions are semilinear), but the de Bruijn proof is self-contained,
elementary, and localizes the failure (strong connectivity of the abstract
quotient — "the abstraction is mixing"), which is the correct general
diagnostic: **a finite abstract domain proves nothing iff the induced
abstract graph lets Bad be reached from everywhere.**

**L10 (entropy obstruction at the regular tier — the sound direction of the
n-gram barometer).** [PROVED, weak form] Let L be a regular certificate
recognized by a (complete, deterministic) q-state DFA, and let
h = lim sup (1/ℓ) log |Fact_ℓ(Reach(I))| be the factor-growth entropy of the
reachable language. Then Reach(I) ⊆ L forces h ≤ h(L), and h(L) = log λ(A_L)
where λ(A_L) is the spectral radius of the transition graph of the minimal
DFA restricted to its live part. In particular if h = log |Σ| (full factor
growth) then every regular certificate's trim automaton has λ = |Σ|: its
factor dynamics is itself full. *Proof.* Monotonicity of factor counts
under inclusion; Perron bound for path counts. ∎ Honest scope: over a
binary alphabet this forces no state-count bound (λ ≤ 2 always), which is
*why* blind DFA exhaustion (M(d)) cannot be replaced by an entropy argument
at the regular tier — the entropy obstruction bites only at the SFT/window
tier (L9), where fullness leaves no room at all.
The bbchallenge converse ("low entropy ⟹ small certificate") is empirical
and probably false in general (Skelet 17 as candidate counterexample)
[CONJECTURAL]. For Collatz, L9's fullness makes the weak form bite: the
chart₂ factor dynamics of any T-closed set is full, which is the
measure-free content of "ergodicity kills the SFT tier."

---

## 3. The current measurement: rank(Collatz) from below, today

**Theorem M (assembled measurement, 2026-07-20).** Let T be the Collatz map,
and call L ⊆ ℤ⁺ a divergence certificate if L ≠ ∅, T(L) ⊆ L, 1 ∉ L. Then:

(a) **[PROVED — cycles tier V₀]** Every *finite* divergence certificate
contains a nontrivial cycle (pigeonhole on iteration); any nontrivial cycle
has minimal element > 2⁷¹ (Barina verification, 2025:
papers/barina-2025-improved-verification-limit.pdf; extended by
Angeltveit 2026) and ≥ 2.18×10¹¹ T-steps with > 1.375×10¹¹ odd terms
(Hercher 2023, no m-cycles m ≤ 91, papers/hercher-2023-*, combined with the
verification bound).

(b) **[PROVED — semilinear tier V₁]** No infinite semilinear divergence
certificate exists. (Monks 2006, Proc. AMS 134: every AP is a sufficient
set; corollary in notes/two-bases.md — an infinite semilinear set contains
an infinite AP, whose orbits merge with orbit(1).) Hence also no
ultimately-periodic, no finite-union-of-APs, and — by inclusion — no
residue-class-union certificate in any modulus.

(c) **[PROVED — window/SFT tier W₂]** Independently of (b), with an
elementary graph proof: no union of residue classes mod 2ⁿ (any n) and no
union of residue classes mod 3 is a divergence certificate (L9; de Bruijn
strong connectivity, Laarhoven–de Weger 2013). Full SLT_n word tier:
[PROVABLE-LOOKING], sketch in L9.

(d) **[PROVED by exhaustive verified computation for q ≤ 4; q = 5–7
claimed, provenance gap flagged — regular tier W₃(2, q)]**
No divergence certificate is recognized by a complete DFA with ≤ 7 states
over LSB-first binary (intersected with valid encodings). Exhaustion counts:
q ≤ 4: 83,968 DFAs scanned; q = 5: 5.1×10⁶; q = 6: 379.6×10⁶; q = 7:
32.79×10⁹ (= canonical ICDFA tables × 2^q accepting sets — the stated
counts are arithmetically consistent with complete enumeration); searcher
with property-tested transducer, positive/negative controls, independent
__int128 verification of candidates; q = 8 (≈3.2×10¹²) in flight.
**Provenance audit (2026-07-20):** the in-repo results table
(experiments/dfacert/README.md, with --plain cross-checks) documents only
q ≤ 4; the q = 5–7 counts appear in STRATEGY.md §3.3 but no run logs are
committed under results/. Until logs land, cite this as
"q ≤ 4 [PROVED, in-repo]; q ≤ 7 [claimed, STRATEGY §3.3]". Action item in
§6.

(e) **[PROVED by exhaustive verified computation for q ≤ 4; q = 5 claimed,
same provenance gap — regular tier W₃(3, q)]**
No divergence certificate is recognized by a complete DFA with ≤ 5 states
over MSD-first base 3 (q ≤ 4: 34,049,024 DFAs scanned, in-repo with --plain
cross-checks; q = 5: 29.3×10⁹ claimed in STRATEGY §3.3; mutation-tested,
OEIS-cross-validated enumeration). (experiments/dfacert3.) By (f) this is a
channel provably independent of (d).

(f) **[PROVED — bi-chart tier, and its Mahler closure W₆(2) ∩ W₆(3)]** No
divergence certificate is recognizable in two multiplicatively independent
bases unless it is finite — hence, by (a), a nontrivial-cycle witness
(Cobham 1969 + Monks corollary; notes/two-bases.md). Upgrade: no exotic
Collatz-graph component has a generating function satisfying both a 2-Mahler
and a 3-Mahler equation (Adamczewski–Bell 2017 solving Loxton–van der
Poorten + Fatou/Kronecker; notes/two-bases.md v2, notes/mahler-cartier-
lemma0.md). Since b-automatic ⟹ b-regular ⟹ b-Mahler (Becker 1994), this
subsumes the automatic bi-chart statement and closes the entire
bi-(2,3)-Mahler tier.

(g) **[PROVED — proof-side, termination hierarchy, ℕ-matrix tier]** For
Zantema's rewriting presentation Z of (shortcut-)Collatz iteration
(termination of Z ⟺ Collatz convergence on the represented domain), there is
no collection of natural (ℕ-)matrix interpretations, of **any** dimension,
removing any rule — even after the dependency-pair transformation
(Yolcu–Aaronson–Heule 2021, CADE, Theorems 3.8 and 3.10; the proof pivots on
Berstel's theorem: an ℕ-rational sequence cannot satisfy x_{8n+1} > x_{9n+2}
for all n, against the derivation h1^{8n+1}▢ →* h1^{9n+2}▢). The arctic
(max-plus) tier is their stated open problem (our CRACKS #2 target;
notes/arctic-prethink-gpt.md).

**Reading of Theorem M.** On the divergence (safety/disproof) side, in
chart₂: rank exceeds V₀-as-non-cycle, V₁, W₂, and W₃(2, 4) [in-repo]
(W₃(2, 7) per STRATEGY-claimed runs); in chart₃ it exceeds W₃(3, 4)
[in-repo] (W₃(3, 5) claimed); and the bi-chart regular and bi-Mahler tiers are closed
*unconditionally* (not just up to a state bound). The open frontier today is
the antichain

  { W₃(2, q ≥ 8) } ∪ { W₃(3, q ≥ 6) } ∪ { W₄ (det-Parikh/WFAR, dim ≥ 1) }
  ∪ { W₅ (weighted/path-complete, safety orientation) }
  ∪ { V₁ᵖ (Semenov: semilinear + powers) } ∪ { single-chart Mahler W₆(b) }
  ∪ { non-integer-base charts (3/2; Zeckendorf) }.

On the convergence (liveness/proof) side: rank exceeds the ℕ-matrix tier at
every dimension (g); arctic and path-complete termination tiers open.

**A pitfall this formalization exposes (important).** Invariant complexity
is not reach-set complexity. Hopcroft–Pansiot exhibits VAS whose reachable
sets are non-semilinear, yet by Leroux (LICS 2009, arXiv:1009.1076) VAS
non-reachability *always* has a semilinear inductive separator: wild Reach,
tame certificate. Consequently, arguments showing that Collatz orbits /
Pred(1) / parity words are non-automatic or equidistributed do **not** bound
rank — lower bounds must kill *all* separators in the tier, as (b), (c),
(d), (f), (g) each do. This is the precise sense in which Theorem M's
components were correctly chosen, and a filter for future proposed lower
bounds.

---

## 4. Theory hunt: nearest existing theories and the precise gaps

Verdict first: **no unified "least-certificate-tier" functional over
dynamical systems exists in the literature under any name we could find**
(searches over: invariant rank, certificate rank, minimal invariant
complexity, hierarchy of inductive invariants, proof complexity of
nontermination; re-run 2026-07-20 during audit with the same negative
result). Every ingredient has an established home; the functional,
its invariance theory (L5, L6), the atlas/chart collapse, and measured
distributions (census) do not. The audit added three neighbors that
sharpen the boundary: regular abstraction frameworks (item 10 — a (D, γ)
pair in the wild, with size lower bounds), the Kesten–Pnueli completeness
theorem (item 11 — the hierarchy closes iff effectiveness is dropped), and
the derivational-complexity converse (item 12 — the one literature that
proves tier exclusions routinely). Nearest neighbors, with what each has
and lacks:

1. **The Monniaux problem** (Monniaux 2019; Fijalkow–Lefaucheux–Ohlmann–
   Ouaknine–Pouly–Worrell SAS 2019 / JACM 2024, arXiv:1907.08257).
   *Has:* the fixed-tier existence decision problem, with a decidability
   landscape (undecidable for semilinear invariants of affine programs;
   decidable for simple linear loops). *Lacks:* the rank functional across
   tiers; any dynamics-side invariance; arithmetic instantiations.
   *Use:* L7(c); and it names our new open question (Collatz–Monniaux).

2. **Abstract inductive invariants in a fixed domain** (Ranzato, CONCUR
   2020, arXiv:2004.03170 — decidability/synthesis of invariants ranging in
   an abstract domain, positive for Kildall and Karr domains; Padon–
   Immerman–Karbyshev–Sagiv–Shoham POPL 2016 — decidability of inferring
   inductive invariants in EPR-style logics). *Has:* "tier" as abstract
   domain, existence decidability per tier. *Lacks:* hierarchies, rank,
   lower-bound assembly.

3. **Cousot's completeness lattice** (Cousot–Cousot POPL 1977/1979;
   Giacobazzi–Ranzato–Scozzari, "Making abstract interpretations complete,"
   JACM 47(2), 2000; Giacobazzi–Logozzo–Ranzato POPL 2015). *Has:* the
   lattice of abstract domains, complete shells/cores — the right home for
   "hierarchy of tiers" as a lattice with refinement operators; L7(a) is
   their finite-domain fixpoint fact. *Lacks:* certificate existence as the
   question (their completeness concerns transformer precision, not
   separator existence); no recursion-theoretic top; no dynamics invariance.
   *Gap worth writing:* rank = the height function induced on their lattice
   by a fixed behavior; complete-shell refinement = tier climbing.

4. **Tier-completeness theorems for restricted classes** — the model
   theorem-shape for the whole program:
   - Leroux (LICS 2009; POPL 2011 short proof, arXiv:1009.1076): a VAS
     configuration is unreachable iff a **Presburger (semilinear) inductive
     invariant** separates it. I.e. the certification ordinal of the class
     VAS-non-reachability is the semilinear tier: co(VAS) = V₁. (New
     forward-only constructions: arXiv:2606.27166.)
   - WSTS coverability: upward-closed invariants with finite bases (ideal
     completions; Abdulla et al.; Finkel–Goubault-Larrecq): co(WSTS-cover)
     = the finite-ideal tier.
   - Match-bounded string rewriting preserves regularity (Geser–Hofbauer–
     Waldmann 2004): a syntactic subclass where the regular tier is
     complete.
   Define **co(𝒦, H) := sup over true instances in class 𝒦 of rank_H**.
   Then: co(VAS) = semilinear [CITED]; co(WSTS) = finite-ideal [CITED];
   co(TM-nonhalt) = ∞ = co(generalized Collatz) (L8) [PROVED]. The
   program's Conjecture B is exactly "the single (2,3) instance realizes
   the class supremum."

5. **Invariant-inference complexity** (Feldman–Immerman–Sagiv–Shoham,
   POPL 2020, "Complexity and information in invariant inference":
   exponential Hoare-query lower bounds for inferring polynomial-length
   invariants, information-theoretic, IC3/PDR-shaped; Feldman–Shoham SAS
   2022 monotone-theory upper bounds; "Learning the boundary of inductive
   invariants" POPL 2021). *Has:* lower bounds! — but on the *search* for an
   invariant that exists. *Lacks:* existence/rank. Orthogonal axis:
   rank(S, φ) vs. query-cost(S, φ, tier). Both are needed to theorize the
   bbchallenge census cascade (occupancy = existence; solve-rate-per-CPU =
   search cost; the UCB bandit of 2B.7 empirically orders the second).

6. **Path-complete Lyapunov ordering** (Ahmadi–Jungers–Parrilo–Roozbehani
   arXiv:1111.3427; Angeli–Athanasopoulos–Philippe–Jungers HSCC 2017/2019
   complete characterization of the ordering of path-complete methods;
   template-dependent lifts: Debauche–Philippe–Jungers arXiv:2110.13474,
   NAHS 2022; composition lifts arXiv:2503.18189; addition-closed templates
   HSCC 2023). *Has:* a genuine partial-order theory of certificate
   templates with comparison theorems and lift operators — the
   control-theory twin of "admissible hierarchy" (their lifts = our (H1)
   translations). *Lacks:* recursion-theoretic top, discrete/arithmetic
   instantiation. *Fusion:* their ordering theorems should transfer to the
   FAR/WFAR ladder verbatim (REVERSE-MINING #1 fusion play); note their
   De Bruijn expansions vs. our L9 de Bruijn obstruction are the same graph
   in dual roles.

7. **Medvedev/Muchnik degrees of subshifts** (Simpson ETDS 2014: Medvedev
   degrees of 2D SFTs realize exactly the Π⁰₁ degrees; recent classification
   on groups: arXiv:2406.12777; strong topological Rokhlin property:
   arXiv:2601.03501). *Has:* a *semantic*, conjugacy-invariant complexity
   measure of a dynamical object (degree of the set of points/witnesses),
   with transfer theorems along quotients/subgroups/quasi-isometries —
   exactly the invariance theory rank lacks beyond rational recodings.
   *Lacks:* syntax; certificates; anything sub-Σ⁰₁-graded.
   *Bridge* [SPECULATIVE]: for a true safety instance, consider the Π⁰₁
   class of "potential counterexample witnesses consistent with all tier-i
   checks"; rank ≤ i should force this class to be Medvedev-trivializable
   at level i; a Medvedev-hardness assumption on the witness class would
   yield rank lower bounds *uniform in the tier*. Nothing like this is in
   print on either side.

8. **Proof-theoretic ordinal analysis** (Goodstein/Paris–Harrington genre;
   for rewriting: derivational complexity and termination-order strength,
   e.g. Steila–Yokoyama 2015 in papers/). *Has:* "least theory proving φ" —
   the rank functional with tiers = arithmetic theories; the original
   provability-as-graded-invariant. *Lacks:* certificate/automata tiers;
   dynamics. Rank is certificate-theoretic ordinal analysis; the slogan is
   exact, including incompleteness (L8) playing Gödel's role. Note the
   recorded no-go (STRATEGY §6b): fast-growing-hierarchy unprovability is
   structurally inapplicable to Collatz (stopping times ~ log n), so the
   *ordinal* content of Collatz rank must come from certificate classes,
   not from growth rates — a genuine reason the automata-graded hierarchy
   is the right one here.

9. **The bbchallenge census itself** (BB(5) determination paper 2024/25,
   papers/bbchallenge-2025-bb5-determination.pdf; the deciders paper
   "Turing machines deciders, part I", bbchallenge Collaboration,
   arXiv:2504.20563 — title verified on audit; the FAR/universal-regular-CTL
   material lives there, via the Nerode-congruence closure argument,
   papers/bbchallenge-2025-deciders-part1-2504.20563.pdf). *Has:* the only
   measured occupancy distribution of rank over an exhaustive program
   population, plus the per-tier universality lemma (regular certificate ⟺
   finite-index left congruence with pre*-avoidance) that makes W₃ a
   congruence-indexed tier. *Lacks:* all theory. That is the vacuum this
   note fills.

10. **Regular abstraction frameworks — fixed-tier invariant computation
    with genuine size lower bounds** (Esparza–Raskin–Welzel-Mohr, "Regular
    Model Checking Upside-Down: An Invariant-Based Approach", CONCUR 2022;
    Czerner–Esparza–Krasotin–Welzel-Mohr, arXiv:2404.10752,
    papers/czerner-esparza-krasotin-welzelmohr-2024-regular-abstraction-
    invariants-2404.10752.pdf). *Has:* the closest existing formal object
    to a tier: a regular language of *constraints* plus a transducer
    *interpretation* assigning meaning — i.e., literally our (D, γ) with D
    regular; they compute the strongest inductive invariant expressible in
    the framework, prove the decision problem EXPSPACE-complete for
    length-preserving regular transition systems, and — the item the task
    hunt asked for — worst-case **double-exponential lower bounds on the
    automaton size** of the invariant. *Lacks:* the rank functional across
    frameworks; anything non-length-preserving (the Collatz transducer is
    not length-preserving — the odd step grows the word — so their
    machinery does not directly apply; a padding/section reduction is a
    well-posed open port). *Use:* their "framework = constraint language +
    interpretation" is the right generalization of our scheme definition
    (§1.3) and the natural place to push W₃-size lower bounds beyond
    exhaustion.

11. **Completeness at the non-effective top: augmented finitary
    abstraction** (Kesten–Pnueli, "Verification by augmented finitary
    abstraction", Inf. Comput. 163 (2000); the automata-theoretic view,
    JCSS 62 (2001); Dams–Namjoshi, "The existence of finite abstractions
    for branching time model checking", LICS 2004, and "Automata as
    abstractions", VMCAI 2005). *Has:* the theorem that the hierarchy
    *closes at the top if effectiveness is dropped*: for every true
    temporal property of an infinite-state system there exists a finitary
    abstraction (plus progress monitors/ranking augmentation) proving it —
    sound AND complete. *Lacks:* effectiveness — the abstraction is
    produced from the (undecidable) truth of the property, i.e., their
    "tier" violates our (S2)/checkability. *Use:* this is the precise
    foil for L8: admissible (effective) hierarchies are never complete;
    Kesten–Pnueli show *non-effective* ones are. Rank is interesting
    exactly in the gap between these two theorems.

12. **The derivational-complexity converse — rank lower bounds as daily
    practice in termination** (Hofbauer–Lautemann 1989: polynomial
    interpretations ⟹ double-exponential derivational complexity;
    Geser–Hofbauer–Waldmann 2004: match-bounded ⟹ linear; Endrullis–
    Waldmann–Zantema JAR 2008: ℕ-matrix ⟹ exponential; Moser–Schnabl–
    Waldmann FSTTCS 2008: triangular ℕ-matrix of dimension d ⟹ polynomial
    of degree ≤ d; organizing principle: Cichon's principle — the order
    type of the termination order bounds derivation lengths — Moser,
    AAECC 20 (2009)). *Has:* the only literature where "no certificate in
    tier X" is routinely *proved*, via the mechanism
    tier ⟹ growth bound ⟹ (system exceeding the bound has rank > tier).
    This is the termination-side twin of our L10, developed and sharp.
    *Lacks:* the safety orientation, and any bite on Collatz: Collatz
    stopping times are ~2 log n — derivational complexity is *tiny* — so
    the growth mechanism is structurally mute here (consistent with the
    STRATEGY §6b fast-growing-hierarchy no-go). That muteness is exactly
    why Yolcu–Aaronson–Heule's M(g) had to use an ℕ-rationality
    obstruction (Berstel: no ℕ-rational sequence has x_{8n+1} > x_{9n+2})
    instead of a growth obstruction — the first, and so far only,
    *non-growth* tier-exclusion in the termination literature we know of.
    *Use:* the model for what W₅-tier exclusions must look like: find the
    algebraic invariant of the tier (ℕ-rationality, arctic linearity) and
    contradict it with an exact derivation family, never with growth.

---

## 5. The central conjecture, stated precisely

### 5.1 Conway-unsettleability as rank = ∞

Fix any effectively axiomatized, arithmetically sound theory Th ⊇ PA (read:
ZFC). Say a hierarchy H is **Th-certified** if each scheme's soundness
relation (S1) is a theorem of Th.

**Proposition U (the settled part).** [PROVED]
(i) If a true safety instance (S, φ) is unprovable in Th, then
rank_H(S, φ) = ∞ for *every* Th-certified admissible hierarchy H.
(ii) Such instances exist, and exist within the generalized-Collatz class.
*Proof.* (i) A passing code d at any tier plus Th's proof of (S1) plus the
(finite, Th-formalizable) computation check(d) = 1 yields a Th-proof of φ.
(ii) Standard: the machine searching for a Th-proof of 0 = 1 never halts iff
Con(Th); Gödel 2 makes this true-but-unprovable (soundness); Conway 1972 /
Kurtz–Simon 2007 push nonhalting into residue-affine Collatz-like maps, and
L6 transports rank. ∎

**Conjecture U′ (Conway's actual claim — naturalness).** [CONJECTURAL,
not attackable by proof] Specific *natural* instances are unsettleable in
this sense — Conway 2013 (papers/conway-2013-on-unsettleable-arithmetical-
problems.pdf) proposes the amusical permutation orbits (e.g. of 8). In rank
language: naturally occurring dynamics realizes rank = ∞ against every
ZFC-certified hierarchy. Proposition U is the correct formalization of
"unsettleable ⟹ certificate-transcendent"; U′ is philosophy until a
naturalness measure is fixed (the census heavy-tail, §5.3, is the only
quantitative handle we know).

### 5.2 The program's conjecture: the (2,3)-instance saturates its class

**Conjecture B (Collatz certificate-transcendence).**
Let H_auto be the reference hierarchy of §1.5 over the full rational-
numeration atlas (all integer bases; rational bases p/q; linear/Pisot
numeration systems — every chart in which T is a finite transducer).

**(B1) Disproof side.** [CONJECTURAL; sub-tiers PROVED] No tier of H_auto,
in any chart of the atlas, contains a Collatz divergence certificate:
rank_{H_auto}(disproof) = ∞ chart-uniformly. Status: implied by the Collatz
conjecture itself, but strictly weaker and attackable tier by tier *now*;
proven through the tiers of Theorem M; the bi-chart tier closed
unconditionally (M(f)) — the only unconditional infinite-tier closure known.

**(B2) Proof side.** [CONJECTURAL] In the termination hierarchy (matrix /
arctic / path-complete / ranking functions with automatic support, over
every chart of the atlas), rank of "every orbit reaches 1" is ∞: every
correct proof of Collatz must consume arithmetic that is not expressible as
a fixed-tier certificate — i.e., inputs of Baker/Diophantine or
density/equidistribution type, as every partial result to date in fact does.
Evidence: M(g) (ℕ-matrix tier empty, all dimensions); Conway/Kurtz–Simon
class-hardness (no uniform argument); the cryptid resistance census
(CRYPTIDS.md finding 3: every solved holdout fell to discovered *rigidity*,
never to a generic tier). Tension deliberately kept: the Skelet-10 lesson
says re-coordinatization can collapse rank; B2 asserts it cannot here, for
every chart at once — and Cobham–Semenov rigidity (M(f)) is the standing
partial theorem in exactly that quantifier position.

**(B3) Relative version (safe formulation).** [PROVABLE-LOOKING as a
program] For each tier i of H_auto there is a *finite, checkable* reason
excluding tier i (as M(a)–(g) each provide), and the excluding arguments
themselves form an effective sequence — "rank = ∞, effectively witnessed."
B3 for the full regular tower W₃(2, q) all q — i.e. replacing exhaustion by
a single theorem "no regular divergence certificate at any index" — is the
program's sharpest realistic milestone (candidate routes: FAR-universality
+ congruence analysis; Mahler-analytic exclusion via mahler-cartier
Lemma 0 extended from bi-Mahler to single-base 2-Mahler at the
kernel-dimension level; Bartholdi-style ω-regularity no-go, SMELL.md).

### 5.3 The census conjecture (context, kept)

**Conjecture C.** [SPECULATIVE, empirical] Over natural ensembles of small
programs (BB(n), bred cryptid families), the rank occupancy follows a
description-length (Levin-prior) cascade — each tier's residue smaller by a
roughly constant factor (measured ~10⁻³ at BB(5)) — and rank correlates with
the conditional Kolmogorov complexity K(minimal invariant | machine).
Testable against the BB(6) census as it completes; our
experiments/family critical-drift protocol measures the same object along
one-cylinder deformations (certificate-size growth as drift → 0).

---

## 6. Consequences and queue

1. **Lean targets (cheap, high-value):** L0–L6, L9 formalize in an
   afternoon each; Theorem M(a)–(c) glue is elementary given Monks as a
   hypothesis; the scheme/soundness discipline (S1) is exactly the
   verified-checker architecture already planned in STRATEGY §5.2.
2. **New well-posed problems this note isolates:** (i) the Collatz–Monniaux
   problem (L7(c)); (ii) co(𝒦) for the carry-truncated tower T_w of
   STRATEGY §3.1 — is there a w-uniform tier-completeness theorem (the
   Leroux-shape question for our own family)? (iii) superadditivity of rank
   under products (L4 remark); (iv) the Medvedev bridge (§4.7).
3. **Measurement frontier (unchanged by the theory, now justified by it):**
   W₄ dim-2 WFAR with (odd-steps, halvings) weights; congruence-generator
   families mod 3^k (FAR universality says the congruence is the
   certificate); AFS 3/2-chart DFA search before concluding trans-regular
   rank; arctic no-go (M(g) → W₅ closure) as the next unconditional tier
   kill.
4. **Discipline imported from Leroux/Hopcroft–Pansiot (§3 pitfall):** every
   proposed lower bound must be an all-separators argument; orbit-complexity
   results are inadmissible as rank bounds.
5. **Provenance repair (from the M(d,e) audit):** commit the dfacert
   q = 5–7 and dfacert3 q = 5 run logs (or re-run with logs) under
   results/, and update the two READMEs' results tables past q = 4; until
   then all downstream citations must use the split phrasing of M(d,e).
6. **Port target (from §4.10):** reduce the chart₂ Collatz transducer to a
   length-preserving regular transition system (padded window / section
   construction) so the Esparza-school strongest-invariant algorithm and
   its EXPSPACE/size lower-bound machinery apply to W₃(2, q) directly —
   the only visible route to replacing DFA exhaustion by a computed
   strongest invariant.

## 7. Source ledger (external, load-bearing)

- Monniaux problem: arXiv:1907.08257; JACM version (2024); Monniaux 2019
  (polyhedra undecidability).
- Semenov 1984 (decidability of ⟨ℕ; +, n↦2ⁿ⟩ — the correct citation for
  single-power V₁ᵖ). Karimov–Luca–Nieuwveld–Ouaknine–Worrell,
  arXiv:2407.05191 (∃-fragment of ⟨ℤ; 0,1,<,+,2^ℕ,3^ℕ⟩ decidable; ≥3
  quantifier blocks undecidable, after Hieronymi–Schulz) — verified on
  audit; local file papers/karimov-...-presburger-powers.pdf is 2407.05191.
- Esparza–Raskin–Welzel-Mohr, CONCUR 2022 (regular model checking
  upside-down); Czerner–Esparza–Krasotin–Welzel-Mohr, arXiv:2404.10752
  (regular abstraction frameworks: strongest abstract invariant,
  EXPSPACE-complete, double-exponential invariant-size lower bounds) —
  papers/czerner-esparza-krasotin-welzelmohr-2024-regular-abstraction-invariants-2404.10752.pdf.
- Kesten–Pnueli, Verification by augmented finitary abstraction,
  Inf. Comput. 163 (2000); JCSS 62 (2001) automata-theoretic view;
  Dams–Namjoshi LICS 2004; VMCAI 2005 (completeness of non-effective
  abstraction).
- Derivational-complexity converse: Hofbauer–Lautemann 1989;
  Geser–Hofbauer–Waldmann AAECC 2004; Endrullis–Waldmann–Zantema JAR 2008;
  Moser–Schnabl–Waldmann FSTTCS 2008; Moser, The Hydra battle and Cichon's
  principle, AAECC 20 (2009).
- Bizière–Leroux–Sutre, A Forward-Only Construction of Semilinear
  Inductive Invariants for VAS, arXiv:2606.27166 (verified on audit) —
  papers/biziere-leroux-sutre-2026-forward-semilinear-invariants-vas-2606.27166.pdf.
- Ranzato, Decidability and Synthesis of Abstract Inductive Invariants,
  CONCUR 2020, arXiv:2004.03170. Padon et al., POPL 2016.
- Leroux, VAS reachability by Presburger inductive invariants, LICS 2009 /
  POPL 2011, arXiv:1009.1076; forward-only construction arXiv:2606.27166.
- Feldman–Immerman–Sagiv–Shoham, Complexity and Information in Invariant
  Inference, POPL 2020 (+ SAS 2022, POPL 2021 follow-ups).
- Path-complete ordering: HSCC 2017/2019/2022/2023; arXiv:2110.13474;
  arXiv:2503.18189; arXiv:1111.3427.
- Medvedev degrees: Simpson, ETDS 34(2):665–674 (2014) — statement verified
  on audit: Medvedev (and Muchnik) degrees of 2D SFTs = those of nonempty
  Π⁰₁ subsets of Cantor space; arXiv:2406.12777; arXiv:2601.03501.
- Cousot–Cousot POPL 1977; Giacobazzi–Ranzato–Scozzari JACM 2000.
- Cobham 1969; Monks 2006 (papers/monks-2006-*); Adamczewski–Bell
  arXiv:1303.2019; Becker 1994. Laarhoven–de Weger arXiv:1209.3495.
  Bernstein–Lagarias 1996; Lagarias 1985.
- Yolcu–Aaronson–Heule, CADE 2021 (papers/yolcu-aaronson-heule-2021-*),
  Theorems 3.5–3.10; Endrullis–Waldmann–Zantema 2008; Koprowski–Waldmann
  2008. Zantema z079 SRS.
- Conway 1972; Conway 2013; Kurtz–Simon 2007; Blondel–Tsitsiklis 2000
  (all in papers/). Barina 2025; Hercher 2023; Angeltveit 2026 (papers/).
- bbchallenge: BB(5) determination (papers/bbchallenge-2025-bb5-determination.pdf);
  "Turing machines deciders, part I", arXiv:2504.20563 (contains the
  FAR/universal regular CTL scheme via Nerode congruences; title corrected
  on audit) — papers/bbchallenge-2025-deciders-part1-2504.20563.pdf;
  occupancy census figures per REVERSE-MINING.md §2A.2.
- Verified against local PDFs on audit: Monks 2006 (shortcut map; merging
  form of sufficiency — the corollary's use with x = 1 is exactly licensed);
  Yolcu–Aaronson–Heule Theorems 3.5–3.10 (Corollary 3.6 = the
  x_{8n+1} > x_{9n+2} ℕ-rational obstruction; Thm 3.8 = extended monotone
  algebras; Thm 3.10 = weakly monotone + dependency-pair-style top rewrites;
  also holds for Z^rev); Ranzato CONCUR 2020 (Kildall + Karr positive
  cases); Feldman–Immerman–Sagiv–Shoham POPL 2020 (Hoare-query model,
  information-theoretic exponential lower bounds — search complexity, not
  existence).

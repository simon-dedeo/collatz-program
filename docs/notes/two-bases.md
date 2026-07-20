# No divergence certificate can live in two bases

2026-07-20. Status: elementary but apparently unrecorded; statement-complete,
proof assembled from cited results. Lean-ability: medium (needs Monks 2006
sufficiency + Cobham 1969 as inputs; the glue is elementary).

**v2 upgrade (same day, verified by hand — see docs/CRACKS.md crack #1):** the
statement extends from automatic sets to the strictly larger Mahler class.
For any exotic Collatz-graph component C (divergent orbit or exotic cycle),
the series h_C(z) = Σ_{n∈C} z^n cannot satisfy both a 2-Mahler and a 3-Mahler
linear functional equation. Chain: Adamczewski–Bell 2017 (arXiv:1303.2019,
solving Loxton–van der Poorten) ⟹ h_C rational; 0/1 coefficients + rational
⟹ eventually periodic support (Fatou/Kronecker); ⟹ C infinite semilinear
forward-closed avoiding 1, contradicting the Monks corollary below. Since
k-automatic ⟹ k-regular ⟹ k-Mahler (Becker 1994), the Proposition below is
the special case. Context: Berg–Meinardus 1994 shows Collatz ⟺ the kernel of
L = 1 − M₂ − z·M₂·Λ₃ in H(D) is 2-dimensional (verified coefficientwise:
ker L = component-constant series); exotic components are exactly extra
kernel dimensions, and this note says no extra dimension is (2,3)-bi-Mahler.

## Definitions

A **divergence certificate** is a set L ⊆ ℕ with (i) L ≠ ∅, (ii) T(L) ⊆ L,
(iii) 1 ∉ L, where T is the Collatz step. (Existence of any such L refutes the
conjecture: Lean `Collatz.not_conjecture_of_invariant_set`.) Note (ii)+(iii)
force 2, 4 ∉ L. A set is *b-recognizable* if some DFA accepts exactly the
base-b encodings of its elements.

## Inputs

1. **Monks 2006** (Proc. AMS 134:2861–2872): every arithmetic progression
   A+Bℕ (B ≥ 1) is a *sufficient set*: the T-orbit of every positive integer
   intersects the T-orbit of some element of the AP.
2. **Corollary** (elementary; derived in our landscape sweep): no infinite
   semilinear T-invariant set avoiding 1 exists. *Proof:* an infinite
   semilinear L ⊆ ℕ contains an infinite AP. Apply Monks with x = 1: orbits
   merge, so some s in that AP has orbit(s) ∩ {1,4,2} ≠ ∅, i.e. s reaches 1.
   But s ∈ L and L forward-closed give 1 ∈ L. ∎
3. **Cobham 1969**: a set S ⊆ ℕ recognizable in two multiplicatively
   independent bases is ultimately periodic (= semilinear).

## Statement

**Proposition.** Let L be a divergence certificate recognizable in two
multiplicatively independent bases (e.g. 2-automatic and 3-automatic). Then L
is finite, and L contains a nontrivial Collatz cycle all of whose elements
exceed 2⁷¹ (Barina 2025) with ≥ 2.18×10¹¹ T-steps (Hercher 2023 + Barina).

*Proof.* By Cobham, L is semilinear; by the corollary above it cannot be
infinite; a finite nonempty forward-closed set contains a periodic orbit
(iterate any element; pigeonhole), which avoids 1, hence is nontrivial;
verification and cycle bounds give the size claims. ∎

**Corollary (conditional).** If there is no nontrivial cycle, then every
2-automatic divergence certificate fails to be 3-automatic, and vice versa.
The multiplicative independence of 2 and 3 — the source of the problem's
difficulty — also constrains the syntax of any disproof.

## Context and honesty

- Adjacent prior art: Dhiman–Pandey (arXiv:2602.06066, **unrefereed math.GM
  preprint**) use Cobham similarly to show the *reachability relation* of
  T_{q,d} is not base-q Büchi-definable for odd q (base 2 explicitly open).
  Our object is invariant *sets*, not the reachability relation; the trick is
  the same family. Neither statement subsumes the other.
- This is a constraint on disproofs, not progress on the conjecture. Its value:
  (a) it cleanly separates the base-2 and base-3 certificate search channels —
  they are provably disjoint except through cycles; (b) it is a worked example
  of the "cracks" method: a rigidity theorem from an unvisited field
  (Cobham–Semenov, model theory of numeration) imported as a structural
  constraint.

## Consequence for the experiment queue

Run the DFA certificate search in **base 3** (MSD-first: odd step 3n+1 =
append digit 1; halving = 2-state carry transducer; parity = digit-sum parity
tracked in the product). This explores a certificate space provably disjoint
from the base-2 search (modulo cycles). Then LSD/MSD variants and base 6
(where both operations are local in different digit positions).

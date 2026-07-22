/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CanonicalSplashDynamics

/-!
# The boundary between finite dyadic routing and a natural seed

Finite affine routing repeatedly restricts a tail to a dyadic cylinder.  An
infinite compatible sequence always defines a 2-adic integer, but generally
not an ordinary natural number.  This file isolates the elementary obstruction:
at unbounded precision, the canonical residues of any fixed natural seed are
eventually the seed itself.
-/

namespace KontoroC

/-- Precision grows strongly enough that every fixed natural is eventually
smaller than every later modulus. -/
def DyadicPrecisionDiverges (bits : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → B < 2 ^ bits k

/-- A natural number realizes all prescribed low-bit residues. -/
def RealizesDyadicResidues (bits residue : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, n % (2 ^ bits k) = residue k

/-- The ordinary natural members of one dyadic affine cylinder. -/
def dyadicCylinder (bitCount residue : ℕ) : Set ℕ :=
  Set.range fun t => residue + 2 ^ bitCount * t

theorem mod_eq_residue_of_mem_dyadicCylinder {bitCount residue n : ℕ}
    (hcanonical : residue < 2 ^ bitCount)
    (hn : n ∈ dyadicCylinder bitCount residue) :
    n % (2 ^ bitCount) = residue := by
  obtain ⟨t, rfl⟩ := hn
  simp [Nat.add_mod, Nat.mod_eq_of_lt hcanonical]

/-- Core natural-versus-2-adic boundary: if one ordinary natural has all the
prescribed residues and precision diverges, those residues eventually stop
changing and equal that natural literally. -/
theorem realizesDyadicResidues_eventually_constant
    {bits residue : ℕ → ℕ} {n : ℕ}
    (hprecision : DyadicPrecisionDiverges bits)
    (hrealizes : RealizesDyadicResidues bits residue n) :
    ∃ K, ∀ k, K ≤ k → residue k = n := by
  obtain ⟨K, hK⟩ := hprecision n
  refine ⟨K, fun k hk => ?_⟩
  calc
    residue k = n % (2 ^ bits k) := (hrealizes k).symm
    _ = n := Nat.mod_eq_of_lt (hK k hk)

/-- Cylinder form of the same theorem.  This is the form consumed directly
by nested affine-tail constructions. -/
theorem mem_all_dyadicCylinders_eventually_constant
    {bits residue : ℕ → ℕ} {n : ℕ}
    (hprecision : DyadicPrecisionDiverges bits)
    (hcanonical : ∀ k, residue k < 2 ^ bits k)
    (hmem : ∀ k, n ∈ dyadicCylinder (bits k) (residue k)) :
    ∃ K, ∀ k, K ≤ k → residue k = n := by
  apply realizesDyadicResidues_eventually_constant hprecision
  intro k
  exact mod_eq_residue_of_mem_dyadicCylinder (hcanonical k) (hmem k)

/-- Operational no-go: a genuinely non-stabilizing address sequence cannot
be realized by any ordinary natural, even if every finite subsystem is
nonempty and compatible. -/
theorem no_natural_of_residues_never_eventually_constant
    {bits residue : ℕ → ℕ}
    (hprecision : DyadicPrecisionDiverges bits)
    (hchanges : ∀ n K, ∃ k, K ≤ k ∧ residue k ≠ n) :
    ¬ ∃ n, RealizesDyadicResidues bits residue n := by
  rintro ⟨n, hn⟩
  obtain ⟨K, hK⟩ :=
    realizesDyadicResidues_eventually_constant hprecision hn
  obtain ⟨k, hk, hne⟩ := hchanges n K
  exact hne (hK k hk)

/-- The same no-go phrased as empty intersection of the natural-number
cylinders.  Compactness in `ℤ₂` does not contradict this theorem. -/
theorem no_natural_in_all_dyadicCylinders
    {bits residue : ℕ → ℕ}
    (hprecision : DyadicPrecisionDiverges bits)
    (hcanonical : ∀ k, residue k < 2 ^ bits k)
    (hchanges : ∀ n K, ∃ k, K ≤ k ∧ residue k ≠ n) :
    ¬ ∃ n, ∀ k, n ∈ dyadicCylinder (bits k) (residue k) := by
  rintro ⟨n, hn⟩
  obtain ⟨K, hK⟩ := mem_all_dyadicCylinders_eventually_constant
    hprecision hcanonical hn
  obtain ⟨k, hk, hne⟩ := hchanges n K
  exact hne (hK k hk)

end KontoroC

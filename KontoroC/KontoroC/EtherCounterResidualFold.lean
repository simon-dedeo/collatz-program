/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterBareGlue

/-!
# Composition of consecutive EC17 residuals

This is the generic algebra behind QM121e.  It records exactly how one-cycle
residuals compose and proves the fixed-ternary-depth failure ledger: modulo a
covered power of three, a long block remembers only its final residual.
-/

namespace KontoroC
namespace EtherCounterResidualFold

/-- Binary mass accumulated before residual `j`. -/
def prefixMass (m : ℕ → ℕ) (q T : ℕ) : ℕ :=
  ∑ i ∈ Finset.range T, m (q + i)

/-- Ternary mass strictly after residual `j` and before the end `T`. -/
def suffixMass (Q : ℕ → ℕ) (q j T : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico j T, Q (q + i)

/-- Recursive composition of one-cycle signed residuals. -/
def residualFold (m Q : ℕ → ℕ) (E : ℕ → ℤ) (q : ℕ) : ℕ → ℤ
  | 0 => 0
  | T + 1 =>
      (3 : ℤ) ^ Q (q + T) * residualFold m Q E q T +
        (2 : ℤ) ^ prefixMass m q T * E (q + T)

/-- Closed expansion of the residual fold. -/
def residualExpansion (m Q : ℕ → ℕ) (E : ℕ → ℤ) (q T : ℕ) : ℤ :=
  ∑ j ∈ Finset.range T,
    E (q + j) * (2 : ℤ) ^ prefixMass m q j *
      (3 : ℤ) ^ suffixMass Q q (j + 1) T

theorem suffixMass_succ (Q : ℕ → ℕ) (q j T : ℕ) (hj : j ≤ T) :
    suffixMass Q q j (T + 1) = suffixMass Q q j T + Q (q + T) := by
  exact Finset.sum_Ico_succ_top hj (fun i => Q (q + i))

/-- QM121e: exact long-block residual composition. -/
theorem residualFold_eq_expansion
    (m Q : ℕ → ℕ) (E : ℕ → ℤ) (q T : ℕ) :
    residualFold m Q E q T = residualExpansion m Q E q T := by
  induction T with
  | zero => simp [residualFold, residualExpansion]
  | succ T ih =>
      rw [residualFold, ih]
      simp only [residualExpansion, Finset.sum_range_succ]
      change
        (3 : ℤ) ^ Q (q + T) * residualExpansion m Q E q T +
            (2 : ℤ) ^ prefixMass m q T * E (q + T) =
          (∑ j ∈ Finset.range T,
            E (q + j) * (2 : ℤ) ^ prefixMass m q j *
              (3 : ℤ) ^ suffixMass Q q (j + 1) (T + 1)) +
            E (q + T) * (2 : ℤ) ^ prefixMass m q T *
              (3 : ℤ) ^ suffixMass Q q (T + 1) (T + 1)
      have hold :
          (3 : ℤ) ^ Q (q + T) * residualExpansion m Q E q T =
            ∑ j ∈ Finset.range T,
              E (q + j) * (2 : ℤ) ^ prefixMass m q j *
                (3 : ℤ) ^ suffixMass Q q (j + 1) (T + 1) := by
        rw [residualExpansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjT : j + 1 ≤ T := by
          simp only [Finset.mem_range] at hj
          omega
        rw [suffixMass_succ Q q (j + 1) T hjT, pow_add]
        ring
      rw [hold]
      simp [suffixMass]
      ring

/-- At ternary depth `d`, the prefix of a nonempty residual fold vanishes as
soon as the final cycle has ternary mass at least `d`; only the last residual
survives, multiplied by a binary unit. -/
theorem residualFold_last_modEq
    (m Q : ℕ → ℕ) (E : ℕ → ℤ) (q T d : ℕ)
    (hcover : d ≤ Q (q + T)) :
    residualFold m Q E q (T + 1) ≡
      (2 : ℤ) ^ prefixMass m q T * E (q + T) [ZMOD (3 : ℤ) ^ d] := by
  rw [Int.modEq_iff_dvd]
  change (3 : ℤ) ^ d ∣
    (2 : ℤ) ^ prefixMass m q T * E (q + T) -
      ((3 : ℤ) ^ Q (q + T) * residualFold m Q E q T +
        (2 : ℤ) ^ prefixMass m q T * E (q + T))
  have hdNat : 3 ^ d ∣ 3 ^ Q (q + T) := Nat.pow_dvd_pow 3 hcover
  have hdInt : (3 : ℤ) ^ d ∣ (3 : ℤ) ^ Q (q + T) := by
    exact Int.natCast_dvd_natCast.mpr hdNat
  have hmul : (3 : ℤ) ^ d ∣
      (3 : ℤ) ^ Q (q + T) * residualFold m Q E q T :=
    dvd_mul_of_dvd_left hdInt _
  have heq :
      (2 : ℤ) ^ prefixMass m q T * E (q + T) -
          ((3 : ℤ) ^ Q (q + T) * residualFold m Q E q T +
            (2 : ℤ) ^ prefixMass m q T * E (q + T)) =
        -((3 : ℤ) ^ Q (q + T) * residualFold m Q E q T) := by ring
  rw [heq]
  exact dvd_neg.mpr hmul

/-- Consequently a fixed-depth long-block divisibility test is equivalent to
testing only the final residual.  Earlier residuals cannot make the result
nonzero or zero at this depth. -/
theorem residualFold_dvd_iff_last_dvd
    (m Q : ℕ → ℕ) (E : ℕ → ℤ) (q T d : ℕ)
    (hcover : d ≤ Q (q + T)) :
    (3 : ℤ) ^ d ∣ residualFold m Q E q (T + 1) ↔
      (3 : ℤ) ^ d ∣ E (q + T) := by
  have hmod := residualFold_last_modEq m Q E q T d hcover
  have hdiff := (Int.modEq_iff_dvd.mp hmod)
  have hsame :
      ((3 : ℤ) ^ d ∣ residualFold m Q E q (T + 1)) ↔
        ((3 : ℤ) ^ d ∣
          (2 : ℤ) ^ prefixMass m q T * E (q + T)) := by
    constructor
    · intro hleft
      simpa using hdiff.add hleft
    · intro hright
      simpa using dvd_sub hright hdiff
  rw [hsame]
  have hcop : IsCoprime ((3 : ℤ) ^ d)
      ((2 : ℤ) ^ prefixMass m q T) :=
    EtherCounterBareGlue.isCoprime_three_pow_two_pow d (prefixMass m q T)
  constructor
  · exact hcop.dvd_of_dvd_mul_left
  · intro hdvd
    exact dvd_mul_of_dvd_right hdvd _

end EtherCounterResidualFold
end KontoroC

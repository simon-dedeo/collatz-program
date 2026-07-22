/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.RankOneBankBoundary

/-!
# Exact link arithmetic for the synthesized-marker bank

The rank-one normal form has source and output slopes

`2^(P+155) * M` and `2 * M * 3^Q`.

This file isolates the arithmetic which must be checked before a collection
of finite instructions can be called a dispatcher.  Their slope gcd is
exactly `2*M`.  Consequently an output base `Y` can link to a source base
`X` only if the two bases agree modulo `2*M`.  Once their difference is
written as `2*M*c`, an exact link forces one dyadic congruence on the current
register at precision `P+154`.

These are necessary closure conditions, not an existence theorem for an
infinite Collatz orbit.
-/

namespace KontoroC

namespace MarkerBankLink

def sourceCoefficient (P M : ℕ) : ℕ :=
  2 ^ (P + 155) * M

def outputCoefficient (Q M : ℕ) : ℕ :=
  2 * M * 3 ^ Q

/-- The common slope divisor is exactly the visibly shared `2*M`; no hidden
power of two or three remains after the common register factor is removed. -/
theorem coefficient_gcd (P Q M : ℕ) :
    Nat.gcd (sourceCoefficient P M) (outputCoefficient Q M) = 2 * M := by
  rw [sourceCoefficient, outputCoefficient]
  rw [show 2 ^ (P + 155) = 2 * 2 ^ (P + 154) by
    rw [show P + 155 = (P + 154) + 1 by omega, pow_succ]
    ring]
  rw [show 2 * 2 ^ (P + 154) * M =
      (2 ^ (P + 154)) * (2 * M) by ring]
  rw [show 2 * M * 3 ^ Q = (3 ^ Q) * (2 * M) by ring]
  rw [Nat.gcd_mul_right]
  have hcop : Nat.Coprime (2 ^ (P + 154)) (3 ^ Q) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  rw [hcop.gcd_eq_one, one_mul]

theorem common_dvd_sourceCoefficient (P M : ℕ) :
    2 * M ∣ sourceCoefficient P M := by
  refine ⟨2 ^ (P + 154), ?_⟩
  rw [sourceCoefficient]
  rw [show P + 155 = (P + 154) + 1 by omega, pow_succ]
  ring

theorem common_dvd_outputCoefficient (Q M : ℕ) :
    2 * M ∣ outputCoefficient Q M := by
  refine ⟨3 ^ Q, ?_⟩
  simp [outputCoefficient, mul_assoc]

/-- Any genuine output-to-source link must first pass the base congruence
`X = Y (mod 2*M)`. -/
theorem base_modEq_of_link {X Y P Q M v v' : ℕ}
    (hlink :
      X + sourceCoefficient P M * v' =
        Y + outputCoefficient Q M * v) :
    X ≡ Y [MOD 2 * M] := by
  have hs : sourceCoefficient P M * v' ≡ 0 [MOD 2 * M] :=
    ((common_dvd_sourceCoefficient P M).mul_right v').modEq_zero_nat
  have ho : outputCoefficient Q M * v ≡ 0 [MOD 2 * M] :=
    ((common_dvd_outputCoefficient Q M).mul_right v).modEq_zero_nat
  have hsum :
      X + sourceCoefficient P M * v' ≡
        Y + outputCoefficient Q M * v [MOD 2 * M] :=
    congrArg (fun n ↦ n % (2 * M)) hlink
  exact (hs.trans ho.symm).add_iff_right.mp hsum

/-- If `Y-X=2*M*c`, cancellation of the visible common factor puts a link
in its primitive one-register form. -/
theorem normalize_link {X Y P Q M v v' c : ℕ}
    (hM : 0 < M)
    (hbase : Y = X + 2 * M * c)
    (hlink :
      X + sourceCoefficient P M * v' =
        Y + outputCoefficient Q M * v) :
    2 ^ (P + 154) * v' = c + 3 ^ Q * v := by
  have hfactor : 0 < 2 * M := by omega
  apply Nat.eq_of_mul_eq_mul_left hfactor
  rw [hbase, sourceCoefficient, outputCoefficient] at hlink
  have hcancel :
      2 ^ (P + 155) * M * v' =
        2 * M * c + 2 * M * 3 ^ Q * v := by
    apply Nat.add_left_cancel (n := X)
    simpa [Nat.add_assoc] using hlink
  calc
    2 * M * (2 ^ (P + 154) * v') =
        2 ^ (P + 155) * M * v' := by
      rw [show P + 155 = (P + 154) + 1 by omega, pow_succ]
      ring
    _ = 2 * M * c + 2 * M * 3 ^ Q * v := hcancel
    _ = 2 * M * (c + 3 ^ Q * v) := by ring

/-- Thus a linked current register lies in a prescribed dyadic cylinder. -/
theorem register_congruence_of_link {X Y P Q M v v' c : ℕ}
    (hM : 0 < M)
    (hbase : Y = X + 2 * M * c)
    (hlink :
      X + sourceCoefficient P M * v' =
        Y + outputCoefficient Q M * v) :
    c + 3 ^ Q * v ≡ 0 [MOD 2 ^ (P + 154)] := by
  rw [← normalize_link hM hbase hlink]
  exact (dvd_mul_right _ _).modEq_zero_nat

/-- The opposite ordering of the bases gives the companion primitive link
equation. -/
theorem normalize_link_reverse {X Y P Q M v v' c : ℕ}
    (hM : 0 < M)
    (hbase : X = Y + 2 * M * c)
    (hlink :
      X + sourceCoefficient P M * v' =
        Y + outputCoefficient Q M * v) :
    c + 2 ^ (P + 154) * v' = 3 ^ Q * v := by
  have hfactor : 0 < 2 * M := by omega
  apply Nat.eq_of_mul_eq_mul_left hfactor
  rw [hbase, sourceCoefficient, outputCoefficient] at hlink
  have hcancel :
      2 * M * c + 2 ^ (P + 155) * M * v' =
        2 * M * 3 ^ Q * v := by
    apply Nat.add_left_cancel (n := Y)
    simpa [Nat.add_assoc] using hlink
  calc
    2 * M * (c + 2 ^ (P + 154) * v') =
        2 * M * c + 2 ^ (P + 155) * M * v' := by
      rw [show P + 155 = (P + 154) + 1 by omega, pow_succ]
      ring
    _ = 2 * M * 3 ^ Q * v := hcancel
    _ = 2 * M * (3 ^ Q * v) := by ring

/-- In the reverse-base case, the current register is congruent to the
normalized base gap after multiplication by the odd coefficient. -/
theorem register_congruence_of_link_reverse {X Y P Q M v v' c : ℕ}
    (hM : 0 < M)
    (hbase : X = Y + 2 * M * c)
    (hlink :
      X + sourceCoefficient P M * v' =
        Y + outputCoefficient Q M * v) :
    3 ^ Q * v ≡ c [MOD 2 ^ (P + 154)] := by
  rw [← normalize_link_reverse hM hbase hlink]
  exact (dvd_mul_right _ _).modEq_zero_nat.add_left c

/-- For fixed source/output bases and opcodes, two linkable current registers
must occupy the same dyadic residue class.  Oddness of `3^Q` is what permits
cancellation. -/
theorem linked_registers_modEq {X Y P Q M v₁ v₂ v₁' v₂' c : ℕ}
    (hM : 0 < M)
    (hbase : Y = X + 2 * M * c)
    (hlink₁ :
      X + sourceCoefficient P M * v₁' =
        Y + outputCoefficient Q M * v₁)
    (hlink₂ :
      X + sourceCoefficient P M * v₂' =
        Y + outputCoefficient Q M * v₂) :
    v₁ ≡ v₂ [MOD 2 ^ (P + 154)] := by
  have h₁ := register_congruence_of_link hM hbase hlink₁
  have h₂ := register_congruence_of_link hM hbase hlink₂
  have hmul :
      3 ^ Q * v₁ ≡ 3 ^ Q * v₂ [MOD 2 ^ (P + 154)] := by
    exact Nat.ModEq.rfl.add_left_cancel (h₁.trans h₂.symm)
  apply Nat.ModEq.cancel_left_of_coprime _ hmul
  exact ((by norm_num : Nat.Coprime 2 3).pow (P + 154) Q).gcd_eq_one

end MarkerBankLink

end KontoroC

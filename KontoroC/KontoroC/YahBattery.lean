/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahPacketFamilyNoGo
import Mathlib.NumberTheory.Multiplicity

/-!
# Dyadic recharge battery for the YAH queue macro

For a pure ternary word `w`, set

`D(w) = value(w)+1`,
`Battery(w) = 2*length(w) + v₂(D(w))`.

Every reproducing macro satisfies `4*D(next)=9*D(w)`.  Since nine is odd,
the gained cell consumes exactly two units of dyadic valuation, so the
battery is exactly invariant.  This turns the finite `-1 mod 4^r` obstruction
into a local conserved quantity and isolates what a neutral or shrinking
"recharge" macro would have to replenish.
-/

namespace KontoroC
namespace YahBattery

open YahQueueMacro
open YahPerpetualGrowthNoGo

def defect (w : List Trit) : ℕ := tritEvalFrom 1 w + 1

def battery (w : List Trit) : ℕ :=
  2 * w.length + padicValNat 2 (defect w)

theorem defect_pos (w : List Trit) : 0 < defect w := by
  simp [defect]

/-- The fixed-point balance removes exactly two powers of two from the
positive defect. -/
theorem padicVal_defect_growth {D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hbalance : 4 * E = 9 * D) :
    padicValNat 2 E + 2 = padicValNat 2 D := by
  have hfour : 4 ≠ 0 := by norm_num
  have hnine : 9 ≠ 0 := by norm_num
  have hv := congrArg (padicValNat 2) hbalance
  rw [padicValNat.mul hfour hE.ne',
      padicValNat.mul hnine hD.ne'] at hv
  have hvalFour : padicValNat 2 4 = 2 := by
    rw [show 4 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hvalNine : padicValNat 2 9 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    norm_num
  rw [hvalFour, hvalNine] at hv
  omega

/-- QM9: every `+1` queue macro conserves the dyadic recharge battery. -/
theorem battery_invariant_of_growth (w : List Trit) (hnonempty : w ≠ [])
    (hgrows : (queueMacro w).length = w.length + 1) :
    battery (queueMacro w) = battery w := by
  have hbalance := queueMacro_growth_balance w hnonempty hgrows
  have hval := padicVal_defect_growth
    (defect_pos w) (defect_pos (queueMacro w)) (by
      simpa [defect] using hbalance)
  simp only [battery]
  rw [hgrows]
  omega

/-! ## Exact recharge laws -/

/-- Valuation extraction from a positive balance with one power of two on
the left and an odd multiplier on the right. -/
theorem padicVal_of_twoPow_balance {k E A X : ℕ}
    (hE : 0 < E) (hA : A ≠ 0) (hX : 0 < X) (hAodd : ¬2 ∣ A)
    (hbalance : 2 ^ k * E = A * X) :
    padicValNat 2 E + k = padicValNat 2 X := by
  have hpow : 2 ^ k ≠ 0 := by positivity
  have hv := congrArg (padicValNat 2) hbalance
  rw [padicValNat.mul hpow hE.ne', padicValNat.prime_pow,
      padicValNat.mul hA hX.ne',
      padicValNat.eq_zero_of_not_dvd hAodd] at hv
  omega

private theorem carry_eq_zero_of_bit_zero {c : Carry} (h : carryBit c = 0) :
    c = Carry.zero := by
  cases c <;> simp [carryBit] at h ⊢

private theorem carry_eq_one_of_bit_one {c : Carry} (h : carryBit c = 1) :
    c = Carry.one := by
  cases c <;> simp [carryBit] at h ⊢

/-- First QM10 row, written without natural subtraction:
`B(next)+3 = B(start)+v₂(D(start)+1)`. -/
theorem zeroHead_even_battery (v : List Trit)
    (heven : tritEvalFrom 1 (Trit.zero :: v) % 2 = 0) :
    battery (carrySweep Carry.one v) + 3 =
      battery (Trit.zero :: v) +
        padicValNat 2 (defect (Trit.zero :: v) + 1) := by
  let N := tritEvalFrom 1 (Trit.zero :: v)
  let E := tritEvalFrom 1 (carrySweep Carry.one v)
  let D := N + 1
  let DE := E + 1
  have hbit := macro_zero_terminal_bit v
  have hc : terminalCarry Carry.one v = Carry.zero :=
    carry_eq_zero_of_bit_zero (by omega)
  have hvalue := carrySweep_value 1 Carry.one v
  simp [hc, carryBit] at hvalue
  have hN : N = tritEvalFrom 3 v := rfl
  have hdefect : 2 * DE = D + 1 := by
    dsimp [DE, D, E, N]
    nlinarith [hN]
  have hval := padicVal_of_twoPow_balance
    (k := 1) (E := DE) (A := 1) (X := D + 1)
    (by dsimp [DE]; omega) (by omega) (by dsimp [D]; omega)
    (by norm_num) (by simpa using hdefect)
  have hDodd : ¬2 ∣ D := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [D, N]
    omega
  have hvalD : padicValNat 2 D = 0 :=
    padicValNat.eq_zero_of_not_dvd hDodd
  have hlen := macro_zero_length_charge v
  simp [hc, carryBit] at hlen
  simp only [battery, defect]
  change 2 * (carrySweep Carry.one v).length + padicValNat 2 DE + 3 =
    2 * (Trit.zero :: v).length + padicValNat 2 D +
      padicValNat 2 (D + 1)
  simp only [List.length_cons]
  omega

/-- Second QM10 row: an odd zero-head macro preserves length and spends one
unit of battery. -/
theorem zeroHead_odd_battery (v : List Trit)
    (hodd : tritEvalFrom 1 (Trit.zero :: v) % 2 = 1) :
    battery (carrySweep Carry.one v) + 1 =
      battery (Trit.zero :: v) := by
  let N := tritEvalFrom 1 (Trit.zero :: v)
  let E := tritEvalFrom 1 (carrySweep Carry.one v)
  let D := N + 1
  let DE := E + 1
  have hbit := macro_zero_terminal_bit v
  have hc : terminalCarry Carry.one v = Carry.one :=
    carry_eq_one_of_bit_one (by omega)
  have hvalue := carrySweep_value 1 Carry.one v
  simp [hc, carryBit] at hvalue
  have hN : N = tritEvalFrom 3 v := rfl
  have hdefect : 2 * DE = 3 * D := by
    dsimp [DE, D, E, N]
    nlinarith [hN]
  have hval := padicVal_of_twoPow_balance
    (k := 1) (E := DE) (A := 3) (X := D)
    (by dsimp [DE]; omega) (by omega) (by dsimp [D]; omega)
    (by norm_num) (by simpa using hdefect)
  have hlen := macro_zero_length_charge v
  simp [hc, carryBit] at hlen
  simp only [battery, defect]
  change 2 * (carrySweep Carry.one v).length + padicValNat 2 DE + 1 =
    2 * (Trit.zero :: v).length + padicValNat 2 D
  simp only [List.length_cons]
  omega

/-! The remaining four rows are uniform in heads one and two.  The initial
carry selects the head: carry zero means trit one, and carry one means trit
two. -/

def twoHeadTrit : Carry → Trit
  | Carry.zero => Trit.one
  | Carry.one => Trit.two

def twoHeadWord (c : Carry) (v : List Trit) : List Trit :=
  twoHeadTrit c :: v

def twoHeadEndpoint (c : Carry) (v : List Trit) : List Trit :=
  carrySweep Carry.zero (carrySweep c v)

@[simp] theorem twoHeadWord_value (c : Carry) (v : List Trit) :
    tritEvalFrom 1 (twoHeadWord c v) =
      tritEvalFrom (4 + carryBit c) v := by
  cases c <;> rfl

private theorem twoSweep_carries_mod_zero (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom (4 + carryBit c) v % 4 = 0) :
    terminalCarry c v = Carry.zero ∧
      terminalCarry Carry.zero (carrySweep c v) = Carry.zero := by
  have hres := twoSweep_residue c v
  rw [hmod] at hres
  generalize hfc : terminalCarry c v = fc at hres ⊢
  generalize hsc : terminalCarry Carry.zero (carrySweep c v) = sc at hres ⊢
  cases fc <;> cases sc <;> simp [carryBit] at hres ⊢

private theorem twoSweep_carries_mod_one (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom (4 + carryBit c) v % 4 = 1) :
    terminalCarry c v = Carry.one ∧
      terminalCarry Carry.zero (carrySweep c v) = Carry.zero := by
  have hres := twoSweep_residue c v
  rw [hmod] at hres
  generalize hfc : terminalCarry c v = fc at hres ⊢
  generalize hsc : terminalCarry Carry.zero (carrySweep c v) = sc at hres ⊢
  cases fc <;> cases sc <;> simp [carryBit] at hres ⊢

private theorem twoSweep_carries_mod_two (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom (4 + carryBit c) v % 4 = 2) :
    terminalCarry c v = Carry.zero ∧
      terminalCarry Carry.zero (carrySweep c v) = Carry.one := by
  have hres := twoSweep_residue c v
  rw [hmod] at hres
  generalize hfc : terminalCarry c v = fc at hres ⊢
  generalize hsc : terminalCarry Carry.zero (carrySweep c v) = sc at hres ⊢
  cases fc <;> cases sc <;> simp [carryBit] at hres ⊢

private theorem twoSweep_carries_mod_three (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom (4 + carryBit c) v % 4 = 3) :
    terminalCarry c v = Carry.one ∧
      terminalCarry Carry.zero (carrySweep c v) = Carry.one := by
  have hres := twoSweep_residue c v
  rw [hmod] at hres
  generalize hfc : terminalCarry c v = fc at hres ⊢
  generalize hsc : terminalCarry Carry.zero (carrySweep c v) = sc at hres ⊢
  cases fc <;> cases sc <;> simp [carryBit] at hres ⊢

private theorem twoSweep_defect_balance_zero (c : Carry) (v : List Trit)
    (hfirst : terminalCarry c v = Carry.zero)
    (hsecond : terminalCarry Carry.zero (carrySweep c v) = Carry.zero) :
    4 * defect (twoHeadEndpoint c v) = defect (twoHeadWord c v) + 3 := by
  have h1 := carrySweep_value 2 c v
  have h2 := carrySweep_value 1 Carry.zero (carrySweep c v)
  cases c <;>
    simp [hfirst, hsecond, carryBit, defect, twoHeadEndpoint] at h1 h2 ⊢ <;>
    nlinarith

private theorem twoSweep_defect_balance_one (c : Carry) (v : List Trit)
    (hfirst : terminalCarry c v = Carry.one)
    (hsecond : terminalCarry Carry.zero (carrySweep c v) = Carry.zero) :
    4 * defect (twoHeadEndpoint c v) =
      3 * defect (twoHeadWord c v) + 2 := by
  have h1 := carrySweep_value 2 c v
  have h2 := carrySweep_value 1 Carry.zero (carrySweep c v)
  cases c <;>
    simp [hfirst, hsecond, carryBit, defect, twoHeadEndpoint] at h1 h2 ⊢ <;>
    nlinarith

private theorem twoSweep_defect_balance_two (c : Carry) (v : List Trit)
    (hfirst : terminalCarry c v = Carry.zero)
    (hsecond : terminalCarry Carry.zero (carrySweep c v) = Carry.one) :
    4 * defect (twoHeadEndpoint c v) =
      3 * (defect (twoHeadWord c v) + 1) := by
  have h1 := carrySweep_value 2 c v
  have h2 := carrySweep_value 1 Carry.zero (carrySweep c v)
  cases c <;>
    simp [hfirst, hsecond, carryBit, defect, twoHeadEndpoint] at h1 h2 ⊢ <;>
    nlinarith

private theorem twoSweep_defect_balance_three (c : Carry) (v : List Trit)
    (hfirst : terminalCarry c v = Carry.one)
    (hsecond : terminalCarry Carry.zero (carrySweep c v) = Carry.one) :
    4 * defect (twoHeadEndpoint c v) =
      9 * defect (twoHeadWord c v) := by
  have h := twoSweep_growth_balance c v hfirst hsecond
  simp only [defect, twoHeadEndpoint, twoHeadWord_value]
  nlinarith

private theorem padicVal_eq_one_of_mod_four_eq_two {D : ℕ} (hD : D % 4 = 2) :
    padicValNat 2 D = 1 := by
  have hD0 : D ≠ 0 := by omega
  have hdvdTwo : 2 ^ 1 ∣ D := by
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num
    omega
  have hnotFour : ¬2 ^ 2 ∣ D := by
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num
    omega
  have hone : 1 ≤ padicValNat 2 D :=
    (Nat.pow_dvd_iff_le_padicValNat (by omega) hD0).mp hdvdTwo
  have hnotTwo : ¬2 ≤ padicValNat 2 D := by
    intro h
    exact hnotFour ((Nat.pow_dvd_iff_le_padicValNat (by omega) hD0).mpr h)
  omega

/-- QM10, residue zero for either nonzero head. -/
theorem twoHead_mod_zero_battery (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom 1 (twoHeadWord c v) % 4 = 0) :
    battery (twoHeadEndpoint c v) + 4 =
      battery (twoHeadWord c v) +
        padicValNat 2 (defect (twoHeadWord c v) + 3) := by
  have hmod' : tritEvalFrom (4 + carryBit c) v % 4 = 0 := by simpa using hmod
  obtain ⟨hfirst, hsecond⟩ := twoSweep_carries_mod_zero c v hmod'
  have hbalance := twoSweep_defect_balance_zero c v hfirst hsecond
  have hval := padicVal_of_twoPow_balance
    (k := 2) (E := defect (twoHeadEndpoint c v)) (A := 1)
    (X := defect (twoHeadWord c v) + 3)
    (defect_pos _) (by omega) (by have := defect_pos (twoHeadWord c v); omega)
    (by norm_num) (by simpa using hbalance)
  have hDodd : ¬2 ∣ defect (twoHeadWord c v) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp only [defect, twoHeadWord_value]
    omega
  have hvalD : padicValNat 2 (defect (twoHeadWord c v)) = 0 :=
    padicValNat.eq_zero_of_not_dvd hDodd
  have hlen1 := carrySweep_length c v
  have hlen2 := carrySweep_length Carry.zero (carrySweep c v)
  have hlen : (twoHeadEndpoint c v).length + 1 = (twoHeadWord c v).length := by
    simp only [twoHeadEndpoint, twoHeadWord, List.length_cons]
    simp [hfirst, hsecond, carryBit] at hlen1 hlen2
    omega
  simp only [battery]
  omega

/-- QM10, residue one for either nonzero head. -/
theorem twoHead_mod_one_battery (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom 1 (twoHeadWord c v) % 4 = 1) :
    battery (twoHeadEndpoint c v) + 3 =
      battery (twoHeadWord c v) +
        padicValNat 2 (3 * defect (twoHeadWord c v) + 2) := by
  have hmod' : tritEvalFrom (4 + carryBit c) v % 4 = 1 := by simpa using hmod
  obtain ⟨hfirst, hsecond⟩ := twoSweep_carries_mod_one c v hmod'
  have hbalance := twoSweep_defect_balance_one c v hfirst hsecond
  have hval := padicVal_of_twoPow_balance
    (k := 2) (E := defect (twoHeadEndpoint c v)) (A := 1)
    (X := 3 * defect (twoHeadWord c v) + 2)
    (defect_pos _) (by omega) (by have := defect_pos (twoHeadWord c v); omega)
    (by norm_num) (by simpa using hbalance)
  have hDmod : defect (twoHeadWord c v) % 4 = 2 := by
    simp only [defect]
    omega
  have hvalD := padicVal_eq_one_of_mod_four_eq_two hDmod
  have hlen1 := carrySweep_length c v
  have hlen2 := carrySweep_length Carry.zero (carrySweep c v)
  have hlen : (twoHeadEndpoint c v).length = (twoHeadWord c v).length := by
    simp only [twoHeadEndpoint, twoHeadWord, List.length_cons]
    simp [hfirst, hsecond, carryBit] at hlen1 hlen2
    omega
  simp only [battery]
  omega

/-- QM10, residue two for either nonzero head. -/
theorem twoHead_mod_two_battery (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom 1 (twoHeadWord c v) % 4 = 2) :
    battery (twoHeadEndpoint c v) + 2 =
      battery (twoHeadWord c v) +
        padicValNat 2 (defect (twoHeadWord c v) + 1) := by
  have hmod' : tritEvalFrom (4 + carryBit c) v % 4 = 2 := by simpa using hmod
  obtain ⟨hfirst, hsecond⟩ := twoSweep_carries_mod_two c v hmod'
  have hbalance := twoSweep_defect_balance_two c v hfirst hsecond
  have hval := padicVal_of_twoPow_balance
    (k := 2) (E := defect (twoHeadEndpoint c v)) (A := 3)
    (X := defect (twoHeadWord c v) + 1)
    (defect_pos _) (by omega) (by have := defect_pos (twoHeadWord c v); omega)
    (by norm_num) (by simpa using hbalance)
  have hDodd : ¬2 ∣ defect (twoHeadWord c v) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp only [defect]
    omega
  have hvalD : padicValNat 2 (defect (twoHeadWord c v)) = 0 :=
    padicValNat.eq_zero_of_not_dvd hDodd
  have hlen1 := carrySweep_length c v
  have hlen2 := carrySweep_length Carry.zero (carrySweep c v)
  have hlen : (twoHeadEndpoint c v).length = (twoHeadWord c v).length := by
    simp only [twoHeadEndpoint, twoHeadWord, List.length_cons]
    simp [hfirst, hsecond, carryBit] at hlen1 hlen2
    omega
  simp only [battery]
  omega

/-- QM10, residue three for either nonzero head: this is exactly the
reproducing case, so the battery is conserved. -/
theorem twoHead_mod_three_battery (c : Carry) (v : List Trit)
    (hmod : tritEvalFrom 1 (twoHeadWord c v) % 4 = 3) :
    battery (twoHeadEndpoint c v) = battery (twoHeadWord c v) := by
  have hmod' : tritEvalFrom (4 + carryBit c) v % 4 = 3 := by simpa using hmod
  obtain ⟨hfirst, hsecond⟩ := twoSweep_carries_mod_three c v hmod'
  have hbalance := twoSweep_defect_balance_three c v hfirst hsecond
  have hval := padicVal_defect_growth
    (defect_pos (twoHeadWord c v)) (defect_pos (twoHeadEndpoint c v)) hbalance
  have hlen1 := carrySweep_length c v
  have hlen2 := carrySweep_length Carry.zero (carrySweep c v)
  have hlen : (twoHeadEndpoint c v).length = (twoHeadWord c v).length + 1 := by
    simp only [twoHeadEndpoint, twoHeadWord, List.length_cons]
    simp [hfirst, hsecond, carryBit] at hlen1 hlen2
    omega
  simp only [battery]
  omega

end YahBattery
end KontoroC

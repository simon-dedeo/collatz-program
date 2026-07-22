/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerPadic
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Thue--Morse charge-bouncer schedules

For a two-symbol Thue--Morse opcode schedule, pairs of consecutive symbols
contain one copy of each symbol.  This file proves that the apparently
nonstationary weighted defect series therefore collapses to an affine
transform of the ordinary one-variable Thue--Morse power series.

The result is algebraic and exact.  It does not assume, or prove, an
irrationality theorem for the resulting 2-adic Mahler value.
-/

namespace KontoroC

open Filter Topology MersennePacketRenewal

/-- The parity of the sum of the binary digits of `n`, as a natural bit. -/
def thueMorseBit (n : ℕ) : ℕ :=
  (Nat.digits 2 n).sum % 2

theorem thueMorseBit_lt_two (n : ℕ) : thueMorseBit n < 2 := by
  exact Nat.mod_lt _ (by omega)

theorem thueMorseBit_eq_zero_or_one (n : ℕ) :
    thueMorseBit n = 0 ∨ thueMorseBit n = 1 := by
  have h := thueMorseBit_lt_two n
  omega

@[simp]
theorem thueMorseBit_zero : thueMorseBit 0 = 0 := by
  simp [thueMorseBit]

@[simp]
theorem thueMorseBit_one : thueMorseBit 1 = 1 := by
  simp [thueMorseBit]

@[simp]
theorem thueMorseBit_even (n : ℕ) :
    thueMorseBit (2 * n) = thueMorseBit n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [thueMorseBit, thueMorseBit,
      Nat.digits_base_mul (by omega) (Nat.pos_of_ne_zero hn)]
    simp

@[simp]
theorem thueMorseBit_odd (n : ℕ) :
    thueMorseBit (2 * n + 1) = 1 - thueMorseBit n := by
  rw [thueMorseBit, thueMorseBit]
  have hd := Nat.digits_add 2 (by omega) 1 n (by omega)
    (Or.inl (by omega))
  rw [show 2 * n + 1 = 1 + 2 * n by omega, hd]
  simp only [List.sum_cons]
  have hmod := Nat.mod_lt (Nat.digits 2 n).sum (by omega : 0 < 2)
  omega

/-- Select the symbol indexed by a natural bit.  Values other than zero are
sent to the second symbol; `thueMorseBit_lt_two` ensures only `0` and `1`
occur below. -/
def bitSelect {R : Type*} (x₀ x₁ : R) (b : ℕ) : R :=
  if b = 0 then x₀ else x₁

@[simp] theorem bitSelect_zero {R : Type*} (x₀ x₁ : R) :
    bitSelect x₀ x₁ 0 = x₀ := by simp [bitSelect]

@[simp] theorem bitSelect_one {R : Type*} (x₀ x₁ : R) :
    bitSelect x₀ x₁ 1 = x₁ := by simp [bitSelect]

theorem bitSelect_thue_complement_mul {R : Type*} [CommMonoid R]
    (x₀ x₁ : R) (n : ℕ) :
    bitSelect x₀ x₁ (thueMorseBit n) *
        bitSelect x₀ x₁ (1 - thueMorseBit n) = x₀ * x₁ := by
  rcases thueMorseBit_eq_zero_or_one n with h | h
  · simp [h]
  · simp [h, mul_comm]

/-- A two-symbol word read along the Thue--Morse sequence. -/
def thueMorseWord {R : Type*} (x₀ x₁ : R) (n : ℕ) : R :=
  bitSelect x₀ x₁ (thueMorseBit n)

@[simp]
theorem thueMorseWord_even {R : Type*} (x₀ x₁ : R) (n : ℕ) :
    thueMorseWord x₀ x₁ (2 * n) = thueMorseWord x₀ x₁ n := by
  simp [thueMorseWord]

theorem thueMorseWord_even_mul_odd {R : Type*} [CommMonoid R]
    (x₀ x₁ : R) (n : ℕ) :
    thueMorseWord x₀ x₁ (2 * n) *
        thueMorseWord x₀ x₁ (2 * n + 1) = x₀ * x₁ := by
  simp only [thueMorseWord, thueMorseBit_even, thueMorseBit_odd]
  exact bitSelect_thue_complement_mul x₀ x₁ n

/-- Every completed pair contributes the same multiplicative weight. -/
theorem thueMorse_backwardPrefixProduct_even (a₀ a₁ : ℚ) (n : ℕ) :
    backwardPrefixProduct (thueMorseWord a₀ a₁) (2 * n) =
      (a₀ * a₁) ^ n := by
  induction n with
  | zero => simp [backwardPrefixProduct]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        backwardPrefixProduct, backwardPrefixProduct, ih]
      calc
        (a₀ * a₁) ^ n * thueMorseWord a₀ a₁ (2 * n) *
              thueMorseWord a₀ a₁ (2 * n + 1) =
            (a₀ * a₁) ^ n *
              (thueMorseWord a₀ a₁ (2 * n) *
                thueMorseWord a₀ a₁ (2 * n + 1)) := by ring
        _ = (a₀ * a₁) ^ n * (a₀ * a₁) := by
          rw [thueMorseWord_even_mul_odd]
        _ = (a₀ * a₁) ^ (n + 1) := by rw [pow_succ]

/-- The prefix product just after the even member of a pair. -/
theorem thueMorse_backwardPrefixProduct_odd (a₀ a₁ : ℚ) (n : ℕ) :
    backwardPrefixProduct (thueMorseWord a₀ a₁) (2 * n + 1) =
      (a₀ * a₁) ^ n * thueMorseWord a₀ a₁ n := by
  rw [backwardPrefixProduct, thueMorse_backwardPrefixProduct_even,
    thueMorseWord_even]

/-- The two effective additive digits after pairing the original schedule. -/
def thueMorsePairDigit (a₀ a₁ d₀ d₁ : ℚ) (b : ℕ) : ℚ :=
  bitSelect (d₀ + a₀ * d₁) (d₁ + a₁ * d₀) b

/-- Exact contribution of positions `2n` and `2n+1`. -/
theorem thueMorse_defect_pair (a₀ a₁ d₀ d₁ : ℚ) (n : ℕ) :
    backwardPrefixProduct (thueMorseWord a₀ a₁) (2 * n) *
          thueMorseWord d₀ d₁ (2 * n) +
        backwardPrefixProduct (thueMorseWord a₀ a₁) (2 * n + 1) *
          thueMorseWord d₀ d₁ (2 * n + 1) =
      (a₀ * a₁) ^ n *
        thueMorsePairDigit a₀ a₁ d₀ d₁ (thueMorseBit n) := by
  rw [thueMorse_backwardPrefixProduct_even,
    thueMorse_backwardPrefixProduct_odd]
  rcases thueMorseBit_eq_zero_or_one n with h | h <;>
    simp [thueMorseWord, thueMorsePairDigit, h] <;> ring

/-- Finite pairing identity for the backward defect.  This is independent of
all convergence and p-adic arguments. -/
theorem thueMorse_backwardPrefixDefect_even
    (a₀ a₁ d₀ d₁ : ℚ) (n : ℕ) :
    backwardPrefixDefect (thueMorseWord a₀ a₁)
        (thueMorseWord d₀ d₁) (2 * n) =
      ∑ k ∈ Finset.range n,
        (a₀ * a₁) ^ k *
          thueMorsePairDigit a₀ a₁ d₀ d₁ (thueMorseBit k) := by
  induction n with
  | zero => simp [backwardPrefixDefect]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        backwardPrefixDefect, backwardPrefixDefect, ih,
        Finset.sum_range_succ]
      rw [add_assoc, thueMorse_defect_pair]

/-- A selected pair digit is affine in the Thue--Morse bit. -/
theorem thueMorsePairDigit_eq_affine (a₀ a₁ d₀ d₁ : ℚ) (n : ℕ) :
    thueMorsePairDigit a₀ a₁ d₀ d₁ (thueMorseBit n) =
      (d₀ + a₀ * d₁) +
        ((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁)) * thueMorseBit n := by
  rcases thueMorseBit_eq_zero_or_one n with h | h <;>
    simp [thueMorsePairDigit, h]

/-- The standard one-variable Thue--Morse power series in `ℚ₂`. -/
noncomputable def padicThueMorseSeries (z : ℚ_[2]) : ℚ_[2] :=
  ∑' n : ℕ, (thueMorseBit n : ℚ_[2]) * z ^ n

theorem norm_padicThueMorseTerm_le (z : ℚ_[2]) (n : ℕ) :
    ‖(thueMorseBit n : ℚ_[2]) * z ^ n‖ ≤ ‖z‖ ^ n := by
  rcases thueMorseBit_eq_zero_or_one n with h | h <;> simp [h]

theorem padicThueMorseTerm_tendsto_zero {z : ℚ_[2]} (hz : ‖z‖ < 1) :
    Tendsto (fun n : ℕ => (thueMorseBit n : ℚ_[2]) * z ^ n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_padicThueMorseTerm_le z)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz

theorem padicThueMorseTerm_summable {z : ℚ_[2]} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (thueMorseBit n : ℚ_[2]) * z ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using
    padicThueMorseTerm_tendsto_zero hz

/-- The infinite pairing identity.  The raw weighted-defect series is an
affine transform of one standard Thue--Morse Mahler value. -/
theorem thueMorse_padic_defect_tsum
    (a₀ a₁ d₀ d₁ : ℚ)
    (hraw : Summable (fun n : ℕ =>
      (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
        thueMorseWord d₀ d₁ n : ℚ_[2])))
    (hz : ‖((a₀ * a₁ : ℚ) : ℚ_[2])‖ < 1) :
    ∑' n : ℕ,
        (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
          thueMorseWord d₀ d₁ n : ℚ_[2]) =
      ((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
          (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
        (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
          padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2]) := by
  let f : ℕ → ℚ_[2] := fun n =>
    (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
      thueMorseWord d₀ d₁ n : ℚ_[2])
  let z : ℚ_[2] := ((a₀ * a₁ : ℚ) : ℚ_[2])
  let e₀ : ℚ_[2] := ((d₀ + a₀ * d₁ : ℚ) : ℚ_[2])
  let de : ℚ_[2] :=
    (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2])
  have hf : Summable f := by simpa [f] using hraw
  have heven : Summable (fun n => f (2 * n)) :=
    hf.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hodd : Summable (fun n => f (2 * n + 1)) :=
    hf.comp_injective (by
      intro x y h
      apply mul_right_injective₀ (two_ne_zero' ℕ)
      exact Nat.add_right_cancel h)
  have hgeom : Summable (fun n : ℕ => z ^ n) :=
    (hasSum_geometric_of_norm_lt_one (by simpa [z] using hz)).summable
  have htm : Summable (fun n : ℕ => (thueMorseBit n : ℚ_[2]) * z ^ n) :=
    padicThueMorseTerm_summable (by simpa [z] using hz)
  calc
    (∑' n : ℕ,
        (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
          thueMorseWord d₀ d₁ n : ℚ_[2])) = ∑' n : ℕ, f n := by rfl
    _ = (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) :=
      (tsum_even_add_odd heven hodd).symm
    _ = ∑' n : ℕ, (f (2 * n) + f (2 * n + 1)) :=
      (heven.tsum_add hodd).symm
    _ = ∑' n : ℕ,
        z ^ n * (e₀ + de * (thueMorseBit n : ℚ_[2])) := by
      apply tsum_congr
      intro n
      have hp := congrArg (fun q : ℚ => (q : ℚ_[2]))
        (thueMorse_defect_pair a₀ a₁ d₀ d₁ n)
      have ha := congrArg (fun q : ℚ => (q : ℚ_[2]))
        (thueMorsePairDigit_eq_affine a₀ a₁ d₀ d₁ n)
      simp only [Rat.cast_add, Rat.cast_mul] at hp ha
      simp only [f, z, e₀, de, Rat.cast_mul,
        Rat.cast_sub]
      rw [hp, ha]
      push_cast
      ring
    _ = ∑' n : ℕ,
        (e₀ * z ^ n + de * ((thueMorseBit n : ℚ_[2]) * z ^ n)) := by
      apply tsum_congr
      intro n
      ring
    _ = e₀ * (∑' n : ℕ, z ^ n) +
        de * (∑' n : ℕ, (thueMorseBit n : ℚ_[2]) * z ^ n) := by
      rw [hgeom.mul_left e₀ |>.tsum_add (htm.mul_left de),
        tsum_mul_left, tsum_mul_left]
    _ = e₀ * (1 - z)⁻¹ + de * padicThueMorseSeries z := by
      rw [tsum_geometric_of_norm_lt_one (by simpa [z] using hz)]
      rfl
    _ = ((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
          (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
        (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
          padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2]) := by rfl

namespace ChargeBouncerOpcodeSchedule

/-- Direct interface from a charge-bouncer schedule known to use two
Thue--Morse symbols to the standard Mahler value.  The convergence hypothesis
needed by the abstract pairing theorem is discharged by the bouncer's
uniform coefficient bound. -/
theorem padicDefectSum_eq_thueMorse
    (c : ChargeBouncerOpcodeSchedule) (a₀ a₁ d₀ d₁ : ℚ)
    (hcoeff : c.backwardCoeff = thueMorseWord a₀ a₁)
    (hdefect : c.backwardDefect = thueMorseWord d₀ d₁) :
    c.padicDefectSum =
      ((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
          (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
        (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
          padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2]) := by
  have ha₀ := c.norm_backwardCoeff_le_half 0
  have ha₁ := c.norm_backwardCoeff_le_half 1
  rw [hcoeff] at ha₀ ha₁
  have ha₀' : ‖(a₀ : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
    simpa only [thueMorseWord, thueMorseBit_zero, bitSelect_zero] using ha₀
  have ha₁' : ‖(a₁ : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
    simpa only [thueMorseWord, thueMorseBit_one, bitSelect_one] using ha₁
  have hzle : ‖((a₀ * a₁ : ℚ) : ℚ_[2])‖ ≤ ((2 : ℝ)⁻¹) ^ 2 := by
    rw [Rat.cast_mul, norm_mul, pow_two]
    exact mul_le_mul ha₀' ha₁' (norm_nonneg _) (by positivity)
  have hz : ‖((a₀ * a₁ : ℚ) : ℚ_[2])‖ < 1 :=
    hzle.trans_lt (by norm_num)
  have hterm : c.padicDefectTerm = fun n : ℕ =>
      (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
        thueMorseWord d₀ d₁ n : ℚ_[2]) := by
    funext n
    simp only [padicDefectTerm, hcoeff, hdefect]
  have hraw : Summable (fun n : ℕ =>
      (backwardPrefixProduct (thueMorseWord a₀ a₁) n *
        thueMorseWord d₀ d₁ n : ℚ_[2])) := by
    rw [← hterm]
    exact c.padicDefectTerm_summable
  rw [padicDefectSum, hterm]
  exact thueMorse_padic_defect_tsum a₀ a₁ d₀ d₁ hraw hz

/-- Sign-normalized form used by the no-ray endpoint. -/
theorem padicCandidate_eq_thueMorse
    (c : ChargeBouncerOpcodeSchedule) (a₀ a₁ d₀ d₁ : ℚ)
    (hcoeff : c.backwardCoeff = thueMorseWord a₀ a₁)
    (hdefect : c.backwardDefect = thueMorseWord d₀ d₁) :
    c.padicCandidate =
      -(((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
          (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
        (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
          padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2])) := by
  rw [padicCandidate, c.padicDefectSum_eq_thueMorse a₀ a₁ d₀ d₁
    hcoeff hdefect]

end ChargeBouncerOpcodeSchedule

/-- The rational multiplicative weight of one concrete bouncer opcode. -/
def chargeBouncerSymbolCoeff (m h : ℕ) : ℚ :=
  ((2 : ℚ) ^ 23 / (3 : ℚ) ^ 17) ^ m *
    ((2 : ℚ) ^ 154 / (3 : ℚ) ^ 114) ^ h

/-- The rational additive defect of one concrete bouncer opcode. -/
def chargeBouncerSymbolDefect (m : ℕ) : ℚ :=
  1 - ((2 : ℚ) ^ 23 / (3 : ℚ) ^ 17) ^ m

/-- The charge-bouncer schedule obtained by assigning one positive opcode to
each of the two Thue--Morse symbols. -/
def thueMorseChargeBouncerSchedule
    (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀) (hm₁ : 0 < m₁) (hh₁ : 0 < h₁) :
    ChargeBouncerOpcodeSchedule where
  defect n := thueMorseWord m₀ m₁ n
  recharge n := thueMorseWord h₀ h₁ n
  defect_pos n := by
    rcases thueMorseBit_eq_zero_or_one n with h | h <;>
      simp [thueMorseWord, h, hm₀, hm₁]
  recharge_pos n := by
    rcases thueMorseBit_eq_zero_or_one n with h | h <;>
      simp [thueMorseWord, h, hh₀, hh₁]

theorem thueMorseChargeBouncerSchedule_backwardCoeff
    (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀) (hm₁ : 0 < m₁) (hh₁ : 0 < h₁) :
    (thueMorseChargeBouncerSchedule m₀ h₀ m₁ h₁
      hm₀ hh₀ hm₁ hh₁).backwardCoeff =
      thueMorseWord (chargeBouncerSymbolCoeff m₀ h₀)
        (chargeBouncerSymbolCoeff m₁ h₁) := by
  funext n
  rw [ChargeBouncerOpcodeSchedule.backwardCoeff_factor]
  rcases thueMorseBit_eq_zero_or_one n with h | h <;>
    simp [thueMorseChargeBouncerSchedule, thueMorseWord,
      chargeBouncerSymbolCoeff, h]

theorem thueMorseChargeBouncerSchedule_backwardDefect
    (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀) (hm₁ : 0 < m₁) (hh₁ : 0 < h₁) :
    (thueMorseChargeBouncerSchedule m₀ h₀ m₁ h₁
      hm₀ hh₀ hm₁ hh₁).backwardDefect =
      thueMorseWord (chargeBouncerSymbolDefect m₀)
        (chargeBouncerSymbolDefect m₁) := by
  funext n
  rw [ChargeBouncerOpcodeSchedule.backwardDefect_eq_one_sub]
  rcases thueMorseBit_eq_zero_or_one n with h | h <;>
    simp [thueMorseChargeBouncerSchedule, thueMorseWord,
      chargeBouncerSymbolDefect, h]

/-- Fully explicit value of the 2-adic candidate selected by a two-opcode
Thue--Morse dispatcher. -/
theorem thueMorseChargeBouncerSchedule_candidate
    (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀) (hm₁ : 0 < m₁) (hh₁ : 0 < h₁) :
    let a₀ := chargeBouncerSymbolCoeff m₀ h₀
    let a₁ := chargeBouncerSymbolCoeff m₁ h₁
    let d₀ := chargeBouncerSymbolDefect m₀
    let d₁ := chargeBouncerSymbolDefect m₁
    (thueMorseChargeBouncerSchedule m₀ h₀ m₁ h₁
      hm₀ hh₀ hm₁ hh₁).padicCandidate =
      -(((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
          (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
        (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
          padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2])) := by
  dsimp only
  apply ChargeBouncerOpcodeSchedule.padicCandidate_eq_thueMorse
  · exact thueMorseChargeBouncerSchedule_backwardCoeff
      m₀ h₀ m₁ h₁ hm₀ hh₀ hm₁ hh₁
  · exact thueMorseChargeBouncerSchedule_backwardDefect
      m₀ h₀ m₁ h₁ hm₀ hh₀ hm₁ hh₁

/-- Final no-ray seam for a concrete two-opcode Thue--Morse dispatcher.  All
dynamical and convergence work is kernel-checked; only exclusion of positive
naturals from the displayed explicit Mahler value remains as a premise. -/
theorem no_thueMorse_chargeBouncer_ray_of_value_avoids_positiveNaturals
    (m₀ h₀ m₁ h₁ : ℕ)
    (hm₀ : 0 < m₀) (hh₀ : 0 < h₀) (hm₁ : 0 < m₁) (hh₁ : 0 < h₁)
    (havoid :
      let a₀ := chargeBouncerSymbolCoeff m₀ h₀
      let a₁ := chargeBouncerSymbolCoeff m₁ h₁
      let d₀ := chargeBouncerSymbolDefect m₀
      let d₁ := chargeBouncerSymbolDefect m₁
      ∀ u : ℕ, 0 < u →
        -(((d₀ + a₀ * d₁ : ℚ) : ℚ_[2]) *
            (1 - ((a₀ * a₁ : ℚ) : ℚ_[2]))⁻¹ +
          (((d₁ + a₁ * d₀) - (d₀ + a₀ * d₁) : ℚ) : ℚ_[2]) *
            padicThueMorseSeries ((a₀ * a₁ : ℚ) : ℚ_[2])) ≠
          (u : ℚ_[2])) :
    ¬∃ g : InfiniteChargeBouncerRay,
      g.schedule = thueMorseChargeBouncerSchedule m₀ h₀ m₁ h₁
        hm₀ hh₀ hm₁ hh₁ := by
  apply InfiniteChargeBouncerRay.no_ray_of_candidate_avoids_positiveNaturals
  intro u hu
  rw [thueMorseChargeBouncerSchedule_candidate
    m₀ h₀ m₁ h₁ hm₀ hh₀ hm₁ hh₁]
  exact havoid u hu

end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.PublicPayloadTheta

/-!
# Converse from one public theta lattice value

This file develops the arithmetic direction of QM151b.  In particular, it
does not postulate that a theta value lies on the ordinary lattice: it proves
what follows if one does.
-/

namespace KontoroC
namespace SelfWritingKL
namespace PublicTheta

/-- The reduced `Z/W` factorizations imply the literal public payload
recurrence.  This is the converse of the factor lemmas used to decode an
already supplied orbit. -/
theorem payload_recurrence_of_reduced_factors {m r r' h : ℕ} (hm : 0 < m)
    (hsource : Wbar r = 2 ^ (8 * m - 5) * h)
    (htarget : Zbar r' = 3 ^ (6 * m) * h) :
    2 ^ (8 * m + 15) * (17 * r') =
      3 ^ (6 * m + 11) * (17 * r) + branchDelta m := by
  have hbalance :
      2 ^ (8 * m - 5) * Zbar r' = 3 ^ (6 * m) * Wbar r := by
    rw [htarget, hsource]
    ring
  have hdelta := branchDelta_factor hm
  have hle := (branchDelta_raw_positive hm).le
  apply Nat.cast_injective (R := ℤ)
  have hbalanceInt := congrArg (fun n : ℕ => (n : ℤ)) hbalance
  have hdeltaInt := congrArg (fun n : ℕ => (n : ℤ)) hdelta
  push_cast at hbalanceInt hdeltaInt ⊢
  rw [Nat.cast_sub hle] at hdeltaInt
  simp only [Zbar, Wbar, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hbalanceInt
  have height : 8 * m + 15 = (8 * m - 5) + 20 := by omega
  have hdepth : 6 * m + 11 = 6 * m + 11 := rfl
  rw [height, hdepth, pow_add, pow_add]
  norm_num at hbalanceInt hdeltaInt ⊢
  apply mul_left_cancel₀ (by norm_num : (473 : ℤ) ≠ 0)
  linear_combination 17 * hbalanceInt - hdeltaInt

/-- The source `Wbar` factor determines the target `Zbar` residue modulo
`473`. -/
theorem target_core_mod_473 {m r h : ℕ} (hm : 0 < m)
    (hsource : Wbar r = 2 ^ (8 * m - 5) * h) :
    Nat.ModEq 473 (3 ^ (6 * m) * h) (Zbar 0) := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hs := congrArg (fun n : ℕ => (n : ZMod 473)) hsource
  simp only [Wbar, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow] at hs ⊢
  have hslope : (83790531 : ZMod 473) = 0 := by decide
  have hperiod : (3 : ZMod 473) ^ 6 = 2 ^ 8 := by decide
  have hbase : (32 : ZMod 473) * 4911712 = 29073613 := by decide
  rw [hslope] at hs
  rw [pow_mul, hperiod, ← pow_mul,
    show 8 * m = (8 * m - 5) + 5 by omega, pow_add]
  norm_num only [pow_succ, pow_zero]
  calc
    ((2 : ZMod 473) ^ (8 * m - 5) * 32) * h =
        32 * (2 ^ (8 * m - 5) * h) := by ring
    _ = 32 * 4911712 := by rw [← hs]; simp
    _ = 29073613 := hbase

/-- Divisibility of the next negative tail by `2^20` determines the same
target core modulo `2^20`. -/
theorem target_core_mod_two_pow {m h : ℕ}
    (hdiv : 2 ^ 20 ∣ 3 ^ (6 * m + 11) * h + 1) :
    Nat.ModEq (2 ^ 20) (3 ^ (6 * m) * h) (Zbar 0) := by
  rw [← ZMod.natCast_eq_natCast_iff]
  obtain ⟨k, hk⟩ := hdiv
  have hnext := congrArg (fun n : ℕ => (n : ZMod (2 ^ 20))) hk
  have hdet := congrArg (fun n : ℕ => (n : ZMod (2 ^ 20)))
    (reduced_determinant_identity 0)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
    Nat.cast_ofNat] at hnext hdet ⊢
  have hmod : ((2 : ZMod (2 ^ 20)) ^ 20) = 0 := by
    change ((2 ^ 20 : ℕ) : ZMod (2 ^ 20)) = 0
    exact ZMod.natCast_self (2 ^ 20)
  rw [hmod, zero_mul] at hnext hdet
  have hpow : (3 : ZMod (2 ^ 20)) ^ (6 * m + 11) =
      3 ^ 11 * 3 ^ (6 * m) := by
    rw [show 6 * m + 11 = 11 + 6 * m by omega, pow_add]
  rw [hpow] at hnext
  have hunit3 : IsUnit (3 : ZMod (2 ^ 20)) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ 20)).mpr (by norm_num)
  have hunit : IsUnit ((3 : ZMod (2 ^ 20)) ^ 11) := hunit3.pow 11
  apply hunit.mul_left_cancel
  apply add_right_cancel (b := (1 : ZMod (2 ^ 20)))
  simpa [mul_assoc] using hnext.trans hdet.symm

/-- The two local congruences put the target core on the unique nonnegative
`Zbar` lattice. -/
theorem exists_target_Zbar {m r h : ℕ} (hm : 0 < m)
    (hsource : Wbar r = 2 ^ (8 * m - 5) * h)
    (hdiv : 2 ^ 20 ∣ 3 ^ (6 * m + 11) * h + 1) :
    ∃ r' : ℕ, Zbar r' = 3 ^ (6 * m) * h := by
  let y := 3 ^ (6 * m) * h
  have h473 : Nat.ModEq 473 y (Zbar 0) :=
    target_core_mod_473 hm hsource
  have htwo : Nat.ModEq (2 ^ 20) y (Zbar 0) :=
    target_core_mod_two_pow hdiv
  have hcoprime : Nat.Coprime 473 (2 ^ 20) := by norm_num
  have hprod : Nat.ModEq (473 * 2 ^ 20) y (Zbar 0) :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp ⟨h473, htwo⟩
  have hzlt : Zbar 0 < 473 * 2 ^ 20 := by norm_num [Zbar]
  have hyMod : y % (473 * 2 ^ 20) = Zbar 0 := by
    rw [hprod]
    exact Nat.mod_eq_of_lt hzlt
  refine ⟨y / (473 * 2 ^ 20), ?_⟩
  change 29073613 + 495976448 * (y / (473 * 2 ^ 20)) = y
  have hyMod' : y % (473 * 2 ^ 20) = 29073613 := by
    simpa [Zbar] using hyMod
  rw [show 495976448 = 473 * 2 ^ 20 by norm_num, ← hyMod']
  exact Nat.mod_add_div y (473 * 2 ^ 20)

/-- One exact lattice hit propagates to the next suffix and simultaneously
produces the public payload recurrence needed by the orbit constructor. -/
theorem next_Wbar_lattice
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (t r : ℕ)
    (htail : padicTail m t =
      -(((2 : ℕ) ^ 20 * Wbar r : ℕ) : ℚ_[2])) :
    ∃ r' : ℕ,
      padicTail m (t + 1) =
          -(((2 : ℕ) ^ 20 * Wbar r' : ℕ) : ℚ_[2]) ∧
      2 ^ (8 * m t + 15) * (17 * r') =
        3 ^ (6 * m t + 11) * (17 * r) + branchDelta (m t) := by
  obtain ⟨h, hfactor, hnext⟩ := negative_integer_tail_step m hm t
    (2 ^ 20 * Wbar r) htail
  have hmt := hm t
  have hsource : Wbar r = 2 ^ (8 * m t - 5) * h := by
    apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ 20)
    calc
      2 ^ 20 * Wbar r = 2 ^ (8 * m t + 15) * h := hfactor
      _ = 2 ^ 20 * (2 ^ (8 * m t - 5) * h) := by
        rw [show 8 * m t + 15 = 20 + (8 * m t - 5) by omega, pow_add]
        ring
  obtain ⟨h', hfactor', _⟩ := negative_integer_tail_step m hm (t + 1)
    (3 ^ (6 * m t + 11) * h + 1) hnext
  have hexp : 20 ≤ 8 * m (t + 1) + 15 := by
    have := hm (t + 1)
    omega
  have hdiv : 2 ^ 20 ∣ 3 ^ (6 * m t + 11) * h + 1 := by
    rw [hfactor']
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hexp) h'
  obtain ⟨r', htarget⟩ := exists_target_Zbar (hm t) hsource hdiv
  refine ⟨r', ?_, payload_recurrence_of_reduced_factors
    (hm t) hsource htarget⟩
  have hnextValue :
      3 ^ (6 * m t + 11) * h + 1 = 2 ^ 20 * Wbar r' := by
    calc
      3 ^ (6 * m t + 11) * h + 1 =
          3 ^ 11 * (3 ^ (6 * m t) * h) + 1 := by
        rw [show 6 * m t + 11 = 11 + 6 * m t by omega, pow_add]
        ring
      _ = 3 ^ 11 * Zbar r' + 1 := by rw [htarget]
      _ = 2 ^ 20 * Wbar r' := reduced_determinant_identity r'
  rw [hnextValue] at hnext
  exact hnext

/-- The dependent state retained while recursively propagating a lattice
hit.  Storing the equality in the subtype prevents the recursion from ever
choosing an unrelated payload. -/
def WbarTailState (m : ℕ → ℕ) (t : ℕ) :=
  {r : ℕ // padicTail m t =
    -(((2 : ℕ) ^ 20 * Wbar r : ℕ) : ℚ_[2])}

@[simp] theorem padicTail_zero (m : ℕ → ℕ) :
    padicTail m 0 = padicSum m := by
  unfold padicTail
  congr 1
  funext j
  simp

noncomputable def WbarTailChain
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (r₀ : ℕ)
    (h₀ : padicTail m 0 =
      -(((2 : ℕ) ^ 20 * Wbar r₀ : ℕ) : ℚ_[2])) :
    (t : ℕ) → WbarTailState m t
  | 0 => ⟨r₀, h₀⟩
  | t + 1 => by
      let previous := WbarTailChain m hm r₀ h₀ t
      let witness := next_Wbar_lattice m hm t previous.1 previous.2
      exact ⟨Classical.choose witness, (Classical.choose_spec witness).1⟩

@[simp] theorem WbarTailChain_zero
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (r₀ : ℕ)
    (h₀ : padicTail m 0 =
      -(((2 : ℕ) ^ 20 * Wbar r₀ : ℕ) : ℚ_[2])) :
    (WbarTailChain m hm r₀ h₀ 0).1 = r₀ := rfl

theorem WbarTailChain_recurrence
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (r₀ : ℕ)
    (h₀ : padicTail m 0 =
      -(((2 : ℕ) ^ 20 * Wbar r₀ : ℕ) : ℚ_[2])) (t : ℕ) :
    2 ^ (8 * m t + 15) *
        (17 * (WbarTailChain m hm r₀ h₀ (t + 1)).1) =
      3 ^ (6 * m t + 11) *
          (17 * (WbarTailChain m hm r₀ h₀ t).1) + branchDelta (m t) := by
  let previous := WbarTailChain m hm r₀ h₀ t
  let witness := next_Wbar_lattice m hm t previous.1 previous.2
  change 2 ^ (8 * m t + 15) *
        (17 * (Classical.choose witness)) =
      3 ^ (6 * m t + 11) * (17 * previous.1) + branchDelta (m t)
  exact (Classical.choose_spec witness).2

/-- Dummy-prepend a target schedule so that the existing shifted orbit
constructor reads exactly `m t` at step `t`. -/
def prependTarget (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => m t

@[simp] theorem prependTarget_zero (m : ℕ → ℕ) : prependTarget m 0 = 1 := rfl

@[simp] theorem prependTarget_succ (m : ℕ → ℕ) (t : ℕ) :
    prependTarget m (t + 1) = m t := rfl

/-- Full QM151b converse: one hit on the reduced ordinary unit lattice is
sufficient to construct a complete accepted public orbit having exactly the
requested target schedule. -/
theorem exists_orbit_of_padicTail_eq_Wbar_lattice
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (r₀ : ℕ)
    (h₀ : padicTail m 0 =
      -(((2 : ℕ) ^ 20 * Wbar r₀ : ℕ) : ℚ_[2])) :
    ∃ o : Orbit, (fun t => o.branch t) = m := by
  let state := WbarTailChain m hm r₀ h₀
  let q : ℕ → ℤ := fun t => (17 * (state t).1 : ℕ)
  have hprepend : ∀ t, 0 < prependTarget m t := by
    intro t
    cases t with
    | zero => simp
    | succ t => simpa using hm t
  have hfollows : KLDyadicReset.Follows
      (Orbit.payloadResetProgramOfBranch (prependTarget m)) q := by
    intro t
    simp only [Orbit.payloadResetProgramOfBranch, prependTarget_succ,
      Orbit.payloadResetStep]
    dsimp only [q, state]
    exact_mod_cast WbarTailChain_recurrence m hm r₀ h₀ t
  let o := Orbit.promotePayloadChain (prependTarget m) hprepend q hfollows
    (by positivity : 0 ≤ q 0)
  refine ⟨o, ?_⟩
  rfl

/-- User-facing form of the converse, stated directly for the single
variable-exponent theta series. -/
theorem exists_orbit_of_padicSum_eq_Wbar_lattice
    (m : ℕ → ℕ) (hm : ∀ t, 0 < m t) (r₀ : ℕ)
    (h₀ : padicSum m =
      -(((2 : ℕ) ^ 20 * Wbar r₀ : ℕ) : ℚ_[2])) :
    ∃ o : Orbit, o.branch = m := by
  apply exists_orbit_of_padicTail_eq_Wbar_lattice m hm r₀
  simpa using h₀

end PublicTheta
end SelfWritingKL
end KontoroC

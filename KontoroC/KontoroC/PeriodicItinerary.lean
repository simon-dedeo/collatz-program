/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineBlock

/-!
# Periodic valuation itineraries cannot be growing gliders

The core is an elementary denominator-growth lemma.  For a natural sequence
satisfying `Q*x_(t+1)=P*x_t+A`, with coprime `P,Q` and `Q>1`, the integral
affine defect must vanish.  Applying this to repeated exact valuation blocks
shows that their first endpoint is already their start.
-/

namespace KontoroC

/-- An integer recurrence with a new coprime denominator at every step can
remain integral forever only at its rational fixed point. -/
theorem coprime_recurrence_fixed
    {P Q A : ℕ} (hcop : P.Coprime Q) (hQ : 1 < Q)
    (x : ℕ → ℕ) (hrec : ∀ t, Q * x (t + 1) = P * x t + A) :
    ((Q : ℤ) - P) * x 0 = A := by
  let z : ℕ → ℤ := fun t => ((Q : ℤ) - P) * x t - A
  have hzrec (t : ℕ) : (Q : ℤ) * z (t + 1) = (P : ℤ) * z t := by
    have h : (Q : ℤ) * x (t + 1) = (P : ℤ) * x t + A := by
      exact_mod_cast hrec t
    dsimp [z]
    nlinarith [h]
  have hpow (m : ℕ) : (Q : ℤ) ^ m * z m = (P : ℤ) ^ m * z 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ]
        calc
          (Q : ℤ) ^ m * Q * z (m + 1) =
              (Q : ℤ) ^ m * (Q * z (m + 1)) := by ring
          _ = (Q : ℤ) ^ m * (P * z m) := by rw [hzrec]
          _ = P * ((Q : ℤ) ^ m * z m) := by ring
          _ = P * ((P : ℤ) ^ m * z 0) := by rw [ih]
          _ = (P : ℤ) ^ m * P * z 0 := by ring
  have hdvd (m : ℕ) : (Q : ℤ) ^ m ∣ z 0 := by
    have hmul : (Q : ℤ) ^ m ∣ (P : ℤ) ^ m * z 0 := by
      refine ⟨z m, ?_⟩
      rw [← hpow m]
    have hrel : IsCoprime ((Q : ℤ) ^ m) ((P : ℤ) ^ m) :=
      (hcop.symm.pow m m).cast
    exact hrel.dvd_of_dvd_mul_left hmul
  have hz : z 0 = 0 := by
    by_contra hnz
    let m := (z 0).natAbs + 1
    have hnatdvd : Q ^ m ∣ (z 0).natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr (hdvd m)
      simpa [Int.natAbs_pow] using h
    have habspos : 0 < (z 0).natAbs := Int.natAbs_pos.mpr hnz
    have hle : Q ^ m ≤ (z 0).natAbs := Nat.le_of_dvd habspos hnatdvd
    have hQpow : 2 ^ m ≤ Q ^ m := Nat.pow_le_pow_left (by omega) m
    have hlt : (z 0).natAbs < 2 ^ m := by
      have hm : (z 0).natAbs < m := by simp [m]
      exact lt_trans hm (Nat.lt_pow_self (by omega))
    omega
  dsimp [z] at hz
  exact sub_eq_zero.mp hz

/-- Macro-orbit obtained by repeating one valuation block. -/
def repeatedBlockOrbit (x : ℕ) (w : List ℕ) : ℕ → ℕ
  | 0 => x
  | t + 1 => runWord (repeatedBlockOrbit x w t) w

@[simp] theorem repeatedBlockOrbit_zero (x : ℕ) (w : List ℕ) :
    repeatedBlockOrbit x w 0 = x := rfl

@[simp] theorem repeatedBlockOrbit_succ (x : ℕ) (w : List ℕ) (t : ℕ) :
    repeatedBlockOrbit x w (t + 1) =
      runWord (repeatedBlockOrbit x w t) w := rfl

/-- A nonempty valuation word that remains exactly legal under every
repetition is already a cycle on its first repetition. -/
theorem repeated_legal_block_fixed {x : ℕ} {w : List ℕ}
    (hw : w ≠ [])
    (hlegal : ∀ t, WordLegal (repeatedBlockOrbit x w t) w) :
    runWord x w = x := by
  let P := 3 ^ w.length
  let Q := 2 ^ totalValuation w
  let A := affineOffset w
  have hrec (t : ℕ) :
      Q * repeatedBlockOrbit x w (t + 1) =
        P * repeatedBlockOrbit x w t + A := by
    simpa [P, Q, A] using
      valuationWord_affine_identity (hlegal t)
  have hhead := hlegal 0
  have hS : 0 < totalValuation w := by
    cases w with
    | nil => exact (hw rfl).elim
    | cons k ks =>
        rw [totalValuation_cons]
        have hk : 0 < k := by
          rw [hhead.1.2.2]
          exact oddValuation_pos_of_odd hhead.1.2.1
        omega
  have hQ : 1 < Q := by
    dsimp [Q]
    exact Nat.one_lt_pow hS.ne' (by omega)
  have hcop : P.Coprime Q := by
    dsimp [P, Q]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  have hfixed := coprime_recurrence_fixed hcop hQ
    (repeatedBlockOrbit x w) hrec
  have hfixed0 : ((Q : ℤ) - P) * x = A := by
    simpa using hfixed
  have hfixed' : (Q : ℤ) * x = (P : ℤ) * x + A := by
    nlinarith [hfixed0]
  have hfixedNat : Q * x = P * x + A := by
    exact_mod_cast hfixed'
  have hone := hrec 0
  simp only [repeatedBlockOrbit_zero, repeatedBlockOrbit_succ] at hone
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hQ)
  rw [hone, hfixedNat]

/-- Interface for an arbitrary macro-state sequence carrying the same legal
block at every step. -/
theorem legal_block_chain_first_fixed
    (state : ℕ → ℕ) {w : List ℕ} (hw : w ≠ [])
    (hlegal : ∀ t, WordLegal (state t) w)
    (htransition : ∀ t, runWord (state t) w = state (t + 1)) :
    state 1 = state 0 := by
  have horbit : ∀ t, state t = repeatedBlockOrbit (state 0) w t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [repeatedBlockOrbit_succ, ← ih, htransition]
  have hlegal' : ∀ t, WordLegal (repeatedBlockOrbit (state 0) w t) w := by
    intro t
    rw [← horbit t]
    exact hlegal t
  have hfixed := repeated_legal_block_fixed hw hlegal'
  calc
    state 1 = runWord (state 0) w := (htransition 0).symm
    _ = state 0 := hfixed

/-- Explicit eventually-periodic-tail form: once the same block repeats
legally forever, the first transition of that tail is fixed. -/
theorem eventually_periodic_legal_tail_fixed
    (state : ℕ → ℕ) (t₀ : ℕ) {w : List ℕ} (hw : w ≠ [])
    (hlegal : ∀ t, WordLegal (state (t₀ + t)) w)
    (htransition : ∀ t,
      runWord (state (t₀ + t)) w = state (t₀ + (t + 1))) :
    state (t₀ + 1) = state t₀ := by
  let tail : ℕ → ℕ := fun t => state (t₀ + t)
  have htail := legal_block_chain_first_fixed tail hw hlegal htransition
  simpa [tail] using htail

/-- Sign corollary: an infinitely repeatable positive block must satisfy the
strict positive-cycle shape `3^N < 2^S`. -/
theorem repeated_legal_block_shape_strict {x : ℕ} {w : List ℕ}
    (hw : w ≠ [])
    (hlegal : ∀ t, WordLegal (repeatedBlockOrbit x w t) w) :
    3 ^ w.length < 2 ^ totalValuation w := by
  have h0 : WordLegal x w := by simpa using hlegal 0
  have hx : 0 < x := by
    cases w with
    | nil => exact (hw rfl).elim
    | cons k ks => exact h0.1.1
  exact cycle_shape_strict hx hw h0 (repeated_legal_block_fixed hw hlegal)

theorem no_repeated_legal_block_of_twoPow_le_threePow {x : ℕ} {w : List ℕ}
    (hw : w ≠ [])
    (hshape : 2 ^ totalValuation w ≤ 3 ^ w.length) :
    ¬∀ t, WordLegal (repeatedBlockOrbit x w t) w := by
  intro hlegal
  exact (Nat.not_lt_of_ge hshape) (repeated_legal_block_shape_strict hw hlegal)

/-- Consequently, a fixed positive block cannot drive strict growth forever. -/
theorem not_repeated_legal_block_strictly_growing {x : ℕ} {w : List ℕ}
    (hw : w ≠ [])
    (hlegal : ∀ t, WordLegal (repeatedBlockOrbit x w t) w) :
    ¬∀ t, repeatedBlockOrbit x w t < repeatedBlockOrbit x w (t + 1) := by
  intro hgrow
  have hfixed := repeated_legal_block_fixed hw hlegal
  have hfirst := hgrow 0
  simpa [hfixed] using hfirst

end KontoroC

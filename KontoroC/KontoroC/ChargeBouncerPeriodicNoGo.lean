/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerConstantNoGo

/-!
# No finite-period compressed charge-bouncer schedule

The one- and two-block arguments are instances of a uniform affine fold.
This file compresses an arbitrary nonempty finite opcode period to one
expanding coprime affine-gain instruction and applies the existing denominator
contradiction.  It concerns the arithmetic bouncer surrogate; no Collatz
semantic compiler is assumed here.
-/

namespace KontoroC
namespace ChargeBouncerPeriodicNoGo

open ChargeBouncerConstantNoGo

/-- Product of the first `n` coefficients, accumulated in chronological
order. -/
def prefixProduct (A : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => prefixProduct A n * A n

/-- Gain left after eliminating the first `n` intermediate states. -/
def prefixGain (A B G : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => A n * prefixGain A B G n + prefixProduct B n * G n

/-- Universal affine elimination for a finite string of local recurrences. -/
theorem prefix_balance (A B G x : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n → B i * x (i + 1) = A i * x i + G i) :
    prefixProduct B n * x n =
      prefixProduct A n * x 0 + prefixGain A B G n := by
  induction n with
  | zero => simp [prefixProduct, prefixGain]
  | succ n ih =>
      have hlast := h n (by omega)
      have hprev : ∀ i, i < n → B i * x (i + 1) = A i * x i + G i := by
        intro i hi
        exact h i (by omega)
      rw [prefixProduct, prefixProduct, prefixGain]
      calc
        prefixProduct B n * B n * x (n + 1) =
            prefixProduct B n * (B n * x (n + 1)) := by ring
        _ = prefixProduct B n * (A n * x n + G n) := by rw [hlast]
        _ = A n * (prefixProduct B n * x n) +
            prefixProduct B n * G n := by ring
        _ = A n *
              (prefixProduct A n * x 0 + prefixGain A B G n) +
            prefixProduct B n * G n := by rw [ih hprev]
        _ = prefixProduct A n * A n * x 0 +
            (A n * prefixGain A B G n + prefixProduct B n * G n) := by ring

theorem prefixProduct_pos (A : ℕ → ℕ)
    (hA : ∀ i, 0 < A i) (n : ℕ) : 0 < prefixProduct A n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
      simp only [prefixProduct]
      exact Nat.mul_pos ih (hA n)

theorem prefixProduct_le (A B : ℕ → ℕ)
    (n : ℕ) (h : ∀ i, i < n → B i ≤ A i) :
    prefixProduct B n ≤ prefixProduct A n := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
      simp only [prefixProduct]
      apply Nat.mul_le_mul
      · exact ih (fun i hi => h i (by omega))
      · exact h n (by omega)

/-- A nonempty product of termwise strict positive gaps retains a strict
gap. -/
theorem prefixProduct_lt (A B : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hB : ∀ i, 0 < B i)
    (hgap : ∀ i, i < n → B i < A i) :
    prefixProduct B n < prefixProduct A n := by
  cases n with
  | zero => omega
  | succ n =>
      have hprefix := prefixProduct_le A B n
        (fun i hi => le_of_lt (hgap i (by omega)))
      have hBprefix := prefixProduct_pos B hB n
      simp only [prefixProduct]
      exact ((Nat.mul_lt_mul_left hBprefix).2 (hgap n (by omega))).trans_le
        (Nat.mul_le_mul_right (A n) hprefix)

def periodA (m h : ℕ → ℕ) (p : ℕ) : ℕ :=
  prefixProduct (fun i => blockA (m i) (h i)) p

def periodB (m h : ℕ → ℕ) (p : ℕ) : ℕ :=
  prefixProduct (fun i => blockB (m i) (h i)) p

def periodGain (m h : ℕ → ℕ) (p : ℕ) : ℕ :=
  prefixGain (fun i => blockA (m i) (h i))
    (fun i => blockB (m i) (h i))
    (fun i => blockGain (m i) (h i)) p

def prefixSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixSum f n + f n

theorem periodA_eq_pow (m h : ℕ → ℕ) (p : ℕ) :
    periodA m h p = 3 ^ prefixSum (fun i => 17 * m i + 114 * h i) p := by
  induction p with
  | zero => simp [periodA, prefixProduct, prefixSum]
  | succ p ih =>
      simp only [periodA, prefixProduct, prefixSum] at ih ⊢
      rw [ih, blockA, ← pow_add]

theorem periodB_eq_pow (m h : ℕ → ℕ) (p : ℕ) :
    periodB m h p = 2 ^ prefixSum (fun i => 23 * m i + 154 * h i) p := by
  induction p with
  | zero => simp [periodB, prefixProduct, prefixSum]
  | succ p ih =>
      simp only [periodB, prefixProduct, prefixSum] at ih ⊢
      rw [ih, blockB, ← pow_add]

/-- Sample an arithmetic bouncer ray once per supplied period. -/
def periodicOpcodeOrbit
    (g : InfiniteChargeBouncerRay) (p : ℕ) (m h : ℕ → ℕ)
    (hm : ∀ t i, i < p → (g.stepData (p * t + i)).defectOpcode = m i)
    (hh : ∀ t i, i < p → (g.stepData (p * t + i)).rechargeCount = h i) :
    PositiveAffineGainOrbit (periodA m h p) (periodB m h p)
      (periodGain m h p) where
  value t := g.state (p * t)
  value_pos t := g.state_pos (p * t)
  balance t := by
    let A := fun i => blockA (m i) (h i)
    let B := fun i => blockB (m i) (h i)
    let G := fun i => blockGain (m i) (h i)
    let x := fun i => g.state (p * t + i)
    have hlocal : ∀ i, i < p → B i * x (i + 1) = A i * x i + G i := by
      intro i hi
      have hr := g.recurrence (p * t + i)
      simp only [InfiniteChargeBouncerRay.schedule,
        ChargeBouncerOpcodeSchedule.binaryExponent,
        ChargeBouncerOpcodeSchedule.ternaryExponent,
        ChargeBouncerOpcodeSchedule.gain] at hr
      rw [hm t i hi, hh t i hi] at hr
      simpa [A, B, G, x, blockA, blockB, blockGain, Nat.add_assoc] using hr
    have hfold := prefix_balance A B G x p hlocal
    change periodB m h p * g.state (p * (t + 1)) =
      periodA m h p * g.state (p * t) + periodGain m h p
    simpa [periodA, periodB, periodGain, A, B, G, x,
      show p * (t + 1) = p * t + p by ring] using hfold

theorem period_gap (p : ℕ) (hp : 0 < p) (m h : ℕ → ℕ)
    (hm_pos : ∀ i, i < p → 0 < m i)
    (hh_pos : ∀ i, i < p → 0 < h i) :
    periodB m h p < periodA m h p := by
  apply prefixProduct_lt _ _ hp
  · intro i
    simp [blockB]
  · intro i hi
    exact block_gap (hm_pos i hi) (hh_pos i hi)

/-- Every nonempty finite periodic compressed opcode schedule is impossible. -/
theorem no_periodic_opcode_ray
    (g : InfiniteChargeBouncerRay) (p : ℕ) (hp : 0 < p)
    (m h : ℕ → ℕ)
    (hm_pos : ∀ i, i < p → 0 < m i)
    (hh_pos : ∀ i, i < p → 0 < h i)
    (hm : ∀ t i, i < p → (g.stepData (p * t + i)).defectOpcode = m i)
    (hh : ∀ t i, i < p → (g.stepData (p * t + i)).rechargeCount = h i) :
    False := by
  let o := periodicOpcodeOrbit g p m h hm hh
  have hcop : (periodA m h p).Coprime (periodB m h p) := by
    rw [periodA_eq_pow, periodB_eq_pow]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  have hBone : 1 < periodB m h p := by
    cases p with
    | zero => omega
    | succ p =>
        simp only [periodB, prefixProduct]
        have hprefix : 0 < prefixProduct (fun i => blockB (m i) (h i)) p :=
          prefixProduct_pos _ (fun i => by simp [blockB]) p
        have hlast : 1 < blockB (m p) (h p) := by
          apply Nat.one_lt_pow
          · have hm := hm_pos p (by omega)
            omega
          · omega
        exact hlast.trans_le (Nat.le_mul_of_pos_left _ hprefix)
  exact o.impossible hcop hBone (period_gap p hp m h hm_pos hh_pos)

/-- Finite periodicity remains impossible after an arbitrary transient. -/
theorem no_eventually_periodic_opcode_ray
    (g : InfiniteChargeBouncerRay) (K p : ℕ) (hp : 0 < p)
    (m h : ℕ → ℕ)
    (hm_pos : ∀ i, i < p → 0 < m i)
    (hh_pos : ∀ i, i < p → 0 < h i)
    (hm : ∀ t i, i < p →
      (g.stepData (K + (p * t + i))).defectOpcode = m i)
    (hh : ∀ t i, i < p →
      (g.stepData (K + (p * t + i))).rechargeCount = h i) : False := by
  apply no_periodic_opcode_ray (ChargeBouncerConstantNoGo.tail g K) p hp
    m h hm_pos hh_pos
  · intro t i hi
    change (g.stepData (K + (p * t + i))).defectOpcode = m i
    exact hm t i hi
  · intro t i hi
    change (g.stepData (K + (p * t + i))).rechargeCount = h i
    exact hh t i hi

end ChargeBouncerPeriodicNoGo
end KontoroC

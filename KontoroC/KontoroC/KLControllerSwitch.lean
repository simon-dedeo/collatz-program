/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLRechargeLedger
import Mathlib.Data.Int.NatAbs

/-!
# Precision costs length when changing a negative controller

The positive magnitude of a negative KL center evolves by one of three maps:
`h ↦ 4h`, `h ↦ (4h+2)/3`, or `h ↦ (2h+1)/3`.  Every move grows a positive
center by at most a factor of four.  Consequently a word of length `L` has
endpoint at most `4^L h`.

If that endpoint is nontrivially congruent to a target `g` modulo `3^k`, its
ordinary distance from `g` is at least `3^k`.  Combining the two estimates
is QM133: increasing ternary switch precision cannot be supplied by a
connector of fixed length and fixed initial height.
-/

namespace KontoroC
namespace KLControllerSwitch

open KLRechargeLedger

/-- The three positive-center moves induced by the KL branches. -/
inductive CenterMove
  | transport
  | retarded
  | advanced
  deriving DecidableEq, Repr

/-- Apply a positive-center move. -/
def CenterMove.apply : CenterMove → ℕ → ℕ
  | .transport, h => transportCenter h
  | .retarded, h => retardedCenter h
  | .advanced, h => advancedCenter h

/-- The residue restrictions on the two divided center maps.  Transport is
left unrestricted because the size argument does not need a narrower domain.
-/
def CenterMove.Legal (m : CenterMove) (h : ℕ) : Prop :=
  match m with
  | .transport => True
  | .retarded => h % 9 = 7
  | .advanced => h % 9 = 1

/-- All three center moves preserve strict positivity. -/
theorem CenterMove.apply_pos (m : CenterMove) {h : ℕ} (hh : 0 < h) :
    0 < m.apply h := by
  cases m with
  | transport => simp [CenterMove.apply, transportCenter, hh]
  | retarded =>
      simp only [CenterMove.apply, retardedCenter]
      apply Nat.div_pos
      · omega
      · norm_num
  | advanced =>
      simp only [CenterMove.apply, advancedCenter]
      apply Nat.div_pos
      · omega
      · norm_num

/-- The local height estimate behind QM133a.  It is valid even without the
residue restrictions, so every legal step inherits it automatically. -/
theorem CenterMove.apply_le_four_mul (m : CenterMove) {h : ℕ} (hh : 0 < h) :
    m.apply h ≤ 4 * h := by
  cases m with
  | transport => simp [CenterMove.apply, transportCenter]
  | retarded =>
      simp only [CenterMove.apply, retardedCenter]
      apply Nat.div_le_of_le_mul
      omega
  | advanced =>
      simp only [CenterMove.apply, advancedCenter]
      apply Nat.div_le_of_le_mul
      omega

/-- The advanced divided move does not increase a positive center. -/
theorem advanced_apply_le {h : ℕ} (hh : 0 < h) :
    CenterMove.advanced.apply h ≤ h := by
  simp only [CenterMove.apply, advancedCenter]
  apply Nat.div_le_of_le_mul
  omega

/-- The retarded divided move grows a positive center by at most two. -/
theorem retarded_apply_le_two_mul {h : ℕ} (hh : 0 < h) :
    CenterMove.retarded.apply h ≤ 2 * h := by
  simp only [CenterMove.apply, retardedCenter]
  apply Nat.div_le_of_le_mul
  omega

/-- Endpoint obtained by reading a controller word from left to right. -/
def runCenter : List CenterMove → ℕ → ℕ
  | [], h => h
  | m :: w, h => runCenter w (m.apply h)

/-- A word is legal when every divided move is used in its indicated residue
class. -/
def LegalWord : List CenterMove → ℕ → Prop
  | [], _ => True
  | m :: w, h => m.Legal h ∧ LegalWord w (m.apply h)

theorem runCenter_pos (w : List CenterMove) {h : ℕ} (hh : 0 < h) :
    0 < runCenter w h := by
  induction w generalizing h with
  | nil => simpa [runCenter]
  | cons m w ih =>
      simp only [runCenter]
      exact ih (m.apply_pos hh)

/-- QM133a, in a form stronger than requested: legality is unnecessary for
the height estimate because all three raw maps satisfy the same bound. -/
theorem runCenter_le_four_pow_mul (w : List CenterMove) {h : ℕ} (hh : 0 < h) :
    runCenter w h ≤ 4 ^ w.length * h := by
  induction w generalizing h with
  | nil => simp [runCenter]
  | cons m w ih =>
      simp only [runCenter, List.length_cons, pow_succ]
      calc
        runCenter w (m.apply h) ≤ 4 ^ w.length * m.apply h :=
          ih (m.apply_pos hh)
        _ ≤ 4 ^ w.length * (4 * h) :=
          Nat.mul_le_mul_left _ (m.apply_le_four_mul hh)
        _ = 4 ^ w.length * 4 * h := by ring

theorem legal_runCenter_le_four_pow_mul (w : List CenterMove) {h : ℕ}
    (hh : 0 < h) (_hw : LegalWord w h) :
    runCenter w h ≤ 4 ^ w.length * h :=
  runCenter_le_four_pow_mul w hh

/-- QM133c: only transport and retarded letters contribute to the sharp
height budget.  Advanced letters have multiplicative cost one. -/
theorem runCenter_le_counted_budget (w : List CenterMove) {h : ℕ}
    (hh : 0 < h) :
    runCenter w h ≤
      4 ^ w.count .transport * 2 ^ w.count .retarded * h := by
  induction w generalizing h with
  | nil => simp [runCenter]
  | cons m w ih =>
      simp only [runCenter]
      have hih := ih (m.apply_pos hh)
      cases m with
      | transport =>
          simp only [List.count_cons, ↓reduceIte, pow_succ]
          calc
            runCenter w (CenterMove.transport.apply h) ≤
                4 ^ w.count .transport * 2 ^ w.count .retarded *
                  CenterMove.transport.apply h := hih
            _ ≤ 4 ^ w.count .transport * 2 ^ w.count .retarded * (4 * h) :=
              Nat.mul_le_mul_left _
                (CenterMove.apply_le_four_mul .transport hh)
            _ = (4 ^ w.count .transport * 4) *
                2 ^ w.count .retarded * h := by ring
      | retarded =>
          simp only [List.count_cons, ↓reduceIte, pow_succ]
          calc
            runCenter w (CenterMove.retarded.apply h) ≤
                4 ^ w.count .transport * 2 ^ w.count .retarded *
                  CenterMove.retarded.apply h := hih
            _ ≤ 4 ^ w.count .transport * 2 ^ w.count .retarded * (2 * h) :=
              Nat.mul_le_mul_left _ (retarded_apply_le_two_mul hh)
            _ = 4 ^ w.count .transport *
                (2 ^ w.count .retarded * 2) * h := by ring
      | advanced =>
          simp only [List.count_cons, ↓reduceIte]
          calc
            runCenter w (CenterMove.advanced.apply h) ≤
                4 ^ w.count .transport * 2 ^ w.count .retarded *
                  CenterMove.advanced.apply h := hih
            _ ≤ 4 ^ w.count .transport * 2 ^ w.count .retarded * h :=
              Nat.mul_le_mul_left _ (advanced_apply_le hh)

/-- Ordinary distance between two natural centers, represented without
truncated subtraction. -/
def centerDistance (h g : ℕ) : ℕ :=
  Int.natAbs ((h : ℤ) - (g : ℤ))

theorem centerDistance_pos {h g : ℕ} (hne : h ≠ g) :
    0 < centerDistance h g := by
  rw [centerDistance, Int.natAbs_sub_pos_iff]
  exact_mod_cast hne

/-- Triangle bound for the ordinary distance between two nonnegative
centers. -/
theorem centerDistance_le_add (h g : ℕ) : centerDistance h g ≤ h + g := by
  by_cases hgh : g ≤ h
  · rw [centerDistance, Int.natAbs_natCast_sub_natCast_of_ge hgh]
    omega
  · have hhg : h ≤ g := Nat.le_of_not_ge hgh
    rw [centerDistance, Int.natAbs_natCast_sub_natCast_of_le hhg]
    omega

/-- Nonzero congruence modulo `3^k` has ordinary size at least `3^k`. -/
theorem three_pow_le_centerDistance {h g k : ℕ} (hne : h ≠ g)
    (hdiv : ((3 ^ k : ℕ) : ℤ) ∣ (h : ℤ) - (g : ℤ)) :
    3 ^ k ≤ centerDistance h g := by
  apply Nat.le_of_dvd (centerDistance_pos hne)
  rw [centerDistance, ← Int.natCast_dvd]
  exact hdiv

/-- QM133b: the complete power inequality for a nontrivial controller
switch.  Exact connections `h' = g` are deliberately outside its scope. -/
theorem controller_switch_precision_cost
    (w : List CenterMove) {h g k : ℕ} (hh : 0 < h)
    (hne : runCenter w h ≠ g)
    (hdiv : ((3 ^ k : ℕ) : ℤ) ∣
      (runCenter w h : ℤ) - (g : ℤ)) :
    3 ^ k ≤ centerDistance (runCenter w h) g ∧
      centerDistance (runCenter w h) g ≤ runCenter w h + g ∧
      runCenter w h + g ≤ 4 ^ w.length * h + g := by
  refine ⟨three_pow_le_centerDistance hne hdiv,
    centerDistance_le_add _ _, ?_⟩
  exact Nat.add_le_add_right (runCenter_le_four_pow_mul w hh) g

/-- The concise endpoint form most useful to subsequent arguments. -/
theorem three_pow_le_four_pow_mul_add
    (w : List CenterMove) {h g k : ℕ} (hh : 0 < h)
    (hne : runCenter w h ≠ g)
    (hdiv : ((3 ^ k : ℕ) : ℤ) ∣
      (runCenter w h : ℤ) - (g : ℤ)) :
    3 ^ k ≤ 4 ^ w.length * h + g := by
  obtain ⟨h₁, h₂, h₃⟩ :=
    controller_switch_precision_cost w hh hne hdiv
  exact h₁.trans (h₂.trans h₃)

/-- QM133d: count-sensitive precision cost. -/
theorem three_pow_le_counted_budget_add
    (w : List CenterMove) {h g k : ℕ} (hh : 0 < h)
    (hne : runCenter w h ≠ g)
    (hdiv : ((3 ^ k : ℕ) : ℤ) ∣
      (runCenter w h : ℤ) - (g : ℤ)) :
    3 ^ k ≤
      4 ^ w.count .transport * 2 ^ w.count .retarded * h + g := by
  exact (three_pow_le_centerDistance hne hdiv).trans
    ((centerDistance_le_add _ _).trans
      (Nat.add_le_add_right (runCenter_le_counted_budget w hh) g))

end KLControllerSwitch
end KontoroC

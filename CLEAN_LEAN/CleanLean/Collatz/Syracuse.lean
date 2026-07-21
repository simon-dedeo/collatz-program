/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Defs

/-!
# The Syracuse normalization

On an odd input the Syracuse map performs the odd Collatz step and the
immediately following halving in one move.  We prove that eventual arrival at
`1` is equivalent for the standard and Syracuse maps.
-/

namespace CleanLean.Collatz

/-- The one-halving accelerated Collatz, or Syracuse, map. -/
def syracuseStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Eventual arrival at `1` under the Syracuse map. -/
def SyracuseReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, syracuseStep^[k] n = 1

/-- Syracuse formulation of the Collatz conjecture. -/
def SyracuseConjecture : Prop :=
  ∀ n : ℕ, 0 < n → SyracuseReachesOne n

theorem syracuseStep_of_even {n : ℕ} (h : n % 2 = 0) :
    syracuseStep n = step n := by
  simp [syracuseStep, step, h]

theorem odd_remainder {n : ℕ} (h : n % 2 ≠ 0) : n % 2 = 1 := by
  omega

theorem odd_image_even {n : ℕ} (h : n % 2 ≠ 0) : (3 * n + 1) % 2 = 0 := by
  have := odd_remainder h
  omega

theorem two_steps_of_odd {n : ℕ} (h : n % 2 ≠ 0) :
    step^[2] n = syracuseStep n := by
  have he := odd_image_even h
  norm_num [Function.iterate_succ_apply, step, syracuseStep, h, he]

theorem syracuseReachesOne_of_next {n : ℕ}
    (h : SyracuseReachesOne (syracuseStep n)) : SyracuseReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem reachesOne_of_syracuse {n : ℕ} : SyracuseReachesOne n → ReachesOne n := by
  rintro ⟨k, hk⟩
  induction k generalizing n with
  | zero => exact ⟨0, by simpa using hk⟩
  | succ k ih =>
      have htail : syracuseStep^[k] (syracuseStep n) = 1 := by
        simpa [Function.iterate_succ_apply] using hk
      have hr : ReachesOne (syracuseStep n) := ih htail
      by_cases he : n % 2 = 0
      · rw [syracuseStep_of_even he] at hr
        exact reachesOne_of_iterate (k := 1) (by simpa using hr)
      · rw [← two_steps_of_odd he] at hr
        exact reachesOne_of_iterate (k := 2) hr

theorem syracuse_of_reachesOne {n : ℕ} : ReachesOne n → SyracuseReachesOne n := by
  rintro ⟨k, hk⟩
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
      cases k with
      | zero => exact ⟨0, by simpa using hk⟩
      | succ k =>
          have htail : step^[k] (step n) = 1 := by
            simpa [Function.iterate_succ_apply] using hk
          by_cases he : n % 2 = 0
          · have hr : SyracuseReachesOne (step n) := ih k (by omega) htail
            rw [← syracuseStep_of_even he] at hr
            exact syracuseReachesOne_of_next hr
          · cases k with
            | zero =>
                have hs : step n = 1 := by simpa using htail
                rw [step_of_odd he] at hs
                omega
            | succ j =>
                have htail' : step^[j] (step^[2] n) = 1 := by
                  simpa [Function.iterate_succ_apply] using htail
                rw [two_steps_of_odd he] at htail'
                have hr : SyracuseReachesOne (syracuseStep n) :=
                  ih j (by omega) htail'
                exact syracuseReachesOne_of_next hr

theorem reachesOne_iff_syracuse {n : ℕ} :
    ReachesOne n ↔ SyracuseReachesOne n :=
  ⟨syracuse_of_reachesOne, reachesOne_of_syracuse⟩

theorem conjecture_iff_syracuse : Conjecture ↔ SyracuseConjecture := by
  constructor <;> intro h n hn
  · exact reachesOne_iff_syracuse.mp (h n hn)
  · exact reachesOne_iff_syracuse.mpr (h n hn)

end CleanLean.Collatz


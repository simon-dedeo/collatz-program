/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ShortcutParityPeriodicNoGo
import KontoroC.PrefixKraft

/-!
# The minimal outward shortcut code

This file formalizes the combinatorial foundation of the outward
first-passage experiment.  It contains no inference from code mass to an
ordinary Collatz seed.
-/

namespace KontoroC
namespace OutwardFirstPassage

open ShortcutParityPeriodicNoGo

def ProperPrefix {α : Type*} (u v : List α) : Prop := u <+: v ∧ u ≠ v

def FirstPassage (w : List Bool) : Prop :=
  WordOutward w ∧ ∀ u, ProperPrefix u w → ¬ WordOutward u

theorem firstPassage_outward {w : List Bool} (hw : FirstPassage w) :
    WordOutward w := hw.1

theorem firstPassage_ne_nil {w : List Bool} (hw : FirstPassage w) : w ≠ [] := by
  intro hnil
  subst w
  norm_num [FirstPassage, WordOutward] at hw

theorem properPrefix_length_lt {α : Type*} {u v : List α}
    (h : ProperPrefix u v) : u.length < v.length := by
  obtain ⟨tail, rfl⟩ := h.1
  cases tail with
  | nil => exact (h.2 (by simp)).elim
  | cons a tail => simp

/-- The first-passage words are prefix-free. -/
theorem prefixFree :
    PrefixKraft.PrefixFree {w : List Bool | FirstPassage w} := by
  intro u hu v hv huv
  by_contra hne
  exact hv.2 u ⟨huv, hne⟩ hu.1

/-- Every outward word contains a minimal outward prefix. -/
theorem exists_firstPassage_prefix (w : List Bool) (hout : WordOutward w) :
    ∃ u : List Bool, u <+: w ∧ FirstPassage u := by
  by_cases hfirst : FirstPassage w
  · exact ⟨w, List.prefix_refl w, hfirst⟩
  · have hproper : ¬ ∀ u, ProperPrefix u w → ¬ WordOutward u := by
      intro hall
      exact hfirst ⟨hout, hall⟩
    push Not at hproper
    obtain ⟨u, hup, huout⟩ := hproper
    obtain ⟨v, hvpre, hvfirst⟩ := exists_firstPassage_prefix u huout
    exact ⟨v, hvpre.trans hup.1, hvfirst⟩
termination_by w.length
decreasing_by exact properPrefix_length_lt hup

/-- The minimal outward prefix of an outward word is unique. -/
theorem exists_unique_firstPassage_prefix (w : List Bool) (hout : WordOutward w) :
    ∃! u : List Bool, u <+: w ∧ FirstPassage u := by
  obtain ⟨u, hup, hu⟩ := exists_firstPassage_prefix w hout
  refine ⟨u, ⟨hup, hu⟩, ?_⟩
  intro v hv
  rcases PrefixKraft.comparable_of_common_prefix hup hv.1 with huv | hvu
  · exact (prefixFree hu hv.2 huv).symm
  · exact prefixFree hv.2 hu hvu

theorem firstPassage_last_eq_true {w : List Bool} (hw : FirstPassage w) :
    w.getLast (firstPassage_ne_nil hw) = true := by
  let hne := firstPassage_ne_nil hw
  let u := w.dropLast
  have hdecomp : u ++ [w.getLast hne] = w := List.dropLast_append_getLast hne
  cases hlast : w.getLast hne with
  | true => rfl
  | false =>
      rw [hlast] at hdecomp
      have hup : ProperPrefix u w := by
        constructor
        · exact hdecomp ▸ List.prefix_append u [false]
        · intro heq
          have hlen := congrArg List.length heq
          rw [← hdecomp] at hlen
          simp at hlen
      have hnot := hw.2 u hup
      exfalso
      apply hnot
      have hout := hw.1
      rw [← hdecomp] at hout
      simp only [WordOutward, List.length_append, List.length_singleton,
        List.count_append, List.count_cons, List.count_nil] at hout ⊢
      have hpow : 2 ^ u.length ≤ 2 ^ (u.length + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact hpow.trans_lt hout

/-- A first-passage word crosses by one odd multiplier, so its slope is at
most `3/2`: `2*3^O ≤ 3*2^S`. -/
theorem firstPassage_overshoot {w : List Bool} (hw : FirstPassage w) :
    2 * 3 ^ w.count true ≤ 3 * 2 ^ w.length := by
  let hne := firstPassage_ne_nil hw
  let u := w.dropLast
  have hlast := firstPassage_last_eq_true hw
  have hdecomp : u ++ [true] = w := by
    calc
      u ++ [true] = u ++ [w.getLast hne] := by rw [hlast]
      _ = w := List.dropLast_append_getLast hne
  have hup : ProperPrefix u w := by
    constructor
    · exact hdecomp ▸ List.prefix_append u [true]
    · intro heq
      have hlen := congrArg List.length heq
      rw [← hdecomp] at hlen
      simp at hlen
  have hu : 3 ^ u.count true ≤ 2 ^ u.length :=
    Nat.le_of_not_gt (hw.2 u hup)
  rw [← hdecomp]
  have hcount : (u ++ [true]).count true = u.count true + 1 := by simp
  have hlength : (u ++ [true]).length = u.length + 1 := by simp
  rw [hcount, hlength, pow_succ, pow_succ]
  nlinarith

end OutwardFirstPassage
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCylinderRenewal

/-!
# Finite-height closure of the outward renewal

This file begins QM158g.  Its first task is the combinatorial fact needed to
make the finite-height word set genuinely finite: on first-passage words the
canonical dyadic source residue is injective.
-/

namespace KontoroC
namespace OutwardFiniteHeight

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardFirstPassage OutwardCylinderRenewal

/-- Two parity words executable from the same source are comparable in the
prefix order.  This is determinism at the level of parity words, with no
iteration function hidden in the statement. -/
theorem executes_common_source_comparable
    {u v : List Bool} {source targetU targetV : ℕ}
    (hu : Executes u source targetU) (hv : Executes v source targetV) :
    u <+: v ∨ v <+: u := by
  induction u generalizing v source targetU targetV with
  | nil => exact Or.inl (by simp)
  | cons bu u ih =>
      cases v with
      | nil => exact Or.inr (by simp)
      | cons bv v =>
          obtain ⟨middleU, hstepU, htailU⟩ := hu
          obtain ⟨middleV, hstepV, htailV⟩ := hv
          have hbit : bu = bv := by
            cases bu <;> cases bv
            · rfl
            · simp only [Bool.false_eq_true, ↓reduceIte] at hstepU hstepV
              omega
            · simp only [Bool.false_eq_true, ↓reduceIte] at hstepU hstepV
              omega
            · rfl
          subst bv
          have hmiddle : middleU = middleV := by
            cases bu <;> simp only [Bool.false_eq_true, ↓reduceIte] at hstepU hstepV <;>
              omega
          subst middleV
          rcases ih htailU htailV with huv | hvu
          · obtain ⟨tail, rfl⟩ := huv
            exact Or.inl (by simp)
          · obtain ⟨tail, rfl⟩ := hvu
            exact Or.inr (by simp)

/-- First-passage prefix-freeness upgrades deterministic comparability to
equality. -/
theorem firstPassage_eq_of_common_source
    {u v : List Bool} {source targetU targetV : ℕ}
    (huFirst : FirstPassage u) (hvFirst : FirstPassage v)
    (hu : Executes u source targetU) (hv : Executes v source targetV) :
    u = v := by
  rcases executes_common_source_comparable hu hv with huv | hvu
  · exact prefixFree huFirst hvFirst huv
  · exact (prefixFree hvFirst huFirst hvu).symm

/-- An execution starting at zero can contain no odd instruction. -/
theorem executes_zero_count_true_eq_zero
    {w : List Bool} {target : ℕ} (h : Executes w 0 target) :
    w.count true = 0 := by
  induction w generalizing target with
  | nil => simp
  | cons bit w ih =>
      obtain ⟨middle, hstep, htail⟩ := h
      cases bit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          have hmiddle : middle = 0 := by omega
          subst middle
          simpa using ih htail
      | true =>
          simp only [↓reduceIte] at hstep
          omega

/-- Every first-passage cylinder has a positive canonical source.  This is
the point that makes the active-word cardinality bound `B`, not `B+1`. -/
theorem canonicalSource_pos {w : List Bool} (hw : FirstPassage w) :
    0 < (canonicalExecution w).1 := by
  by_contra hnot
  have hzero : (canonicalExecution w).1 = 0 := by omega
  have hcount := executes_zero_count_true_eq_zero
    (hzero ▸ (canonicalExecution_spec w).2.2)
  have hout := hw.1
  simp only [WordOutward, hcount, pow_zero] at hout
  have hpow : 0 < 2 ^ w.length := by positivity
  omega

/-- The canonical dyadic source is injective on the first-passage code. -/
theorem canonicalSource_injective_on_firstPassage
    {u v : List Bool} (hu : FirstPassage u) (hv : FirstPassage v)
    (hsource : (canonicalExecution u).1 = (canonicalExecution v).1) :
    u = v := by
  apply firstPassage_eq_of_common_source hu hv
    (canonicalExecution_spec u).2.2
  simpa [hsource] using (canonicalExecution_spec v).2.2

/-- The words of a finite first-passage code whose canonical source is at
most `B`. -/
noncomputable def activeWords (F : Finset (List Bool)) (B : ℕ) :
    Finset (List Bool) :=
  F.filter fun w => (canonicalExecution w).1 ≤ B

/-- QM158g's finite-word bound.  Positivity of canonical first-passage
sources eliminates the otherwise possible residue zero and gives the sharp
cardinality bound `B`. -/
theorem card_activeWords_le
    (F : Finset (List Bool)) (hfirst : ∀ w ∈ F, FirstPassage w) (B : ℕ) :
    (activeWords F B).card ≤ B := by
  let sourceImage : Finset ℕ :=
    (activeWords F B).image fun w => (canonicalExecution w).1
  have hinj : Set.InjOn (fun w : List Bool => (canonicalExecution w).1)
      (activeWords F B : Set (List Bool)) := by
    intro u hu v hv huv
    apply canonicalSource_injective_on_firstPassage
    · exact hfirst u (Finset.mem_filter.mp hu).1
    · exact hfirst v (Finset.mem_filter.mp hv).1
    · exact huv
  have hcard : (activeWords F B).card = sourceImage.card := by
    symm
    exact Finset.card_image_iff.mpr hinj
  rw [hcard]
  apply (Finset.card_le_card ?_).trans
    (show (Finset.Icc 1 B).card ≤ B by simp)
  intro r hr
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hwF : w ∈ F := (Finset.mem_filter.mp hw).1
  have hwB : (canonicalExecution w).1 ≤ B := (Finset.mem_filter.mp hw).2
  exact Finset.mem_Icc.mpr ⟨canonicalSource_pos (hfirst w hwF), hwB⟩

/-- A nonzero cylinder lift cannot send a bounded source above three times
that source.  This is the quantitative finite-height clause in QM158g; the
strict form avoids any subtraction bookkeeping. -/
theorem positive_parameter_target_lt_three_source
    {w : List Bool} (hw : FirstPassage w) {t source target : ℕ}
    (ht : 0 < t)
    (hsource : source =
      (canonicalExecution w).1 + 2 ^ w.length * t)
    (htarget : target =
      (canonicalExecution w).2 + 3 ^ w.count true * t) :
    target < 3 * source := by
  have hb := (canonicalExecution_spec w).2.1
  have hover := firstPassage_overshoot hw
  have htOne : t + 1 ≤ 2 * t := by omega
  have htargetBound :
      target < 3 ^ w.count true * (t + 1) := by
    rw [htarget]
    nlinarith
  have hscaled := Nat.mul_le_mul_right (t + 1) hover
  have htime := Nat.mul_le_mul_left (3 * 2 ^ w.length) htOne
  have hslope :
      3 ^ w.count true * (t + 1) ≤ 3 * 2 ^ w.length * t := by
    have : 2 * (3 ^ w.count true * (t + 1)) ≤
        2 * (3 * 2 ^ w.length * t) := by
      calc
        2 * (3 ^ w.count true * (t + 1)) =
            (2 * 3 ^ w.count true) * (t + 1) := by ring
        _ ≤ (3 * 2 ^ w.length) * (t + 1) := by
          simpa [mul_assoc] using hscaled
        _ ≤ (3 * 2 ^ w.length) * (2 * t) := htime
        _ = 2 * (3 * 2 ^ w.length * t) := by ring
    omega
  rw [hsource]
  have hbase : 3 * 2 ^ w.length * t ≤
      3 * ((canonicalExecution w).1 + 2 ^ w.length * t) := by
    rw [show 3 * 2 ^ w.length * t = 3 * (2 ^ w.length * t) by ring]
    apply Nat.mul_le_mul_left
    exact Nat.le_add_left _ _
  exact htargetBound.trans_le (hslope.trans hbase)

/-- Worker-facing finite-window form: a positive-parameter first-passage
execution beginning at or below `B` ends at or below `3*B-1`. -/
theorem positive_parameter_target_le_three_bound_sub_one
    {w : List Bool} (hw : FirstPassage w) {t source target B : ℕ}
    (ht : 0 < t)
    (hsource : source =
      (canonicalExecution w).1 + 2 ^ w.length * t)
    (htarget : target =
      (canonicalExecution w).2 + 3 ^ w.count true * t)
    (hB : source ≤ B) :
    target ≤ 3 * B - 1 := by
  have hlt := positive_parameter_target_lt_three_source
    hw ht hsource htarget
  have hsourcePos : 0 < 3 * source :=
    lt_of_le_of_lt (Nat.zero_le target) hlt
  have hpos : 0 < 3 * B :=
    hsourcePos.trans_le (Nat.mul_le_mul_left 3 hB)
  omega

/-- Largest family parameter whose source can still lie below `B`. -/
noncomputable def parameterCapacity (w : List Bool) (B : ℕ) : ℕ :=
  (B - (canonicalExecution w).1) / 2 ^ w.length

/-- Target reached at the last member of `w`'s dyadic cylinder lying below
`B`. -/
noncomputable def wordTargetCeiling (w : List Bool) (B : ℕ) : ℕ :=
  (canonicalExecution w).2 +
    3 ^ w.count true * parameterCapacity w B

/-- QM158g's literal finite target cutoff.  The supremum of an empty active
set is zero, which is the correct harmless convention. -/
noncomputable def finiteHeightTargetBound
    (F : Finset (List Bool)) (B : ℕ) : ℕ :=
  (activeWords F B).sup fun w => wordTargetCeiling w B

/-- Every target reached from the source window `[0,B]` lies in the finite
window defined above. -/
theorem execution_target_le_finiteHeightTargetBound
    {F : Finset (List Bool)} {w : List Bool} (hwF : w ∈ F)
    {source target B : ℕ} (hexec : Executes w source target)
    (hB : source ≤ B) :
    target ≤ finiteHeightTargetBound F B := by
  obtain ⟨t, hsource, htarget⟩ :=
    (executes_iff_canonical_family w).1 hexec
  have hrSource : (canonicalExecution w).1 ≤ source := by
    rw [hsource]
    exact Nat.le_add_right _ _
  have hrB : (canonicalExecution w).1 ≤ B := hrSource.trans hB
  have hwActive : w ∈ activeWords F B :=
    Finset.mem_filter.mpr ⟨hwF, hrB⟩
  have hmul : 2 ^ w.length * t ≤
      B - (canonicalExecution w).1 := by
    rw [hsource] at hB
    omega
  have ht : t ≤ parameterCapacity w B := by
    rw [parameterCapacity]
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ w.length)).2
    simpa [mul_comm] using hmul
  have htargetCeiling : target ≤ wordTargetCeiling w B := by
    rw [htarget, wordTargetCeiling]
    gcongr
  rw [finiteHeightTargetBound]
  exact htargetCeiling.trans
    (Finset.le_sup (f := fun v => wordTargetCeiling v B) hwActive)

/-- Consequently, membership below source height `B` depends only on the old
target predicate below `finiteHeightTargetBound F B`.  This is the precise
finite-height closure assertion, independent of how membership is stored. -/
theorem nextSource_congr_on_finiteHeight
    (F : Finset (List Bool)) (E E' : ℕ → Prop) (B : ℕ)
    (hEE' : ∀ y ≤ finiteHeightTargetBound F B, E y ↔ E' y)
    {source : ℕ} (hsource : source ≤ B) :
    NextSource F E source ↔ NextSource F E' source := by
  constructor
  · rintro ⟨w, hwF, target, htargetE, hexec⟩
    refine ⟨w, hwF, target, ?_, hexec⟩
    exact (hEE' target
      (execution_target_le_finiteHeightTargetBound hwF hexec hsource)).1 htargetE
  · rintro ⟨w, hwF, target, htargetE', hexec⟩
    refine ⟨w, hwF, target, ?_, hexec⟩
    exact (hEE' target
      (execution_target_le_finiteHeightTargetBound hwF hexec hsource)).2 htargetE'

end OutwardFiniteHeight
end KontoroC

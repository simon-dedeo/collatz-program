/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCylinderRenewal

/-!
# The odd-source / residue-two target slice

This file proves the exact scalar bijection behind QM158d.  It separates that
cheap arithmetic fact from the harder combinatorial claim that deleting an
initial even bit cannot lower first-passage depth.
-/

namespace KontoroC
namespace OutwardOddSlice

open ShortcutParityPeriodicNoGo OutwardFirstPassage
  OutwardCodeCompactness OutwardBoundaryRenewal

def FirstPassageCode : Set (List Bool) := {w | FirstPassage w}

def RealizesFirstPassageDepth (n x : ℕ) : Prop :=
  RealizesDepth FirstPassageCode n x

/-- Literal odd parity plus first-passage minimality forces the first word to
be `[true]`. -/
theorem firstPassage_execution_of_odd_source_eq_true
    {w : List Bool} {source target : ℕ}
    (hodd : Odd source) (hfirst : FirstPassage w)
    (hw : Executes w source target) :
    w = [true] ∧ 2 * target = 3 * source + 1 := by
  cases w with
  | nil => exact (firstPassage_ne_nil hfirst rfl).elim
  | cons bit tail =>
      obtain ⟨middle, hstep, htail⟩ := hw
      cases bit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          have heven : 2 ∣ source := ⟨middle, hstep.symm⟩
          exact (hodd.not_two_dvd_nat heven).elim
      | true =>
          have ht : tail = [] := firstPassage_cons_true_eq_singleton hfirst
          subst tail
          simp only [Executes] at htail
          subst target
          exact ⟨rfl, by simpa using hstep⟩

/-- Forward half of QM158d: an odd source completing `n+1` blocks begins
with the forced word `[true]` and lands in the residue-two slice at depth
`n`. -/
theorem odd_successor_to_residueTwo {n source : ℕ}
    (hodd : Odd source) (hdepth : RealizesFirstPassageDepth (n + 1) source) :
    ∃ target,
      RealizesFirstPassageDepth n target ∧ target % 3 = 2 ∧
        2 * target = 3 * source + 1 := by
  rcases hdepth with ⟨hsource, ws, hlen, hwords, hexec⟩
  cases ws with
  | nil => simp at hlen
  | cons w ws =>
      obtain ⟨middle, hw, hrest⟩ := hexec
      have hfirst : FirstPassage w := hwords w (by simp)
      obtain ⟨hwEq, hstep⟩ :=
        firstPassage_execution_of_odd_source_eq_true hodd hfirst hw
      have hmiddle : 0 < middle := by omega
      have htailWords : WordsIn FirstPassageCode ws := by
        intro v hv
        exact hwords v (by simp [hv])
      have htailDepth : RealizesFirstPassageDepth n middle := by
        refine ⟨hmiddle, ws, ?_, htailWords, hrest⟩
        simpa [hwEq] using hlen
      have hmod : middle % 3 = 2 := by
        have hc := congrArg (fun z : ℕ => z % 3) hstep
        simp [Nat.add_mod, Nat.mul_mod] at hc
        have hlt := Nat.mod_lt middle (by omega : 0 < 3)
        omega
      exact ⟨middle, htailDepth, hmod, hstep⟩

/-- Reverse half of QM158d: every positive depth-`n` target in class two
modulo three has the positive odd predecessor `(2y-1)/3`, which gains the
forced first-passage word `[true]`. -/
theorem residueTwo_to_odd_successor {n target : ℕ}
    (hdepth : RealizesFirstPassageDepth n target)
    (hmod : target % 3 = 2) :
    let source := (2 * target - 1) / 3
    0 < source ∧ Odd source ∧
      RealizesFirstPassageDepth (n + 1) source ∧
      2 * target = 3 * source + 1 := by
  let source := (2 * target - 1) / 3
  have htarget : 0 < target := hdepth.1
  have hnumDiv : 3 ∣ 2 * target - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hsourceEq : 3 * source = 2 * target - 1 := by
    dsimp [source]
    exact Nat.mul_div_cancel' hnumDiv
  have hsource : 0 < source := by omega
  have hodd : Odd source := by
    rw [Nat.odd_iff]
    have hlt := Nat.mod_lt source (by omega : 0 < 2)
    omega
  have hstep : 2 * target = 3 * source + 1 := by omega
  have honeFirst : FirstPassage [true] := by
    constructor
    · norm_num [WordOutward]
    · intro u hu
      have hlen := properPrefix_length_lt hu
      have hueq : u = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst u
      norm_num [WordOutward]
  have hexecOne : Executes [true] source target := by
    simp only [Executes]
    exact ⟨target, by simpa using hstep, rfl⟩
  rcases hdepth with ⟨_, ws, hlen, hwords, hexec⟩
  have hnewDepth : RealizesFirstPassageDepth (n + 1) source := by
    refine ⟨hsource, [true] :: ws, by simp [hlen], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact honeFirst
      · exact hwords w hw
    · exact ⟨target, hexecOne, hexec⟩
  exact ⟨hsource, hodd, hnewDepth, hstep⟩

/-- Conditional scalar minimum theorem.  Once oddness of the least
depth-`n+1` source is supplied, the residue-two slice formula is forced. -/
theorem least_successor_eq_residueTwo_slice
    {n h m : ℕ}
    (hh : RealizesFirstPassageDepth (n + 1) h)
    (hhOdd : Odd h)
    (hhLeast : ∀ x, RealizesFirstPassageDepth (n + 1) x → h ≤ x)
    (hm : RealizesFirstPassageDepth n m)
    (hmMod : m % 3 = 2)
    (hmLeast : ∀ y, RealizesFirstPassageDepth n y → y % 3 = 2 → m ≤ y) :
    h = (2 * m - 1) / 3 := by
  obtain ⟨y, hyDepth, hyMod, hyEq⟩ := odd_successor_to_residueTwo hhOdd hh
  have hmy : m ≤ y := hmLeast y hyDepth hyMod
  have hs := residueTwo_to_odd_successor hm hmMod
  dsimp only at hs
  rcases hs with ⟨_, _, hsDepth, hsEq⟩
  let s := (2 * m - 1) / 3
  have hhs : h ≤ s := hhLeast s hsDepth
  have hsh : s ≤ h := by
    have hsourceEq : 3 * s = 2 * m - 1 := by omega
    omega
  exact le_antisymm hhs hsh

end OutwardOddSlice
end KontoroC

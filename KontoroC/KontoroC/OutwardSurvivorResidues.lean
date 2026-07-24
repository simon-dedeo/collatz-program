/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardStrictKraftGap
import KontoroC.OutwardFiniteHeight

/-!
# Finite ordinary residues behind the first-passage survivor mass

The strict Kraft gap is initially a statement about Boolean words.  This file
uses the exact shortcut execution semantics to transport it to ordinary
source residues modulo `2^L`.

The conclusion remains finite-level.  It gives many ordinary residues whose
first `L` literal shortcut steps have no outward prefix; it does not choose one
ordinary natural compatible with these survivor sets for every `L`.
-/

namespace KontoroC
namespace OutwardSurvivorResidues

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardCylinderRenewal OutwardFiniteHeight OutwardStrictKraftGap
  OutwardFiniteStateKraftGap.FirstPassageGrammar

/-- Two canonical words of the same length cannot share a source residue. -/
theorem canonicalSource_injective_fixedLength
    {u v : List Bool} (hulen : u.length = v.length)
    (hsource : (canonicalExecution u).1 = (canonicalExecution v).1) :
    u = v := by
  have hu := (canonicalExecution_spec u).2.2
  have hv := (canonicalExecution_spec v).2.2
  have hv' : Executes v (canonicalExecution u).1 (canonicalExecution v).2 := by
    simpa [hsource] using hv
  rcases executes_common_source_comparable hu hv' with huv | hvu
  · exact huv.eq_of_length hulen
  · exact (hvu.eq_of_length hulen.symm).symm

/-- Length-`L` parity words which have no outward prefix. -/
noncomputable def survivorWords (L : ℕ) : Finset (List Bool) :=
  binaryWords L \
    coveredAtDepth (firstPassageWordsUpTo L) L

/-- Their canonical ordinary source residues. -/
noncomputable def survivorSources (L : ℕ) : Finset ℕ :=
  (survivorWords L).image fun w => (canonicalExecution w).1

theorem mem_survivorWords_iff {L : ℕ} {w : List Bool} :
    w ∈ survivorWords L ↔
      w.length = L ∧ ∀ u, u <+: w → ¬ WordOutward u := by
  constructor
  · intro hw
    have hw' : w ∈ binaryWords L \
        coveredAtDepth (firstPassageWordsUpTo L) L := hw
    exact ⟨mem_binaryWords_iff.mp (Finset.mem_sdiff.mp hw').1,
      no_outward_prefix_of_mem_uncovered hw'⟩
  · rintro ⟨hwlen, hprefix⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_binaryWords_iff.mpr hwlen, ?_⟩
    intro hcovered
    rcases Finset.mem_biUnion.mp hcovered with ⟨v, hvC, hvext⟩
    rcases Finset.mem_image.mp hvext with ⟨tail, _, htail⟩
    have hvfirst := (mem_firstPassageWordsUpTo_iff.mp hvC).1
    have hvw : v <+: w := by
      exact ⟨tail, htail⟩
    exact hprefix v hvw hvfirst.1

/-- The canonical source map loses no cardinality on one survivor level. -/
theorem card_survivorSources (L : ℕ) :
    (survivorSources L).card = (survivorWords L).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro u hu v hv hsource
  apply canonicalSource_injective_fixedLength
  · have hulen := (mem_survivorWords_iff.mp hu).1
    have hvlen := (mem_survivorWords_iff.mp hv).1
    omega
  · exact hsource

/-- At least fifteen percent of the residue classes modulo `2^L` have a
canonical literal execution with no outward prefix through depth `L`. -/
theorem survivorSources_card_lower_bound (L : ℕ) :
    3 * 2 ^ L ≤ 20 * (survivorSources L).card := by
  rw [card_survivorSources]
  simpa [survivorWords] using firstPassage_uncovered_card_lower_bound L

/-- Every recorded source is an actual residue below `2^L`. -/
theorem survivorSource_lt_twoPow
    {L r : ℕ} (hr : r ∈ survivorSources L) :
    r < 2 ^ L := by
  classical
  rcases Finset.mem_image.mp hr with ⟨w, hw, rfl⟩
  have hwlen := (mem_survivorWords_iff.mp hw).1
  simpa [hwlen] using (canonicalExecution_spec w).1

/-- Endpoint-sensitive semantic package for every survivor residue. -/
theorem survivorSource_has_literalExecution
    {L r : ℕ} (hr : r ∈ survivorSources L) :
    ∃ w target,
      w.length = L ∧
      (canonicalExecution w).1 = r ∧
      Executes w r target ∧
      ∀ u, u <+: w → ¬ WordOutward u := by
  classical
  rcases Finset.mem_image.mp hr with ⟨w, hw, hsource⟩
  refine ⟨w, (canonicalExecution w).2,
    (mem_survivorWords_iff.mp hw).1, hsource, ?_,
    (mem_survivorWords_iff.mp hw).2⟩
  simpa [← hsource] using (canonicalExecution_spec w).2.2

/-- Every survivor residue lifts to arbitrarily large positive ordinary
sources with exactly the same length-`L` parity word. -/
theorem survivorSource_has_positive_lift
    {L r : ℕ} (hr : r ∈ survivorSources L) (k : ℕ) :
    ∃ w target,
      w.length = L ∧
      0 < r + 2 ^ L * (k + 1) ∧
      (r + 2 ^ L * (k + 1)) % 2 ^ L = r ∧
      Executes w (r + 2 ^ L * (k + 1)) target ∧
      ∀ u, u <+: w → ¬ WordOutward u := by
  classical
  rcases Finset.mem_image.mp hr with ⟨w, hw, hsource⟩
  have hwlen := (mem_survivorWords_iff.mp hw).1
  have hrlt := survivorSource_lt_twoPow hr
  let target := (canonicalExecution w).2 +
    3 ^ w.count true * (k + 1)
  refine ⟨w, target, hwlen, by positivity, ?_, ?_,
    (mem_survivorWords_iff.mp hw).2⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  · have hshift := executes_shift w (canonicalExecution_spec w).2.2 (k + 1)
    simpa [target, hwlen, hsource] using hshift

/-! ## The canonical safe extension is a 2-adic artifact -/

theorem prefix_append_singleton_cases {α : Type*}
    {u w : List α} {a : α} (h : u <+: w ++ [a]) :
    u <+: w ∨ u = w ++ [a] := by
  by_cases hlen : u.length ≤ w.length
  · left
    apply List.prefix_iff_eq_take.mpr
    have hu := List.prefix_iff_eq_take.mp h
    rw [List.take_append_of_le_length hlen] at hu
    exact hu
  · right
    apply h.eq_of_length
    have hp := h.length_le
    have hfullLen : (w ++ [a]).length = w.length + 1 := by simp
    rw [hfullLen] at hp
    omega

theorem not_outward_append_false {w : List Bool}
    (hw : ¬ WordOutward w) :
    ¬ WordOutward (w ++ [false]) := by
  intro hout
  simp [WordOutward] at hw hout
  have hpow : 2 ^ w.length ≤ 2 ^ (w.length + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Every finite survivor has a survivor child obtained by appending one even
shortcut bit. -/
theorem survivorWords_append_false
    {L : ℕ} {w : List Bool} (hw : w ∈ survivorWords L) :
    w ++ [false] ∈ survivorWords (L + 1) := by
  apply mem_survivorWords_iff.mpr
  refine ⟨by simpa using congrArg Nat.succ (mem_survivorWords_iff.mp hw).1,
    ?_⟩
  intro u hu
  rcases prefix_append_singleton_cases hu with huw | rfl
  · exact (mem_survivorWords_iff.mp hw).2 u huw
  · exact not_outward_append_false
      ((mem_survivorWords_iff.mp hw).2 w (List.prefix_refl w))

/-- Canonical source residues along the safe even child are genuinely nested
modulo the preceding dyadic precision. -/
theorem canonicalSource_append_false_mod (w : List Bool) :
    (canonicalExecution (w ++ [false])).1 % 2 ^ w.length =
      (canonicalExecution w).1 := by
  have hfull := (canonicalExecution_spec (w ++ [false])).2.2
  obtain ⟨middle, hprefix, _⟩ := (executes_append w [false]).mp hfull
  have hmod := executes_source_modEq w hprefix
    (canonicalExecution_spec w).2.2
  have hrlt := (canonicalExecution_spec w).1
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hrlt] using hmod

/-- Executing `n` consecutive even shortcut bits forces divisibility by
`2^n` at their source. -/
theorem twoPow_dvd_of_executes_replicate_false
    {n source target : ℕ}
    (h : Executes (List.replicate n false) source target) :
    2 ^ n ∣ source := by
  induction n generalizing source target with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ] at h
      obtain ⟨middle, hstep, htail⟩ := h
      simp only [Bool.false_eq_true, ↓reduceIte] at hstep
      obtain ⟨q, hq⟩ := ih htail
      refine ⟨q, ?_⟩
      rw [← hstep, hq, pow_succ]
      ring

/-- A positive endpoint after a fixed prefix cannot support arbitrarily long
all-even continuations.  This is the elementary ordinary-height obstruction
behind the apparently safe infinite branch. -/
theorem no_positive_all_false_tail
    {w : List Bool} {source finish : ℕ}
    (hfinish : 0 < finish) (hbase : Executes w source finish) :
    ¬ ∀ n, ∃ target,
      Executes (w ++ List.replicate n false) source target := by
  intro hall
  obtain ⟨target, hfull⟩ := hall finish
  obtain ⟨middle, hprefix, htail⟩ := (executes_append w _).mp hfull
  have hmiddle : middle = finish := executes_target_unique w hprefix hbase
  subst middle
  have hdvd := twoPow_dvd_of_executes_replicate_false htail
  have hle : 2 ^ finish ≤ finish := Nat.le_of_dvd hfinish hdvd
  exact (Nat.lt_two_pow_self.trans_le hle).false

/-! ## Calibration: a positive survivor ray may be the trivial cycle -/

/-- Append any bit which leaves the full new word non-outward.  Earlier
prefixes are inherited from the parent survivor. -/
theorem survivorWords_append_of_not_outward
    {L : ℕ} {w : List Bool} {b : Bool}
    (hw : w ∈ survivorWords L) (hfull : ¬ WordOutward (w ++ [b])) :
    w ++ [b] ∈ survivorWords (L + 1) := by
  apply mem_survivorWords_iff.mpr
  refine ⟨by simpa using congrArg Nat.succ (mem_survivorWords_iff.mp hw).1,
    ?_⟩
  intro u hu
  rcases prefix_append_singleton_cases hu with huw | rfl
  · exact (mem_survivorWords_iff.mp hw).2 u huw
  · exact hfull

/-- The first `n` periods of the positive shortcut cycle `2 -> 1 -> 2`. -/
def trivialCyclePrefix : ℕ → List Bool
  | 0 => []
  | n + 1 => trivialCyclePrefix n ++ [false, true]

@[simp] theorem trivialCyclePrefix_length (n : ℕ) :
    (trivialCyclePrefix n).length = 2 * n := by
  induction n with
  | zero => simp [trivialCyclePrefix]
  | succ n ih => simp [trivialCyclePrefix, ih]; omega

@[simp] theorem trivialCyclePrefix_count_true (n : ℕ) :
    (trivialCyclePrefix n).count true = n := by
  induction n with
  | zero => simp [trivialCyclePrefix]
  | succ n ih => simp [trivialCyclePrefix, ih]

theorem trivialCyclePrefix_not_outward (n : ℕ) :
    ¬ WordOutward (trivialCyclePrefix n) := by
  simp only [WordOutward, trivialCyclePrefix_length,
    trivialCyclePrefix_count_true]
  have hp : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by omega) n
  have hpow : 2 ^ (2 * n) = 4 ^ n := by norm_num [pow_mul]
  omega

theorem trivialCyclePrefix_executes (n : ℕ) :
    Executes (trivialCyclePrefix n) 2 2 := by
  induction n with
  | zero => simp [trivialCyclePrefix, Executes]
  | succ n ih =>
      rw [trivialCyclePrefix, executes_append]
      exact ⟨2, ih, by norm_num [Executes]⟩

/-- Every finite prefix of the ordinary positive `2 <-> 1` cycle lies in the
no-outward-prefix survivor tree. -/
theorem trivialCyclePrefix_mem_survivorWords (n : ℕ) :
    trivialCyclePrefix n ∈ survivorWords (2 * n) := by
  induction n with
  | zero =>
      apply mem_survivorWords_iff.mpr
      constructor
      · simp [trivialCyclePrefix]
      · intro u hu
        have : u = [] := by
          simpa [trivialCyclePrefix] using hu.eq_of_length
            (by simpa [trivialCyclePrefix] using hu.length_le)
        subst u
        norm_num [WordOutward]
  | succ n ih =>
      have hfalse := survivorWords_append_false ih
      have hfull :
          ¬ WordOutward ((trivialCyclePrefix n ++ [false]) ++ [true]) := by
        simpa [List.append_assoc, trivialCyclePrefix] using
          trivialCyclePrefix_not_outward (n + 1)
      have htrue := survivorWords_append_of_not_outward hfalse hfull
      simpa [trivialCyclePrefix, Nat.mul_add] using htrue

end OutwardSurvivorResidues
end KontoroC

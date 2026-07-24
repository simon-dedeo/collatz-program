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

end OutwardSurvivorResidues
end KontoroC

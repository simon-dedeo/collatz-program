/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.FiniteCompiler

/-!
# Portable finite-path certificates

This mirrors every mathematical field of the worker's `collatz-k-path-v1`
payload.  The checker recomputes all redundant data.  The structure theorem
then proves canonicality and both progression strides.
-/

namespace KontoroC

structure PathArtifact where
  word : List ℕ
  residueMod6 : ℕ
  seed : ℕ
  seedModulus : ℕ
  endpoint : ℕ
  endpointStride : ℕ
  affineConstant : ℕ
  totalHalvings : ℕ
  acceleratedSteps : ℕ
deriving Repr, DecidableEq

def PathArtifact.Valid (c : PathArtifact) : Prop :=
  c.word ≠ [] ∧
  (c.residueMod6 = 1 ∨ c.residueMod6 = 5) ∧
  0 < c.seed ∧
  c.seed < c.seedModulus ∧
  c.seed % 6 = c.residueMod6 ∧
  WordLegal c.seed c.word ∧
  c.seedModulus = 6 * 2 ^ totalValuation c.word ∧
  c.endpoint = runWord c.seed c.word ∧
  c.endpointStride = 6 * 3 ^ c.word.length ∧
  c.affineConstant = affineOffset c.word ∧
  c.totalHalvings = totalValuation c.word ∧
  c.acceleratedSteps = c.word.length

instance PathArtifact.instDecidableValid (c : PathArtifact) : Decidable c.Valid := by
  unfold PathArtifact.Valid
  infer_instance

def PathArtifact.check (c : PathArtifact) : Bool :=
  decide c.Valid

theorem PathArtifact.valid_of_check {c : PathArtifact}
    (h : c.check = true) : c.Valid := by
  simpa [PathArtifact.check] using h

/-- A checked artifact's seed is the unique representative in its canonical
range and residue class. -/
theorem PathArtifact.seed_unique {c : PathArtifact}
    (hc : c.check = true) {y : ℕ}
    (hylt : y < c.seedModulus)
    (hyres : y % 6 = c.residueMod6)
    (hylegal : WordLegal y c.word) : y = c.seed := by
  obtain ⟨hw, _he, _hseedpos, hseedlt, hseedres, hseedlegal,
    hmodulus, _hendpoint, _hstride, _hconstant, _hhalvings, _hsteps⟩ :=
      c.valid_of_check hc
  have hpositive : PositiveWord c.word := by
    exact wordLegal_positive_entries hseedlegal
  apply canonical_compiled_seed_unique hw hpositive
  · simpa [hmodulus] using hylt
  · simpa [hmodulus] using hseedlt
  · exact hyres
  · exact hseedres
  · exact hylegal
  · exact hseedlegal

/-- All other legal realizations in the same class lie in the checked seed
progression. -/
theorem PathArtifact.seed_modEq {c : PathArtifact}
    (hc : c.check = true) {y : ℕ}
    (hyres : y % 6 = c.residueMod6)
    (hylegal : WordLegal y c.word) :
    y ≡ c.seed [MOD c.seedModulus] := by
  obtain ⟨hw, _he, _hseedpos, _hseedlt, hseedres, hseedlegal,
    hmodulus, _hendpoint, _hstride, _hconstant, _hhalvings, _hsteps⟩ :=
      c.valid_of_check hc
  have hpositive : PositiveWord c.word :=
    wordLegal_positive_entries hseedlegal
  have hmod6 : y ≡ c.seed [MOD 6] := hyres.trans hseedres.symm
  have hfull := wordLegal_unique_mod_progression hw hpositive
    hylegal hseedlegal hmod6
  simpa [hmodulus] using hfull

/-- The redundant endpoint and endpoint-stride fields agree with every lift
of the checked seed. -/
theorem PathArtifact.runWord_lift {c : PathArtifact}
    (hc : c.check = true) (t : ℕ) :
    runWord (c.seed + c.seedModulus * t) c.word =
      c.endpoint + c.endpointStride * t := by
  obtain ⟨hw, _he, _hseedpos, _hseedlt, _hseedres, hseedlegal,
    hmodulus, hendpoint, hstride, _hconstant, _hhalvings, _hsteps⟩ :=
      c.valid_of_check hc
  have hpositive : PositiveWord c.word :=
    wordLegal_positive_entries hseedlegal
  rw [hmodulus, hendpoint, hstride]
  exact runWord_add_seedModulus t hw hpositive hseedlegal

/-- The mathematical payload format is inhabited for every positive word and
either admissible class. -/
theorem exists_valid_pathArtifact (w : List ℕ) (e : ℕ)
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (he : e = 1 ∨ e = 5) : ∃ c : PathArtifact, c.Valid := by
  obtain ⟨x, hxpos, hxlt, hxres, hxlegal⟩ :=
    exists_compiled_seed w e hw hpositive he
  let c : PathArtifact :=
    { word := w
      residueMod6 := e
      seed := x
      seedModulus := 6 * 2 ^ totalValuation w
      endpoint := runWord x w
      endpointStride := 6 * 3 ^ w.length
      affineConstant := affineOffset w
      totalHalvings := totalValuation w
      acceleratedSteps := w.length }
  refine ⟨c, ?_⟩
  exact ⟨hw, he, hxpos, hxlt, hxres, hxlegal, rfl, rfl, rfl, rfl, rfl, rfl⟩

end KontoroC

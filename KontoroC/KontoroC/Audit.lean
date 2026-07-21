/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC

/-!
# Axiom audit for the Kontorovich certificate seam

The `Examples` module deliberately contains compiler-backed `native_decide`
regressions.  None is a dependency of the soundness theorems printed here.
-/

#print axioms KontoroC.valuationWord_affine_identity
#print axioms KontoroC.cycle_denominator_mul_seed
#print axioms KontoroC.cycle_shape_strict
#print axioms KontoroC.runWord_eq_self_iff_cycle_equation
#print axioms KontoroC.cycle_seed_eq_affineOffset_div
#print axioms KontoroC.step_iterate_ordinaryDuration
#print axioms KontoroC.not_conjecture_of_legal_cycle
#print axioms KontoroC.CycleCertificate.not_conjecture_of_check
#print axioms KontoroC.CycleArtifact.not_conjecture_of_checkNontrivial
#print axioms KontoroC.AffineBlock.ofWord_append
#print axioms KontoroC.AffineBlock.concat_assoc
#print axioms KontoroC.MacroGlider.step_iterate_time
#print axioms KontoroC.MacroGlider.not_conjecture
#print axioms KontoroC.coprime_recurrence_fixed
#print axioms KontoroC.repeated_legal_block_fixed
#print axioms KontoroC.legal_block_chain_first_fixed
#print axioms KontoroC.eventually_periodic_legal_tail_fixed
#print axioms KontoroC.repeated_legal_block_shape_strict
#print axioms KontoroC.no_repeated_legal_block_of_twoPow_le_threePow
#print axioms KontoroC.not_repeated_legal_block_strictly_growing
#print axioms KontoroC.affineOddFactor_iff_wordLegal
#print axioms KontoroC.affineOddFactor_iff_finalCongruence
#print axioms KontoroC.finalCongruence_iff_wordLegal
#print axioms KontoroC.exists_finalCongruence
#print axioms KontoroC.finalCongruence_unique_mod
#print axioms KontoroC.finalCongruence_unique_mod_progression
#print axioms KontoroC.wordLegal_unique_mod_progression
#print axioms KontoroC.exists_finalCongruence_mod_three
#print axioms KontoroC.exists_compiled_seed
#print axioms KontoroC.canonical_compiled_seed_unique
#print axioms KontoroC.wordLegal_of_mod_progression
#print axioms KontoroC.runWord_add_seedModulus
#print axioms KontoroC.PathArtifact.seed_unique
#print axioms KontoroC.PathArtifact.seed_modEq
#print axioms KontoroC.PathArtifact.runWord_lift
#print axioms KontoroC.exists_valid_pathArtifact

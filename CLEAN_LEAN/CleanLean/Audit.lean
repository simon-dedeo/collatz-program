/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Relational
import CleanLean.Collatz.Syracuse
import CleanLean.KL.FiniteSystem
import CleanLean.KL.ResidueSystem
import CleanLean.KL.ExactCertificate
import CleanLean.KL.ScaledCertificate
import CleanLean.KL.IrrationalWeights
import CleanLean.KL.KLWeights
import CleanLean.KL.OscillationIdentity
import CleanLean.KL.LimitBridge
import CleanLean.KL.ConcreteLimit
import CleanLean.KL.CriticalParameter
import CleanLean.KL.LevelLift
import CleanLean.KL.RetardedComparison
import CleanLean.KL.TreeRewrite
import CleanLean.KL.CriticalAssignment
import CleanLean.KL.EliminationTree
import CleanLean.KL.ConcreteElimination
import CleanLean.KL.FiniteRecord
import CleanLean.KL.WeightedTail
import CleanLean.KL.LocalRenormalization
import CleanLean.KL.RootLaw
import CleanLean.KL.Mixer
import CleanLean.KL.TransportResolvent
import CleanLean.KL.PressureCertificate
import CleanLean.KL.ChargedLyapunov
import CleanLean.KL.MarginalObstruction
import CleanLean.KL.OrbitHitting
import CleanLean.KL.NonlinearPerron
import CleanLean.KL.CountingTransfer

/-!
# Trust-boundary audit

These commands make Lean report the axioms used by the principal proved
specification theorems during a build.
-/

#print axioms CleanLean.Collatz.conjecture_iff_relational
#print axioms CleanLean.Collatz.conjecture_iff_syracuse
#print axioms CleanLean.Collatz.conjecture_of_descent
#print axioms CleanLean.KL.FiniteSystem.operator_mono
#print axioms CleanLean.KL.FiniteSystem.fiberMin_le_average
#print axioms CleanLean.KL.ResidueSystem.transport_apply
#print axioms CleanLean.KL.ResidueSystem.transport_residue_modEq
#print axioms CleanLean.KL.ResidueSystem.card_state
#print axioms CleanLean.KL.ResidueSystem.fiber_injective
#print axioms CleanLean.KL.ResidueSystem.retarded_target_numerator
#print axioms CleanLean.KL.ResidueSystem.advanced_target_numerator
#print axioms CleanLean.KL.ResidueSystem.branch_eq_advanced_iff_residue
#print axioms CleanLean.KL.ResidueSystem.fiber_partition
#print axioms CleanLean.KL.ResidueSystem.branch_balance
#print axioms CleanLean.KL.ResidueSystem.concrete_oscillation_identity
#print axioms CleanLean.KL.FiniteSystem.feasible_of_checkFeasibleRat
#print axioms CleanLean.KL.FiniteSystem.ScaledCertificate.feasibleRat_of_check
#print axioms CleanLean.KL.div_lt_alpha_of_check
#print axioms CleanLean.KL.alpha_lt_div_of_check
#print axioms CleanLean.KL.two_rpow_alpha
#print axioms CleanLean.KL.annealedKL_two
#print axioms CleanLean.KL.annealedKL_strictAntiOn
#print axioms CleanLean.KL.checkBranchWeightLowerData_eq_true_iff
#print axioms CleanLean.KL.branchWeightLower_of_checks
#print axioms CleanLean.KL.FiniteSystem.operator_mono_weights
#print axioms CleanLean.KL.FiniteSystem.feasible_of_feasibleRat
#print axioms CleanLean.KL.FiniteSystem.ScaledCertificate.feasibleKL_of_checks
#print axioms CleanLean.KL.FiniteSystem.annealedValue_sub_one_eq_branchWeight_mul_normalizedDefect
#print axioms CleanLean.KL.tendsto_two_of_annealed_tendsto_one
#print axioms CleanLean.KL.klWeightedDefect_mul_tendsto_zero
#print axioms CleanLean.KL.klLambda_tendsto_two_of_defect
#print axioms CleanLean.KL.levelFeasible_one
#print axioms CleanLean.KL.le_criticalLambda_of_feasible
#print axioms CleanLean.KL.levelFeasible_of_scaledCertificate
#print axioms CleanLean.KL.criticalLambda_tendsto_two_of_feasible_lower
#print axioms CleanLean.KL.ResidueSystem.operator_liftValue_ge
#print axioms CleanLean.KL.levelFeasible_succ
#print axioms CleanLean.KL.criticalLambda_mono_step
#print axioms CleanLean.KL.RetardedExpr.factor_coeffEval_le_eval
#print axioms CleanLean.KL.RetardedExpr.exponential_lower_bound_of_retarded
#print axioms CleanLean.KL.RetardedExpr.quarter_exponential_lower_bound_of_retarded
#print axioms CleanLean.KL.RetardedExpr.eval_split_le_original
#print axioms CleanLean.KL.RetardedExpr.original_coeff_le_split
#print axioms CleanLean.KL.RetardedExpr.local_min_deletion_not_sound
#print axioms CleanLean.KL.RetardedExpr.Assignment.exists_isCritical
#print axioms CleanLean.KL.RetardedExpr.Assignment.selectedEval_eq_eval
#print axioms CleanLean.KL.RetardedExpr.Assignment.selectedEval_pos
#print axioms CleanLean.KL.RetardedExpr.Assignment.eval_inf_eq_right_of_no_critical_left
#print axioms CleanLean.KL.RetardedExpr.Assignment.root_inequality_of_delete_left
#print axioms CleanLean.KL.RetardedExpr.Assignment.root_coeff_le_of_delete_left
#print axioms CleanLean.KL.EliminationTree.Assignment.exists_isCritical
#print axioms CleanLean.KL.EliminationTree.Assignment.selectedEval_eq_eval
#print axioms CleanLean.KL.EliminationTree.Assignment.respectsPrincipalBounds_of_locallyValid
#print axioms CleanLean.KL.EliminationTree.Assignment.repeated_label_contradiction
#print axioms CleanLean.KL.EliminationTree.Assignment.repeated_branch_leaf_not_selected
#print axioms CleanLean.KL.ConcreteElimination.eval_splitBody_eq_base
#print axioms CleanLean.KL.ConcreteElimination.splitTree_locallyValid
#print axioms CleanLean.KL.ConcreteElimination.eval_split_in_context_le_leaf
#print axioms CleanLean.KL.ConcreteElimination.eval_eraseToRetarded
#print axioms CleanLean.KL.ConcreteElimination.coeffEval_baseBody_eq_operator
#print axioms CleanLean.KL.ConcreteElimination.leaf_coeff_le_splitTree
#print axioms CleanLean.KL.ConcreteElimination.coeff_leaf_le_split_in_context
#print axioms CleanLean.KL.FiniteRecord.levelFeasible_four_thirds
#print axioms CleanLean.KL.FiniteRecord.four_thirds_le_criticalLambda
#print axioms CleanLean.KL.weightedDefect_le_tail
#print axioms CleanLean.KL.tendsto_zero_of_weighted_tail
#print axioms CleanLean.KL.tail_tendsto_zero_of_geometric_bound
#print axioms CleanLean.KL.tendsto_zero_of_geometric_weighted_tails
#print axioms CleanLean.KL.oscillation3_scale
#print axioms CleanLean.KL.localProfile_two_step
#print axioms CleanLean.KL.advanced_fiber_min_law
#print axioms CleanLean.KL.pureBranch_root_min
#print axioms CleanLean.KL.root_min_harmonic_not_sufficient
#print axioms CleanLean.KL.range_mix3_le
#print axioms CleanLean.KL.retarded_mixer_counterexample
#print axioms CleanLean.KL.transport_cycle_resolvent
#print axioms CleanLean.KL.pressureIter_le_of_certificate
#print axioms CleanLean.KL.pressureIter_tendsto_zero
#print axioms CleanLean.KL.real_pressureCertificate_of_checkRat
#print axioms CleanLean.KL.checkChernoffGapRat_eq_true_iff
#print axioms CleanLean.KL.pressureMass_le_of_certificate
#print axioms CleanLean.KL.real_chernoffRatio_nonneg_lt_one
#print axioms CleanLean.KL.blockTail_le_geometric_of_pressure
#print axioms CleanLean.KL.blockTail_tendsto_zero_of_pressure
#print axioms CleanLean.KL.relativeCarrier_step
#print axioms CleanLean.KL.chargedCarrier_iterate
#print axioms CleanLean.KL.badMass_le_of_chargedCarrier_and_pressure
#print axioms CleanLean.KL.aligned_mean_and_cospine_same_eigenvalue
#print axioms CleanLean.KL.no_strict_relative_contraction_on_aligned_modes
#print axioms CleanLean.KL.retarded_zero_selfLift
#print axioms CleanLean.KL.retarded_zero_uncharged_selfLift
#print axioms CleanLean.KL.orbitHit_iff_exponent_dvd
#print axioms CleanLean.KL.orbitHit_first_time
#print axioms CleanLean.KL.no_orbitHit_before_precision
#print axioms CleanLean.KL.positiveEigenvalue_unique
#print axioms CleanLean.KL.one_le_positiveEigenvalue_of_subeigenvector
#print axioms CleanLean.KL.eventually_rpow_le_of_constant_mul_rpow_le
#print axioms CleanLean.KL.klExponent_tendsto_one
#print axioms CleanLean.KL.almostLinearPredecessorCounting_of_klLambda
#print axioms CleanLean.KL.almostLinearPredecessorCounting_of_feasible_sequence
#print axioms CleanLean.KL.almostLinearPredecessorCounting_of_klDefect

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
import CleanLean.KL.WeightedTail
import CleanLean.KL.LocalRenormalization
import CleanLean.KL.RootLaw
import CleanLean.KL.Mixer
import CleanLean.KL.TransportResolvent
import CleanLean.KL.PressureCertificate
import CleanLean.KL.ChargedLyapunov
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
#print axioms CleanLean.KL.FiniteSystem.annealedValue_sub_one_eq_branchWeight_mul_normalizedDefect
#print axioms CleanLean.KL.tendsto_two_of_annealed_tendsto_one
#print axioms CleanLean.KL.klWeightedDefect_mul_tendsto_zero
#print axioms CleanLean.KL.klLambda_tendsto_two_of_defect
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
#print axioms CleanLean.KL.positiveEigenvalue_unique
#print axioms CleanLean.KL.one_le_positiveEigenvalue_of_subeigenvector
#print axioms CleanLean.KL.eventually_rpow_le_of_constant_mul_rpow_le
#print axioms CleanLean.KL.klExponent_tendsto_one
#print axioms CleanLean.KL.almostLinearPredecessorCounting_of_klLambda
#print axioms CleanLean.KL.almostLinearPredecessorCounting_of_klDefect

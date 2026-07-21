/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.PredecessorCount
import CleanLean.KL.ConcreteLimit
import CleanLean.KL.CriticalParameter
import CleanLean.KL.PredecessorTransfer
import CleanLean.KL.PredecessorBase
import CleanLean.KL.HistoryWitness
import CleanLean.KL.FiniteRecord

/-!
# From KL exponents to almost-linear predecessor counting

This file formalizes the last elementary asymptotic step in the proposed KL
program.  A positive constant in a bound `C * X^gamma` can be absorbed by
lowering the exponent, and `lambda_k → 2` implies
`log₂(lambda_k) → 1`.

The substantive Krasikov--Lagarias difference-inequality theorem is exposed
as the hypothesis `HasPredecessorExponent`; it is not smuggled into the
analytic argument below.
-/

namespace CleanLean.KL

open Filter
open CleanLean.Collatz

/-- The predecessor-counting exponent corresponding to a KL parameter. -/
noncomputable def klExponent (lam : ℝ) : ℝ :=
  Real.logb 2 lam

/-- A fixed target has a predecessor lower bound with exponent `gamma`, up to
a positive target-dependent multiplicative constant. -/
def HasPredecessorExponent (a : ℕ) (gamma : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ gamma ≤ (predecessorCount a X : ℝ)

theorem rpow_logb_swap {lam z : ℝ} (hlam : 0 < lam) (hz : 0 < z) :
    lam ^ Real.logb 2 z = z ^ Real.logb 2 lam := by
  rw [Real.rpow_def_of_pos hlam, Real.rpow_def_of_pos hz]
  congr 1
  unfold Real.logb
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

theorem klCutoff_logb_div
    {a X : ℕ} (ha : 0 < a) (hX : 0 < X) :
    klCutoff a (Real.logb 2 ((X : ℝ) / a)) = X := by
  unfold klCutoff
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hratio : 0 < (X : ℝ) / a := div_pos hXR haR
  rw [Real.rpow_logb (by norm_num) (by norm_num) hratio]
  have hmul : ((X : ℝ) / a) * a = X := by field_simp
  rw [hmul]
  exact Nat.floor_natCast X

/-- Exact finite feasibility supplies the KL exponent for every eligible
target in its concrete residue state. -/
theorem hasPredecessorExponent_klTarget_of_feasible
    {k : ℕ} (hk : 2 ≤ k) {lam C : ℝ}
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (c : ResidueSystem.State k → ℝ)
    (hC : 0 < C) (hcC : ∀ state, c state ≤ C)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c)
    {state : ResidueSystem.State k} (a : KLTarget k state) :
    HasPredecessorExponent a.val (klExponent lam) := by
  let gamma := klExponent lam
  let K : ℝ := (1 / (4 * C)) * c state
  let D : ℝ := K / (a.val : ℝ) ^ gamma
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam1
  have haR : (0 : ℝ) < a.val := by exact_mod_cast a.property.1
  have hcpos : 0 < c state :=
    lt_of_lt_of_le zero_lt_one (hfeasible.1 state)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop a.val] with X hXa
  have hXpos : 0 < X := a.property.1.trans_le hXa
  let z : ℝ := (X : ℝ) / a.val
  let y : ℝ := Real.logb 2 z
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hz : 0 < z := div_pos hXR haR
  have hzOne : 1 ≤ z := by
    dsimp [z]
    apply (le_div_iff₀ haR).2
    have hXaR : (a.val : ℝ) ≤ X := by exact_mod_cast hXa
    simpa using hXaR
  have hy : 0 ≤ y := by
    dsimp [y]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hzOne
  have hcutoff : klCutoff a.val y = X := by
    dsimp [y, z]
    exact klCutoff_logb_div a.property.1 hXpos
  have hquarter := ConcreteElimination.quarter_lower_bound_of_feasible
    (k := k) (klPhi k) c lam C hlam1 hlam2
    (predecessorPhi_satisfiesBaseSystem hk)
    (fun s => one_le_klPhi_unconditional s (le_rfl : (0 : ℝ) ≤ 0))
    (fun s => klPhi_mono_unconditional s)
    hC hcC hfeasible state y hy
  have hphi := klPhi_le_target a y
  have hbounded :
      (klTargetCount a.val y : ℝ) ≤ (predecessorCount a.val X : ℝ) := by
    rw [klTargetCount, hcutoff]
    exact_mod_cast boundedPredecessorCount_le_predecessorCount a.val X
  have hchain : K * lam ^ y ≤ (predecessorCount a.val X : ℝ) := by
    dsimp [K]
    exact hquarter.trans (hphi.trans hbounded)
  have hswap : lam ^ y = z ^ gamma := by
    dsimp [y, gamma]
    exact rpow_logb_swap hlam0 hz
  have hdiv : z ^ gamma = (X : ℝ) ^ gamma / (a.val : ℝ) ^ gamma := by
    dsimp [z]
    exact Real.div_rpow (by positivity) (by positivity) gamma
  have hrearrange : D * (X : ℝ) ^ gamma = K * lam ^ y := by
    rw [hswap, hdiv]
    dsimp [D]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos haR gamma)]
  rw [hrearrange]
  exact hchain

/-- Exact level feasibility supplies the KL exponent for every eligible
target.  The auxiliary uniform bound on the feasible vector is discharged by
summing its finitely many coordinates. -/
theorem hasPredecessorExponent_klTarget_of_levelFeasible
    {k : ℕ} (hk : 2 ≤ k) {lam : ℝ}
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (hlevel : LevelFeasible k lam)
    {state : ResidueSystem.State k} (a : KLTarget k state) :
    HasPredecessorExponent a.val (klExponent lam) := by
  obtain ⟨c, hfeasible⟩ := hlevel
  let C : ℝ := ∑ s : ResidueSystem.State k, c s
  have hcNonneg : ∀ s, 0 ≤ c s := fun s =>
    zero_le_one.trans (hfeasible.1 s)
  have hcC : ∀ s, c s ≤ C := by
    intro s
    dsimp [C]
    exact Finset.single_le_sum
      (fun t _ => hcNonneg t) (Finset.mem_univ s)
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one ((hfeasible.1 state).trans (hcC state))
  exact hasPredecessorExponent_klTarget_of_feasible
    hk hlam1 hlam2 c hC hcC hfeasible a

/-- Above every positive target there is a sufficiently high power-of-two
multiple which is not Syracuse-periodic.  If the target is already
nonperiodic this is immediate.  Otherwise, a doubled multiple larger than the
sum of one displayed cycle cannot itself lie on a cycle, since its halving
path returns to the original target. -/
theorem exists_nonperiodic_two_even_pow_mul {a : ℕ} (ha : 0 < a) :
    ∃ n : ℕ, ¬ IsSyracusePeriodic (2 ^ (2 * n) * a) := by
  by_cases hanon : ¬ IsSyracusePeriodic a
  · exact ⟨0, by simpa using hanon⟩
  · have haperiodic : IsSyracusePeriodic a := by
      simpa using hanon
    obtain ⟨p, hp, hperiod⟩ := haperiodic
    let orbitSum : ℕ :=
      ∑ i ∈ Finset.range p, syracuseStep^[i] a
    let exponent : ℕ := 2 * (orbitSum + 1)
    have horbit_lt_exponent : orbitSum < exponent := by
      dsimp [exponent]
      omega
    have hexponent_lt_pow : exponent < 2 ^ exponent :=
      exponent.lt_two_pow_self
    have horbit_lt_multiple : orbitSum < 2 ^ exponent * a := by
      exact horbit_lt_exponent.trans
        (hexponent_lt_pow.trans_le
          (Nat.le_mul_of_pos_right (2 ^ exponent) ha))
    refine ⟨orbitSum + 1, ?_⟩
    change ¬ IsSyracusePeriodic (2 ^ exponent * a)
    intro hmultiple
    have hreach : syracuseStep^[exponent] (2 ^ exponent * a) = a :=
      iterate_syracuse_two_pow_mul a exponent
    obtain ⟨q, hq⟩ :=
      periodic_predecessor_is_target_iterate hreach hmultiple
    have hqle : syracuseStep^[q] a ≤ orbitSum :=
      periodic_iterate_le_orbitSum hp hperiod
    rw [hq] at hqle
    omega

/-- A positive target not divisible by three has a nonperiodic power-of-two
multiple in the KL target congruence class `2 (mod 3)`. -/
theorem exists_nonperiodic_class_two_pow_mul
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ r : ℕ, (2 ^ r * a) % 3 = 2 ∧
      ¬ IsSyracusePeriodic (2 ^ r * a) := by
  have hamod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt := Nat.mod_lt a (by norm_num : 0 < 3)
    omega
  rcases hamod with ha1 | ha2
  · obtain ⟨n, hn⟩ := exists_nonperiodic_two_even_pow_mul (a := 2 * a) (by omega)
    refine ⟨2 * n + 1, ?_, ?_⟩
    · have hpow : 2 ^ (2 * n) ≡ 1 [MOD 3] := by
        have hfour : 2 ^ 2 ≡ 1 [MOD 3] := by norm_num
        simpa [pow_mul] using hfour.pow n
      have hmul := hpow.mul (Nat.ModEq.refl (2 * a))
      have hrewrite : 2 ^ (2 * n + 1) * a = 2 ^ (2 * n) * (2 * a) := by
        rw [pow_succ]
        ring
      rw [hrewrite]
      exact Nat.mod_eq_of_modEq
        (hmul.trans (by
          rw [Nat.ModEq]
          simp [Nat.mul_mod, ha1])) (by norm_num)
    · simpa [pow_succ, mul_assoc] using hn
  · obtain ⟨n, hn⟩ := exists_nonperiodic_two_even_pow_mul ha
    refine ⟨2 * n, ?_, hn⟩
    have hfour : 2 ^ 2 ≡ 1 [MOD 3] := by norm_num
    have hpow : 2 ^ (2 * n) ≡ 1 [MOD 3] := by
      simpa [pow_mul] using hfour.pow n
    exact Nat.mod_eq_of_modEq
      ((hpow.mul (Nat.ModEq.refl a)).trans
        (by simp [Nat.ModEq, ha2] : 1 * a ≡ 2 [MOD 3])) (by norm_num)

/-- A positive multiplicative constant can be absorbed by any strict decrease
in the power exponent. -/
theorem eventually_rpow_le_of_constant_mul_rpow_le
    {count : ℕ → ℝ} {C gamma' gamma : ℝ}
    (hC : 0 < C) (hgamma : gamma' < gamma)
    (hbound : ∀ᶠ X : ℕ in atTop,
      C * (X : ℝ) ^ gamma ≤ count X) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ gamma' ≤ count X := by
  have hgrowth : ∀ᶠ X : ℕ in atTop,
      C⁻¹ < (X : ℝ) ^ (gamma - gamma') := by
    have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ (gamma - gamma')) atTop atTop :=
      (tendsto_rpow_atTop (sub_pos.mpr hgamma)).comp
        tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_gt_atTop C⁻¹)
  filter_upwards [hbound, hgrowth, eventually_ge_atTop (1 : ℕ)] with X hX hg hX1
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX1
  have hone : 1 ≤ C * (X : ℝ) ^ (gamma - gamma') := by
    have hmul := mul_lt_mul_of_pos_left hg hC
    simpa [ne_of_gt hC] using hmul.le
  calc
    (X : ℝ) ^ gamma' = 1 * (X : ℝ) ^ gamma' := by ring
    _ ≤ (C * (X : ℝ) ^ (gamma - gamma')) * (X : ℝ) ^ gamma' := by
      gcongr
    _ = C * (X : ℝ) ^ gamma := by
      rw [mul_assoc, mul_comm ((X : ℝ) ^ (gamma - gamma'))]
      rw [← Real.rpow_add hXpos]
      congr 2
      linarith
    _ ≤ count X := hX

theorem hasPredecessorExponent_mono {a : ℕ} {gamma' gamma : ℝ}
    (hgamma : gamma' < gamma) (h : HasPredecessorExponent a gamma) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ gamma' ≤ (predecessorCount a X : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := h
  exact eventually_rpow_le_of_constant_mul_rpow_le hC hgamma hbound

/-- A predecessor exponent transfers backward along any finite target orbit.
This is the exact ordinary-count inclusion used after choosing a suitable
doubled target in the corrected all-target argument. -/
theorem hasPredecessorExponent_of_target_reaches
    {a b : ℕ} {gamma : ℝ}
    (hba : IsSyracusePredecessor a b)
    (hbound : HasPredecessorExponent b gamma) :
    HasPredecessorExponent a gamma := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with X hX
  exact hX.trans (by
    exact_mod_cast predecessorCount_mono_of_target_reaches
      (X := X) hba)

/-- Specialization to the target `2^r*a`. -/
theorem hasPredecessorExponent_of_two_pow_mul
    {a : ℕ} {gamma : ℝ} (r : ℕ)
    (hbound : HasPredecessorExponent (2 ^ r * a) gamma) :
    HasPredecessorExponent a gamma := by
  apply hasPredecessorExponent_of_target_reaches
    (b := 2 ^ r * a)
  · exact ⟨r, iterate_syracuse_two_pow_mul a r⟩
  · exact hbound

/-- The fully concrete finite-level KL counting theorem.  Exact feasibility
at any level `k ≥ 2` and parameter `1 < lam ≤ 2` supplies the exponent
`log₂ lam` for every positive target not divisible by three. -/
theorem hasPredecessorExponent_of_levelFeasible
    {k : ℕ} (hk : 2 ≤ k) {lam : ℝ}
    (hlam1 : 1 < lam) (hlam2 : lam ≤ 2)
    (hlevel : LevelFeasible k lam)
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    HasPredecessorExponent a (klExponent lam) := by
  obtain ⟨r, hb3, hbnon⟩ :=
    exists_nonperiodic_class_two_pow_mul ha ha3
  let b : ℕ := 2 ^ r * a
  let state : ResidueSystem.State k := klStateOf k b
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  let target : KLTarget k state :=
    ⟨b, hbpos, klStateOf_target_modEq (by omega) hb3, hbnon⟩
  apply hasPredecessorExponent_of_two_pow_mul r
  simpa [target, b] using
    (hasPredecessorExponent_klTarget_of_levelFeasible
      hk hlam1 hlam2 hlevel target)

/-- A completely closed end-to-end example using the tiny checked level-2
certificate in `FiniteRecord`.  This theorem exercises the same trusted
certificate-to-counting path intended for the larger GPU certificates. -/
theorem hasPredecessorExponent_four_thirds
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    HasPredecessorExponent a (klExponent (4 / 3 : ℝ)) := by
  exact hasPredecessorExponent_of_levelFeasible (k := 2)
    (by norm_num) (by norm_num) (by norm_num)
    FiniteRecord.levelFeasible_four_thirds ha ha3

/-- `lambda_k → 2` gives convergence of the corresponding base-two
counting exponents to one. -/
theorem klExponent_tendsto_one (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop (nhds 2)) :
    Tendsto (fun k => klExponent (lam k)) atTop (nhds 1) := by
  have hcont : ContinuousAt (Real.logb 2) (2 : ℝ) :=
    Real.continuousAt_logb (by norm_num)
  simpa [klExponent, Function.comp_def,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
    hcont.tendsto.comp hlam

/-- The purely analytic endgame: if every finite KL exponent supplies the
corresponding predecessor lower bound and the exponents tend to one, then
predecessor counting is `X^(1-epsilon)` for every positive epsilon. -/
theorem almostLinearPredecessorCounting_of_exponents
    (gamma : ℕ → ℝ)
    (hgamma : Tendsto gamma atTop (nhds 1))
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (gamma k)) :
    AlmostLinearPredecessorCounting := by
  intro a ha ha3 ε hε
  have hnear : ∀ᶠ k : ℕ in atTop, gamma k ∈ Set.Ioi (1 - ε) :=
    hgamma.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨k, hk⟩ := hnear.exists
  exact hasPredecessorExponent_mono hk (hbound a ha ha3 k)

/-- The exact public-facing KL implication.  All analytic limit and
constant-absorption steps are proved here; `hbound` is precisely the
literature transfer theorem that remains to formalize from KL's difference
inequalities. -/
theorem almostLinearPredecessorCounting_of_klLambda
    (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop (nhds 2))
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (klExponent (lam k))) :
    AlmostLinearPredecessorCounting :=
  almostLinearPredecessorCounting_of_exponents
    (fun k => klExponent (lam k)) (klExponent_tendsto_one lam hlam) hbound

/-- Fully direct route from a cofinal family of exact feasible vectors to
almost-linear predecessor counting.  This avoids critical eigenvector
existence and localization; the sole literature hypothesis is the KL
difference-inequality transfer from exact finite feasibility to the power
lower bound. -/
theorem almostLinearPredecessorCounting_of_feasible_sequence
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (nhds 2))
    (hfeasible : ∀ k, LevelFeasible k (mu k))
    (htransfer : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 → ∀ k : ℕ,
      LevelFeasible k (mu k) →
        HasPredecessorExponent a (klExponent (mu k))) :
    AlmostLinearPredecessorCounting := by
  apply almostLinearPredecessorCounting_of_klLambda mu hmu
  intro a ha ha3 k
  exact htransfer a ha ha3 k (hfeasible k)

/-- Fully concrete direct route from exact finite feasibility to
`X^(1-epsilon)` predecessor counting.  The tail begins at level two because
the literal KL base-system theorem has that hypothesis.  There is no longer a
separate literature-transfer assumption in this statement. -/
theorem almostLinearPredecessorCounting_of_feasible_sequence_concrete
    (mu : ℕ → ℝ)
    (hmu : Tendsto mu atTop (nhds 2))
    (hmuUpper : ∀ k, mu k ≤ 2)
    (hfeasible : ∀ k, 2 ≤ k → LevelFeasible k (mu k)) :
    AlmostLinearPredecessorCounting := by
  have heventuallyLower : ∀ᶠ k : ℕ in atTop, 1 < mu k :=
    hmu.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  rw [eventually_atTop] at heventuallyLower
  obtain ⟨N, hN⟩ := heventuallyLower
  let offset : ℕ := max N 2
  let tail : ℕ → ℝ := fun n => mu (n + offset)
  have htail : Tendsto tail atTop (nhds 2) := by
    exact (tendsto_add_atTop_iff_nat offset).2 hmu
  apply almostLinearPredecessorCounting_of_klLambda tail htail
  intro a ha ha3 n
  have hk : 2 ≤ n + offset := by
    dsimp [offset]
    omega
  have hkN : N ≤ n + offset := by
    dsimp [offset]
    omega
  exact hasPredecessorExponent_of_levelFeasible hk
    (hN (n + offset) hkN) (hmuUpper (n + offset))
    (hfeasible (n + offset) hk) ha ha3

/-- A convenience composition with the already formalized concrete
defect-to-endpoint theorem. -/
theorem almostLinearPredecessorCounting_of_klDefect
    (lam delta : ℕ → ℝ)
    (hlam : ∀ k, lam k ∈ Set.Icc (1 : ℝ) 2)
    (hdelta0 : ∀ k, 0 ≤ delta k)
    (hdelta : Tendsto delta atTop (nhds 0))
    (hidentity : ∀ k, annealedKL (lam k) - 1 =
      ((klWeights (lam k)).retarded +
        (klWeights (lam k)).advanced) * delta k)
    (hbound : ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∀ k : ℕ, HasPredecessorExponent a (klExponent (lam k))) :
    AlmostLinearPredecessorCounting :=
  almostLinearPredecessorCounting_of_klLambda lam
    (klLambda_tendsto_two_of_defect lam delta hlam hdelta0 hdelta hidentity)
    hbound

end CleanLean.KL

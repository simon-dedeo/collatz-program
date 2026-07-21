/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.AnnealedIrreducible
import CleanLean.KL.LevelLift

/-!
# Algebra for qualitative adjacent strict lifting

This file develops the parameter-free nonlinear part of the adjacent-level
strict-lift mechanism.  It records exactly which facts use the three-fiber
minimum, which use positivity of the transport edge, and which use the full
transport cycle.  The later parameter-continuity step is kept separate.
-/

namespace CleanLean.KL

open scoped BigOperators

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- The minimum of coordinatewise sums dominates the sum of the two separate
three-point minima. -/
theorem fiberMin_add_super (c d : S.State → ℝ) (r : S.Coarse) :
    S.fiberMin c r + S.fiberMin d r ≤ S.fiberMin (c + d) r := by
  simp only [fiberMin, Pi.add_apply]
  have h12 :
      min (c (S.fiber r 1)) (c (S.fiber r 2)) +
          min (d (S.fiber r 1)) (d (S.fiber r 2)) ≤
        min (c (S.fiber r 1) + d (S.fiber r 1))
          (c (S.fiber r 2) + d (S.fiber r 2)) :=
    min_add_min_le_min_add_add
  exact (min_add_min_le_min_add_add.trans
    (min_le_min le_rfl h12))

/-- The fiber minimum is homogeneous for nonnegative scalars. -/
theorem fiberMin_smul_nonneg (a : ℝ) (ha : 0 ≤ a)
    (c : S.State → ℝ) (r : S.Coarse) :
    S.fiberMin (a • c) r = a * S.fiberMin c r := by
  simp only [fiberMin, Pi.smul_apply, smul_eq_mul]
  rw [mul_min_of_nonneg _ _ ha, mul_min_of_nonneg _ _ ha]

/-- The nonlinear operator is homogeneous for nonnegative scalars. -/
theorem operator_smul_nonneg (w : Weights ℝ) (a : ℝ) (ha : 0 ≤ a)
    (c : S.State → ℝ) :
    S.operator w (a • c) = a • S.operator w c := by
  funext q
  cases hb : S.branch q <;>
    simp only [operator, hb, Pi.smul_apply, smul_eq_mul,
      S.fiberMin_smul_nonneg a ha]
  all_goals ring

/-- For a positive base point, a fixed finite KL expression is continuous in
the real parameter. -/
theorem continuousAt_operator_klWeights
    {lam : ℝ} (hlam : 0 < lam) (c : S.State → ℝ) (q : S.State) :
    ContinuousAt (fun mu => S.operator (klWeights mu) c q) lam := by
  have hne : lam ≠ 0 := hlam.ne'
  have ht := Real.continuousAt_rpow_const lam (-2 : ℝ) (Or.inl hne)
  have hr := Real.continuousAt_rpow_const lam (alpha - 2) (Or.inl hne)
  have ha := Real.continuousAt_rpow_const lam (alpha - 1) (Or.inl hne)
  cases hb : S.branch q with
  | retarded =>
      simp only [operator, klWeights, hb]
      exact (ht.mul_const _).add (hr.mul_const _)
  | neutral =>
      simp only [operator, klWeights, hb]
      exact (ht.mul_const _).add_const 0
  | advanced =>
      simp only [operator, klWeights, hb]
      exact (ht.mul_const _).add (ha.mul_const _)

/-- The nonlinear KL operator is superadditive when its branch coefficients
are nonnegative. -/
theorem operator_superadditive (w : Weights ℝ)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (c d : S.State → ℝ) (q : S.State) :
    S.operator w c q + S.operator w d q ≤ S.operator w (c + d) q := by
  have hf := S.fiberMin_add_super c d (S.refinementTarget q)
  cases hb : S.branch q with
  | retarded =>
      simp only [operator, hb, Pi.add_apply]
      have := mul_le_mul_of_nonneg_left hf hwr
      linarith
  | neutral =>
      simp only [operator, hb, Pi.add_apply]
      ring_nf
      exact le_refl _
  | advanced =>
      simp only [operator, hb, Pi.add_apply]
      have := mul_le_mul_of_nonneg_left hf hwa
      linarith

/-- The transport summand is a pointwise lower bound for the nonlinear
operator on the nonnegative cone. -/
theorem transport_term_le_operator (w : Weights ℝ)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) (q : S.State) :
    w.transport * c (S.transport q) ≤ S.operator w c q := by
  have hf : 0 ≤ S.fiberMin c (S.refinementTarget q) :=
    S.fiberMin_nonneg c hc _
  cases hb : S.branch q with
  | retarded =>
      simp only [operator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hwr hf)
  | neutral => simp [operator, hb]
  | advanced =>
      simp only [operator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hwa hf)

/-- Sum of the first `n` iterates of a vector under an operator. -/
def iterateSum (F : (S.State → ℝ) → S.State → ℝ)
    (n : ℕ) (x : S.State → ℝ) : S.State → ℝ :=
  fun q => ∑ i ∈ Finset.range n, (F^[i] x) q

@[simp] theorem iterateSum_zero
    (F : (S.State → ℝ) → S.State → ℝ) (x : S.State → ℝ) :
    S.iterateSum F 0 x = 0 := by
  funext q
  simp [iterateSum]

theorem iterateSum_succ
    (F : (S.State → ℝ) → S.State → ℝ) (n : ℕ) (x : S.State → ℝ) :
    S.iterateSum F (n + 1) x = S.iterateSum F n x + F^[n] x := by
  funext q
  simp [iterateSum, Finset.sum_range_succ]

/-- Iterates of a nonnegative vector remain nonnegative. -/
theorem operator_iterate_nonneg (w : Weights ℝ)
    (hwt : 0 ≤ w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced) (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) :
    ∀ n q, 0 ≤ ((S.operator w)^[n] c) q := by
  intro n
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact S.operator_nonneg w hwt hwr hwa _ ih

/-- The `n`th nonlinear iterate dominates the `n`th weighted transport
iterate. -/
theorem operator_iterate_transport_lower (w : Weights ℝ)
    (hwt : 0 ≤ w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced) (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) :
    ∀ n q,
      w.transport ^ n * c ((S.transport)^[n] q) ≤
        ((S.operator w)^[n] c) q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply' (S.operator w),
        Function.iterate_succ_apply (S.transport), pow_succ']
      have htransport := S.transport_term_le_operator w hwr hwa
        ((S.operator w)^[n] c)
        (S.operator_iterate_nonneg w hwt hwr hwa c hc n) q
      have hih := ih (S.transport q)
      calc
        w.transport * w.transport ^ n *
              c ((S.transport)^[n] (S.transport q)) =
            w.transport *
              (w.transport ^ n * c ((S.transport)^[n] (S.transport q))) := by
                ring
        _ ≤ w.transport * ((S.operator w)^[n] c) (S.transport q) :=
          mul_le_mul_of_nonneg_left hih hwt
        _ ≤ S.operator w ((S.operator w)^[n] c) q := htransport

/-- The operator of a finite sum dominates the sum of the operators. -/
theorem finset_sum_operator_le {ι : Type} (w : Weights ℝ)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (A : Finset ι) (f : ι → S.State → ℝ) (q : S.State) :
    (∑ i ∈ A, S.operator w (f i) q) ≤
      S.operator w (fun s => ∑ i ∈ A, f i s) q := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      cases hb : S.branch q <;> simp [operator, fiberMin, hb]
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha]
      have hfun :
          (fun s => ∑ i ∈ insert a A, f i s) =
            f a + (fun s => ∑ i ∈ A, f i s) := by
        funext s
        simp [ha]
      rw [hfun]
      have hsuper := S.operator_superadditive w hwr hwa (f a)
        (fun s => ∑ i ∈ A, f i s) q
      have hmono :
          S.operator w (f a) q + (∑ i ∈ A, S.operator w (f i) q) ≤
            S.operator w (f a) q +
              S.operator w (fun s => ∑ i ∈ A, f i s) q :=
        add_le_add (le_refl _) ih
      exact hmono.trans hsuper

/-- Telescoping identity for a shifted finite sequence. -/
theorem sum_range_succ_index (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, a (i + 1)) =
      (∑ i ∈ Finset.range n, a i) + a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

/-- Applying the operator to an orbit sum dominates the shifted orbit sum. -/
theorem operator_iterateSum_ge (w : Weights ℝ)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (n : ℕ) (c : S.State → ℝ) (q : S.State) :
    S.iterateSum (S.operator w) n c q +
        ((S.operator w)^[n] c) q - c q ≤
      S.operator w (S.iterateSum (S.operator w) n c) q := by
  have hsum := S.finset_sum_operator_le w hwr hwa
    (Finset.range n) (fun i => (S.operator w)^[i] c) q
  have hshift :
      (∑ i ∈ Finset.range n,
          S.operator w ((S.operator w)^[i] c) q) =
        S.iterateSum (S.operator w) n c q +
          ((S.operator w)^[n] c) q - c q := by
    rw [iterateSum]
    have htel := sum_range_succ_index
      (fun i => ((S.operator w)^[i] c) q) n
    calc
      (∑ i ∈ Finset.range n,
          S.operator w ((S.operator w)^[i] c) q) =
          ∑ i ∈ Finset.range n, ((S.operator w)^[i + 1] c) q := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Function.iterate_succ_apply']
      _ = S.iterateSum (S.operator w) n c q +
          ((S.operator w)^[n] c) q - c q := by
            simpa [iterateSum] using htel
  rw [← hshift]
  exact hsum

/-- A nonnegative one-step gain propagates through every later iterate. -/
theorem orbit_gain_lower (w : Weights ℝ)
    (hwt : 0 ≤ w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced) (x d : S.State → ℝ)
    (hstep : ∀ q, x q + d q = S.operator w x q) :
    ∀ n q, x q + S.iterateSum (S.operator w) n d q ≤
      ((S.operator w)^[n] x) q := by
  intro n
  induction n with
  | zero => simp [iterateSum]
  | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply']
      have hmono := S.operator_mono w hwt hwr hwa (ih :
        ∀ s, x s + S.iterateSum (S.operator w) n d s ≤
          ((S.operator w)^[n] x) s) q
      have hsuper := S.operator_superadditive w hwr hwa x
        (S.iterateSum (S.operator w) n d) q
      have hsum := S.operator_iterateSum_ge w hwr hwa n d q
      rw [iterateSum_succ]
      have hstepq := hstep q
      calc
        x q + (S.iterateSum (S.operator w) n d +
            (S.operator w)^[n] d) q =
            (x q + d q) +
              (S.iterateSum (S.operator w) n d q +
                ((S.operator w)^[n] d) q - d q) := by
                  simp only [Pi.add_apply]
                  ring
        _ ≤ S.operator w x q +
              S.operator w (S.iterateSum (S.operator w) n d) q := by
                exact add_le_add (le_of_eq hstepq) hsum
        _ ≤ S.operator w
              (x + S.iterateSum (S.operator w) n d) q := hsuper
        _ ≤ S.operator w ((S.operator w)^[n] x) q := hmono

/-- On a full concrete transport cycle, any nonzero nonnegative gain becomes
strictly positive in the orbit sum at every coordinate. -/
theorem ResidueSystem.iterateSum_pos_of_gain
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced) (d : ResidueSystem.State k → ℝ)
    (hd : ∀ q, 0 ≤ d q) (hdpos : ∃ q, 0 < d q) :
    ∀ q, 0 < (ResidueSystem.system k).iterateSum
      ((ResidueSystem.system k).operator w) (3 ^ (k - 1)) d q := by
  intro q
  obtain ⟨r, hr⟩ := hdpos
  obtain ⟨i, hi⟩ := ResidueSystem.exists_transport_iterate_eq k hk q r
  apply Finset.sum_pos'
  · intro n hn
    exact (ResidueSystem.system k).operator_iterate_nonneg w hwt.le hwr hwa d hd n q
  · refine ⟨i.val, ?_, ?_⟩
    · simpa using i.isLt
    · have hlower := (ResidueSystem.system k).operator_iterate_transport_lower
        w hwt.le hwr hwa d hd i.val q
      have hp : 0 < w.transport ^ i.val := pow_pos hwt _
      have hterm : 0 < w.transport ^ i.val * d
          (((ResidueSystem.system k).transport)^[i.val] q) := by
        rw [show ((ResidueSystem.system k).transport)^[i.val] q = r from hi]
        exact mul_pos hp hr
      exact hterm.trans_le hlower

/-- Summing one full transport cycle of nonlinear iterates turns a single
positive gain coordinate into a strict subeigenvector at every coordinate. -/
theorem ResidueSystem.fullCycleSum_strict_subeigen
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced)
    (x d : ResidueSystem.State k → ℝ)
    (hd : ∀ q, 0 ≤ d q) (hdpos : ∃ q, 0 < d q)
    (hstep : ∀ q, x q + d q =
      (ResidueSystem.system k).operator w x q) :
    let y := (ResidueSystem.system k).iterateSum
      ((ResidueSystem.system k).operator w) (3 ^ (k - 1)) x
    ∀ q, y q < (ResidueSystem.system k).operator w y q := by
  let S := ResidueSystem.system k
  let D := 3 ^ (k - 1)
  let y := S.iterateSum (S.operator w) D x
  have horbit := S.orbit_gain_lower w hwt.le hwr hwa x d hstep D
  have hpositive := ResidueSystem.iterateSum_pos_of_gain k hk w hwt hwr hwa
    d hd hdpos
  have hiterate : ∀ q, x q < ((S.operator w)^[D] x) q := by
    intro q
    have hgain := horbit q
    have hp := hpositive q
    dsimp only [S, D] at hgain hp ⊢
    linarith
  have hsum := S.operator_iterateSum_ge w hwr hwa D x
  dsimp only [y, S, D]
  intro q
  have hs := hsum q
  have hi := hiterate q
  dsimp only [S, D] at hs hi
  linarith

/-- A coordinatewise strict KL inequality persists after a small increase of
the parameter, because there are only finitely many coordinates. -/
theorem exists_larger_parameter_of_strict
    {lam : ℝ} (hlam : 0 < lam) (hlam2 : lam < 2)
    (y : S.State → ℝ)
    (hstrict : ∀ q, y q < S.operator (klWeights lam) y q) :
    ∃ mu : ℝ, lam < mu ∧ mu < 2 ∧
      ∀ q, y q < S.operator (klWeights mu) y q := by
  have heach : ∀ q : S.State,
      ∀ᶠ mu in nhds lam, y q < S.operator (klWeights mu) y q := by
    intro q
    exact continuousAt_const.eventually_lt
      (S.continuousAt_operator_klWeights hlam y q) (hstrict q)
  have hall : ∀ᶠ mu in nhds lam,
      ∀ q : S.State, y q < S.operator (klWeights mu) y q := by
    have hall' : ∀ᶠ mu in nhds lam,
        ∀ q ∈ (Finset.univ : Finset S.State),
          y q < S.operator (klWeights mu) y q :=
      (Finset.eventually_all Finset.univ).2 fun q hq => heach q
    simpa using hall'
  have hmem : {mu : ℝ |
      ∀ q : S.State, y q < S.operator (klWeights mu) y q} ∈ nhds lam := hall
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hmem
  let delta := min (eps / 2) ((2 - lam) / 2)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (half_pos heps) (half_pos (sub_pos.mpr hlam2))
  have hdelta_eps : delta < eps := by
    have hle : delta ≤ eps / 2 := min_le_left _ _
    linarith
  have hdelta_two : delta < 2 - lam := by
    have hle : delta ≤ (2 - lam) / 2 := min_le_right _ _
    linarith
  refine ⟨lam + delta, by linarith, by linarith, ?_⟩
  apply hball
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hdelta.le] using hdelta_eps

/-- A positive subeigenvector can be rescaled to meet the KL normalization
`1 ≤ c q`.  In particular, every positive exact fixed vector supplies an
ordinary finite feasibility witness. -/
theorem feasible_of_positive_subeigen [Nonempty S.State]
    (w : Weights ℝ) (y : S.State → ℝ)
    (hy : ∀ q, 0 < y q)
    (hsub : ∀ q, y q ≤ S.operator w y q) :
    ∃ z, S.Feasible w z := by
  obtain ⟨A, hA0, i, hdom, htight⟩ :=
    exists_tight_domination y (fun _ => 1) hy (fun _ => zero_le_one)
  have hApos : 0 < A := by
    have hyi := hy i
    have hone : (0 : ℝ) < 1 := by norm_num
    rw [htight] at hone
    exact pos_of_mul_pos_left hone hyi.le
  let z := A • y
  refine ⟨z, ?_, ?_⟩
  · intro q
    simpa only [z, Pi.smul_apply, smul_eq_mul] using hdom q
  · intro q
    have hscaled := mul_le_mul_of_nonneg_left (hsub q) hA0
    have hhom := congrFun (S.operator_smul_nonneg w A hA0 y) q
    dsimp only [z]
    rw [hhom]
    simpa only [Pi.smul_apply, smul_eq_mul] using hscaled

/-- Strict specialization retained for the adjacent-parameter improvement
argument. -/
theorem feasible_of_positive_strict [Nonempty S.State]
    (w : Weights ℝ) (y : S.State → ℝ)
    (hy : ∀ q, 0 < y q)
    (hstrict : ∀ q, y q < S.operator w y q) :
    ∃ z, S.Feasible w z :=
  S.feasible_of_positive_subeigen w y hy fun q => (hstrict q).le

end

end FiniteSystem

namespace ResidueSystem

noncomputable section

/-- Copying a coarse vector makes every new fine fiber constant, so its
fine-level fiber defect is exactly zero. -/
@[simp] theorem fiberDefect_liftValue_zero (k : ℕ)
    (c : State k → ℝ) (r : Coarse (k + 1)) :
    (system (k + 1)).fiberDefect (liftValue k c) r = 0 := by
  simp [FiniteSystem.fiberDefect, FiniteSystem.fiberSum, liftValue,
    system, FiniteSystem.fiberMin]
  ring

@[simp] theorem defectMass_liftValue_zero (k : ℕ) (c : State k → ℝ) :
    (system (k + 1)).defectMass (liftValue k c) = 0 := by
  unfold FiniteSystem.defectMass
  apply Finset.sum_eq_zero
  intro r hr
  exact fiberDefect_liftValue_zero k c r

theorem totalMass_liftValue_pos (k : ℕ) (c : State k → ℝ)
    (hc : ∀ q, 0 < c q) :
    0 < (system (k + 1)).totalMass (liftValue k c) := by
  apply Finset.sum_pos
  · intro s hs
    exact hc (parent k s)
  · exact ⟨(0 : State (k + 1)), Finset.mem_univ _⟩

@[simp] theorem normalizedDefect_liftValue_zero (k : ℕ)
    (c : State k → ℝ) :
    (system (k + 1)).normalizedDefect (liftValue k c) = 0 := by
  simp [FiniteSystem.normalizedDefect]

/-- A positive coarse subeigenvector below the annealed endpoint creates a
nonzero nonnegative slack vector after copying it to the next level. -/
theorem lifted_gain_nonnegative_nonzero_of_subeigen
    (k : ℕ) (hk : 2 ≤ k) (lam : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam < 2)
    (c : State k → ℝ) (hc : ∀ q, 0 < c q)
    (hsub : ∀ q, c q ≤ (system k).operator (klWeights lam) c q) :
    let x := liftValue k c
    let d := fun q => (system (k + 1)).operator (klWeights lam) x q - x q
    (∀ q, 0 ≤ d q) ∧ ∃ q, 0 < d q := by
  let w := klWeights lam
  let x := liftValue k c
  let d : (system (k + 1)).State → ℝ :=
    fun q => (system (k + 1)).operator w x q - x q
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam1.le
  have hret : 0 ≤ w.retarded := Real.rpow_nonneg hlam0 _
  have hadv : 0 ≤ w.advanced := Real.rpow_nonneg hlam0 _
  have hd : ∀ q : (system (k + 1)).State, 0 ≤ d q := by
    intro q
    let q' : State (k + 1) := q
    apply sub_nonneg.mpr
    have hlift := operator_liftValue_ge k hk w c hret hadv q'
    dsimp only [x, liftValue]
    have hsubq : c (parent k q') ≤
        (system k).operator w c (parent k q') := by
      simpa only [w] using hsub (parent k q')
    simpa only [q'] using hsubq.trans hlift
  refine ⟨hd, ?_⟩
  have hmass : 0 < (system (k + 1)).totalMass x :=
    totalMass_liftValue_pos k c hc
  have hidentity := concrete_oscillation_identity_with_slack
    (k + 1) (by omega) w x hmass.ne'
  have hlamMem : lam ∈ Set.Icc (1 : ℝ) 2 := ⟨hlam1.le, hlam2.le⟩
  have htwoMem : (2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := by norm_num
  have hannealed : 1 < annealedKL lam := by
    rw [← annealedKL_two]
    exact annealedKL_strictAntiOn hlamMem htwoMem hlam2
  have hnormSlack : 0 < (system (k + 1)).normalizedSlack w x := by
    change FiniteSystem.annealedValue w - 1 = _ at hidentity
    have hdefect : (system (k + 1)).normalizedDefect x = 0 := by
      exact normalizedDefect_liftValue_zero k c
    rw [hdefect, mul_zero, zero_add] at hidentity
    change annealedKL lam - 1 = _ at hidentity
    linarith
  have hslack : 0 < (system (k + 1)).slackMass w x := by
    simp only [FiniteSystem.normalizedSlack] at hnormSlack
    rcases (div_pos_iff.mp hnormSlack) with h | h
    · exact h.1
    · exfalso
      linarith
  have hsum : 0 < ∑ q, d q := by
    simpa only [FiniteSystem.slackMass, d] using hslack
  obtain ⟨q, hqmem, hq⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun q _ => hd q).mp hsum
  exact ⟨q, hq⟩

/-- Fixed-vector specialization of the lifted-gain theorem. -/
theorem lifted_gain_nonnegative_nonzero
    (k : ℕ) (hk : 2 ≤ k) (lam : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam < 2)
    (c : State k → ℝ) (hc : ∀ q, 0 < c q)
    (hfixed : ∀ q, c q = (system k).operator (klWeights lam) c q) :
    let x := liftValue k c
    let d := fun q => (system (k + 1)).operator (klWeights lam) x q - x q
    (∀ q, 0 ≤ d q) ∧ ∃ q, 0 < d q := by
  apply lifted_gain_nonnegative_nonzero_of_subeigen k hk lam hlam1 hlam2 c hc
  intro q
  exact (hfixed q).le

/-- Qualitative adjacent strict lift.  A strictly positive subeigenvector at
level `k` and a parameter strictly between `1` and `2` yields exact feasibility
at level `k+1` for some strictly larger parameter.

The theorem gives no uniform lower bound on the parameter increase and does
not by itself prove convergence to `2`. -/
theorem levelFeasible_succ_strict_of_positive_subeigen
    (k : ℕ) (hk : 2 ≤ k) (lam : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam < 2)
    (c : State k → ℝ) (hc : ∀ q, 0 < c q)
    (hsub : ∀ q, c q ≤ (system k).operator (klWeights lam) c q) :
    ∃ mu : ℝ, lam < mu ∧ mu < 2 ∧ LevelFeasible (k + 1) mu := by
  let w := klWeights lam
  let x := liftValue k c
  let d : State (k + 1) → ℝ :=
    fun q => (system (k + 1)).operator w x q - x q
  let D := 3 ^ ((k + 1) - 1)
  let y := (system (k + 1)).iterateSum ((system (k + 1)).operator w) D x
  have hlamPos : 0 < lam := lt_trans (by norm_num) hlam1
  have hlam0 : 0 ≤ lam := hlamPos.le
  have hwt : 0 < w.transport := by
    exact Real.rpow_pos_of_pos hlamPos _
  have hret : 0 ≤ w.retarded := Real.rpow_nonneg hlam0 _
  have hadv : 0 ≤ w.advanced := Real.rpow_nonneg hlam0 _
  have hgain := lifted_gain_nonnegative_nonzero_of_subeigen
    k hk lam hlam1 hlam2 c hc hsub
  dsimp only [x, d, w] at hgain
  have hd : ∀ q, 0 ≤ d q := by
    intro q
    let q' : (system (k + 1)).State := q
    simpa only [d, x, w, q'] using hgain.1 q'
  have hdpos : ∃ q, 0 < d q := by
    obtain ⟨q, hq⟩ := hgain.2
    let q' : State (k + 1) := q
    exact ⟨q', by simpa only [d, x, w, q'] using hq⟩
  have hstep : ∀ q, x q + d q = (system (k + 1)).operator w x q := by
    intro q
    dsimp only [d]
    ring
  have hstrict : ∀ q, y q < (system (k + 1)).operator w y q := by
    have h := FiniteSystem.ResidueSystem.fullCycleSum_strict_subeigen
      (k + 1) (by omega) w
      hwt hret hadv x d hd hdpos hstep
    simpa only [y, D] using h
  have hx : ∀ q, 0 < x q := fun q => hc (parent k q)
  have hx0 : ∀ q, 0 ≤ x q := fun q => (hx q).le
  have hy : ∀ q, 0 < y q := by
    intro q
    apply Finset.sum_pos'
    · intro n hn
      exact (system (k + 1)).operator_iterate_nonneg w hwt.le hret hadv
        x hx0 n q
    · refine ⟨0, ?_, ?_⟩
      · simp [D]
      · change 0 < x q
        exact hx q
  obtain ⟨mu, hlamMu, hmu2, hstrictMu⟩ :=
    (system (k + 1)).exists_larger_parameter_of_strict
      hlamPos hlam2 y (by simpa only [w] using hstrict)
  letI : Nonempty (system (k + 1)).State :=
    ⟨(0 : State (k + 1))⟩
  obtain ⟨z, hz⟩ := (system (k + 1)).feasible_of_positive_strict
    (klWeights mu) y hy hstrictMu
  exact ⟨mu, hlamMu, hmu2, ⟨z, hz⟩⟩

/-- Every exact feasible certificate below the endpoint can be improved at
the next residue level. -/
theorem levelFeasible_succ_strict
    (k : ℕ) (hk : 2 ≤ k) (lam : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam < 2)
    (hfeas : LevelFeasible k lam) :
    ∃ mu : ℝ, lam < mu ∧ mu < 2 ∧ LevelFeasible (k + 1) mu := by
  obtain ⟨c, hc⟩ := hfeas
  apply levelFeasible_succ_strict_of_positive_subeigen
    k hk lam hlam1 hlam2 c
  · intro q
    exact lt_of_lt_of_le (by norm_num) (hc.1 q)
  · exact hc.2

/-- Starting from any exact feasible parameter strictly between `1` and `2`,
one can choose an infinite strictly increasing ladder of exact feasible
parameters, one at each successive residue level.  The theorem does not say
that the ladder tends to `2`; its increasing limit may be smaller. -/
theorem exists_strict_feasible_ladder
    (k0 : ℕ) (hk0 : 2 ≤ k0) (lam0 : ℝ)
    (hlam1 : 1 < lam0) (hlam2 : lam0 < 2)
    (hfeas0 : LevelFeasible k0 lam0) :
    ∃ lam : ℕ → ℝ,
      lam 0 = lam0 ∧
      (∀ n, LevelFeasible (k0 + n) (lam n)) ∧
      (∀ n, lam n < lam (n + 1)) ∧
      ∀ n, lam n < 2 := by
  let Good (n : ℕ) := {lam : ℝ //
    LevelFeasible (k0 + n) lam ∧ 1 < lam ∧ lam < 2}
  let start : Good 0 := ⟨lam0, by simpa using ⟨hfeas0, hlam1, hlam2⟩⟩
  have himprove : ∀ n (g : Good n),
      ∃ h : Good (n + 1), g.val < h.val := by
    intro n g
    obtain ⟨mu, hlt, hmu2, hmuFeas⟩ :=
      levelFeasible_succ_strict (k0 + n) (by omega) g.val
        g.property.2.1 g.property.2.2 g.property.1
    let h : Good (n + 1) :=
      ⟨mu, by
        refine ⟨?_, lt_trans g.property.2.1 hlt, hmu2⟩
        simpa [add_assoc] using hmuFeas⟩
    exact ⟨h, hlt⟩
  let next : ∀ n, Good n → Good (n + 1) :=
    fun n g => Classical.choose (himprove n g)
  let seqGood : ∀ n, Good n :=
    fun n => Nat.rec start (fun m g => next m g) n
  refine ⟨fun n => (seqGood n).val, ?_, ?_, ?_, ?_⟩
  · simp [seqGood, start]
  · intro n
    exact (seqGood n).property.1
  · intro n
    have hnext := Classical.choose_spec (himprove n (seqGood n))
    change (seqGood n).val < (seqGood (n + 1)).val
    rw [show seqGood (n + 1) = next n (seqGood n) by
      simp only [seqGood]]
    exact hnext
  · intro n
    exact (seqGood n).property.2.2

/-- Fixed-vector specialization retained as a convenient public interface. -/
theorem levelFeasible_succ_strict_of_positive_fixed
    (k : ℕ) (hk : 2 ≤ k) (lam : ℝ)
    (hlam1 : 1 < lam) (hlam2 : lam < 2)
    (c : State k → ℝ) (hc : ∀ q, 0 < c q)
    (hfixed : ∀ q, c q = (system k).operator (klWeights lam) c q) :
    ∃ mu : ℝ, lam < mu ∧ mu < 2 ∧ LevelFeasible (k + 1) mu := by
  apply levelFeasible_succ_strict_of_positive_subeigen
    k hk lam hlam1 hlam2 c hc
  intro q
  exact (hfixed q).le

/-- Exact effect on the feasibility suprema, conditional on attainment by a
positive fixed vector.  The attainment premise remains a separate nonlinear
Perron obligation. -/
theorem criticalLambda_lt_succ_of_positive_fixed
    (k : ℕ) (hk : 2 ≤ k)
    (hcrit1 : 1 < criticalLambda k)
    (hcrit2 : criticalLambda k < 2)
    (c : State k → ℝ) (hc : ∀ q, 0 < c q)
    (hfixed : ∀ q, c q =
      (system k).operator (klWeights (criticalLambda k)) c q) :
    criticalLambda k < criticalLambda (k + 1) := by
  obtain ⟨mu, hlt, hmu2, hfeas⟩ :=
    levelFeasible_succ_strict_of_positive_fixed k hk (criticalLambda k)
      hcrit1 hcrit2 c hc hfixed
  have hmuMem : mu ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨le_trans hcrit1.le hlt.le, hmu2.le⟩
  have hmuCrit : mu ≤ criticalLambda (k + 1) := by
    apply le_csSup (criticalSet_bddAbove (k + 1))
    exact ⟨hmuMem, hfeas⟩
  exact hlt.trans_le hmuCrit

end

end ResidueSystem

end CleanLean.KL

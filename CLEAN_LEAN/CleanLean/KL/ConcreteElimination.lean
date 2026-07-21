/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.EliminationTree
import CleanLean.KL.KLWeights
import CleanLean.KL.ResidueSystem

/-!
# The concrete KL split tree

This file instantiates the labelled elimination-tree framework with the three
Krasikov--Lagarias difference rules.  A split always creates the retarded
transport child at shift `beta-2`; on residue branches 2 and 8 modulo 9 it
also creates the three-lift minimum at shift `beta+alpha-2` or
`beta+alpha-1` respectively.

The definitions are independent of an elimination order.  They establish the
local-validity and erasure interfaces needed by a later recursive algorithm.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree

/-- A binary representation of a three-way minimum. -/
def inf3 {ι : Type} (a b c : EliminationTree ι) : EliminationTree ι :=
  .inf a (.inf b c)

/-- The branch minimum over the three fine lifts of the refinement target. -/
def branchMinimum (k : ℕ) (label : PrincipalLabel (ResidueSystem.State k))
    (delta : ℝ) : EliminationTree (ResidueSystem.State k) :=
  inf3
    (.leaf ⟨(ResidueSystem.system k).fiber
      ((ResidueSystem.system k).refinementTarget label.state) 0,
        label.shift + delta⟩)
    (.leaf ⟨(ResidueSystem.system k).fiber
      ((ResidueSystem.system k).refinementTarget label.state) 1,
        label.shift + delta⟩)
    (.leaf ⟨(ResidueSystem.system k).fiber
      ((ResidueSystem.system k).refinementTarget label.state) 2,
        label.shift + delta⟩)

/-- The body attached when one principal KL leaf is split. -/
noncomputable def splitBody (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k)) :
    EliminationTree (ResidueSystem.State k) :=
  let transport : EliminationTree (ResidueSystem.State k) :=
    .leaf ⟨(ResidueSystem.system k).transport label.state, label.shift - 2⟩
  match (ResidueSystem.system k).branch label.state with
  | .retarded => .add transport (branchMinimum k label (alpha - 2))
  | .neutral => transport
  | .advanced => .add transport (branchMinimum k label (alpha - 1))

/-- Split an unsplit principal leaf while retaining its internal label. -/
noncomputable def splitTree (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k)) :
    EliminationTree (ResidueSystem.State k) :=
  .principal label (splitBody k label)

/-- The original unshifted right-hand side for one state. -/
noncomputable def baseBody (k : ℕ) (state : ResidueSystem.State k) :
    EliminationTree (ResidueSystem.State k) :=
  splitBody k ⟨state, 0⟩

/-- A family of functions satisfies the original concrete KL difference
system at all arguments at least two. -/
def SatisfiesBaseSystem (k : ℕ) (φ : ResidueSystem.State k → ℝ → ℝ) : Prop :=
  ∀ state z, 2 ≤ z → (baseBody k state).eval φ z ≤ φ state z

@[simp] theorem eval_inf3 {ι : Type} (a b c : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    (inf3 a b c).eval φ y = min (a.eval φ y) (min (b.eval φ y) (c.eval φ y)) :=
  rfl

/-- Splitting commutes exactly with translating the common root argument. -/
theorem eval_splitBody_eq_base (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k))
    (φ : ResidueSystem.State k → ℝ → ℝ) (y : ℝ) :
    (splitBody k label).eval φ y =
      (baseBody k label.state).eval φ (y + label.shift) := by
  generalize hb : (ResidueSystem.system k).branch label.state = branch
  cases branch <;>
    simp [splitBody, baseBody, branchMinimum, inf3, hb,
      EliminationTree.eval, PrincipalLabel.value] <;>
    congr 1 <;> ring_nf

/-- The attached split body itself has no internal principal inequalities, so
it is locally valid independently of the functions. -/
theorem splitBody_locallyValid (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k))
    (φ : ResidueSystem.State k → ℝ → ℝ) (y : ℝ) :
    (splitBody k label).LocallyValid φ y := by
  unfold splitBody branchMinimum inf3
  split <;> simp [EliminationTree.LocallyValid]

/-- Splitting an advanced term never creates a shift below `-2`. -/
theorem splitBody_leaf_shifts_ge_neg_two (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k))
    (hshift : 0 ≤ label.shift) :
    (splitBody k label).AllLeaves (fun child => -2 ≤ child.shift) := by
  have htransport : -2 ≤ label.shift - 2 := by linarith
  have hretarded : -2 ≤ label.shift + (alpha - 2) := by
    linarith [one_lt_alpha]
  have hadvanced : -2 ≤ label.shift + (alpha - 1) := by
    linarith [one_lt_alpha]
  generalize hb : (ResidueSystem.system k).branch label.state = branch
  cases branch <;>
    simp [splitBody, branchMinimum, inf3, hb, EliminationTree.AllLeaves,
      htransport, hretarded, hadvanced]

/-- Every permitted split (`y+beta >= 2`) is a valid labelled principal
inequality whenever the original KL system holds. -/
theorem splitTree_locallyValid (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k))
    (φ : ResidueSystem.State k → ℝ → ℝ) (y : ℝ)
    (hbase : SatisfiesBaseSystem k φ) (htime : 2 ≤ y + label.shift) :
    (splitTree k label).LocallyValid φ y := by
  constructor
  · rw [eval_splitBody_eq_base]
    exact hbase label.state (y + label.shift) htime
  · exact splitBody_locallyValid k label φ y

/-- One concrete splitting step decreases the functional right-hand side
inside every labelled tree context. -/
theorem eval_split_in_context_le_leaf
    (K : EliminationTree.Context (ResidueSystem.State k))
    (label : PrincipalLabel (ResidueSystem.State k))
    (φ : ResidueSystem.State k → ℝ → ℝ) (y : ℝ)
    (hbase : SatisfiesBaseSystem k φ) (htime : 2 ≤ y + label.shift) :
    (K.fill (splitTree k label)).eval φ y ≤
      (K.fill (.leaf label)).eval φ y := by
  apply K.eval_fill_mono
  exact (splitTree_locallyValid k label φ y hbase htime).1

/-- Forget internal principal labels and translate paper shifts `beta` into
positive backward lags `-beta` for the final retarded comparison tree. -/
def eraseToRetarded : EliminationTree ι → RetardedExpr ι
  | .leaf label => .leaf label.state (-label.shift)
  | .principal _ body => eraseToRetarded body
  | .add left right => .add (eraseToRetarded left) (eraseToRetarded right)
  | .inf left right => .inf (eraseToRetarded left) (eraseToRetarded right)

/-- Every finite fully-retarded tree whose shifts stay above `-2` has a
strictly positive common lag lower bound and maximum lag at most two. -/
theorem exists_lag_bounds_of_allLeaves
    (tree : EliminationTree ι)
    (hretarded : tree.AllLeaves (fun label => label.shift < 0))
    (hlower : tree.AllLeaves (fun label => -2 ≤ label.shift)) :
    ∃ mu : ℝ, 0 < mu ∧ (eraseToRetarded tree).LagsIn mu 2 := by
  induction tree with
  | leaf label =>
      simp only [EliminationTree.AllLeaves] at hretarded hlower
      refine ⟨-label.shift, by linarith, ?_⟩
      exact ⟨le_rfl, by linarith⟩
  | principal label body ih =>
      exact ih hretarded hlower
  | add left right ihLeft ihRight =>
      obtain ⟨muLeft, hmuLeft, hlagsLeft⟩ := ihLeft hretarded.1 hlower.1
      obtain ⟨muRight, hmuRight, hlagsRight⟩ := ihRight hretarded.2 hlower.2
      refine ⟨min muLeft muRight, lt_min hmuLeft hmuRight, ?_⟩
      exact ⟨hlagsLeft.mono_lower (min_le_left _ _),
        hlagsRight.mono_lower (min_le_right _ _)⟩
  | inf left right ihLeft ihRight =>
      obtain ⟨muLeft, hmuLeft, hlagsLeft⟩ := ihLeft hretarded.1 hlower.1
      obtain ⟨muRight, hmuRight, hlagsRight⟩ := ihRight hretarded.2 hlower.2
      refine ⟨min muLeft muRight, lt_min hmuLeft hmuRight, ?_⟩
      exact ⟨hlagsLeft.mono_lower (min_le_left _ _),
        hlagsRight.mono_lower (min_le_right _ _)⟩

/-- Erasure preserves the expanded functional value exactly. -/
@[simp] theorem eval_eraseToRetarded (tree : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    (eraseToRetarded tree).eval φ y = tree.eval φ y := by
  induction tree with
  | leaf label =>
      simp [eraseToRetarded, RetardedExpr.eval, EliminationTree.eval,
        PrincipalLabel.value]
  | principal label body ih =>
      simpa [eraseToRetarded, EliminationTree.eval] using ih
  | add left right ihLeft ihRight =>
      simp [eraseToRetarded, RetardedExpr.eval, EliminationTree.eval,
        ihLeft, ihRight]
  | inf left right ihLeft ihRight =>
      simp [eraseToRetarded, RetardedExpr.eval, EliminationTree.eval,
        ihLeft, ihRight]

/-- Syntactically, a split at shift `beta` is the unshifted base rule with
`-beta` added to all backward lags. -/
theorem erase_splitBody_eq_shiftLags (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k)) :
    eraseToRetarded (splitBody k label) =
      (eraseToRetarded (baseBody k label.state)).shiftLags (-label.shift) := by
  generalize hb : (ResidueSystem.system k).branch label.state = branch
  cases branch <;>
    simp [splitBody, baseBody, branchMinimum, inf3, hb, eraseToRetarded,
      RetardedExpr.shiftLags] <;>
    congr 1 <;> ring_nf <;> simp

/-- Coefficient evaluation therefore acquires the expected common factor
`lambda^beta`. -/
theorem coeffEval_splitBody_eq_base (k : ℕ)
    (label : PrincipalLabel (ResidueSystem.State k))
    (c : ResidueSystem.State k → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (eraseToRetarded (splitBody k label)).coeffEval c lam =
      lam ^ label.shift *
        (eraseToRetarded (baseBody k label.state)).coeffEval c lam := by
  rw [erase_splitBody_eq_shiftLags,
    RetardedExpr.coeffEval_shiftLags _ c hlam]
  congr 1
  ring_nf

/-- On one original KL row, exponential coefficient evaluation of the
labelled split is exactly the concrete nonlinear KL operator.  This pins the
orientation and the three irrational exponents at the tree interface. -/
theorem coeffEval_baseBody_eq_operator (k : ℕ)
    (state : ResidueSystem.State k) (c : ResidueSystem.State k → ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    (eraseToRetarded (baseBody k state)).coeffEval c lam =
      (ResidueSystem.system k).operator (klWeights lam) c state := by
  have hret : 0 ≤ lam ^ (alpha - 2) := Real.rpow_nonneg hlam.le _
  have hadv : 0 ≤ lam ^ (alpha - 1) := Real.rpow_nonneg hlam.le _
  generalize hb : (ResidueSystem.system k).branch state = branch
  cases branch <;>
    simp [baseBody, splitBody, branchMinimum, inf3, hb, eraseToRetarded,
      RetardedExpr.coeffEval, FiniteSystem.operator, FiniteSystem.fiberMin,
      klWeights, hret, hadv, ← min_mul_of_nonneg] <;>
    ring

/-- Exact KL feasibility makes every concrete splitting step monotone in the
LP direction: the old leaf coefficient is no larger than the expanded split
coefficient, at every real shift. -/
theorem leaf_coeff_le_splitTree
    (k : ℕ) (label : PrincipalLabel (ResidueSystem.State k))
    (c : ResidueSystem.State k → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c) :
    (eraseToRetarded (.leaf label)).coeffEval c lam ≤
      (eraseToRetarded (splitTree k label)).coeffEval c lam := by
  rw [show eraseToRetarded (splitTree k label) =
      eraseToRetarded (splitBody k label) by rfl,
    coeffEval_splitBody_eq_base k label c hlam,
    coeffEval_baseBody_eq_operator k label.state c hlam]
  simp only [eraseToRetarded, RetardedExpr.coeffEval]
  have hfactor : 0 ≤ lam ^ label.shift := Real.rpow_nonneg hlam.le _
  have hrow := mul_le_mul_of_nonneg_left (hfeasible.2 label.state) hfactor
  simpa [mul_comm, mul_left_comm, mul_assoc] using hrow

/-- Coefficient evaluation after erasure is monotone in a labelled context
hole. -/
theorem coeffEval_erase_fill_mono
    (K : EliminationTree.Context ι) (a b : EliminationTree ι)
    (c : ι → ℝ) (lam : ℝ)
    (h : (eraseToRetarded a).coeffEval c lam ≤
      (eraseToRetarded b).coeffEval c lam) :
    (eraseToRetarded (K.fill a)).coeffEval c lam ≤
      (eraseToRetarded (K.fill b)).coeffEval c lam := by
  induction K with
  | hole => exact h
  | principal label K ih => simpa [EliminationTree.Context.fill, eraseToRetarded] using ih
  | addLeft K right ih =>
      simpa [EliminationTree.Context.fill, eraseToRetarded, RetardedExpr.coeffEval] using
        add_le_add_right ih ((eraseToRetarded right).coeffEval c lam)
  | addRight left K ih =>
      simpa [EliminationTree.Context.fill, eraseToRetarded, RetardedExpr.coeffEval] using
        add_le_add_left ih ((eraseToRetarded left).coeffEval c lam)
  | infLeft K right ih =>
      simpa [EliminationTree.Context.fill, eraseToRetarded, RetardedExpr.coeffEval] using
        min_le_min ih (le_refl ((eraseToRetarded right).coeffEval c lam))
  | infRight left K ih =>
      simpa [EliminationTree.Context.fill, eraseToRetarded, RetardedExpr.coeffEval] using
        min_le_min (le_refl ((eraseToRetarded left).coeffEval c lam)) ih

/-- Thus exact KL feasibility makes a concrete split increase the coefficient
right-hand side inside every surrounding labelled context. -/
theorem coeff_leaf_le_split_in_context
    (K : EliminationTree.Context (ResidueSystem.State k))
    (label : PrincipalLabel (ResidueSystem.State k))
    (c : ResidueSystem.State k → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfeasible : (ResidueSystem.system k).Feasible (klWeights lam) c) :
    (eraseToRetarded (K.fill (.leaf label))).coeffEval c lam ≤
      (eraseToRetarded (K.fill (splitTree k label))).coeffEval c lam := by
  apply coeffEval_erase_fill_mono
  exact leaf_coeff_le_splitTree k label c hlam hfeasible

end ConcreteElimination

end CleanLean.KL

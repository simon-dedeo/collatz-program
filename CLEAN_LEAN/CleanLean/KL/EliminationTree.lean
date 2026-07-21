/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.CriticalAssignment

/-!
# Labelled trees for KL advanced-term elimination

`RetardedExpr` is the right representation for the final comparison theorem,
but it intentionally forgets internal principal vertices.  KL's deletion rule
needs those vertices: it compares a newly created leaf `(m,beta)` with an
earlier principal vertex having the same residue and smaller shift.

This file introduces the labelled tree needed for that proof.  A principal
vertex is either a leaf or stores the body attached when it was split.  Sums
retain both children; minima retain one minimizing child in a critical
assignment.  The semantics and critical-assignment theorem are kernel checked
here.  The KL-specific recursive splitter and its termination theorem remain
separate.
-/

namespace CleanLean.KL

/-- A principal KL label denotes `phi_state (y + shift)`. -/
structure PrincipalLabel (ι : Type) where
  state : ι
  shift : ℝ

namespace PrincipalLabel

variable {ι : Type}

/-- Evaluate a principal label at the common root argument `y`. -/
def value (label : PrincipalLabel ι) (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  φ label.state (y + label.shift)

/-- Monotonicity compares repeated labels with the same state. -/
theorem value_le_of_same_state
    (earlier later : PrincipalLabel ι) (φ : ι → ℝ → ℝ) (y : ℝ)
    (hstate : earlier.state = later.state)
    (hshift : earlier.shift ≤ later.shift)
    (hmono : Monotone (φ earlier.state)) :
    earlier.value φ y ≤ later.value φ y := by
  rw [value, value, ← hstate]
  exact hmono (by linarith)

end PrincipalLabel

/-- A labelled elimination tree.  `leaf label` is an unsplit principal
vertex; `principal label body` retains the internal principal vertex created
by splitting that leaf. -/
inductive EliminationTree (ι : Type) where
  | leaf (label : PrincipalLabel ι)
  | principal (label : PrincipalLabel ι) (body : EliminationTree ι)
  | add (left right : EliminationTree ι)
  | inf (left right : EliminationTree ι)

namespace EliminationTree

variable {ι : Type}

/-- Expanded right-hand-side evaluation.  An unsplit principal vertex is a
function leaf; a split principal vertex evaluates its attached body. -/
def eval (tree : EliminationTree ι) (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  match tree with
  | .leaf label => label.value φ y
  | .principal _ body => body.eval φ y
  | .add left right => left.eval φ y + right.eval φ y
  | .inf left right => min (left.eval φ y) (right.eval φ y)

/-- Every attached split is a valid local difference inequality at this
evaluation point.  Deletion need not preserve this strong property, which is
why KL maintain the weaker assignment-specific invariant below. -/
def LocallyValid (tree : EliminationTree ι) (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  match tree with
  | .leaf _ => True
  | .principal label body =>
      body.eval φ y ≤ label.value φ y ∧ body.LocallyValid φ y
  | .add left right => left.LocallyValid φ y ∧ right.LocallyValid φ y
  | .inf left right => left.LocallyValid φ y ∧ right.LocallyValid φ y

/-- A predicate holds at every unsplit principal leaf. -/
def AllLeaves (tree : EliminationTree ι) (P : PrincipalLabel ι → Prop) : Prop :=
  match tree with
  | .leaf label => P label
  | .principal _ body => body.AllLeaves P
  | .add left right => left.AllLeaves P ∧ right.AllLeaves P
  | .inf left right => left.AllLeaves P ∧ right.AllLeaves P

/-- Pointwise strengthening transports through the finite leaf predicate. -/
theorem allLeaves_mono {tree : EliminationTree ι}
    {P Q : PrincipalLabel ι → Prop}
    (h : tree.AllLeaves P) (hPQ : ∀ label, P label → Q label) :
    tree.AllLeaves Q := by
  induction tree with
  | leaf label => exact hPQ label h
  | principal label body ih => exact ih h
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | inf left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩

/-- A uniform lower shift bound `-nu` makes every leaf argument nonnegative
when the common root argument is at least `nu`. -/
theorem allLeaves_nonnegative_arguments_of_shift_lower_bound
    {tree : EliminationTree ι} (y nu : ℝ)
    (hshifts : tree.AllLeaves fun label => -nu ≤ label.shift)
    (hy : nu ≤ y) :
    tree.AllLeaves fun label => 0 ≤ y + label.shift := by
  exact allLeaves_mono hshifts fun _ hshift => by linarith

/-- A one-hole context for a labelled elimination tree. -/
inductive Context (ι : Type) where
  | hole
  | principal (label : PrincipalLabel ι) (ctx : Context ι)
  | addLeft (ctx : Context ι) (right : EliminationTree ι)
  | addRight (left : EliminationTree ι) (ctx : Context ι)
  | infLeft (ctx : Context ι) (right : EliminationTree ι)
  | infRight (left : EliminationTree ι) (ctx : Context ι)

namespace Context

/-- Fill the unique context hole. -/
def fill (K : Context ι) (tree : EliminationTree ι) : EliminationTree ι :=
  match K with
  | .hole => tree
  | .principal label K => .principal label (K.fill tree)
  | .addLeft K right => .add (K.fill tree) right
  | .addRight left K => .add left (K.fill tree)
  | .infLeft K right => .inf (K.fill tree) right
  | .infRight left K => .inf left (K.fill tree)

/-- Expanded evaluation is monotone in the context hole. -/
theorem eval_fill_mono (K : Context ι) (a b : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) (h : a.eval φ y ≤ b.eval φ y) :
    (K.fill a).eval φ y ≤ (K.fill b).eval φ y := by
  induction K with
  | hole => exact h
  | principal label K ih => simpa [fill, eval] using ih
  | addLeft K right ih =>
      simpa [fill, eval] using add_le_add_right ih (right.eval φ y)
  | addRight left K ih =>
      simpa [fill, eval] using add_le_add_left ih (left.eval φ y)
  | infLeft K right ih =>
      simpa [fill, eval] using min_le_min ih (le_refl (right.eval φ y))
  | infRight left K ih =>
      simpa [fill, eval] using min_le_min (le_refl (left.eval φ y)) ih

/-- Replacing a context hole by a locally valid tree of no larger evaluation
preserves local validity of the whole filled tree.  At an enclosing principal
node, the replacement only strengthens its numerical body inequality. -/
theorem locallyValid_fill_replace (K : Context ι) (old new : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hold : (K.fill old).LocallyValid φ y)
    (hnew : new.LocallyValid φ y)
    (heval : new.eval φ y ≤ old.eval φ y) :
    (K.fill new).LocallyValid φ y := by
  induction K with
  | hole => exact hnew
  | principal label K ih =>
      constructor
      · exact (K.eval_fill_mono new old φ y heval).trans hold.1
      · exact ih hold.2
  | addLeft K right ih => exact ⟨ih hold.1, hold.2⟩
  | addRight left K ih => exact ⟨hold.1, ih hold.2⟩
  | infLeft K right ih => exact ⟨ih hold.1, hold.2⟩
  | infRight left K ih => exact ⟨hold.1, ih hold.2⟩

end Context

/-- A syntactic assignment through a labelled tree. -/
inductive Assignment : (tree : EliminationTree ι) → Type
  | principalLeaf (label : PrincipalLabel ι) :
      Assignment (.leaf label)
  | principalNode {label : PrincipalLabel ι} {body : EliminationTree ι} :
      Assignment body → Assignment (.principal label body)
  | add {left right : EliminationTree ι} :
      Assignment left → Assignment right → Assignment (.add left right)
  | infLeft {left right : EliminationTree ι} :
      Assignment left → Assignment (.inf left right)
  | infRight {left right : EliminationTree ι} :
      Assignment right → Assignment (.inf left right)

namespace Assignment

/-- Sum the values of all selected leaves. -/
def selectedEval {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ) : ℝ :=
  match A with
  | .principalLeaf label => label.value φ y
  | .principalNode child => child.selectedEval φ y
  | .add left right => left.selectedEval φ y + right.selectedEval φ y
  | .infLeft left => left.selectedEval φ y
  | .infRight right => right.selectedEval φ y

/-- Root-to-leaf principal-label paths retained by the assignment.  Internal
principal labels are prepended, so ancestry survives expansion. -/
def selectedPaths {tree : EliminationTree ι} (A : Assignment tree) :
    List (List (PrincipalLabel ι)) :=
  match A with
  | .principalLeaf label => [[label]]
  | @principalNode _ label _ child =>
      child.selectedPaths.map fun path => label :: path
  | .add left right => left.selectedPaths ++ right.selectedPaths
  | .infLeft left => left.selectedPaths
  | .infRight right => right.selectedPaths

/-- A target leaf occurs after an ancestor label on some selected path. -/
def SelectsLeafAfter {tree : EliminationTree ι} (A : Assignment tree)
    (ancestor target : PrincipalLabel ι) : Prop :=
  ∃ pre middle,
    pre ++ ancestor :: middle ++ [target] ∈ A.selectedPaths

/-- The assignment is critical when each chosen minimum child attains the
minimum. -/
def IsCritical {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  match A with
  | .principalLeaf _ => True
  | .principalNode child => child.IsCritical φ y
  | .add left right => left.IsCritical φ y ∧ right.IsCritical φ y
  | @infLeft _ left right child =>
      left.eval φ y ≤ right.eval φ y ∧ child.IsCritical φ y
  | @infRight _ left right child =>
      right.eval φ y ≤ left.eval φ y ∧ child.IsCritical φ y

/-- KL's invariant (3.4), specialized to one assignment: at every internal
principal vertex on a selected path, its label value bounds the selected-leaf
sum below it. -/
def RespectsPrincipalBounds {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ) : Prop :=
  match A with
  | .principalLeaf _ => True
  | @principalNode _ label _ child =>
      child.selectedEval φ y ≤ label.value φ y ∧
        child.RespectsPrincipalBounds φ y
  | .add left right =>
      left.RespectsPrincipalBounds φ y ∧ right.RespectsPrincipalBounds φ y
  | .infLeft left => left.RespectsPrincipalBounds φ y
  | .infRight right => right.RespectsPrincipalBounds φ y

/-- One selected assignment occurs below another.  At a sum either child may
contain it (the other child is still selected); at a minimum it can occur only
inside the chosen child.  This is the formal critical-path relation needed to
transport the positive sibling contribution upward. -/
inductive SelectedSubassignment :
    {small big : EliminationTree ι} → Assignment small → Assignment big → Prop
  | refl {tree : EliminationTree ι} (A : Assignment tree) :
      SelectedSubassignment A A
  | principal {small body : EliminationTree ι} {label : PrincipalLabel ι}
      {smallA : Assignment small} {bodyA : Assignment body} :
      SelectedSubassignment smallA bodyA →
        SelectedSubassignment smallA (.principalNode (label := label) bodyA)
  | addLeft {small left right : EliminationTree ι}
      {smallA : Assignment small} {leftA : Assignment left}
      (h : SelectedSubassignment smallA leftA) (rightA : Assignment right) :
      SelectedSubassignment smallA (.add leftA rightA)
  | addRight {small left right : EliminationTree ι}
      {smallA : Assignment small} (leftA : Assignment left)
      {rightA : Assignment right} (h : SelectedSubassignment smallA rightA) :
      SelectedSubassignment smallA (.add leftA rightA)
  | infLeft {small left right : EliminationTree ι}
      {smallA : Assignment small} {leftA : Assignment left}
      (h : SelectedSubassignment smallA leftA) :
      SelectedSubassignment smallA (.infLeft (right := right) leftA)
  | infRight {small left right : EliminationTree ι}
      {smallA : Assignment small} {rightA : Assignment right}
      (h : SelectedSubassignment smallA rightA) :
      SelectedSubassignment smallA (.infRight (left := left) rightA)

/-- Every finite labelled tree has a critical assignment. -/
theorem exists_isCritical (tree : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    ∃ A : Assignment tree, A.IsCritical φ y := by
  induction tree with
  | leaf label => exact ⟨.principalLeaf label, trivial⟩
  | principal label body ih =>
      obtain ⟨A, hA⟩ := ih
      exact ⟨.principalNode A, hA⟩
  | add left right ihLeft ihRight =>
      obtain ⟨a, ha⟩ := ihLeft
      obtain ⟨b, hb⟩ := ihRight
      exact ⟨.add a b, ha, hb⟩
  | inf left right ihLeft ihRight =>
      rcases le_total (left.eval φ y) (right.eval φ y) with h | h
      · obtain ⟨a, ha⟩ := ihLeft
        exact ⟨.infLeft a, h, ha⟩
      · obtain ⟨b, hb⟩ := ihRight
        exact ⟨.infRight b, h, hb⟩

/-- A critical assignment evaluates to exactly the expanded tree value. -/
theorem selectedEval_eq_eval {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ) (hA : A.IsCritical φ y) :
    A.selectedEval φ y = tree.eval φ y := by
  induction A with
  | principalLeaf label => rfl
  | principalNode child ih =>
      simpa [selectedEval, eval] using ih hA
  | add left right ihLeft ihRight =>
      exact congrArg₂ (· + ·) (ihLeft hA.1) (ihRight hA.2)
  | @infLeft left right child ih =>
      rw [selectedEval, eval, ih hA.2, min_eq_left hA.1]
  | @infRight left right child ih =>
      rw [selectedEval, eval, ih hA.2, min_eq_right hA.1]

/-- Strict positivity of every function value makes every selected leaf sum
strictly positive. -/
theorem selectedEval_pos {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ) (hφ : ∀ i t, 0 < φ i t) :
    0 < A.selectedEval φ y := by
  induction A with
  | principalLeaf label => exact hφ label.state (y + label.shift)
  | principalNode child ih => exact ih
  | add left right ihLeft ihRight => exact add_pos ihLeft ihRight
  | infLeft left ih => exact ih
  | infRight right ih => exact ih

/-- The positivity lemma in the form needed by the retarded comparison
theorem.  Function values are assumed positive only at nonnegative arguments,
and the tree records that every selected leaf is evaluated there. -/
theorem selectedEval_pos_of_nonnegative_arguments
    {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hargs : tree.AllLeaves fun label => 0 ≤ y + label.shift)
    (hφ : ∀ i t, 0 ≤ t → 0 < φ i t) :
    0 < A.selectedEval φ y := by
  induction A with
  | principalLeaf label => exact hφ label.state (y + label.shift) hargs
  | principalNode child ih => exact ih hargs
  | add left right ihLeft ihRight =>
      exact add_pos (ihLeft hargs.1) (ihRight hargs.2)
  | infLeft left ih => exact ih hargs.1
  | infRight right ih => exact ih hargs.2

/-- A decomposition into one target leaf plus a positive remainder propagates
from a selected subassignment to the whole assignment.  Crossing a sum only
adds another strictly positive selected subtree. -/
theorem decomp_of_selectedSubassignment
    {small big : EliminationTree ι}
    {smallA : Assignment small} {bigA : Assignment big}
    (hsub : SelectedSubassignment smallA bigA)
    (φ : ι → ℝ → ℝ) (y targetValue extra : ℝ)
    (hφ : ∀ i t, 0 < φ i t)
    (hdecomp : smallA.selectedEval φ y = targetValue + extra)
    (hextra : 0 < extra) :
    ∃ extra', bigA.selectedEval φ y = targetValue + extra' ∧ 0 < extra' := by
  induction hsub with
  | refl A => exact ⟨extra, hdecomp, hextra⟩
  | principal h ih => simpa [selectedEval] using ih hdecomp
  | addLeft h rightA ih =>
      obtain ⟨extra', heq, hpos⟩ := ih hdecomp
      refine ⟨extra' + rightA.selectedEval φ y, ?_,
        add_pos hpos (selectedEval_pos rightA φ y hφ)⟩
      simp only [selectedEval, heq]
      ring
  | addRight leftA h ih =>
      obtain ⟨extra', heq, hpos⟩ := ih hdecomp
      refine ⟨extra' + leftA.selectedEval φ y, ?_,
        add_pos hpos (selectedEval_pos leftA φ y hφ)⟩
      simp only [selectedEval, heq]
      ring
  | infLeft h ih => simpa [selectedEval] using ih hdecomp
  | infRight h ih => simpa [selectedEval] using ih hdecomp

/-- Localized-positivity version of `decomp_of_selectedSubassignment`.  This
is the form used after Phase A of elimination, where every remaining leaf has
shift at least `-2` and the comparison is evaluated at `y ≥ 2`. -/
theorem decomp_of_selectedSubassignment_of_nonnegative_arguments
    {small big : EliminationTree ι}
    {smallA : Assignment small} {bigA : Assignment big}
    (hsub : SelectedSubassignment smallA bigA)
    (φ : ι → ℝ → ℝ) (y targetValue extra : ℝ)
    (hargs : big.AllLeaves fun label => 0 ≤ y + label.shift)
    (hφ : ∀ i t, 0 ≤ t → 0 < φ i t)
    (hdecomp : smallA.selectedEval φ y = targetValue + extra)
    (hextra : 0 < extra) :
    ∃ extra', bigA.selectedEval φ y = targetValue + extra' ∧ 0 < extra' := by
  induction hsub with
  | refl A => exact ⟨extra, hdecomp, hextra⟩
  | principal h ih => simpa [selectedEval] using ih hargs hdecomp
  | addLeft h rightA ih =>
      obtain ⟨extra', heq, hpos⟩ := ih hargs.1 hdecomp
      refine ⟨extra' + rightA.selectedEval φ y, ?_,
        add_pos hpos
          (selectedEval_pos_of_nonnegative_arguments rightA φ y hargs.2 hφ)⟩
      simp only [selectedEval, heq]
      ring
  | addRight leftA h ih =>
      obtain ⟨extra', heq, hpos⟩ := ih hargs.2 hdecomp
      refine ⟨extra' + leftA.selectedEval φ y, ?_,
        add_pos hpos
          (selectedEval_pos_of_nonnegative_arguments leftA φ y hargs.1 hφ)⟩
      simp only [selectedEval, heq]
      ring
  | infLeft h ih => simpa [selectedEval] using ih hargs.1 hdecomp
  | infRight h ih => simpa [selectedEval] using ih hargs.2 hdecomp

/-- At a split body, the transport child is the strictly positive extra term
beside whichever leaf/minimum value the branch assignment selects. -/
theorem add_decomp_from_right
    {transport branch : EliminationTree ι}
    (transportA : Assignment transport) (branchA : Assignment branch)
    (φ : ι → ℝ → ℝ) (y targetValue : ℝ)
    (hφ : ∀ i t, 0 < φ i t)
    (hbranch : branchA.selectedEval φ y = targetValue) :
    (Assignment.add transportA branchA).selectedEval φ y =
        targetValue + transportA.selectedEval φ y ∧
      0 < transportA.selectedEval φ y := by
  constructor
  · simp only [selectedEval, hbranch]
    ring
  · exact selectedEval_pos transportA φ y hφ

/-- Localized-positivity version of `add_decomp_from_right`, allowing the
transport sibling to be an arbitrary recursively expanded subtree. -/
theorem add_decomp_from_right_of_nonnegative_arguments
    {transport branch : EliminationTree ι}
    (transportA : Assignment transport) (branchA : Assignment branch)
    (φ : ι → ℝ → ℝ) (y targetValue : ℝ)
    (htransportArgs : transport.AllLeaves fun label => 0 ≤ y + label.shift)
    (hφ : ∀ i t, 0 ≤ t → 0 < φ i t)
    (hbranch : branchA.selectedEval φ y = targetValue) :
    (Assignment.add transportA branchA).selectedEval φ y =
        targetValue + transportA.selectedEval φ y ∧
      0 < transportA.selectedEval φ y := by
  constructor
  · simp only [selectedEval, hbranch]
    ring
  · exact selectedEval_pos_of_nonnegative_arguments
      transportA φ y htransportArgs hφ

/-- Before any deletion, local validity of every attached split implies KL's
critical-path bound (3.4) for every critical assignment.  The deletion proof
must then show that its particular pruning step preserves this weaker
property even though it can destroy `LocallyValid`. -/
theorem respectsPrincipalBounds_of_locallyValid
    {tree : EliminationTree ι} (A : Assignment tree)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hcritical : A.IsCritical φ y) (hvalid : tree.LocallyValid φ y) :
    A.RespectsPrincipalBounds φ y := by
  induction A with
  | principalLeaf label => trivial
  | @principalNode label body child ih =>
      constructor
      · rw [selectedEval_eq_eval child φ y hcritical]
        exact hvalid.1
      · exact ih hcritical hvalid.2
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft hcritical.1 hvalid.1, ihRight hcritical.2 hvalid.2⟩
  | infLeft left ih => exact ih hcritical.2 hvalid.1
  | infRight right ih => exact ih hcritical.2 hvalid.2

/-- Every selected path contains at least its terminal principal leaf. -/
theorem selectedPaths_ne_nil {tree : EliminationTree ι} (A : Assignment tree) :
    A.selectedPaths ≠ [] := by
  induction A with
  | principalLeaf label => simp [selectedPaths]
  | principalNode child ih => simp [selectedPaths, ih]
  | add left right ihLeft ihRight => simp [selectedPaths, ihLeft]
  | infLeft left ih => simpa [selectedPaths] using ih
  | infRight right ih => simpa [selectedPaths] using ih

/-- Deleting the left side of a minimum can only increase expanded
evaluation, in any surrounding context. -/
theorem eval_delete_left_le
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    (K.fill (.inf left right)).eval φ y ≤ (K.fill right).eval φ y := by
  apply K.eval_fill_mono
  simp only [eval]
  exact min_le_right _ _

/-- Global safe-deletion theorem.  The hypothesis says that no critical
assignment of the *whole surrounding tree* contains an assignment choosing
the left side of this particular minimum.  This is KL's “totally
non-critical” condition, expressed without a local shortcut.

Unlike the false local rule, this remains sound when the minimum lies below
other minima: if the path to the hole is not selected, raising its value
cannot make it newly minimizing. -/
theorem eval_delete_left_of_noCriticalUse
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ bigA : Assignment (K.fill (.inf left right)),
      bigA.IsCritical φ y → ∀ leftA : Assignment left,
        ¬SelectedSubassignment
          (.infLeft (right := right) leftA) bigA) :
    (K.fill (.inf left right)).eval φ y = (K.fill right).eval φ y := by
  induction K with
  | hole =>
      have hnot : ¬left.eval φ y ≤ right.eval φ y := by
        intro hle
        obtain ⟨leftA, hleftA⟩ := exists_isCritical left φ y
        let bigA : Assignment (.inf left right) := .infLeft leftA
        exact (havoid bigA ⟨hle, hleftA⟩ leftA) (.refl bigA)
      simp [Context.fill, eval, min_eq_right (le_of_not_ge hnot)]
  | principal label K ih =>
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ leftA : Assignment left,
            ¬SelectedSubassignment (.infLeft (right := right) leftA) bigA := by
        intro bigA hbig leftA hsub
        exact (havoid (.principalNode bigA) hbig leftA) (.principal hsub)
      simpa [Context.fill, eval] using ih hinner
  | addLeft K sibling ih =>
      obtain ⟨siblingA, hsiblingA⟩ := exists_isCritical sibling φ y
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ leftA : Assignment left,
            ¬SelectedSubassignment (.infLeft (right := right) leftA) bigA := by
        intro bigA hbig leftA hsub
        exact (havoid (.add bigA siblingA) ⟨hbig, hsiblingA⟩ leftA)
          (.addLeft hsub siblingA)
      simpa [Context.fill, eval] using congrArg
        (fun z => z + sibling.eval φ y) (ih hinner)
  | addRight sibling K ih =>
      obtain ⟨siblingA, hsiblingA⟩ := exists_isCritical sibling φ y
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ leftA : Assignment left,
            ¬SelectedSubassignment (.infLeft (right := right) leftA) bigA := by
        intro bigA hbig leftA hsub
        exact (havoid (.add siblingA bigA) ⟨hsiblingA, hbig⟩ leftA)
          (.addRight siblingA hsub)
      simpa [Context.fill, eval] using congrArg
        (fun z => sibling.eval φ y + z) (ih hinner)
  | infLeft K sibling ih =>
      let oldInner := (K.fill (.inf left right)).eval φ y
      let newInner := (K.fill right).eval φ y
      have hmono : oldInner ≤ newInner :=
        eval_delete_left_le K left right φ y
      by_cases hchosen : oldInner ≤ sibling.eval φ y
      · have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
            bigA.IsCritical φ y → ∀ leftA : Assignment left,
              ¬SelectedSubassignment (.infLeft (right := right) leftA) bigA := by
          intro bigA hbig leftA hsub
          exact (havoid (.infLeft bigA) ⟨hchosen, hbig⟩ leftA) (.infLeft hsub)
        have heq := ih hinner
        simpa [Context.fill, eval] using congrArg
          (fun z => min z (sibling.eval φ y)) heq
      · have hold : sibling.eval φ y ≤ oldInner := le_of_not_ge hchosen
        have hnew : sibling.eval φ y ≤ newInner := hold.trans hmono
        simp [Context.fill, eval, oldInner, newInner,
          min_eq_right hold, min_eq_right hnew]
  | infRight sibling K ih =>
      let oldInner := (K.fill (.inf left right)).eval φ y
      let newInner := (K.fill right).eval φ y
      have hmono : oldInner ≤ newInner :=
        eval_delete_left_le K left right φ y
      by_cases hchosen : oldInner ≤ sibling.eval φ y
      · have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
            bigA.IsCritical φ y → ∀ leftA : Assignment left,
              ¬SelectedSubassignment (.infLeft (right := right) leftA) bigA := by
          intro bigA hbig leftA hsub
          exact (havoid (.infRight bigA) ⟨hchosen, hbig⟩ leftA) (.infRight hsub)
        have heq := ih hinner
        simpa [Context.fill, eval] using congrArg
          (fun z => min (sibling.eval φ y) z) heq
      · have hold : sibling.eval φ y ≤ oldInner := le_of_not_ge hchosen
        have hnew : sibling.eval φ y ≤ newInner := hold.trans hmono
        simp [Context.fill, eval, oldInner, newInner,
          min_eq_left hold, min_eq_left hnew]

/-- Symmetric monotonicity for deleting the right side of a minimum. -/
theorem eval_delete_right_le
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ) :
    (K.fill (.inf left right)).eval φ y ≤ (K.fill left).eval φ y := by
  apply K.eval_fill_mono
  simp only [eval]
  exact min_le_left _ _

/-- Symmetric global safe-deletion theorem for a totally non-critical right
alternative. -/
theorem eval_delete_right_of_noCriticalUse
    (K : Context ι) (left right : EliminationTree ι)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (havoid : ∀ bigA : Assignment (K.fill (.inf left right)),
      bigA.IsCritical φ y → ∀ rightA : Assignment right,
        ¬SelectedSubassignment
          (.infRight (left := left) rightA) bigA) :
    (K.fill (.inf left right)).eval φ y = (K.fill left).eval φ y := by
  induction K with
  | hole =>
      have hnot : ¬right.eval φ y ≤ left.eval φ y := by
        intro hle
        obtain ⟨rightA, hrightA⟩ := exists_isCritical right φ y
        let bigA : Assignment (.inf left right) := .infRight rightA
        exact (havoid bigA ⟨hle, hrightA⟩ rightA) (.refl bigA)
      simp [Context.fill, eval, min_eq_left (le_of_not_ge hnot)]
  | principal label K ih =>
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ rightA : Assignment right,
            ¬SelectedSubassignment (.infRight (left := left) rightA) bigA := by
        intro bigA hbig rightA hsub
        exact (havoid (.principalNode bigA) hbig rightA) (.principal hsub)
      simpa [Context.fill, eval] using ih hinner
  | addLeft K sibling ih =>
      obtain ⟨siblingA, hsiblingA⟩ := exists_isCritical sibling φ y
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ rightA : Assignment right,
            ¬SelectedSubassignment (.infRight (left := left) rightA) bigA := by
        intro bigA hbig rightA hsub
        exact (havoid (.add bigA siblingA) ⟨hbig, hsiblingA⟩ rightA)
          (.addLeft hsub siblingA)
      simpa [Context.fill, eval] using congrArg
        (fun z => z + sibling.eval φ y) (ih hinner)
  | addRight sibling K ih =>
      obtain ⟨siblingA, hsiblingA⟩ := exists_isCritical sibling φ y
      have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
          bigA.IsCritical φ y → ∀ rightA : Assignment right,
            ¬SelectedSubassignment (.infRight (left := left) rightA) bigA := by
        intro bigA hbig rightA hsub
        exact (havoid (.add siblingA bigA) ⟨hsiblingA, hbig⟩ rightA)
          (.addRight siblingA hsub)
      simpa [Context.fill, eval] using congrArg
        (fun z => sibling.eval φ y + z) (ih hinner)
  | infLeft K sibling ih =>
      let oldInner := (K.fill (.inf left right)).eval φ y
      let newInner := (K.fill left).eval φ y
      have hmono : oldInner ≤ newInner :=
        eval_delete_right_le K left right φ y
      by_cases hchosen : oldInner ≤ sibling.eval φ y
      · have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
            bigA.IsCritical φ y → ∀ rightA : Assignment right,
              ¬SelectedSubassignment (.infRight (left := left) rightA) bigA := by
          intro bigA hbig rightA hsub
          exact (havoid (.infLeft bigA) ⟨hchosen, hbig⟩ rightA) (.infLeft hsub)
        have heq := ih hinner
        simpa [Context.fill, eval] using congrArg
          (fun z => min z (sibling.eval φ y)) heq
      · have hold : sibling.eval φ y ≤ oldInner := le_of_not_ge hchosen
        have hnew : sibling.eval φ y ≤ newInner := hold.trans hmono
        simp [Context.fill, eval, oldInner, newInner,
          min_eq_right hold, min_eq_right hnew]
  | infRight sibling K ih =>
      let oldInner := (K.fill (.inf left right)).eval φ y
      let newInner := (K.fill left).eval φ y
      have hmono : oldInner ≤ newInner :=
        eval_delete_right_le K left right φ y
      by_cases hchosen : oldInner ≤ sibling.eval φ y
      · have hinner : ∀ bigA : Assignment (K.fill (.inf left right)),
            bigA.IsCritical φ y → ∀ rightA : Assignment right,
              ¬SelectedSubassignment (.infRight (left := left) rightA) bigA := by
          intro bigA hbig rightA hsub
          exact (havoid (.infRight bigA) ⟨hchosen, hbig⟩ rightA) (.infRight hsub)
        have heq := ih hinner
        simpa [Context.fill, eval] using congrArg
          (fun z => min (sibling.eval φ y) z) heq
      · have hold : sibling.eval φ y ≤ oldInner := le_of_not_ge hchosen
        have hnew : sibling.eval φ y ≤ newInner := hold.trans hmono
        simp [Context.fill, eval, oldInner, newInner,
          min_eq_left hold, min_eq_left hnew]

/-- The strict numerical contradiction at the heart of KL's deletion rule.
If an ancestor value bounds a selected sum containing the later repeated leaf
plus a positive contribution, monotonicity in the shift makes this impossible.

The remaining tree theorem must derive `hdecomp` and `hbound` from a selected
path through the newly split sum. -/
theorem repeated_label_contradiction
    (ancestor target : PrincipalLabel ι) (φ : ι → ℝ → ℝ)
    (y selectedSum extra : ℝ)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hbound : selectedSum ≤ ancestor.value φ y)
    (hdecomp : selectedSum = target.value φ y + extra)
    (hextra : 0 < extra) : False := by
  have hlabel : ancestor.value φ y ≤ target.value φ y :=
    PrincipalLabel.value_le_of_same_state ancestor target φ y hstate hshift.le hmono
  linarith

/-- Version of the contradiction that reads the ancestor bound directly from
KL's assignment invariant at a principal vertex. -/
theorem repeated_label_contradiction_of_principal_bound
    {body : EliminationTree ι} (ancestor target : PrincipalLabel ι)
    (child : Assignment body) (φ : ι → ℝ → ℝ)
    (y extra : ℝ)
    (hrespect :
      (Assignment.principalNode (label := ancestor) child).RespectsPrincipalBounds φ y)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hdecomp : child.selectedEval φ y = target.value φ y + extra)
    (hextra : 0 < extra) : False := by
  exact repeated_label_contradiction ancestor target φ y
    (child.selectedEval φ y) extra hstate hshift hmono hrespect.1 hdecomp hextra

/-- Full abstract deletion contradiction.  A split subtree contributes the
later repeated leaf plus something strictly positive; if that split lies on a
selected path below the repeated ancestor, the positive decomposition travels
to the ancestor and contradicts monotonicity. -/
theorem repeated_label_contradiction_of_selected_subassignment
    {ancestorBody localTree : EliminationTree ι}
    (ancestor target : PrincipalLabel ι)
    (ancestorA : Assignment ancestorBody) (localA : Assignment localTree)
    (φ : ι → ℝ → ℝ) (y localExtra : ℝ)
    (hrespect :
      (Assignment.principalNode (label := ancestor) ancestorA).RespectsPrincipalBounds φ y)
    (hsub : SelectedSubassignment localA ancestorA)
    (hφ : ∀ i t, 0 < φ i t)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hlocal : localA.selectedEval φ y = target.value φ y + localExtra)
    (hlocalExtra : 0 < localExtra) : False := by
  obtain ⟨extra, hdecomp, hextra⟩ :=
    decomp_of_selectedSubassignment hsub φ y (target.value φ y) localExtra
      hφ hlocal hlocalExtra
  exact repeated_label_contradiction_of_principal_bound ancestor target ancestorA φ
    y extra hrespect hstate hshift hmono hdecomp hextra

/-- Localized-positivity version of the selected-subassignment
contradiction.  Only the leaf arguments actually present in the enclosing
assignment must be nonnegative. -/
theorem repeated_label_contradiction_of_selected_subassignment_of_nonnegative_arguments
    {ancestorBody localTree : EliminationTree ι}
    (ancestor target : PrincipalLabel ι)
    (ancestorA : Assignment ancestorBody) (localA : Assignment localTree)
    (φ : ι → ℝ → ℝ) (y localExtra : ℝ)
    (hrespect :
      (Assignment.principalNode (label := ancestor) ancestorA).RespectsPrincipalBounds φ y)
    (hsub : SelectedSubassignment localA ancestorA)
    (hargs : ancestorBody.AllLeaves fun label => 0 ≤ y + label.shift)
    (hφ : ∀ i t, 0 ≤ t → 0 < φ i t)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hlocal : localA.selectedEval φ y = target.value φ y + localExtra)
    (hlocalExtra : 0 < localExtra) : False := by
  obtain ⟨extra, hdecomp, hextra⟩ :=
    decomp_of_selectedSubassignment_of_nonnegative_arguments
      hsub φ y (target.value φ y) localExtra hargs hφ hlocal hlocalExtra
  exact repeated_label_contradiction_of_principal_bound ancestor target ancestorA φ
    y extra hrespect hstate hshift hmono hdecomp hextra

/-- KL deletion-rule interface for the actual split shape.  The local split is
an addition of a transport assignment and a chosen branch assignment.  If the
branch chooses a later occurrence of the ancestor's state, the transport side
supplies the strict positive contribution and the leaf cannot lie on a
critical path satisfying (3.4). -/
theorem repeated_branch_leaf_not_selected
    {ancestorBody transport branch : EliminationTree ι}
    (ancestor target : PrincipalLabel ι)
    (ancestorA : Assignment ancestorBody)
    (transportA : Assignment transport) (branchA : Assignment branch)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hrespect :
      (Assignment.principalNode (label := ancestor) ancestorA).RespectsPrincipalBounds φ y)
    (hsub : SelectedSubassignment (.add transportA branchA) ancestorA)
    (hφ : ∀ i t, 0 < φ i t)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hbranch : branchA.selectedEval φ y = target.value φ y) : False := by
  obtain ⟨hlocal, htransport⟩ :=
    add_decomp_from_right transportA branchA φ y (target.value φ y) hφ hbranch
  exact repeated_label_contradiction_of_selected_subassignment
    ancestor target ancestorA (.add transportA branchA) φ y
      (transportA.selectedEval φ y) hrespect hsub hφ hstate hshift hmono
      hlocal htransport

/-- The Phase-A deletion contradiction with the exact positivity interface
needed by the final retarded theorem.  In particular, `transport` can be any
recursively expanded subtree: its selected evaluation is positive because
all of its terminal arguments are nonnegative. -/
theorem repeated_branch_leaf_not_selected_of_nonnegative_arguments
    {ancestorBody transport branch : EliminationTree ι}
    (ancestor target : PrincipalLabel ι)
    (ancestorA : Assignment ancestorBody)
    (transportA : Assignment transport) (branchA : Assignment branch)
    (φ : ι → ℝ → ℝ) (y : ℝ)
    (hrespect :
      (Assignment.principalNode (label := ancestor) ancestorA).RespectsPrincipalBounds φ y)
    (hsub : SelectedSubassignment (.add transportA branchA) ancestorA)
    (hancestorArgs :
      ancestorBody.AllLeaves fun label => 0 ≤ y + label.shift)
    (htransportArgs :
      transport.AllLeaves fun label => 0 ≤ y + label.shift)
    (hφ : ∀ i t, 0 ≤ t → 0 < φ i t)
    (hstate : ancestor.state = target.state)
    (hshift : ancestor.shift < target.shift)
    (hmono : Monotone (φ ancestor.state))
    (hbranch : branchA.selectedEval φ y = target.value φ y) : False := by
  obtain ⟨hlocal, htransport⟩ :=
    add_decomp_from_right_of_nonnegative_arguments
      transportA branchA φ y (target.value φ y) htransportArgs hφ hbranch
  exact
    repeated_label_contradiction_of_selected_subassignment_of_nonnegative_arguments
      ancestor target ancestorA (.add transportA branchA) φ y
      (transportA.selectedEval φ y) hrespect hsub hancestorArgs hφ hstate hshift hmono
      hlocal htransport

end Assignment

end EliminationTree

end CleanLean.KL

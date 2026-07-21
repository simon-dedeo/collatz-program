/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.RawHistoryTree

/-!
# Selected paths through compiled raw histories

The occurrence pruner needs syntactic evidence that a marked branch and its
earlier same-state principal lie on the same selected raw path.  This zipper
retains the raw node and the exact assignment at every selected edge; unlike a
bare `SelectedSubassignment`, it therefore remembers which KL history word was
traversed.
-/

namespace CleanLean.KL

namespace ConcreteElimination

open EliminationTree
open EliminationTree.OccurrenceTree

/-- One raw node equipped with an assignment of its compiled erased tree. -/
structure RawSelection (k : ℕ) (root : ResidueSystem.State k) where
  word : OccurrenceId
  tree : RawHistoryTree k root word
  assignment : Assignment tree.compile.erase

/-- One selected child edge in the exact compiled raw grammar. -/
inductive SelectedRawEdge {k : ℕ} {root : ResidueSystem.State k} :
    RawSelection k root → RawSelection k root → Prop
  | neutralTransport {word : OccurrenceId}
      {shift_nonneg branch_eq transport}
      (childA : Assignment transport.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.transport], transport, childA⟩
        ⟨word, .neutral shift_nonneg branch_eq transport,
          by simpa [RawHistoryTree.compile, OccurrenceTree.erase] using
            (Assignment.principalNode childA)⟩
  | retardedTransport {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (childA : Assignment transport.compile.erase)
      (branchA : Assignment
        (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.transport], transport, childA⟩
        ⟨word, .retarded shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, OccurrenceTree.erase] using
            (Assignment.principalNode (.add childA branchA))⟩
  | retarded0 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch0.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.retarded 0], branch0, childA⟩
        ⟨word, .retarded shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infLeft childA)))⟩
  | retarded1 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch1.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.retarded 1], branch1, childA⟩
        ⟨word, .retarded shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infRight (.infLeft childA))))⟩
  | retarded2 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch2.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.retarded 2], branch2, childA⟩
        ⟨word, .retarded shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infRight (.infRight childA))))⟩
  | advancedTransport {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (childA : Assignment transport.compile.erase)
      (branchA : Assignment
        (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.transport], transport, childA⟩
        ⟨word, .advanced shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, OccurrenceTree.erase] using
            (Assignment.principalNode (.add childA branchA))⟩
  | advanced0 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch0.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.advanced 0], branch0, childA⟩
        ⟨word, .advanced shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infLeft childA)))⟩
  | advanced1 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch1.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.advanced 1], branch1, childA⟩
        ⟨word, .advanced shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infRight (.infLeft childA))))⟩
  | advanced2 {word : OccurrenceId}
      {shift_nonneg branch_eq transport branch0 branch1 branch2}
      (transportA : Assignment transport.compile.erase)
      (childA : Assignment branch2.compile.erase) :
      SelectedRawEdge
        ⟨word ++ [HistoryStep.advanced 2], branch2, childA⟩
        ⟨word, .advanced shift_nonneg branch_eq transport
          branch0 branch1 branch2,
          by simpa [RawHistoryTree.compile, RawHistoryTree.occurrenceInf3,
              OccurrenceTree.erase] using
            (Assignment.principalNode
              (.add transportA (.infRight (.infRight childA))))⟩

namespace SelectedRawEdge

/-- Every selected raw edge appends exactly one history symbol. -/
theorem word_eq_append_singleton
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) :
    ∃ step : HistoryStep, child.word = parent.word ++ [step] := by
  cases edge with
  | neutralTransport => exact ⟨.transport, rfl⟩
  | retardedTransport => exact ⟨.transport, rfl⟩
  | retarded0 => exact ⟨.retarded 0, rfl⟩
  | retarded1 => exact ⟨.retarded 1, rfl⟩
  | retarded2 => exact ⟨.retarded 2, rfl⟩
  | advancedTransport => exact ⟨.transport, rfl⟩
  | advanced0 => exact ⟨.advanced 0, rfl⟩
  | advanced1 => exact ⟨.advanced 1, rfl⟩
  | advanced2 => exact ⟨.advanced 2, rfl⟩

/-- The parent word is a prefix of the selected child word. -/
theorem parent_prefix
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) : parent.word <+: child.word := by
  obtain ⟨step, hword⟩ := edge.word_eq_append_singleton
  rw [hword]
  exact List.prefix_append _ _

/-- Every selected raw edge raises word length by one. -/
theorem child_length_eq_succ
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) :
    child.word.length = parent.word.length + 1 := by
  obtain ⟨step, hword⟩ := edge.word_eq_append_singleton
  simp [hword]

/-- Erasing a raw selected edge gives an ordinary selected-subassignment. -/
theorem assignmentSelected
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) :
    Assignment.SelectedSubassignment child.assignment parent.assignment := by
  cases edge with
  | neutralTransport childA => exact .principal (.refl childA)
  | retardedTransport childA branchA =>
      exact .principal (.addLeft (.refl childA) branchA)
  | retarded0 transportA childA =>
      exact .principal (.addRight transportA (.infLeft (.refl childA)))
  | retarded1 transportA childA =>
      exact .principal
        (.addRight transportA (.infRight (.infLeft (.refl childA))))
  | retarded2 transportA childA =>
      exact .principal
        (.addRight transportA (.infRight (.infRight (.refl childA))))
  | advancedTransport childA branchA =>
      exact .principal (.addLeft (.refl childA) branchA)
  | advanced0 transportA childA =>
      exact .principal (.addRight transportA (.infLeft (.refl childA)))
  | advanced1 transportA childA =>
      exact .principal
        (.addRight transportA (.infRight (.infLeft (.refl childA))))
  | advanced2 transportA childA =>
      exact .principal
        (.addRight transportA (.infRight (.infRight (.refl childA))))

/-- The information retained at the parent side of a raw edge: its principal
body assignment and the selected child embedded inside that body, before the
principal wrapper is added. -/
structure ParentBodySelection
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) where
  body : EliminationTree (ResidueSystem.State k)
  bodyA : Assignment body
  parentPrincipalSelected : Assignment.SelectedSubassignment
    (Assignment.principalNode
      (label := OccurrenceId.labelAt k root parent.word) bodyA)
    parent.assignment
  childInBody : Assignment.SelectedSubassignment child.assignment bodyA

/-- Exact source-split data for a selected branch edge.  Transport edges are
excluded by the supplied last-symbol equation. -/
structure BranchBodySelection
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) where
  transport : EliminationTree (ResidueSystem.State k)
  branch : EliminationTree (ResidueSystem.State k)
  transportA : Assignment transport
  branchA : Assignment branch
  parentPrincipalSelected : Assignment.SelectedSubassignment
    (Assignment.principalNode
      (label := OccurrenceId.labelAt k root parent.word)
      (Assignment.add transportA branchA))
    parent.assignment
  branch_selects_child : ∀ (ψ : ResidueSystem.State k → ℝ → ℝ) (z : ℝ),
    branchA.selectedEval ψ z = child.assignment.selectedEval ψ z
  transport_shifts : transport.AllLeaves fun label => -2 ≤ label.shift

/-- Extract the parent-body data from each of the nine exact edge shapes. -/
theorem exists_parentBodySelection
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent) :
    Nonempty (ParentBodySelection edge) := by
  cases edge with
  | @neutralTransport word shift_nonneg branch_eq transport childA =>
      refine ⟨{
        body := transport.compile.erase
        bodyA := childA
        parentPrincipalSelected := .refl _
        childInBody := .refl childA }⟩
  | @retardedTransport word shift_nonneg branch_eq transport branch0 branch1
      branch2 childA branchA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add childA branchA
        parentPrincipalSelected := .refl _
        childInBody := .addLeft (.refl childA) branchA }⟩
  | @retarded0 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infLeft childA)
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA (.infLeft (.refl childA)) }⟩
  | @retarded1 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infRight (.infLeft childA))
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA
          (.infRight (.infLeft (.refl childA))) }⟩
  | @retarded2 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infRight (.infRight childA))
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA
          (.infRight (.infRight (.refl childA))) }⟩
  | @advancedTransport word shift_nonneg branch_eq transport branch0 branch1
      branch2 childA branchA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add childA branchA
        parentPrincipalSelected := .refl _
        childInBody := .addLeft (.refl childA) branchA }⟩
  | @advanced0 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infLeft childA)
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA (.infLeft (.refl childA)) }⟩
  | @advanced1 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infRight (.infLeft childA))
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA
          (.infRight (.infLeft (.refl childA))) }⟩
  | @advanced2 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        body := .add transport.compile.erase
          (RawHistoryTree.occurrenceInf3
            branch0.compile branch1.compile branch2.compile).erase
        bodyA := .add transportA (.infRight (.infRight childA))
        parentPrincipalSelected := .refl _
        childInBody := .addRight transportA
          (.infRight (.infRight (.refl childA))) }⟩

/-- A selected edge carrying a certified branch symbol exposes the split
addition, the arbitrary transport sibling, and the selected branch minimum. -/
theorem exists_branchBodySelection
    {k : ℕ} {root : ResidueSystem.State k}
    {child parent : RawSelection k root}
    (edge : SelectedRawEdge child parent)
    (kind : ArrivalKind) (lift : Fin 3)
    (hstep : child.word =
      parent.word ++ [arrivalHistoryStep kind lift]) :
    Nonempty (BranchBodySelection edge) := by
  cases edge with
  | neutralTransport =>
      cases kind <;> simp [arrivalHistoryStep] at hstep
  | retardedTransport =>
      cases kind <;> simp [arrivalHistoryStep] at hstep
  | @retarded0 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infLeft childA
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]
  | @retarded1 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infRight (.infLeft childA)
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]
  | @retarded2 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infRight (.infRight childA)
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]
  | advancedTransport =>
      cases kind <;> simp [arrivalHistoryStep] at hstep
  | @advanced0 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infLeft childA
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]
  | @advanced1 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infRight (.infLeft childA)
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]
  | @advanced2 word shift_nonneg branch_eq transport branch0 branch1 branch2
      transportA childA =>
      refine ⟨{
        transport := transport.compile.erase
        branch := (RawHistoryTree.occurrenceInf3
          branch0.compile branch1.compile branch2.compile).erase
        transportA := transportA
        branchA := .infRight (.infRight childA)
        parentPrincipalSelected := .refl _
        branch_selects_child := ?_
        transport_shifts := transport.compile_shift_lower }⟩
      · intro ψ z
        simp [Assignment.selectedEval]

end SelectedRawEdge

/-- A finite selected path from a descendant raw node to an ancestor node. -/
inductive SelectedRawPath {k : ℕ} {root : ResidueSystem.State k} :
    RawSelection k root → RawSelection k root → Prop
  | refl (node : RawSelection k root) : SelectedRawPath node node
  | cons {child parent ancestor : RawSelection k root}
      (edge : SelectedRawEdge child parent)
      (rest : SelectedRawPath parent ancestor) :
      SelectedRawPath child ancestor

namespace SelectedRawPath

/-- The assignment of a strict descendant embedded in the body of the final
ancestor principal.  Keeping the principal wrapper separate is exactly what
the occurrence-pruning repeat payload requires. -/
structure DescendantInAncestorBody
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant parent ancestor : RawSelection k root}
    (edge : SelectedRawEdge descendant parent)
    (rest : SelectedRawPath parent ancestor) where
  body : EliminationTree (ResidueSystem.State k)
  bodyA : Assignment body
  ancestorPrincipalSelected : Assignment.SelectedSubassignment
    (Assignment.principalNode
      (label := OccurrenceId.labelAt k root ancestor.word) bodyA)
    ancestor.assignment
  descendantInBody : Assignment.SelectedSubassignment
    descendant.assignment bodyA

/-- A nonempty selected path embeds its first assignment in the body of its
last principal. -/
theorem exists_descendantInAncestorBody
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant parent ancestor : RawSelection k root}
    (edge : SelectedRawEdge descendant parent)
    (rest : SelectedRawPath parent ancestor) :
    Nonempty (DescendantInAncestorBody edge rest) := by
  induction rest generalizing descendant with
  | refl parent =>
      obtain ⟨frame⟩ := edge.exists_parentBodySelection
      exact ⟨{
        body := frame.body
        bodyA := frame.bodyA
        ancestorPrincipalSelected := frame.parentPrincipalSelected
        descendantInBody := frame.childInBody }⟩
  | @cons parent middle ancestor next tail ih =>
      obtain ⟨frame⟩ := ih next
      exact ⟨{
        body := frame.body
        bodyA := frame.bodyA
        ancestorPrincipalSelected := frame.ancestorPrincipalSelected
        descendantInBody := edge.assignmentSelected.trans
          frame.descendantInBody }⟩

/-- A selected source split, embedded in the body of an earlier principal on
the same raw path.  The earlier principal may be the source itself. -/
structure SplitInAncestorBody
    {k : ℕ} {root : ResidueSystem.State k}
    {source ancestor : RawSelection k root}
    {target : RawSelection k root}
    {edge : SelectedRawEdge target source}
    (branchFrame : SelectedRawEdge.BranchBodySelection edge)
    (path : SelectedRawPath source ancestor) where
  body : EliminationTree (ResidueSystem.State k)
  bodyA : Assignment body
  ancestorPrincipalSelected : Assignment.SelectedSubassignment
    (Assignment.principalNode
      (label := OccurrenceId.labelAt k root ancestor.word) bodyA)
    ancestor.assignment
  splitSelected : Assignment.SelectedSubassignment
    (Assignment.add branchFrame.transportA branchFrame.branchA) bodyA

/-- The source addition embeds below every earlier principal reached by its
selected raw path. -/
theorem exists_splitInAncestorBody
    {k : ℕ} {root : ResidueSystem.State k}
    {source ancestor target : RawSelection k root}
    {edge : SelectedRawEdge target source}
    (branchFrame : SelectedRawEdge.BranchBodySelection edge)
    (path : SelectedRawPath source ancestor) :
    Nonempty (SplitInAncestorBody branchFrame path) := by
  cases path with
  | refl source =>
      exact ⟨{
        body := .add branchFrame.transport branchFrame.branch
        bodyA := .add branchFrame.transportA branchFrame.branchA
        ancestorPrincipalSelected := branchFrame.parentPrincipalSelected
        splitSelected := .refl _ }⟩
  | @cons source parent ancestor first rest =>
      obtain ⟨ancestorFrame⟩ :=
        exists_descendantInAncestorBody first rest
      have splitInSource : Assignment.SelectedSubassignment
          (Assignment.add branchFrame.transportA branchFrame.branchA)
          source.assignment :=
        (Assignment.SelectedSubassignment.principal
          (Assignment.SelectedSubassignment.refl _)).trans
            branchFrame.parentPrincipalSelected
      exact ⟨{
        body := ancestorFrame.body
        bodyA := ancestorFrame.bodyA
        ancestorPrincipalSelected := ancestorFrame.ancestorPrincipalSelected
        splitSelected := splitInSource.trans ancestorFrame.descendantInBody }⟩

/-- Selected raw paths compose. -/
theorem trans
    {k : ℕ} {root : ResidueSystem.State k}
    {child middle ancestor : RawSelection k root}
    (first : SelectedRawPath child middle)
    (second : SelectedRawPath middle ancestor) :
    SelectedRawPath child ancestor := by
  induction first with
  | refl node => exact second
  | cons edge rest ih => exact .cons edge (ih second)

/-- Extend a selected raw path by one ancestor edge. -/
theorem snoc
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant child parent : RawSelection k root}
    (path : SelectedRawPath descendant child)
    (edge : SelectedRawEdge child parent) :
    SelectedRawPath descendant parent :=
  path.trans (.cons edge (.refl parent))

/-- The ancestor word is a prefix of the descendant word along every selected
raw path. -/
theorem ancestor_prefix
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant ancestor : RawSelection k root}
    (path : SelectedRawPath descendant ancestor) :
    ancestor.word <+: descendant.word := by
  induction path with
  | refl node => exact List.prefix_rfl
  | cons edge rest ih => exact ih.trans edge.parent_prefix

/-- Every raw selected path erases to selected-subassignment containment. -/
theorem assignmentSelected
    {k : ℕ} {root : ResidueSystem.State k}
    {child ancestor : RawSelection k root}
    (path : SelectedRawPath child ancestor) :
    Assignment.SelectedSubassignment child.assignment ancestor.assignment := by
  induction path with
  | refl node => exact .refl node.assignment
  | cons edge rest ih => exact edge.assignmentSelected.trans ih

/-- A selected path whose endpoint lengths differ by exactly one consists of
exactly one raw edge. -/
theorem edge_of_length_eq_succ
    {k : ℕ} {root : ResidueSystem.State k}
    {child ancestor : RawSelection k root}
    (path : SelectedRawPath child ancestor)
    (hlength : child.word.length = ancestor.word.length + 1) :
    SelectedRawEdge child ancestor := by
  cases path with
  | refl node => simp at hlength
  | @cons child parent ancestor edge rest =>
      cases rest with
      | refl parent => exact edge
      | @cons parent middle ancestor next tail =>
          have hedge := edge.child_length_eq_succ
          have hnext := next.child_length_eq_succ
          have hprefix := tail.ancestor_prefix.length_le
          omega

/-- A raw frame at an exact intermediate word of a selected path. -/
structure Factor
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant ancestor : RawSelection k root}
    (path : SelectedRawPath descendant ancestor)
    (word : OccurrenceId) where
  node : RawSelection k root
  word_eq : node.word = word
  below : SelectedRawPath descendant node
  above : SelectedRawPath node ancestor

/-- Every word between the ancestor and descendant words occurs as a unique
raw frame on the selected path.  Only existence is needed downstream. -/
theorem factorAt
    {k : ℕ} {root : ResidueSystem.State k}
    {descendant ancestor : RawSelection k root}
    (path : SelectedRawPath descendant ancestor)
    (word : OccurrenceId)
    (hbelow : word <+: descendant.word)
    (habove : ancestor.word <+: word) :
    Nonempty (Factor path word) := by
  induction path with
  | refl node =>
      have hword : node.word = word :=
        habove.eq_of_length_le hbelow.length_le
      exact ⟨{
        node := node
        word_eq := hword
        below := .refl node
        above := .refl node }⟩
  | @cons child parent ancestor edge rest ih =>
      obtain ⟨step, hchild⟩ := edge.word_eq_append_singleton
      rw [hchild, List.prefix_concat_iff] at hbelow
      rcases hbelow with hword | hparent
      · subst word
        exact ⟨{
          node := child
          word_eq := hchild
          below := .refl child
          above := .cons edge rest }⟩
      · obtain ⟨factor⟩ := ih hparent habove
        exact ⟨{
          node := factor.node
          word_eq := factor.word_eq
          below := .cons edge factor.below
          above := factor.above }⟩

end SelectedRawPath

/-- The raw selection at a marked terminal. -/
noncomputable def markedSelection
    {k : ℕ} {root : ResidueSystem.State k} {word : OccurrenceId}
    (provenance : WordRepeatProvenance k root)
    (target_eq : provenance.targetWord = word)
    (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value) :
    RawSelection k root where
  word := word
  tree := .marked provenance target_eq shift_nonneg
  assignment := by
    simpa [RawHistoryTree.compile, OccurrenceTree.erase] using
      Assignment.principalLeaf (OccurrenceId.labelAt k root word)

/-- A selected marked endpoint and its complete raw path to an ancestor
selection. -/
structure SelectedMarkedPath
    {k : ℕ} {root : ResidueSystem.State k}
    (ancestor : RawSelection k root) where
  word : OccurrenceId
  provenance : WordRepeatProvenance k root
  target_eq : provenance.targetWord = word
  shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value
  path : SelectedRawPath
    (markedSelection provenance target_eq shift_nonneg) ancestor

/-- Every selected occurrence hit in a compiled raw history yields an exact
raw zipper ending at the corresponding marked constructor. -/
theorem exists_selectedMarkedPath_of_hits
    {k : ℕ} {root : ResidueSystem.State k} {word : OccurrenceId}
    (tree : RawHistoryTree k root word)
    (A : Assignment tree.compile.erase) (hhit : tree.compile.Hits A) :
    Nonempty (SelectedMarkedPath
      (⟨word, tree, A⟩ : RawSelection k root)) := by
  induction tree with
  | negative shift_neg shift_lower =>
      cases A
      simp [RawHistoryTree.compile, OccurrenceTree.Hits] at hhit
  | @marked word provenance target_eq shift_nonneg =>
      cases A
      exact ⟨{
        word := word
        provenance := provenance
        target_eq := target_eq
        shift_nonneg := shift_nonneg
        path := .refl (markedSelection provenance target_eq shift_nonneg) }⟩
  | @neutral word shift_nonneg branch_eq transport ih =>
      cases A with
      | principalNode childA =>
          obtain ⟨W⟩ := ih childA hhit
          exact ⟨{
            word := W.word
            provenance := W.provenance
            target_eq := W.target_eq
            shift_nonneg := W.shift_nonneg
            path := W.path.snoc (.neutralTransport childA) }⟩
  | @retarded word shift_nonneg branch_eq transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      cases A with
      | principalNode bodyA =>
          cases bodyA with
          | add transportA branchA =>
              rcases hhit with htransport | hbranch
              · obtain ⟨W⟩ := ihTransport transportA htransport
                exact ⟨{
                  word := W.word
                  provenance := W.provenance
                  target_eq := W.target_eq
                  shift_nonneg := W.shift_nonneg
                  path := W.path.snoc
                    (.retardedTransport transportA branchA) }⟩
              · cases branchA with
                | infLeft child0A =>
                    obtain ⟨W⟩ := ih0 child0A hbranch
                    exact ⟨{
                      word := W.word
                      provenance := W.provenance
                      target_eq := W.target_eq
                      shift_nonneg := W.shift_nonneg
                      path := W.path.snoc (.retarded0 transportA child0A) }⟩
                | infRight restA =>
                    cases restA with
                    | infLeft child1A =>
                        obtain ⟨W⟩ := ih1 child1A hbranch
                        exact ⟨{
                          word := W.word
                          provenance := W.provenance
                          target_eq := W.target_eq
                          shift_nonneg := W.shift_nonneg
                          path := W.path.snoc
                            (.retarded1 transportA child1A) }⟩
                    | infRight child2A =>
                        obtain ⟨W⟩ := ih2 child2A hbranch
                        exact ⟨{
                          word := W.word
                          provenance := W.provenance
                          target_eq := W.target_eq
                          shift_nonneg := W.shift_nonneg
                          path := W.path.snoc
                            (.retarded2 transportA child2A) }⟩
  | @advanced word shift_nonneg branch_eq transport branch0 branch1 branch2
      ihTransport ih0 ih1 ih2 =>
      cases A with
      | principalNode bodyA =>
          cases bodyA with
          | add transportA branchA =>
              rcases hhit with htransport | hbranch
              · obtain ⟨W⟩ := ihTransport transportA htransport
                exact ⟨{
                  word := W.word
                  provenance := W.provenance
                  target_eq := W.target_eq
                  shift_nonneg := W.shift_nonneg
                  path := W.path.snoc
                    (.advancedTransport transportA branchA) }⟩
              · cases branchA with
                | infLeft child0A =>
                    obtain ⟨W⟩ := ih0 child0A hbranch
                    exact ⟨{
                      word := W.word
                      provenance := W.provenance
                      target_eq := W.target_eq
                      shift_nonneg := W.shift_nonneg
                      path := W.path.snoc (.advanced0 transportA child0A) }⟩
                | infRight restA =>
                    cases restA with
                    | infLeft child1A =>
                        obtain ⟨W⟩ := ih1 child1A hbranch
                        exact ⟨{
                          word := W.word
                          provenance := W.provenance
                          target_eq := W.target_eq
                          shift_nonneg := W.shift_nonneg
                          path := W.path.snoc
                            (.advanced1 transportA child1A) }⟩
                    | infRight child2A =>
                        obtain ⟨W⟩ := ih2 child2A hbranch
                        exact ⟨{
                          word := W.word
                          provenance := W.provenance
                          target_eq := W.target_eq
                          shift_nonneg := W.shift_nonneg
                          path := W.path.snoc
                            (.advanced2 transportA child2A) }⟩

@[simp] theorem markedSelection_selectedEval
    {k : ℕ} {root : ResidueSystem.State k} {word : OccurrenceId}
    (provenance : WordRepeatProvenance k root)
    (target_eq : provenance.targetWord = word)
    (shift_nonneg : 0 ≤ (OccurrenceId.shiftAt word).value)
    (ψ : ResidueSystem.State k → ℝ → ℝ) (z : ℝ) :
    (markedSelection provenance target_eq shift_nonneg).assignment.selectedEval
        ψ z =
      (OccurrenceId.labelAt k root word).value ψ z := by
  generalize hassignment :
    (markedSelection provenance target_eq shift_nonneg).assignment = assigned
  cases assigned with
  | principalLeaf label => rfl

/-- Closed raw histories carry complete prefix provenance for every selected
mark.  This is the final syntactic bridge from the well-founded history
builder to sound occurrence pruning. -/
theorem RawHistoryTree.allMarkProvenance_root
    {k : ℕ} {root : ResidueSystem.State k}
    (tree : RawHistoryTree k root []) : tree.compile.AllMarkProvenance := by
  intro A hhit
  let rootSelection : RawSelection k root := ⟨[], tree, A⟩
  obtain ⟨markedPath⟩ :=
    exists_selectedMarkedPath_of_hits tree A hhit
  let targetSelection : RawSelection k root :=
    markedSelection markedPath.provenance markedPath.target_eq
      markedPath.shift_nonneg
  have htargetWord : targetSelection.word =
      markedPath.provenance.targetWord := by
    exact markedPath.target_eq.symm
  have hsourceBelow : markedPath.provenance.source <+:
      targetSelection.word := by
    rw [htargetWord, WordRepeatProvenance.targetWord]
    exact List.prefix_append _ _
  have hrootSource : rootSelection.word <+:
      markedPath.provenance.source := by
    exact List.nil_prefix
  obtain ⟨sourceFactor⟩ := markedPath.path.factorAt
    markedPath.provenance.source hsourceBelow hrootSource
  have hearlierBelow : markedPath.provenance.earlier <+:
      sourceFactor.node.word := by
    rw [sourceFactor.word_eq]
    exact markedPath.provenance.earlierPrefixSource
  have hrootEarlier : rootSelection.word <+:
      markedPath.provenance.earlier := by
    exact List.nil_prefix
  obtain ⟨earlierFactor⟩ := sourceFactor.above.factorAt
    markedPath.provenance.earlier hearlierBelow hrootEarlier
  have hlength : targetSelection.word.length =
      sourceFactor.node.word.length + 1 := by
    rw [htargetWord, sourceFactor.word_eq,
      WordRepeatProvenance.targetWord]
    simp
  let sourceEdge : SelectedRawEdge targetSelection sourceFactor.node :=
    sourceFactor.below.edge_of_length_eq_succ hlength
  have hsourceStep : targetSelection.word =
      sourceFactor.node.word ++
        [arrivalHistoryStep markedPath.provenance.kind
          markedPath.provenance.lift] := by
    rw [htargetWord, sourceFactor.word_eq]
    rfl
  obtain ⟨branchFrame⟩ := sourceEdge.exists_branchBodySelection
    markedPath.provenance.kind markedPath.provenance.lift hsourceStep
  obtain ⟨splitFrame⟩ :=
    SelectedRawPath.exists_splitInAncestorBody
      branchFrame earlierFactor.below
  refine ⟨{
    ancestor := OccurrenceId.labelAt k root earlierFactor.node.word
    target := OccurrenceId.labelAt k root targetSelection.word
    ancestorBody := splitFrame.body
    ancestorA := splitFrame.bodyA
    ancestorSelected := splitFrame.ancestorPrincipalSelected.trans
      earlierFactor.above.assignmentSelected
    transport := branchFrame.transport
    branch := branchFrame.branch
    transportA := branchFrame.transportA
    branchA := branchFrame.branchA
    splitSelected := splitFrame.splitSelected
    branch_selects_target := ?_
    same_state := ?_
    strictly_higher := ?_
    transport_shifts := branchFrame.transport_shifts }⟩
  · intro ψ z
    exact branchFrame.branch_selects_child ψ z |>.trans
      (markedSelection_selectedEval markedPath.provenance
        markedPath.target_eq markedPath.shift_nonneg ψ z)
  · rw [earlierFactor.word_eq, htargetWord]
    exact markedPath.provenance.label_same_state
  · rw [earlierFactor.word_eq, htargetWord]
    exact markedPath.provenance.label_strictly_higher

end ConcreteElimination

end CleanLean.KL

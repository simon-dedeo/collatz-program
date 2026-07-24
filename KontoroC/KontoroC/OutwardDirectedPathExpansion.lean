/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardSUnitSyntaxGate
import KontoroC.OutwardInvariantBridge

/-!
# Exact directed path certificates for finite recharge graphs

Finite reset-graph experiments should return a replayable directed path or a
small exact obstruction, not an undirected expansion score.  This file proves
the elementary directed theorem needed for the first layer of that audit:
minimum out-degree `d` in a finite loopless directed graph produces a simple
directed path with exactly `d` edges.  Conversely, failure to find such a path
certifies a vertex with out-degree below `d`.

The specialization uses literal positive `RechargeMacro` edges.  It yields
only a finite path at one chosen state set; it supplies neither compatible
paths at growing precision nor one ordinary infinite seed.
-/

namespace KontoroC
namespace OutwardDirectedPathExpansion

open OutwardInvariantBridge

variable {Vertex : Type*} [DecidableEq Vertex]

/-- Out-neighbors retained inside the exact finite state set. -/
def outNeighbors (vertices : Finset Vertex)
    (edge : Vertex → Vertex → Prop) [DecidableRel edge]
    (v : Vertex) : Finset Vertex :=
  vertices.filter (edge v)

/-- Executable list of singleton out-degree obstructions to a proposed path
length lower bound. -/
def lowOutdegreeVertices (vertices : Finset Vertex)
    (edge : Vertex → Vertex → Prop) [DecidableRel edge]
    (d : ℕ) : Finset Vertex :=
  vertices.filter fun v ↦ (outNeighbors vertices edge v).card < d

omit [DecidableEq Vertex] in
@[simp] theorem mem_lowOutdegreeVertices_iff
    {vertices : Finset Vertex} {edge : Vertex → Vertex → Prop}
    [DecidableRel edge] {d : ℕ} {v : Vertex} :
    v ∈ lowOutdegreeVertices vertices edge d ↔
      v ∈ vertices ∧ (outNeighbors vertices edge v).card < d := by
  simp [lowOutdegreeVertices]

omit [DecidableEq Vertex] in
/-- Empty checker output is exactly the global minimum out-degree premise. -/
theorem lowOutdegreeVertices_eq_empty_iff
    (vertices : Finset Vertex) (edge : Vertex → Vertex → Prop)
    [DecidableRel edge] (d : ℕ) :
    lowOutdegreeVertices vertices edge d = ∅ ↔
      ∀ v ∈ vertices, d ≤ (outNeighbors vertices edge v).card := by
  simp only [lowOutdegreeVertices, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv
    exact Nat.le_of_not_gt (h hv)
  · intro h v hv hlt
    exact (Nat.not_lt_of_ge (h v hv)) hlt

/-- A nonempty, vertex-simple directed path contained in `vertices`. -/
def IsSimpleDirectedPath (vertices : Finset Vertex)
    (edge : Vertex → Vertex → Prop) (path : List Vertex) : Prop :=
  path ≠ [] ∧
  path.Nodup ∧
  (∀ v ∈ path, v ∈ vertices) ∧
  path.IsChain edge

private theorem exists_reversed_extension
    (vertices : Finset Vertex) (edge : Vertex → Vertex → Prop)
    [DecidableRel edge] (d : ℕ) (start : Vertex)
    (hirrefl : ∀ v, ¬edge v v)
    (hdegree : ∀ v ∈ vertices, d ≤ (outNeighbors vertices edge v).card)
    (remaining : ℕ) (revPath : List Vertex)
    (hne : revPath ≠ [])
    (hstart : start ∈ revPath)
    (hnodup : revPath.Nodup)
    (hmem : ∀ v ∈ revPath, v ∈ vertices)
    (hchain : revPath.IsChain (fun newer older ↦ edge older newer))
    (hlength : revPath.length + remaining = d + 1) :
    ∃ completed : List Vertex,
      completed.length = d + 1 ∧
      start ∈ completed ∧
      completed.Nodup ∧
      (∀ v ∈ completed, v ∈ vertices) ∧
      completed.IsChain (fun newer older ↦ edge older newer) := by
  induction remaining generalizing revPath with
  | zero =>
      exact ⟨revPath, by omega, hstart, hnodup, hmem, hchain⟩
  | succ n ih =>
      obtain ⟨v, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
      let neighbors := outNeighbors vertices edge v
      let usedWithoutHead := (v :: tail).toFinset.erase v
      have hvVertices : v ∈ vertices := hmem v (by simp)
      have hdegreeV : d ≤ neighbors.card := hdegree v hvVertices
      have hvUsed : v ∈ (v :: tail).toFinset := by simp
      have husedCard : usedWithoutHead.card = tail.length := by
        dsimp only [usedWithoutHead]
        rw [Finset.card_erase_of_mem hvUsed,
          List.toFinset_card_of_nodup hnodup]
        simp
      have hcardLt : usedWithoutHead.card < neighbors.card := by
        rw [husedCard]
        simp only [List.length_cons] at hlength
        omega
      have hnsubset : ¬neighbors ⊆ usedWithoutHead := by
        intro hsubset
        exact (not_lt_of_ge (Finset.card_le_card hsubset)) hcardLt
      obtain ⟨w, hwNeighbor, hwUnused⟩ := Finset.not_subset.mp hnsubset
      have hwData := Finset.mem_filter.mp hwNeighbor
      have hwVertices : w ∈ vertices := hwData.1
      have hvw : edge v w := hwData.2
      have hwne : w ≠ v := by
        intro hwv
        subst w
        exact hirrefl v hvw
      have hwNotMem : w ∉ v :: tail := by
        intro hwMem
        apply hwUnused
        exact Finset.mem_erase.mpr ⟨hwne, by simpa using hwMem⟩
      have hnewLength : (w :: v :: tail).length + n = d + 1 := by
        simp only [List.length_cons] at hlength ⊢
        omega
      apply ih (w :: v :: tail) (by simp) (by simp [hstart])
        (hnodup.cons hwNotMem)
        (by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hwVertices
          · exact hmem x (by simpa using hx))
        (by
          rw [List.isChain_cons_cons]
          exact ⟨hvw, hchain⟩)
        hnewLength

/-- Exact directed longest-path lower bound.  The output has `d + 1`
distinct vertices, hence exactly `d` directed edges. -/
theorem exists_simpleDirectedPath_of_minOutdegree
    (vertices : Finset Vertex) (edge : Vertex → Vertex → Prop)
    [DecidableRel edge] (d : ℕ)
    (hirrefl : ∀ v, ¬edge v v)
    (hvertices : vertices.Nonempty)
    (hdegree : ∀ v ∈ vertices, d ≤ (outNeighbors vertices edge v).card) :
    ∃ path : List Vertex,
      IsSimpleDirectedPath vertices edge path ∧ path.length = d + 1 := by
  obtain ⟨start, hstartVertices⟩ := hvertices
  obtain ⟨revPath, hlength, hstart, hnodup, hmem, hchain⟩ :=
    exists_reversed_extension vertices edge d start hirrefl hdegree
      d [start] (by simp) (by simp) (by simp)
      (by simpa using hstartVertices) (by simp) (by simp [Nat.add_comm])
  refine ⟨revPath.reverse, ⟨?_, ?_, ?_, ?_⟩, by simpa using hlength⟩
  · intro hempty
    have : revPath = [] := by
      simpa using congrArg List.reverse hempty
    subst revPath
    simp at hlength
  · exact List.nodup_reverse.mpr hnodup
  · intro v hv
    exact hmem v (by simpa using hv)
  · rw [List.isChain_reverse]
    exact hchain

/-- Failure form suitable for a finite checker: if there is no simple path
of `d` edges, some exact vertex has fewer than `d` retained out-neighbors. -/
theorem exists_lowOutdegree_of_no_simpleDirectedPath
    (vertices : Finset Vertex) (edge : Vertex → Vertex → Prop)
    [DecidableRel edge] (d : ℕ)
    (hirrefl : ∀ v, ¬edge v v)
    (hvertices : vertices.Nonempty)
    (hnoPath : ¬∃ path : List Vertex,
      IsSimpleDirectedPath vertices edge path ∧ path.length = d + 1) :
    ∃ v ∈ vertices, (outNeighbors vertices edge v).card < d := by
  by_contra hnoLow
  push Not at hnoLow
  have hdegree :
      ∀ v ∈ vertices, d ≤ (outNeighbors vertices edge v).card := by
    intro v hv
    exact hnoLow v hv
  exact hnoPath (exists_simpleDirectedPath_of_minOutdegree
    vertices edge d hirrefl hvertices hdegree)

/-! ## Literal first-passage specialization -/

/-- A directed edge exists only when a literal positive recharge macro has
been supplied. -/
def RechargeEdge (H H' : ℕ) : Prop :=
  ∃ words, RechargeMacro H H' words

theorem RechargeEdge.lt {H H' : ℕ} (h : RechargeEdge H H') : H < H' := by
  obtain ⟨words, hmacro⟩ := h
  exact hmacro.lt

/-- Literal recharge edges compose because their block lists concatenate. -/
theorem RechargeEdge.trans {H K L : ℕ}
    (hHK : RechargeEdge H K) (hKL : RechargeEdge K L) :
    RechargeEdge H L := by
  obtain ⟨left, hleft⟩ := hHK
  obtain ⟨right, hright⟩ := hKL
  exact ⟨left ++ right, hleft.append hright⟩

theorem rechargeEdge_irrefl (H : ℕ) : ¬RechargeEdge H H := by
  intro h
  exact (Nat.lt_irrefl H) h.lt

/-- A finite charge set with literal recharge out-degree at least `d`
contains a replayable simple charge path of `d` macros.  Each adjacent edge
retains an existential `RechargeMacro` witness by definition. -/
theorem exists_literalRechargePath_of_minOutdegree
    (charges : Finset ℕ) [DecidableRel RechargeEdge] (d : ℕ)
    (hcharges : charges.Nonempty)
    (hdegree : ∀ H ∈ charges,
      d ≤ (outNeighbors charges RechargeEdge H).card) :
    ∃ path : List ℕ,
      IsSimpleDirectedPath charges RechargeEdge path ∧
      path.length = d + 1 :=
  exists_simpleDirectedPath_of_minOutdegree charges RechargeEdge d
    rechargeEdge_irrefl hcharges hdegree

/-- Executable-table adapter.  The finite checker may use any decidable edge
relation, provided every accepted edge is accompanied by a literal recharge
witness.  The resulting path is therefore replayable in the first-passage
system even when `RechargeEdge` itself is not used as a decision procedure. -/
theorem exists_literalRechargePath_of_certified_minOutdegree
    (charges : Finset ℕ) (edge : ℕ → ℕ → Prop)
    [DecidableRel edge] (d : ℕ)
    (hsound : ∀ H H', edge H H' → RechargeEdge H H')
    (hcharges : charges.Nonempty)
    (hdegree : ∀ H ∈ charges,
      d ≤ (outNeighbors charges edge H).card) :
    ∃ path : List ℕ,
      IsSimpleDirectedPath charges edge path ∧
      path.length = d + 1 := by
  apply exists_simpleDirectedPath_of_minOutdegree charges edge d
  · intro H hloop
    exact rechargeEdge_irrefl H (hsound H H hloop)
  · exact hcharges
  · exact hdegree

end OutwardDirectedPathExpansion
end KontoroC

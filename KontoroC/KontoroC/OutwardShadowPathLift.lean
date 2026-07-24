/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeChain

/-!
# Exact finite lifting audit for quotient paths

A path in a residue, spectral, or other quotient is useful only if one can
choose compatible literal states along the whole path.  This module gives the
finite dynamic-programming audit.  Starting from the exact fiber over the
first shadow vertex, `reachableAfter` repeatedly retains precisely the exact
states which realize the next shadow edge.

The terminal frontier is nonempty exactly when the complete shadow path has
an exact lift.  An empty intermediate frontier remains empty under every
extension and is therefore a replayable finite nonlifting certificate.
Nonempty raw fibers at each shadow vertex are not enough: compatibility of
successive edges is essential.
-/

namespace KontoroC
namespace OutwardShadowPathLift

open OutwardDirectedPathExpansion

variable {Exact Shadow : Type*}

/-- Endpoint-sensitive realization of exactly the listed future shadow
vertices, starting from one exact state. -/
def FollowsTo (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) :
    Exact → List Shadow → Exact → Prop
  | source, [], terminal => terminal = source
  | source, nextShadow :: rest, terminal =>
      ∃ next ∈ states, edge source next ∧ shadow next = nextShadow ∧
        FollowsTo states shadow edge next rest terminal

/-- A nonempty shadow path has a compatible exact-state lift inside the
declared finite state set. -/
def LiftsShadowPath (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) : List Shadow → Prop
  | [] => False
  | firstShadow :: rest =>
      ∃ source ∈ states, shadow source = firstShadow ∧
        ∃ terminal, FollowsTo states shadow edge source rest terminal

/-- A fully replayable exact path certificate: exact and shadow vertex lists
match pointwise, every exact vertex is in the declared state set, and all
successive exact vertices satisfy the edge relation. -/
def ExactPathLift (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop)
    (exactPath : List Exact) (shadowPath : List Shadow) : Prop :=
  exactPath ≠ [] ∧
  exactPath.Forall₂ (fun exactState shadowState =>
    shadow exactState = shadowState) shadowPath ∧
  exactPath.IsChain edge ∧
  ∀ exactState ∈ exactPath, exactState ∈ states

/-- Endpoint-sensitive future execution is equivalent, after forgetting the
chosen endpoint, to an explicit exact-state tail. -/
theorem exists_followsTo_iff_exists_exactTail
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) (source : Exact) (rest : List Shadow) :
    (∃ terminal, FollowsTo states shadow edge source rest terminal) ↔
      ∃ exactTail,
        exactTail.Forall₂ (fun exactState shadowState =>
          shadow exactState = shadowState) rest ∧
        (source :: exactTail).IsChain edge ∧
        ∀ exactState ∈ exactTail, exactState ∈ states := by
  induction rest generalizing source with
  | nil => simp [FollowsTo]
  | cons nextShadow rest ih =>
      constructor
      · rintro ⟨terminal, next, hstates, hedge, hshadow, hfollow⟩
        obtain ⟨tail, htailShadow, htailChain, htailStates⟩ :=
          (ih next).mp ⟨terminal, hfollow⟩
        refine ⟨next :: tail, ?_, ?_, ?_⟩
        · exact htailShadow.cons hshadow
        · rw [List.isChain_cons_cons]
          exact ⟨hedge, htailChain⟩
        · intro exactState hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hstates
          · exact htailStates exactState hmem
      · rintro ⟨exactTail, htailShadow, htailChain, htailStates⟩
        cases exactTail with
        | nil => cases htailShadow
        | cons next tail =>
            cases htailShadow with
            | cons hshadow hrestShadow =>
                rw [List.isChain_cons_cons] at htailChain
                obtain ⟨hedge, hrestChain⟩ := htailChain
                have hnextStates : next ∈ states :=
                  htailStates next (by simp)
                have htailStates' :
                    ∀ exactState ∈ tail, exactState ∈ states := by
                  intro exactState hmem
                  exact htailStates exactState (by simp [hmem])
                obtain ⟨terminal, hfollow⟩ :=
                  (ih next).mpr ⟨tail, hrestShadow,
                    hrestChain, htailStates'⟩
                exact ⟨terminal, next, hnextStates, hedge,
                  hshadow, hfollow⟩

/-- The relational lift predicate is exactly existence of one fully
replayable exact-state path list. -/
theorem liftsShadowPath_iff_exists_exactPathLift
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) (shadowPath : List Shadow) :
    LiftsShadowPath states shadow edge shadowPath ↔
      ∃ exactPath, ExactPathLift states shadow edge exactPath shadowPath := by
  cases shadowPath with
  | nil =>
      simp [LiftsShadowPath, ExactPathLift]
  | cons firstShadow rest =>
      constructor
      · rintro ⟨source, hsource, hshadow, terminal, hfollow⟩
        obtain ⟨tail, htailShadow, hchain, htailStates⟩ :=
          (exists_followsTo_iff_exists_exactTail
            states shadow edge source rest).mp ⟨terminal, hfollow⟩
        refine ⟨source :: tail, by simp, ?_, hchain, ?_⟩
        · exact htailShadow.cons hshadow
        · intro exactState hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hsource
          · exact htailStates exactState hmem
      · rintro ⟨exactPath, hne, hpointwise, hchain, hstates⟩
        cases exactPath with
        | nil => exact (hne rfl).elim
        | cons source tail =>
            cases hpointwise with
            | cons hshadow htailShadow =>
                have hsource : source ∈ states :=
                  hstates source (by simp)
                have htailStates :
                    ∀ exactState ∈ tail, exactState ∈ states := by
                  intro exactState hmem
                  exact hstates exactState (by simp [hmem])
                obtain ⟨terminal, hfollow⟩ :=
                  (exists_followsTo_iff_exists_exactTail
                    states shadow edge source rest).mpr
                    ⟨tail, htailShadow, hchain, htailStates⟩
                exact ⟨source, hsource, hshadow, terminal, hfollow⟩

section Computable

variable [Fintype Exact] [DecidableEq Exact] [DecidableEq Shadow]

/-- One exact forward-fiber update. -/
def advance (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (current : Finset Exact) (nextShadow : Shadow) : Finset Exact :=
  states.filter fun next =>
    shadow next = nextShadow ∧ ∃ source ∈ current, edge source next

@[simp] theorem mem_advance_iff
    {states current : Finset Exact} {shadow : Exact → Shadow}
    {edge : Exact → Exact → Prop} [DecidableRel edge]
    {next : Exact} {nextShadow : Shadow} :
    next ∈ advance states shadow edge current nextShadow ↔
      next ∈ states ∧ shadow next = nextShadow ∧
        ∃ source ∈ current, edge source next := by
  simp [advance]

/-- Repeated exact frontier update along a list of future shadow vertices. -/
def reachableAfter (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge] :
    Finset Exact → List Shadow → Finset Exact
  | current, [] => current
  | current, nextShadow :: rest =>
      reachableAfter states shadow edge
        (advance states shadow edge current nextShadow) rest

/-- Exact source fiber over one shadow vertex. -/
def initialFiber (states : Finset Exact) (shadow : Exact → Shadow)
    (firstShadow : Shadow) : Finset Exact :=
  states.filter fun source => shadow source = firstShadow

@[simp] theorem mem_initialFiber_iff
    {states : Finset Exact} {shadow : Exact → Shadow}
    {source : Exact} {firstShadow : Shadow} :
    source ∈ initialFiber states shadow firstShadow ↔
      source ∈ states ∧ shadow source = firstShadow := by
  simp [initialFiber]

/-- The exact terminal-state frontier of a shadow path. -/
def terminalFiber (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge] :
    List Shadow → Finset Exact
  | [] => ∅
  | firstShadow :: rest =>
      reachableAfter states shadow edge
        (initialFiber states shadow firstShadow) rest

/-- Dynamic programming is semantically exact: membership in the computed
frontier is equivalent to one endpoint-sensitive path realization. -/
theorem mem_reachableAfter_iff
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (current : Finset Exact) (rest : List Shadow) (terminal : Exact) :
    terminal ∈ reachableAfter states shadow edge current rest ↔
      ∃ source ∈ current,
        FollowsTo states shadow edge source rest terminal := by
  induction rest generalizing current with
  | nil =>
      simp [reachableAfter, FollowsTo]
  | cons nextShadow rest ih =>
      rw [reachableAfter, ih]
      constructor
      · rintro ⟨next, hnext, hfollow⟩
        rw [mem_advance_iff] at hnext
        obtain ⟨hstates, hshadow, source, hsource, hedge⟩ := hnext
        exact ⟨source, hsource, next, hstates, hedge, hshadow, hfollow⟩
      · rintro ⟨source, hsource, next, hstates, hedge, hshadow, hfollow⟩
        exact ⟨next,
          mem_advance_iff.mpr
            ⟨hstates, hshadow, source, hsource, hedge⟩,
          hfollow⟩

/-- A less elaboration-sensitive source-set form of `mem_reachableAfter_iff`.
The finite ambient set enters every noninitial step through `advance`. -/
theorem mem_reachableAfter_iff_exists_follows
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (current : Finset Exact) (rest : List Shadow) (terminal : Exact) :
    terminal ∈ reachableAfter states shadow edge current rest ↔
      ∃ source ∈ current,
        FollowsTo states shadow edge source rest terminal :=
  mem_reachableAfter_iff states shadow edge current rest terminal

/-- The computed terminal frontier is nonempty exactly when the entire
nonempty shadow path has a compatible exact lift. -/
theorem terminalFiber_nonempty_iff_liftsShadowPath
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (path : List Shadow) :
    (terminalFiber states shadow edge path).Nonempty ↔
      LiftsShadowPath states shadow edge path := by
  cases path with
  | nil => simp [terminalFiber, LiftsShadowPath]
  | cons firstShadow rest =>
      constructor
      · rintro ⟨terminal, hterminal⟩
        rw [terminalFiber,
          mem_reachableAfter_iff] at hterminal
        obtain ⟨source, hsource, hfollow⟩ := hterminal
        rw [mem_initialFiber_iff] at hsource
        exact ⟨source, hsource.1, hsource.2, terminal, hfollow⟩
      · rintro ⟨source, hstates, hshadow, terminal, hfollow⟩
        refine ⟨terminal, ?_⟩
        rw [terminalFiber, mem_reachableAfter_iff]
        exact ⟨source, mem_initialFiber_iff.mpr
          ⟨hstates, hshadow⟩, hfollow⟩

/-- Computable frontier output is nonempty exactly when there is a concrete,
fully replayable exact-state path certificate. -/
theorem terminalFiber_nonempty_iff_exists_exactPathLift
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (path : List Shadow) :
    (terminalFiber states shadow edge path).Nonempty ↔
      ∃ exactPath, ExactPathLift states shadow edge exactPath path :=
  (terminalFiber_nonempty_iff_liftsShadowPath
    states shadow edge path).trans
    (liftsShadowPath_iff_exists_exactPathLift
      states shadow edge path)

/-- Empty terminal frontier is exactly failure of the finite lift. -/
theorem terminalFiber_eq_empty_iff_not_liftsShadowPath
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (path : List Shadow) :
    terminalFiber states shadow edge path = ∅ ↔
      ¬LiftsShadowPath states shadow edge path := by
  rw [← Finset.not_nonempty_iff_eq_empty,
    terminalFiber_nonempty_iff_liftsShadowPath]

/-- Empty checker output is equivalently the nonexistence of any replayable
exact-state path list. -/
theorem terminalFiber_eq_empty_iff_no_exactPathLift
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (path : List Shadow) :
    terminalFiber states shadow edge path = ∅ ↔
      ¬∃ exactPath, ExactPathLift states shadow edge exactPath path := by
  rw [terminalFiber_eq_empty_iff_not_liftsShadowPath,
    liftsShadowPath_iff_exists_exactPathLift]

@[simp] theorem advance_empty
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (nextShadow : Shadow) :
    advance states shadow edge ∅ nextShadow = ∅ := by
  ext next
  simp [advance]

@[simp] theorem reachableAfter_empty
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (rest : List Shadow) :
    reachableAfter states shadow edge ∅ rest = ∅ := by
  induction rest with
  | nil => rfl
  | cons nextShadow rest ih =>
      simp [reachableAfter, ih]

/-- Frontier computation composes over concatenated shadow suffixes. -/
theorem reachableAfter_append
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (current : Finset Exact) (left right : List Shadow) :
    reachableAfter states shadow edge current (left ++ right) =
      reachableAfter states shadow edge
        (reachableAfter states shadow edge current left) right := by
  induction left generalizing current with
  | nil => rfl
  | cons nextShadow left ih =>
      simp only [List.cons_append, reachableAfter]
      exact ih (advance states shadow edge current nextShadow)

/-- Nonempty-path terminal frontiers compose across a path extension. -/
theorem terminalFiber_cons_append
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (firstShadow : Shadow) (left right : List Shadow) :
    terminalFiber states shadow edge (firstShadow :: (left ++ right)) =
      reachableAfter states shadow edge
        (terminalFiber states shadow edge (firstShadow :: left)) right := by
  simp only [terminalFiber]
  exact reachableAfter_append states shadow edge
    (initialFiber states shadow firstShadow) left right

/-- Once an exact frontier is empty, no continuation of the shadow path can
restore a lift. -/
theorem empty_prefix_frontier_obstructs_every_extension
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (current : Finset Exact) (initialSegment suffix : List Shadow)
    (hempty : reachableAfter states shadow edge current initialSegment = ∅) :
    reachableAfter states shadow edge current (initialSegment ++ suffix) = ∅ := by
  rw [reachableAfter_append, hempty, reachableAfter_empty]

/-- Worker-facing first-empty-fiber certificate for an actual shadow-path
prefix. -/
theorem empty_terminalFiber_obstructs_path_extension
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (firstShadow : Shadow) (initialSegment suffix : List Shadow)
    (hempty : terminalFiber states shadow edge
      (firstShadow :: initialSegment) = ∅) :
    terminalFiber states shadow edge
      (firstShadow :: (initialSegment ++ suffix)) = ∅ := by
  rw [terminalFiber_cons_append, hempty, reachableAfter_empty]

/-- The same certificate stated semantically: an empty exact prefix frontier
rules out a lift of every longer shadow path with that prefix. -/
theorem empty_terminalFiber_gives_no_extendedLift
    (states : Finset Exact) (shadow : Exact → Shadow)
    (edge : Exact → Exact → Prop) [DecidableRel edge]
    (firstShadow : Shadow) (initialSegment suffix : List Shadow)
    (hempty : terminalFiber states shadow edge
      (firstShadow :: initialSegment) = ∅) :
    ¬LiftsShadowPath states shadow edge
      (firstShadow :: (initialSegment ++ suffix)) := by
  rw [← terminalFiber_eq_empty_iff_not_liftsShadowPath]
  exact empty_terminalFiber_obstructs_path_extension
    states shadow edge firstShadow initialSegment suffix hempty

end Computable

/-! ## Logical transport and a sharp compatibility warning -/

/-- Strengthening every exact edge transports endpoint-sensitive lifts. -/
theorem FollowsTo.mono
    {states : Finset Exact} {shadow : Exact → Shadow}
    {edge accepted : Exact → Exact → Prop}
    (hsound : ∀ source target, edge source target → accepted source target)
    {source terminal : Exact} {rest : List Shadow}
    (hfollow : FollowsTo states shadow edge source rest terminal) :
    FollowsTo states shadow accepted source rest terminal := by
  induction rest generalizing source with
  | nil => exact hfollow
  | cons nextShadow rest ih =>
      obtain ⟨next, hstates, hedge, hshadow, hrest⟩ := hfollow
      exact ⟨next, hstates, hsound source next hedge, hshadow, ih hrest⟩

/-- A lift through a certified finite edge table is a lift through the
semantic edge relation itself. -/
theorem LiftsShadowPath.mono
    {states : Finset Exact} {shadow : Exact → Shadow}
    {edge accepted : Exact → Exact → Prop}
    (hsound : ∀ source target, edge source target → accepted source target)
    {path : List Shadow}
    (hlift : LiftsShadowPath states shadow edge path) :
    LiftsShadowPath states shadow accepted path := by
  cases path with
  | nil => exact hlift
  | cons firstShadow rest =>
      obtain ⟨source, hsource, hshadow, terminal, hfollow⟩ := hlift
      exact ⟨source, hsource, hshadow, terminal, hfollow.mono hsound⟩

/-- Literal specialization: a shadow lift through a sound finite table
really does lift through positive first-passage recharge edges. -/
theorem certifiedLift_gives_literalRechargeLift
    {states : Finset ℕ} {shadow : ℕ → Shadow}
    {edge : ℕ → ℕ → Prop}
    (hsound : ∀ source target, edge source target →
      RechargeEdge source target)
    {path : List Shadow}
    (hlift : LiftsShadowPath states shadow edge path) :
    LiftsShadowPath states shadow RechargeEdge path :=
  hlift.mono hsound

/-- Every raw fiber of `id : Bool → Bool` is nonempty. -/
theorem bool_identity_rawFiber_nonempty (shadowState : Bool) :
    (Finset.univ.filter fun exactState : Bool =>
      exactState = shadowState).Nonempty := by
  exact ⟨shadowState, by simp⟩

/-- Nevertheless the shadow step `false → true` has no lift when the exact
edge relation permits only equality.  Pointwise fiber nonemptiness therefore
does not imply pathwise compatibility. -/
theorem bool_nonempty_rawFibers_but_no_compatibleLift :
    (∀ shadowState : Bool,
      (Finset.univ.filter fun exactState : Bool =>
        exactState = shadowState).Nonempty) ∧
    ¬LiftsShadowPath (Finset.univ : Finset Bool) id (· = ·)
      [false, true] := by
  constructor
  · exact bool_identity_rawFiber_nonempty
  · simp [LiftsShadowPath, FollowsTo]

end OutwardShadowPathLift
end KontoroC

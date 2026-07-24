/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardResourceConeNoGo
import KontoroC.OutwardRechargeSemilinearOrder

/-!
# Exact path-drift certificates for first-passage quotients

A finite symbolic recharge graph can support an infinite walk only after it
forgets the unbounded ordinary boundary charge: if every symbolic state has
one literal charge and every graph edge is a sound positive recharge, then
charge rises by at least one per edge and no nonempty closed walk exists.

For a genuinely quotient-valued graph, the missing information can instead
be carried by an integer or rational edge cocycle.  The exact Bellman
inequality below is a small kernel-checkable certificate: a bounded vertex
potential and a positive edge margin force the accumulated cocycle to grow
linearly along every finite walk.  On a closed walk the potential cancels
exactly, so every directed cycle has positive total drift.

These results are deliberately conditional.  A finite search must still
prove that its quotient edges lift coherently to one ordinary first-passage
execution and that its chosen cocycle measures the intended ordinary
counter.  Neither fact follows from a positive-cycle calculation alone.
-/

namespace KontoroC
namespace OutwardRechargeDriftCertificate

open OutwardFiniteStateKraftGap OutwardResourceConeNoGo
  OutwardDirectedPathExpansion
open OutwardResourceConeNoGo.FirstPassageGrammar

variable {State Edge : Type*}
variable [Fintype State] [Fintype Edge]

namespace FirstPassageGrammar

/-- Exact rational Bellman inequalities telescope along every composable
finite walk.  The orientation is chosen so that positive `score` means
outward drift. -/
theorem EdgeWalk.bellman_score_lower_bound
    (G : FirstPassageGrammar State Edge)
    (potential : State → ℚ) (score : Edge → ℚ) (margin : ℚ)
    (hedge : ∀ e,
      margin ≤ score e + potential (G.target e) - potential (G.source e))
    {i j : State} {edges : List Edge} (walk : EdgeWalk G i j edges) :
    margin * edges.length + potential i - potential j ≤
      (edges.map score).sum := by
  induction walk with
  | nil i => simp
  | @cons i j e edges hsource tail ih =>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, List.sum_cons]
      have he := hedge e
      rw [hsource] at he
      linarith

/-- If the Bellman potential is uniformly bounded by `bound`, endpoint
effects cost at most `2 * bound`; the remaining drift is linear in path
length. -/
theorem EdgeWalk.bellman_boundedPotential_lower_bound
    (G : FirstPassageGrammar State Edge)
    (potential : State → ℚ) (score : Edge → ℚ)
    (margin bound : ℚ)
    (hedge : ∀ e,
      margin ≤ score e + potential (G.target e) - potential (G.source e))
    (hbound : ∀ v, |potential v| ≤ bound)
    {i j : State} {edges : List Edge} (walk : EdgeWalk G i j edges) :
    margin * edges.length - 2 * bound ≤ (edges.map score).sum := by
  have hpath :=
    OutwardRechargeDriftCertificate.FirstPassageGrammar.EdgeWalk.bellman_score_lower_bound
      G potential score margin hedge walk
  have hiLower : -bound ≤ potential i :=
    (neg_le_of_abs_le (hbound i))
  have hjUpper : potential j ≤ bound :=
    (le_of_abs_le (hbound j))
  linarith

/-- On a closed walk the potential cancels, so no global potential bound is
needed. -/
theorem EdgeWalk.closed_bellman_score_lower_bound
    (G : FirstPassageGrammar State Edge)
    (potential : State → ℚ) (score : Edge → ℚ) (margin : ℚ)
    (hedge : ∀ e,
      margin ≤ score e + potential (G.target e) - potential (G.source e))
    {i : State} {edges : List Edge} (walk : EdgeWalk G i i edges) :
    margin * edges.length ≤ (edges.map score).sum := by
  simpa using
    (OutwardRechargeDriftCertificate.FirstPassageGrammar.EdgeWalk.bellman_score_lower_bound
      G potential score margin hedge walk)

/-- A strictly positive Bellman margin certifies strictly positive total
score on every nonempty closed walk. -/
theorem EdgeWalk.closed_score_pos_of_bellman
    (G : FirstPassageGrammar State Edge)
    (potential : State → ℚ) (score : Edge → ℚ) (margin : ℚ)
    (hmargin : 0 < margin)
    (hedge : ∀ e,
      margin ≤ score e + potential (G.target e) - potential (G.source e))
    {i : State} {edges : List Edge} (hne : edges ≠ [])
    (walk : EdgeWalk G i i edges) :
    0 < (edges.map score).sum := by
  have hlower :=
    OutwardRechargeDriftCertificate.FirstPassageGrammar.EdgeWalk.closed_bellman_score_lower_bound
      G potential score margin hedge walk
  have hlength : 0 < (edges.length : ℚ) := by
    exact_mod_cast (List.length_pos_iff.mpr hne)
  have hproduct : 0 < margin * (edges.length : ℚ) :=
    mul_pos hmargin hlength
  exact lt_of_lt_of_le hproduct hlower

/-! ## Literal ordinary-charge faithfulness -/

/-- Every edge of the finite grammar is sound for one literal assignment of
ordinary boundary charges. -/
def LiteralRechargeSound
    (G : FirstPassageGrammar State Edge) (charge : State → ℕ) : Prop :=
  ∀ e, RechargeEdge (charge (G.source e)) (charge (G.target e))

/-- A literally charge-faithful finite walk escapes by at least one ordinary
boundary-charge unit per edge. -/
theorem EdgeWalk.literalCharge_linear_escape
    (G : FirstPassageGrammar State Edge) (charge : State → ℕ)
    (hsound : LiteralRechargeSound G charge)
    {i j : State} {edges : List Edge} (walk : EdgeWalk G i j edges) :
    charge i + edges.length ≤ charge j := by
  induction walk with
  | nil i => simp
  | @cons i j e edges hsource tail ih =>
      have hstep : charge i < charge (G.target e) := by
        have := (hsound e).lt
        simpa [hsource] using this
      simp only [List.length_cons]
      omega

/-- Therefore a finite graph with one literal ordinary charge attached to
each state has no nonempty closed recharge walk.  Any recurrent finite
quotient must forget charge and separately certify an unbounded lift. -/
theorem no_nonempty_closedWalk_of_literalRechargeSound
    (G : FirstPassageGrammar State Edge) (charge : State → ℕ)
    (hsound : LiteralRechargeSound G charge)
    {i : State} {edges : List Edge} (hne : edges ≠ []) :
    ¬ EdgeWalk G i i edges := by
  intro walk
  have hescape :=
    OutwardRechargeDriftCertificate.FirstPassageGrammar.EdgeWalk.literalCharge_linear_escape
      G charge hsound walk
  have hlength : 0 < edges.length := List.length_pos_iff.mpr hne
  omega

/-- Strong finite-state architecture no-go: there is no infinite edge path
in a finite grammar when every symbolic state has one fixed literal charge
and every edge is a sound positive recharge.  A recurrent abstraction must
therefore represent the ordinary charge in an unbounded lift (or make the
charge assignment state-dependent in some richer sense). -/
theorem no_infinitePath_of_literalRechargeSound
    [DecidableEq State]
    (G : FirstPassageGrammar State Edge) (charge : State → ℕ)
    (hsound : LiteralRechargeSound G charge)
    (state : ℕ → State) (edge : ℕ → Edge)
    (hsource : ∀ n, G.source (edge n) = state n)
    (htarget : ∀ n, G.target (edge n) = state (n + 1)) :
    False := by
  have hstep : ∀ n, charge (state n) < charge (state (n + 1)) := by
    intro n
    have h := (hsound (edge n)).lt
    simpa [hsource n, htarget n] using h
  have hlinear : ∀ n, charge (state 0) + n ≤ charge (state n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hn := hstep n
        omega
  let bound : ℕ := ∑ s : State, charge s
  have hupper : ∀ n, charge (state n) ≤ bound := by
    intro n
    exact Finset.single_le_sum
      (fun s _ ↦ Nat.zero_le (charge s)) (Finset.mem_univ (state n))
  have hlower := hlinear (bound + 1)
  have hbounded := hupper (bound + 1)
  omega

end FirstPassageGrammar

end OutwardRechargeDriftCertificate
end KontoroC

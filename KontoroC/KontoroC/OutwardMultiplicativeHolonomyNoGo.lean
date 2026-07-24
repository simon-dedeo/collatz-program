/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardPositiveCycleSemanticGap

/-!
# Exact multiplicative holonomy for finite first-passage grammars

Suppose an edge ratio is only a change of finite-state gauge,

`ratio(e) = potential(target(e)) / potential(source(e))`.

Along every composable walk the internal vertex factors cancel.  On a closed
walk the product is exactly one.  Therefore a nontrivial closed-walk product
is a finite certificate that no such vertex potential exists.

This is useful both positively and adversarially.  Holonomy can detect failed
gluing of local charts, but a ratio which is a pure finite-state gauge cannot
also carry positive recurrent drift.  Conversely, nontrivial holonomy is not
itself a literal recharge orbit or an ordinary counter: those semantic lifts
remain separate obligations.
-/

namespace KontoroC
namespace OutwardMultiplicativeHolonomyNoGo

open OutwardFiniteStateKraftGap OutwardResourceConeNoGo
open OutwardResourceConeNoGo.FirstPassageGrammar

variable {State Edge A : Type*}
variable [Fintype State] [Fintype Edge] [CommGroup A]

namespace FirstPassageGrammar

/-- An edge ratio is a pure multiplicative gauge when it is the quotient of
one vertex potential at the target and source. -/
def IsMultiplicativeGauge
    (G : FirstPassageGrammar State Edge) (ratio : Edge → A) : Prop :=
  ∃ potential : State → A, ∀ e,
    ratio e = potential (G.target e) / potential (G.source e)

/-- Multiplicative gauge factors telescope along every composable walk. -/
theorem EdgeWalk.gauge_product
    (G : FirstPassageGrammar State Edge)
    (ratio : Edge → A) (potential : State → A)
    (hgauge : ∀ e,
      ratio e = potential (G.target e) / potential (G.source e))
    {i j : State} {edges : List Edge}
    (walk : EdgeWalk G i j edges) :
    (edges.map ratio).prod = potential j / potential i := by
  induction walk with
  | nil i => simp
  | @cons i j e edges hsource tail ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [hgauge e, ih, hsource]
      simp only [div_eq_mul_inv]
      calc
        (potential (G.target e) * (potential i)⁻¹) *
            (potential j * (potential (G.target e))⁻¹) =
            (potential (G.target e) *
              (potential (G.target e))⁻¹) *
              (potential j * (potential i)⁻¹) := by ac_rfl
        _ = potential j * (potential i)⁻¹ := by simp

/-- In particular, every pure-gauge product around a closed walk is one. -/
theorem EdgeWalk.closed_gauge_product_eq_one
    (G : FirstPassageGrammar State Edge)
    (ratio : Edge → A) (potential : State → A)
    (hgauge : ∀ e,
      ratio e = potential (G.target e) / potential (G.source e))
    {i : State} {edges : List Edge}
    (walk : EdgeWalk G i i edges) :
    (edges.map ratio).prod = 1 := by
  simpa using
    (OutwardMultiplicativeHolonomyNoGo.FirstPassageGrammar.EdgeWalk.gauge_product
      G ratio potential hgauge walk)

/-- Existential gauge form used by finite chart checkers. -/
theorem closed_product_eq_one_of_isMultiplicativeGauge
    (G : FirstPassageGrammar State Edge) (ratio : Edge → A)
    (hgauge : IsMultiplicativeGauge G ratio)
    {i : State} {edges : List Edge}
    (walk : EdgeWalk G i i edges) :
    (edges.map ratio).prod = 1 := by
  obtain ⟨potential, hpotential⟩ := hgauge
  exact
    OutwardMultiplicativeHolonomyNoGo.FirstPassageGrammar.EdgeWalk.closed_gauge_product_eq_one
      G ratio potential hpotential walk

/-- A single nontrivial closed-walk product rules out every vertex-potential
representation of the edge ratios. -/
theorem nontrivialHolonomy_not_multiplicativeGauge
    (G : FirstPassageGrammar State Edge) (ratio : Edge → A)
    {i : State} {edges : List Edge}
    (walk : EdgeWalk G i i edges)
    (hne : (edges.map ratio).prod ≠ 1) :
    ¬ IsMultiplicativeGauge G ratio := by
  intro hgauge
  exact hne (closed_product_eq_one_of_isMultiplicativeGauge
    G ratio hgauge walk)

/-- Balance-equation input form: a checker may avoid division and certify
`ratio(e) * potential(source(e)) = potential(target(e))` instead. -/
theorem closed_product_eq_one_of_edge_balance
    (G : FirstPassageGrammar State Edge)
    (ratio : Edge → A) (potential : State → A)
    (hbalance : ∀ e,
      ratio e * potential (G.source e) = potential (G.target e))
    {i : State} {edges : List Edge}
    (walk : EdgeWalk G i i edges) :
    (edges.map ratio).prod = 1 := by
  refine
    OutwardMultiplicativeHolonomyNoGo.FirstPassageGrammar.EdgeWalk.closed_gauge_product_eq_one
      G ratio potential ?_ walk
  intro e
  calc
    ratio e =
        (ratio e * potential (G.source e)) *
          (potential (G.source e))⁻¹ := by group
    _ = potential (G.target e) * (potential (G.source e))⁻¹ := by
      rw [hbalance e]
    _ = potential (G.target e) / potential (G.source e) := by
      rw [div_eq_mul_inv]

end FirstPassageGrammar

end OutwardMultiplicativeHolonomyNoGo
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ComponentHolonomyBar

/-!
# The ordinary/condensed boundary of a holonomy bar

Condensed mathematics does not turn a compatible profinite point into an
ordinary integer.  Its useful first role here is diagnostic: it distinguishes
the discrete ordinary locus from its compact `2`-adic ambient space.

At the elementary level needed by the holonomy-bar program, that distinction
has a sharp consequence.  Every collision shadow is a clopen binary cylinder,
but a bar of all ordinary naturals above `1` can have no bounded cylinder
width.  Indeed, the ordinary points `1 + 2^W` approach `1` `2`-adically, while
no valid descent shadow can contain `1`.

Thus compactness cannot replace the productive-bar theorem by a finite
subcover.  The correct object is an increasing family of finite ordinary
stages with unbounded binary resolution.  All statements in this file are
ordinary set-level theorems; no condensed-mathematics library is assumed.
-/

namespace KontoroC
namespace ComponentHolonomyCondensedBoundary

open ComponentHolonomyBar

/-- A holonomy family bars the finite ordinary stage through `bound`. -/
def BarsThrough {ι : Type} (shadow : ι → CollisionShadow) (bound : ℕ) : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ bound → ∃ a : ι, (shadow a).Covers n

/-- The ordinary bar is exactly the compatible collection of all bounded
ordinary stages.  This is the elementary ind-finite interface suggested by
the condensed viewpoint. -/
theorem ordinaryHolonomyBar_iff_barsThrough {ι : Type}
    (shadow : ι → CollisionShadow) :
    OrdinaryHolonomyBar shadow ↔ ∀ bound : ℕ, BarsThrough shadow bound := by
  constructor
  · intro hbar bound n hn _
    exact hbar n hn
  · intro hstages n hn
    exact hstages n n hn (by omega)

/-- A genuine descent cylinder can never contain the component minimum `1`. -/
theorem CollisionShadow.not_covers_one (s : CollisionShadow) :
    ¬ s.Covers 1 := by
  intro hcover
  obtain ⟨x, hx, hlt, _⟩ := s.descent hcover
  omega

/-- If a width-`w` cylinder contains `1 + 2^W` with `w ≤ W`, it also contains
`1`.  This is the exact finite congruence behind the `2`-adic convergence
`1 + 2^W → 1`. -/
theorem CollisionShadow.covers_one_of_covers_one_add_pow
    (s : CollisionShadow) {W : ℕ} (hwidth : s.width ≤ W)
    (hcover : s.Covers (1 + 2 ^ W)) :
    s.Covers 1 := by
  have hdvd : 2 ^ s.width ∣ 2 ^ W := pow_dvd_pow 2 hwidth
  have hpowMod : 2 ^ W % 2 ^ s.width = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hsame :
      (1 + 2 ^ W) % 2 ^ s.width = 1 % 2 ^ s.width := by
    calc
      (1 + 2 ^ W) % 2 ^ s.width =
          (1 % 2 ^ s.width + 2 ^ W % 2 ^ s.width) % 2 ^ s.width := by
            rw [Nat.add_mod]
      _ = 1 % 2 ^ s.width := by simp [hpowMod]
  unfold CollisionShadow.Covers at hcover ⊢
  rw [← hsame]
  exact hcover

/-- Every ordinary holonomy bar uses arbitrarily deep binary cylinders.

This rules out a finite or bounded-precision compactness proof before any
particular shadow grammar is considered. -/
theorem unbounded_width_of_ordinaryHolonomyBar {ι : Type}
    (shadow : ι → CollisionShadow)
    (hbar : OrdinaryHolonomyBar shadow) :
    ∀ W : ℕ, ∃ a : ι, W < (shadow a).width := by
  intro W
  have hpowPos : 0 < 2 ^ W := by positivity
  have hn : 1 < 1 + 2 ^ W := by omega
  obtain ⟨a, ha⟩ := hbar (1 + 2 ^ W) hn
  refine ⟨a, ?_⟩
  by_contra hnot
  have hwidth : (shadow a).width ≤ W := by omega
  exact CollisionShadow.not_covers_one (shadow a)
    (CollisionShadow.covers_one_of_covers_one_add_pow (shadow a) hwidth ha)

/-- In particular, no family indexed by a finite type can be an ordinary
holonomy bar. -/
theorem no_finite_ordinaryHolonomyBar
    {ι : Type} [Finite ι] (shadow : ι → CollisionShadow) :
    ¬ OrdinaryHolonomyBar shadow := by
  classical
  letI := Fintype.ofFinite ι
  intro hbar
  let W := ∑ a : ι, (shadow a).width
  obtain ⟨a, ha⟩ := unbounded_width_of_ordinaryHolonomyBar shadow hbar W
  have hle : (shadow a).width ≤ W := by
    dsimp [W]
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le (shadow i).width) (Finset.mem_univ a)
  omega

end ComponentHolonomyCondensedBoundary
end KontoroC

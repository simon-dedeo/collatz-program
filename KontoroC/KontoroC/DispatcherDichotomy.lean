/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineQuotientNoGo

/-!
# Stable address versus changing affine level

This file combines two architecture-level obstructions.  Suppose an infinite
positive dispatcher has a nondecreasing charge level.  A strict level change
must visibly advance its canonical address, while an address coming from one
ordinary natural is eventually constant.  The level therefore eventually
freezes.  If every cell at level `m` obeys the fixed-form affine charge law,
the frozen tail is an impossible `PositiveAffineGainOrbit`.

The hypotheses are intentionally explicit.  Applying the theorem to a
concrete register construction requires proving that defect cells obey the
same one-cell law, that level never decreases, and that every strict level
change advances the ordinary address.
-/

namespace KontoroC

/-- Abstract semantic interface for the fixed-form charge dispatcher. -/
structure MonotoneFixedFormDispatcher where
  /-- Current charge/refinement level. -/
  level : ℕ → ℕ
  /-- Canonical finite address presented at each time. -/
  address : ℕ → ℕ
  /-- Positive quotient/charge state. -/
  value : ℕ → ℕ
  level_mono : Monotone level
  address_eventually_constant :
    ∃ K, ∀ t, K ≤ t → address t = address K
  level_step_forces_address_step :
    ∀ t, level t < level (t + 1) → address t < address (t + 1)
  value_pos : ∀ t, 0 < value t
  balance : ∀ t,
    2 ^ (154 + 23 * level t) * value (t + 1) =
      3 ^ (114 + 17 * level t) * value t +
        PositiveAffineGainOrbit.fixedFormGain (level t)

namespace MonotoneFixedFormDispatcher

/-- Once the ordinary address has stabilized, monotonicity prevents any
further increase of the charge level. -/
theorem level_step_eq_of_address_stable (d : MonotoneFixedFormDispatcher)
    {K t : ℕ} (hstable : ∀ u, K ≤ u → d.address u = d.address K)
    (ht : K ≤ t) :
    d.level (t + 1) = d.level t := by
  have hle : d.level t ≤ d.level (t + 1) := d.level_mono (by omega)
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : d.level t < d.level (t + 1) := by omega
    have ha := d.level_step_forces_address_step t hlt
    rw [hstable t ht, hstable (t + 1) (by omega)] at ha
    exact (Nat.lt_irrefl _ ha)
  · exact hle

/-- An eventually stable ordinary address forces the nondecreasing level to
be eventually constant as well. -/
theorem level_eventually_constant (d : MonotoneFixedFormDispatcher) :
    ∃ K, ∀ t, K ≤ t → d.level t = d.level K := by
  obtain ⟨K, hstable⟩ := d.address_eventually_constant
  refine ⟨K, ?_⟩
  intro t ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        d.level (K + (r + 1)) = d.level ((K + r) + 1) := by
          congr 1
        _ = d.level (K + r) :=
          d.level_step_eq_of_address_stable hstable (by omega)
        _ = d.level K := ih (by omega)

/-- The stable tail is exactly a positive orbit of one fixed affine law. -/
noncomputable def toFixedTailOrbit (d : MonotoneFixedFormDispatcher) :
    PositiveAffineGainOrbit
      (3 ^ (114 + 17 * d.level d.level_eventually_constant.choose))
      (2 ^ (154 + 23 * d.level d.level_eventually_constant.choose))
      (PositiveAffineGainOrbit.fixedFormGain
        (d.level d.level_eventually_constant.choose)) := by
  let K := d.level_eventually_constant.choose
  let m := d.level K
  have hlevel : ∀ t, K ≤ t → d.level t = m := by
    intro t ht
    exact d.level_eventually_constant.choose_spec t ht
  exact {
    value := fun t => d.value (K + t)
    value_pos := fun t => d.value_pos (K + t)
    balance := fun t => by
      have hb := d.balance (K + t)
      rw [hlevel (K + t) (by omega)] at hb
      simpa [K, m, Nat.add_assoc] using hb
  }

/-- No positive infinite dispatcher can simultaneously have stable ordinary
addresses, monotone visible levels, and the fixed-form affine cell law. -/
theorem impossible (d : MonotoneFixedFormDispatcher) : False := by
  let m := d.level d.level_eventually_constant.choose
  exact (PositiveAffineGainOrbit.no_fixedFormCharge_orbit m)
    ⟨d.toFixedTailOrbit⟩

theorem no_dispatcher : ¬ Nonempty MonotoneFixedFormDispatcher := by
  rintro ⟨d⟩
  exact d.impossible

end MonotoneFixedFormDispatcher

end KontoroC

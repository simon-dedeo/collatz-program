/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardResourceMinimumCompactness

/-!
# Exact dynamics of the mixed two-three resource

The coercive resource `R23` is unchanged by the forced shortcut step from an
odd natural.  This explains the forced-prehistory quotient used by the exact
resource-sublevel census; it does not assert that the resource is bounded on
an infinite first-passage execution.
-/

namespace KontoroC
namespace OutwardMixedResourceDynamics

open OutwardResourceMinimumCompactness

/-- Removing powers of two commutes with multiplication by three. -/
theorem divMaxPow_two_three_mul (t : ℕ) :
    (3 * t).divMaxPow 2 = 3 * t.divMaxPow 2 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hthree : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hval : padicValNat 2 (3 * t) = padicValNat 2 t := by
    rw [padicValNat.mul (by norm_num) ht, hthree, zero_add]
  have hleft := Nat.pow_padicValNat_mul_divMaxPow 2 (3 * t)
  have hright := Nat.pow_padicValNat_mul_divMaxPow 2 t
  rw [hval] at hleft
  have hscale :
      2 ^ padicValNat 2 t * (3 * t.divMaxPow 2) = 3 * t := by
    calc
      2 ^ padicValNat 2 t * (3 * t.divMaxPow 2) =
          3 * (2 ^ padicValNat 2 t * t.divMaxPow 2) := by ring
      _ = 3 * t := by rw [hright]
  exact Nat.eq_of_mul_eq_mul_left (by positivity)
    (hleft.trans hscale.symm)

/-- Exact arithmetic of one odd shortcut step in shifted coordinates. -/
theorem odd_shortcut_add_one {n : ℕ} (hn : Odd n) :
    (3 * n + 1) / 2 + 1 = 3 * ((n + 1) / 2) := by
  rcases hn with ⟨k, hk⟩
  omega

/-- QM173e: `R23` is an exact isometry under the forced odd shortcut step. -/
theorem mixedBaseResource_odd_shortcut {n : ℕ} (hn : Odd n) :
    mixedBaseResource ((3 * n + 1) / 2) = mixedBaseResource n := by
  let t := (n + 1) / 2
  have htpos : 0 < t := by
    rcases hn with ⟨k, hk⟩
    dsimp [t]
    omega
  have hnadd : n + 1 = 2 * t := by
    dsimp [t]
    exact (Nat.two_mul_div_two_of_even hn.add_one).symm
  have hmadd : (3 * n + 1) / 2 + 1 = 3 * t := by
    simpa [t] using odd_shortcut_add_one hn
  have htwoN : mixedBaseTwoExponent n = padicValNat 2 t + 1 := by
    rw [mixedBaseTwoExponent, hnadd]
    exact padicValNat_base_mul (p := 2) (by omega) htpos.ne'
  have hafterN : mixedBaseAfterTwo n = t.divMaxPow 2 := by
    simp [mixedBaseAfterTwo, hnadd, Nat.divMaxPow_base_mul]
  have htwoM : mixedBaseTwoExponent ((3 * n + 1) / 2) = padicValNat 2 t := by
    rw [mixedBaseTwoExponent, hmadd]
    have hthree : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by norm_num)
    rw [padicValNat.mul (by norm_num) htpos.ne', hthree, zero_add]
  have hafterM : mixedBaseAfterTwo ((3 * n + 1) / 2) =
      3 * t.divMaxPow 2 := by
    rw [mixedBaseAfterTwo, hmadd]
    exact divMaxPow_two_three_mul t
  have hthreeM : mixedBaseThreeExponent ((3 * n + 1) / 2) =
      mixedBaseThreeExponent n + 1 := by
    rw [mixedBaseThreeExponent, hafterM, mixedBaseThreeExponent, hafterN]
    exact padicValNat_base_mul (by omega) (by
      have := Nat.divMaxPow_mul_pow_padicValNat 2 t
      intro hzero
      rw [hzero, zero_mul] at this
      omega)
  have hunitM : mixedBaseUnit ((3 * n + 1) / 2) = mixedBaseUnit n := by
    rw [mixedBaseUnit, hafterM, mixedBaseUnit, hafterN]
    exact Nat.divMaxPow_base_mul (by norm_num) _
  simp only [mixedBaseResource]
  rw [htwoN, htwoM, hthreeM, hunitM]
  omega

/-! ## Forced all-odd prehistory -/

/-- The shifted seed used by the exact forced-prehistory quotient. -/
def forcedPrehistorySeed (a b u : ℕ) : ℕ :=
  2 ^ a * 3 ^ b * u - 1

theorem forcedPrehistorySeed_succ_odd {a b u : ℕ} (hu : 0 < u) :
    Odd (forcedPrehistorySeed (a + 1) b u) := by
  let A := 2 ^ a * 3 ^ b * u
  have hpos : 0 < A := by positivity
  have hform : forcedPrehistorySeed (a + 1) b u = 2 * A - 1 := by
    simp only [forcedPrehistorySeed, pow_succ]
    dsimp [A]
    ring_nf
  rw [hform]
  refine ⟨A - 1, ?_⟩
  omega

/-- One forced odd shortcut transfers one two-adic exponent into one
three-adic exponent. -/
theorem forcedPrehistorySeed_succ_shortcut {a b u : ℕ} (hu : 0 < u) :
    (3 * forcedPrehistorySeed (a + 1) b u + 1) / 2 =
      forcedPrehistorySeed a (b + 1) u := by
  let A := 2 ^ a * 3 ^ b * u
  have hpos : 0 < A := by positivity
  have hsource : forcedPrehistorySeed (a + 1) b u = 2 * A - 1 := by
    simp only [forcedPrehistorySeed, pow_succ]
    dsimp [A]
    ring_nf
  have htarget : forcedPrehistorySeed a (b + 1) u = 3 * A - 1 := by
    simp only [forcedPrehistorySeed, pow_succ]
    dsimp [A]
    ring_nf
  rw [hsource, htarget]
  omega

/-- The whole forced all-odd prehistory preserves `R23`: the powers of two
are transferred exactly into powers of three. -/
theorem mixedBaseResource_forcedPrehistory {a b u : ℕ} (hu : 0 < u) :
    mixedBaseResource (forcedPrehistorySeed a b u) =
      mixedBaseResource (forcedPrehistorySeed 0 (a + b) u) := by
  induction a generalizing b with
  | zero => simp [forcedPrehistorySeed]
  | succ a ih =>
      have hodd := forcedPrehistorySeed_succ_odd (a := a) (b := b) hu
      have hstep := mixedBaseResource_odd_shortcut hodd
      rw [forcedPrehistorySeed_succ_shortcut hu] at hstep
      calc
        mixedBaseResource (forcedPrehistorySeed (a + 1) b u) =
            mixedBaseResource (forcedPrehistorySeed a (b + 1) u) := hstep.symm
        _ = mixedBaseResource (forcedPrehistorySeed 0 (a + (b + 1)) u) :=
          ih (b := b + 1)
        _ = mixedBaseResource (forcedPrehistorySeed 0 (a + 1 + b) u) := by
          rw [show a + (b + 1) = a + 1 + b by omega]

/-- Literal arithmetic form of the worker's forced-prehistory quotient. -/
theorem oddShortcut_iterate_forcedPrehistory {a b u : ℕ} (hu : 0 < u) :
    (fun n : ℕ ↦ (3 * n + 1) / 2)^[a] (forcedPrehistorySeed a b u) =
      forcedPrehistorySeed 0 (a + b) u := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      rw [forcedPrehistorySeed_succ_shortcut hu]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (b := b + 1)

theorem mixedBaseResource_forcedPrehistory_display
    {a b u : ℕ} (hu : 0 < u) :
    mixedBaseResource (2 ^ a * 3 ^ b * u - 1) =
      mixedBaseResource (3 ^ (a + b) * u - 1) := by
  simpa [forcedPrehistorySeed] using
    mixedBaseResource_forcedPrehistory (a := a) (b := b) hu

end OutwardMixedResourceDynamics
end KontoroC

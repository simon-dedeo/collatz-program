/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLRechargeLedger
import Mathlib.Data.Int.GCD

/-!
# Universal finite depth of a signed Syracuse shadow

Two shortcut Syracuse trajectories with the same branch choice obey a
linear difference cocycle: an even source multiplies their difference by
`1/2`, and an odd source by `3/2`.  This file isolates that arithmetic from
the particular presentation of the signed map.

The consequence is controller-independent.  Sharing `N` branch choices
forces the initial difference to be divisible by `2^N`; distinct ordinary
integers can therefore share only finitely many choices.  The controller may
be periodic, aperiodic, positive, or negative.
-/

namespace KontoroC
namespace KLUniversalShadow

/-- Number of odd-branch labels in the first `N` positions. -/
def oddCount (eps : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => oddCount eps N + if eps N then 1 else 0

@[simp] theorem oddCount_zero (eps : ℕ → Bool) : oddCount eps 0 = 0 := rfl

@[simp] theorem oddCount_succ (eps : ℕ → Bool) (N : ℕ) :
    oddCount eps (N + 1) =
      oddCount eps N + if eps N then 1 else 0 := rfl

/-- Abstract form of two trajectories following the same shortcut branch.
The bit is `true` on an odd branch. -/
structure DifferenceCocycle where
  x : ℕ → ℤ
  y : ℕ → ℤ
  eps : ℕ → Bool
  step : ∀ j,
    2 * (x (j + 1) - y (j + 1)) =
      (if eps j then 3 else 1) * (x j - y j)

namespace DifferenceCocycle

/-- QM132a: exact finite difference cocycle. -/
theorem exact (C : DifferenceCocycle) (N : ℕ) :
    (2 : ℤ) ^ N * (C.x N - C.y N) =
      (3 : ℤ) ^ oddCount C.eps N * (C.x 0 - C.y 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := C.step N
      by_cases heps : C.eps N = true
      · simp [heps] at hs
        rw [show N + 1 = N.succ by omega, pow_succ]
        simp only [oddCount_succ, heps, Bool.true_eq, if_true, pow_succ]
        calc
          (2 : ℤ) ^ N * 2 * (C.x (N + 1) - C.y (N + 1)) =
              (2 : ℤ) ^ N *
                (2 * (C.x (N + 1) - C.y (N + 1))) := by ring
          _ = (2 : ℤ) ^ N * (3 * (C.x N - C.y N)) := by rw [hs]
          _ = 3 * ((2 : ℤ) ^ N * (C.x N - C.y N)) := by ring
          _ = 3 * ((3 : ℤ) ^ oddCount C.eps N *
                (C.x 0 - C.y 0)) := by rw [ih]
          _ = (3 : ℤ) ^ oddCount C.eps N * 3 *
                (C.x 0 - C.y 0) := by ring
      · have hepsFalse : C.eps N = false := Bool.eq_false_of_not_eq_true heps
        simp [hepsFalse] at hs
        rw [show N + 1 = N.succ by omega, pow_succ]
        simp only [oddCount_succ, hepsFalse, Bool.false_eq, if_false, add_zero]
        calc
          (2 : ℤ) ^ N * 2 * (C.x (N + 1) - C.y (N + 1)) =
              (2 : ℤ) ^ N *
                (2 * (C.x (N + 1) - C.y (N + 1))) := by ring
          _ = (2 : ℤ) ^ N * (C.x N - C.y N) := by rw [hs]
          _ = (3 : ℤ) ^ oddCount C.eps N *
                (C.x 0 - C.y 0) := ih

/-- Natural absolute-value form of the exact cocycle. -/
theorem exact_natAbs (C : DifferenceCocycle) (N : ℕ) :
    2 ^ N * (C.x N - C.y N).natAbs =
      3 ^ oddCount C.eps N * (C.x 0 - C.y 0).natAbs := by
  have h := congrArg Int.natAbs (C.exact N)
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h

/-- QM132b: a shared branch itinerary of length `N` forces a fresh binary
cylinder of depth `N` at the initial state. -/
theorem two_pow_dvd_initial_difference_natAbs
    (C : DifferenceCocycle) (N : ℕ) :
    2 ^ N ∣ (C.x 0 - C.y 0).natAbs := by
  have hprod : 2 ^ N ∣
      3 ^ oddCount C.eps N * (C.x 0 - C.y 0).natAbs := by
    use (C.x N - C.y N).natAbs
    exact (C.exact_natAbs N).symm
  have hcop : Nat.Coprime (2 ^ N) (3 ^ oddCount C.eps N) :=
    Nat.coprime_pow_primes N (oddCount C.eps N)
      Nat.prime_two Nat.prime_three (by norm_num)
  exact hcop.dvd_of_dvd_mul_left hprod

theorem two_pow_dvd_initial_difference
    (C : DifferenceCocycle) (N : ℕ) :
    ((2 ^ N : ℕ) : ℤ) ∣ C.x 0 - C.y 0 := by
  rw [Int.natCast_dvd]
  exact C.two_pow_dvd_initial_difference_natAbs N

/-- QM132c: distinct initial states cannot share more branch choices than
their ordinary separation can pay for. -/
theorem two_pow_le_initial_distance (C : DifferenceCocycle) (N : ℕ)
    (hne : C.x 0 ≠ C.y 0) :
    2 ^ N ≤ (C.x 0 - C.y 0).natAbs := by
  apply Nat.le_of_dvd
  · exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  · exact C.two_pow_dvd_initial_difference_natAbs N

/-- No two distinct ordinary integers can satisfy one common infinite
shortcut branch schedule. -/
theorem initial_eq_of_infinite_shared_itinerary (C : DifferenceCocycle) :
    C.x 0 = C.y 0 := by
  by_contra hne
  let D := (C.x 0 - C.y 0).natAbs
  have hle := C.two_pow_le_initial_distance (D + 1) hne
  have hlt : D < 2 ^ (D + 1) := by
    exact D.lt_two_pow_self.trans
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self D))
  exact (not_lt_of_ge hle) hlt

end DifferenceCocycle

/-! ## Literal signed shortcut map -/

/-- Shortcut Syracuse map on all integers.  Exact division is automatic on
both parity branches. -/
def signedSyracuse (x : ℤ) : ℤ :=
  if Even x then x / 2 else (3 * x + 1) / 2

theorem signedSyracuse_difference_of_sameParity {x y : ℤ}
    (hsame : Even x ↔ Even y) :
    2 * (signedSyracuse x - signedSyracuse y) =
      (if Even x then 1 else 3) * (x - y) := by
  by_cases hx : Even x
  · have hy : Even y := hsame.mp hx
    rcases hx with ⟨kx, hkx⟩
    rcases hy with ⟨ky, hky⟩
    rw [hkx, hky]
    have hex : Even (kx + kx) := ⟨kx, rfl⟩
    have hey : Even (ky + ky) := ⟨ky, rfl⟩
    rw [signedSyracuse, if_pos hex, signedSyracuse, if_pos hey]
    have hkxdiv : (kx + kx) / 2 = kx := by
      rw [show kx + kx = 2 * kx by ring,
        Int.mul_ediv_cancel_left kx (by norm_num)]
    have hkydiv : (ky + ky) / 2 = ky := by
      rw [show ky + ky = 2 * ky by ring,
        Int.mul_ediv_cancel_left ky (by norm_num)]
    rw [hkxdiv, hkydiv]
    rw [if_pos hex]
    ring
  · have hy : ¬Even y := fun hey => hx (hsame.mpr hey)
    have hox : Odd x := Int.not_even_iff_odd.mp hx
    have hoy : Odd y := Int.not_even_iff_odd.mp hy
    rcases hox with ⟨kx, hkx⟩
    rcases hoy with ⟨ky, hky⟩
    rw [hkx, hky]
    have hox' : ¬Even (2 * kx + 1) := Int.not_even_two_mul_add_one kx
    have hoy' : ¬Even (2 * ky + 1) := Int.not_even_two_mul_add_one ky
    rw [signedSyracuse, if_neg hox', signedSyracuse, if_neg hoy']
    have hkxdiv : (3 * (2 * kx + 1) + 1) / 2 = 3 * kx + 2 := by
      rw [show 3 * (2 * kx + 1) + 1 = 2 * (3 * kx + 2) by ring,
        Int.mul_ediv_cancel_left (3 * kx + 2) (by norm_num)]
    have hkydiv : (3 * (2 * ky + 1) + 1) / 2 = 3 * ky + 2 := by
      rw [show 3 * (2 * ky + 1) + 1 = 2 * (3 * ky + 2) by ring,
        Int.mul_ediv_cancel_left (3 * ky + 2) (by norm_num)]
    rw [hkxdiv, hkydiv]
    rw [if_neg hox']
    ring

def signedOrbit (x : ℤ) (j : ℕ) : ℤ := signedSyracuse^[j] x

def signedBranchBit (x : ℤ) (j : ℕ) : Bool :=
  decide (¬Even (signedOrbit x j))

/-- A literal pair of signed Syracuse trajectories with a common infinite
parity itinerary supplies the abstract difference cocycle. -/
def signedOrbitCocycle (x y : ℤ)
    (hsame : ∀ j, Even (signedOrbit x j) ↔ Even (signedOrbit y j)) :
    DifferenceCocycle where
  x := signedOrbit x
  y := signedOrbit y
  eps := signedBranchBit x
  step := by
    intro j
    have hstep := signedSyracuse_difference_of_sameParity (hsame j)
    have hxiter : signedOrbit x (j + 1) =
        signedSyracuse (signedOrbit x j) := by
      simp [signedOrbit, Function.iterate_succ_apply']
    have hyiter : signedOrbit y (j + 1) =
        signedSyracuse (signedOrbit y j) := by
      simp [signedOrbit, Function.iterate_succ_apply']
    rw [hxiter, hyiter]
    rw [hstep]
    by_cases heven : Even (signedOrbit x j)
    · simp [signedBranchBit, heven]
    · simp [signedBranchBit, heven]

/-- Literal controller-independent endpoint: equal infinite shortcut parity
itineraries determine the initial integer uniquely. -/
theorem signed_initial_eq_of_sameParity (x y : ℤ)
    (hsame : ∀ j, Even (signedOrbit x j) ↔ Even (signedOrbit y j)) :
    x = y := by
  have h := (signedOrbitCocycle x y hsame).initial_eq_of_infinite_shared_itinerary
  change signedOrbit x 0 = signedOrbit y 0 at h
  simpa [signedOrbit] using h

/-! ## Converse: dyadic cylinders are exact

The divisibility obstruction above is sharp at every finite depth.  Two
integers congruent modulo `2^N` necessarily have the same first `N` branch
choices.  Thus finite signed shadows can always be manufactured; only a
single coherent infinite shadow is excluded by the preceding theorem.
-/

/-- One dyadic digit of agreement gives the same parity, and removing that
digit by one shortcut step leaves the remaining dyadic agreement. -/
theorem sameParity_and_next_dvd_of_two_pow_succ_dvd {x y : ℤ} {N : ℕ}
    (hdiv : (((2 ^ (N + 1) : ℕ) : ℤ)) ∣ x - y) :
    (Even x ↔ Even y) ∧
      (((2 ^ N : ℕ) : ℤ)) ∣ signedSyracuse x - signedSyracuse y := by
  rcases hdiv with ⟨t, ht⟩
  have htwo : Even (x - y) := by
    refine ⟨((2 : ℤ) ^ N) * t, ?_⟩
    rw [ht]
    push_cast
    rw [pow_succ]
    ring
  have hsame : Even x ↔ Even y := Int.even_sub.mp htwo
  refine ⟨hsame, ?_⟩
  use (if Even x then 1 else 3) * t
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  calc
    2 * (signedSyracuse x - signedSyracuse y) =
        (if Even x then 1 else 3) * (x - y) :=
      signedSyracuse_difference_of_sameParity hsame
    _ = (if Even x then 1 else 3) *
        (((2 : ℤ) ^ (N + 1)) * t) := by
      rw [ht]
      push_cast
      rfl
    _ = 2 * (((2 : ℤ) ^ N) *
        ((if Even x then 1 else 3) * t)) := by
      rw [pow_succ]
      ring

/-- Sufficiency direction: congruence modulo `2^N` fixes every one of the
first `N` shortcut parity labels. -/
theorem sameParity_of_two_pow_dvd (N : ℕ) (x y : ℤ)
    (hdiv : (((2 ^ N : ℕ) : ℤ)) ∣ x - y) :
    ∀ j < N, Even (signedOrbit x j) ↔ Even (signedOrbit y j) := by
  induction N generalizing x y with
  | zero => simp
  | succ N ih =>
      have hsplit :=
        sameParity_and_next_dvd_of_two_pow_succ_dvd (N := N) hdiv
      intro j hj
      cases j with
      | zero => simpa [signedOrbit] using hsplit.1
      | succ j =>
          have hjN : j < N := by omega
          have htail := ih (signedSyracuse x) (signedSyracuse y) hsplit.2 j hjN
          simpa [signedOrbit, Function.iterate_succ_apply] using htail

/-- Necessity direction, localized to a finite common itinerary. -/
theorem two_pow_dvd_of_sameParity (N : ℕ) (x y : ℤ)
    (hsame : ∀ j < N,
      Even (signedOrbit x j) ↔ Even (signedOrbit y j)) :
    (((2 ^ N : ℕ) : ℤ)) ∣ x - y := by
  induction N generalizing x y with
  | zero => simp
  | succ N ih =>
      have hhead : Even x ↔ Even y := by
        simpa [signedOrbit] using hsame 0 (by omega)
      have htail : ∀ j < N,
          Even (signedOrbit (signedSyracuse x) j) ↔
            Even (signedOrbit (signedSyracuse y) j) := by
        intro j hj
        have h := hsame (j + 1) (by omega)
        simpa [signedOrbit, Function.iterate_succ_apply] using h
      rcases ih (signedSyracuse x) (signedSyracuse y) htail with ⟨t, ht⟩
      have hstep := signedSyracuse_difference_of_sameParity hhead
      have hmul : (((2 ^ (N + 1) : ℕ) : ℤ)) ∣
          (if Even x then 1 else 3) * (x - y) := by
        use t
        push_cast
        rw [pow_succ]
        calc
          (if Even x then 1 else 3) * (x - y) =
              2 * (signedSyracuse x - signedSyracuse y) := hstep.symm
          _ = 2 * (((2 : ℤ) ^ N) * t) := by
            rw [ht]
            push_cast
            rfl
          _ = ((2 : ℤ) ^ N * 2) * t := by ring
      by_cases hx : Even x
      · simpa [hx] using hmul
      · have hcop : Nat.Coprime (2 ^ (N + 1)) 3 :=
          Nat.Coprime.pow_left (N + 1) (by norm_num)
        have hmul' : (((2 ^ (N + 1) : ℕ) : ℤ)) ∣ 3 * (x - y) := by
          simpa [hx] using hmul
        rw [Int.natCast_dvd] at hmul' ⊢
        rw [Int.natAbs_mul] at hmul'
        norm_num at hmul'
        exact hcop.dvd_of_dvd_mul_left hmul'

/-- Exact finite cylinder theorem: the first `N` signed shortcut choices are
equal exactly when the starts agree modulo `2^N`. -/
theorem two_pow_dvd_iff_sameParity (N : ℕ) (x y : ℤ) :
    (((2 ^ N : ℕ) : ℤ)) ∣ x - y ↔
      ∀ j < N, Even (signedOrbit x j) ↔ Even (signedOrbit y j) := by
  exact ⟨sameParity_of_two_pow_dvd N x y,
    two_pow_dvd_of_sameParity N x y⟩

/-- A canonical negative representative of the depth-`N` dyadic cylinder
containing `x`. -/
def negativeShadow (x : ℤ) (N : ℕ) : ℤ :=
  x - (2 : ℤ) ^ N * ((x.natAbs : ℤ) + 1)

theorem negativeShadow_lt_zero (x : ℤ) (N : ℕ) :
    negativeShadow x N < 0 := by
  have hx : x ≤ (x.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    exact le_abs_self x
  have hp : (1 : ℤ) ≤ (2 : ℤ) ^ N :=
    one_le_pow₀ (by norm_num)
  have ha : (0 : ℤ) ≤ (x.natAbs : ℤ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hp ha
  dsimp [negativeShadow]
  omega

theorem two_pow_dvd_sub_negativeShadow (x : ℤ) (N : ℕ) :
    (2 : ℤ) ^ N ∣ x - negativeShadow x N := by
  use (x.natAbs : ℤ) + 1
  simp [negativeShadow]

/-- Every signed shortcut cylinder has negative representatives.  Therefore
finite positive/negative shadowing alone is not evidence for an exceptional
orbit; a construction must add coherence or an independent controller
constraint. -/
theorem exists_negative_sameParity_prefix (x : ℤ) (N : ℕ) :
    ∃ y < 0, ∀ j < N,
      Even (signedOrbit x j) ↔ Even (signedOrbit y j) := by
  refine ⟨negativeShadow x N, negativeShadow_lt_zero x N, ?_⟩
  apply sameParity_of_two_pow_dvd N
  change (2 : ℤ) ^ N ∣ x - negativeShadow x N
  exact two_pow_dvd_sub_negativeShadow x N

end KLUniversalShadow
end KontoroC

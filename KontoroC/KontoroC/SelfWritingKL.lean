/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterAperiodic
import KontoroC.EtherCounterStateNoRepeat

/-!
# The self-writing KL/EC17 coordinate

This file packages the exact one-coordinate recurrence found in the returning
ether-glider audit.  An `Orbit` is still a hypothesis: the definitions do not
assert that an infinite accepted execution, an ordinary initial address, or a
Collatz counterexample exists.

The useful conclusions are semantic.  Every supplied self-writing orbit is
an exact positive EC17 orbit, its public payload grows strictly, and its
branch schedule cannot be eventually periodic.
-/

namespace KontoroC
namespace SelfWritingKL

def Z (q : ℕ) : ℕ := 494251421 + 495976448 * q
def W (q : ℕ) : ℕ := 83499104 + 83790531 * q

/-- SW1, including both the constant and slope identities. -/
theorem determinant_identity (q : ℕ) :
    3 ^ 11 * Z q + 17 = 2 ^ 20 * W q := by
  simp [Z, W]
  ring

/-- QM145i: the packet color is multiplied by `316` at every positive EC17
step.  The large offset is kept literally to match the executable chart; the
statement is only a congruence modulo `473`. -/
theorem packetColor_transport {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Nat.ModEq 473 (s' + 291427) (316 * (s + 291427)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk : Nat.succ 0 + k = k + 1 := by omega
  simp_rw [hk] at hs ht ⊢
  have hcoef :
      (3 : ZMod 473) ^ (6 * (k + 1) + 11) =
        2 ^ 20 * 316 * 2 ^ (8 * (k + 1) - 5) := by
    rw [show 6 * (k + 1) + 11 = 17 + 6 * k by omega,
      show 8 * (k + 1) - 5 = 3 + 8 * k by omega,
      pow_add, pow_add, pow_mul, pow_mul]
    have hb : (3 : ZMod 473) ^ 17 = 2 ^ 20 * 316 * 2 ^ 3 := by decide
    have hr : (3 : ZMod 473) ^ 6 = 2 ^ 8 := by decide
    rw [hb, hr]
    ring
  have hconst :
      (17 : ZMod 473) + 2 ^ 20 * 291427 =
        2 ^ 20 * 316 * 291427 := by decide
  have htZ := congrArg (fun x : ℕ => (x : ZMod 473)) ht
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add] at htZ
  have hsZ := congrArg (fun x : ℕ => (x : ZMod 473)) hs
  have hs'Z := congrArg (fun x : ℕ => (x : ZMod 473)) hs'
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hsZ hs'Z
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
  have hunit : IsUnit (2 ^ 20 : ZMod 473) := by
    change IsUnit ((2 ^ 20 : ℕ) : ZMod 473)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  rw [← hunit.mul_left_inj]
  rw [mul_comm _ (2 ^ 20), mul_comm _ (2 ^ 20)]
  rw [mul_add, hs'Z, ← mul_assoc, ← pow_add]
  rw [show 20 + (8 * m - 5) = 8 * m + 15 by omega, htZ]
  rw [hsZ]
  linear_combination (u : ZMod 473) * hcoef + hconst

/-- Packet color zero is an invariant of every positive EC17 step. -/
theorem packetColor_zero_propagates {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hzero : Nat.ModEq 473 (s + 291427) 0) :
    Nat.ModEq 473 (s' + 291427) 0 := by
  have htransport := packetColor_transport hn hm hs hs' ht
  exact htransport.trans (by simpa using hzero.mul_left 316)

/-- A hypothetical infinite execution of the deterministic self-writing
coordinate.  `z_factor` records the current ternary branch and `w_factor`
records the next binary branch.  Requiring the next `z_factor` is exactly the
fixed return cylinder; it is not inferred from a finite computation. -/
structure Orbit where
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  core_odd : ∀ t, Odd (core t)
  core_mod_three : ∀ t, core t % 3 = 1
  payload : ℕ → ℕ
  z_factor : ∀ t,
    Z (payload t) = 3 ^ (6 * branch t) * core t
  w_factor : ∀ t,
    W (payload t) = 2 ^ (8 * branch (t + 1) - 5) * core (t + 1)

namespace Orbit

/-! ## Rational centered coordinates -/

def recharge (R : ℚ) : ℚ := (3 ^ 11 * R + 1221) / 2 ^ 15
def ether (R : ℚ) : ℚ := (729 * R + 4) / 256
def boundary (R : ℚ) : ℚ := 2 ^ 18 * R + 2215

/-- QM145a: the recharge map is exactly conjugate to the two-rail
determinant identity in the centered coordinate. -/
theorem recharge_identity (R : ℚ) :
    3 ^ 11 * (473 * R + 4) + 17 =
      2 ^ 15 * (473 * recharge R + 4) := by
  simp [recharge]
  ring

/-- QM145b: one ether cell multiplies the centered `Z` coordinate by
`729`, with denominator `256`. -/
theorem ether_identity (R : ℚ) :
    256 * (473 * ether R + 4) = 729 * (473 * R + 4) := by
  simp [ether]
  ring

/-- Iterated integer-denominator form of the ether conjugacy. -/
theorem ether_iterate_identity (m : ℕ) (R : ℚ) :
    256 ^ m * (473 * ((ether^[m]) R) + 4) =
      729 ^ m * (473 * R + 4) := by
  induction m generalizing R with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, pow_succ, pow_succ]
      calc
        256 ^ m * 256 * (473 * ((ether^[m]) (ether R)) + 4) =
            256 * (256 ^ m *
              (473 * ((ether^[m]) (ether R)) + 4)) := by ring
        _ = 256 * (729 ^ m * (473 * ether R + 4)) := by rw [ih]
        _ = 729 ^ m * (256 * (473 * ether R + 4)) := by ring
        _ = 729 ^ m * (729 * (473 * R + 4)) := by rw [ether_identity]
        _ = 729 ^ m * 729 * (473 * R + 4) := by ring

/-- First half of QM145d: the literal KL boundary conjugates one ether cell
to `(729*C+881)/256`. -/
theorem boundary_ether_conjugacy (R : ℚ) :
    boundary (ether R) = (729 * boundary R + 881) / 256 := by
  simp [boundary, ether]
  ring

/-- Second half of QM145d: the recharge map becomes the stated affine KL
boundary update. -/
theorem boundary_recharge_conjugacy (R : ℚ) :
    boundary (recharge R) =
      (3 ^ 11 * boundary R + 278339) / 2 ^ 15 := by
  simp [boundary, recharge]
  ring

/-- QM145c without a valuation API.  The exact EC17 balance factors the
recharged centered coordinate by `2^(8m)`. -/
theorem recharge_factor_of_transition {R u u' : ℚ} {n m : ℕ}
    (hsource : 473 * R + 4 = 3 ^ (6 * n) * u)
    (htransition : 2 ^ (8 * m + 15) * u' =
      3 ^ (6 * n + 11) * u + 17) :
    473 * recharge R + 4 = 2 ^ (8 * m) * u' := by
  have h := recharge_identity R
  rw [hsource] at h
  have hthree : (3 : ℚ) ^ 11 * (3 ^ (6 * n) * u) =
      3 ^ (6 * n + 11) * u := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hthree, ← htransition] at h
  have htwo : (2 : ℚ) ^ (8 * m + 15) = 2 ^ 15 * 2 ^ (8 * m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [htwo] at h
  have hpos : (0 : ℚ) < 2 ^ 15 := by positivity
  nlinarith

/-- Full centered conjugacy of one accepted EC17 transition. -/
theorem transition_conjugacy {R R' u u' : ℚ} {n m : ℕ}
    (hsource : 473 * R + 4 = 3 ^ (6 * n) * u)
    (htransition : 2 ^ (8 * m + 15) * u' =
      3 ^ (6 * n + 11) * u + 17)
    (htarget : 473 * R' + 4 = 3 ^ (6 * m) * u') :
    R' = (ether^[m]) (recharge R) := by
  have hD := recharge_factor_of_transition hsource htransition
  have hiter := ether_iterate_identity m (recharge R)
  have h256 : (256 : ℚ) ^ m = 2 ^ (8 * m) := by
    rw [show (256 : ℚ) = 2 ^ 8 by norm_num, ← pow_mul]
  have h729 : (729 : ℚ) ^ m = 3 ^ (6 * m) := by
    rw [show (729 : ℚ) = 3 ^ 6 by norm_num, ← pow_mul]
  rw [h256, h729, hD] at hiter
  have hpos : (0 : ℚ) < 2 ^ (8 * m) := by positivity
  have hz : 473 * ((ether^[m]) (recharge R)) + 4 =
      3 ^ (6 * m) * u' := by
    nlinarith
  rw [← htarget] at hz
  nlinarith

/-- SW1 turns every accepted self-writing step into the literal EC17
balance. -/
theorem balance (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
      3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
  have hnext := o.branch_pos (t + 1)
  calc
    2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) =
        2 ^ 20 *
          (2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1)) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ = 2 ^ 20 * W (o.payload t) := by rw [o.w_factor]
    _ = 3 ^ 11 * Z (o.payload t) + 17 :=
      (determinant_identity (o.payload t)).symm
    _ = 3 ^ (6 * o.branch t + 11) * o.core t + 17 := by
      rw [o.z_factor, ← mul_assoc, ← pow_add]
      congr 3
      omega

/-- The ternary factor displayed by the self-writing rail is exact, not only
a lower bound. -/
theorem z_exact_factor (o : Orbit) (t : ℕ) :
    3 ^ (6 * o.branch t) ∣ Z (o.payload t) ∧
      ¬ 3 ^ (6 * o.branch t + 1) ∣ Z (o.payload t) := by
  constructor
  · rw [o.z_factor]
    exact dvd_mul_right _ _
  · intro h
    rw [o.z_factor, show 6 * o.branch t + 1 =
      (6 * o.branch t) + 1 by omega, pow_succ'] at h
    have h' : 3 ^ (6 * o.branch t) * 3 ∣
        3 ^ (6 * o.branch t) * o.core t := by
      simpa [mul_comm] using h
    have hthree : 3 ∣ o.core t :=
      (Nat.mul_dvd_mul_iff_left
        (pow_pos (by norm_num : 0 < (3 : ℕ)) _)).mp h'
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hthree
    rw [o.core_mod_three] at hzero
    omega

/-- The binary delay is likewise exact because the normalized successor core
is odd. -/
theorem w_exact_factor (o : Orbit) (t : ℕ) :
    2 ^ (8 * o.branch (t + 1) - 5) ∣ W (o.payload t) ∧
      ¬ 2 ^ (8 * o.branch (t + 1) - 5 + 1) ∣ W (o.payload t) := by
  constructor
  · rw [o.w_factor]
    exact dvd_mul_right _ _
  · intro h
    rw [o.w_factor, pow_succ'] at h
    have h' : 2 ^ (8 * o.branch (t + 1) - 5) * 2 ∣
        2 ^ (8 * o.branch (t + 1) - 5) * o.core (t + 1) := by
      simpa [mul_comm] using h
    have htwo : 2 ∣ o.core (t + 1) :=
      (Nat.mul_dvd_mul_iff_left
        (pow_pos (by norm_num : 0 < (2 : ℕ)) _)).mp h'
    exact (Nat.not_even_iff_odd.mpr (o.core_odd (t + 1)))
      (even_iff_two_dvd.mpr htwo)

/-- Forgetting the packet coordinate gives precisely the universal positive
EC17 orbit used by the existing obstruction library. -/
def toEC17 (o : Orbit) : EtherCounterStateNoRepeat.Orbit where
  branch := o.branch
  branch_pos := o.branch_pos
  core := o.core
  core_pos := o.core_pos
  balance := o.balance

/-- In zero-based indexing the same object is the exact ternary-core orbit
of the autonomous ether-counter development. -/
def toTernaryCore (o : Orbit) : EtherCounterAperiodic.TernaryCoreOrbit where
  level t := o.branch t - 1
  core := o.core
  core_pos := o.core_pos
  balance t := by
    have ht := o.branch_pos t
    have ht1 := o.branch_pos (t + 1)
    rw [show 8 * (o.branch (t + 1) - 1) + 23 =
        8 * o.branch (t + 1) + 15 by omega,
      show 6 * (o.branch t - 1) + 17 =
        6 * o.branch t + 11 by omega]
    exact o.balance t

/-- Reinsert the forced factor `3` and the dyadic public register.  This is
the converse normalization needed to reuse the audited periodic-schedule
obstruction. -/
def ternaryCoreToNormalized (o : EtherCounterAperiodic.TernaryCoreOrbit) :
    EtherCounterAperiodic.NormalizedOrbit where
  level := o.level
  value := fun t => 2 ^ (8 * o.level t + 3) * (3 * o.core t)
  oddPart := fun t => 3 * o.core t
  value_pos t := Nat.mul_pos (pow_pos (by omega) _)
    (Nat.mul_pos (by omega) (o.core_pos t))
  factor t := rfl
  transition t := by
    calc
      2 ^ 20 *
          (2 ^ (8 * o.level (t + 1) + 3) * (3 * o.core (t + 1))) =
          3 * (2 ^ (8 * o.level (t + 1) + 23) * o.core (t + 1)) := by
        rw [show 8 * o.level (t + 1) + 23 =
          20 + (8 * o.level (t + 1) + 3) by omega, pow_add]
        ring
      _ = 3 * (3 ^ (6 * o.level t + 17) * o.core t + 17) := by
        rw [o.balance]
      _ = 3 ^ (6 * o.level t + 17) * (3 * o.core t) + 51 := by ring

def toNormalized (o : Orbit) : EtherCounterAperiodic.NormalizedOrbit :=
  ternaryCoreToNormalized o.toTernaryCore

/-- Every accepted step is outward in the public self-writing coordinate.
This is a theorem about a supplied exact orbit, not evidence that one exists. -/
theorem payload_strictMono (o : Orbit) : StrictMono o.payload := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hfirst :
      3 ^ 11 * Z (o.payload t) <
        2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
    calc
      3 ^ 11 * Z (o.payload t) =
          3 ^ (6 * o.branch t + 11) * o.core t := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
      _ < 2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) := by
        rw [o.balance]
        omega
  have hsecond :
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
        3 ^ 11 * Z (o.payload (t + 1)) := by
    calc
      2 ^ (8 * o.branch (t + 1) + 15) * o.core (t + 1) <
          3 ^ (6 * o.branch (t + 1) + 11) * o.core (t + 1) :=
        Nat.mul_lt_mul_of_pos_right
          (EtherCounterStateNoRepeat.Orbit.binary_lt_ternary_at_branch
            (o.branch (t + 1))) (o.core_pos (t + 1))
      _ = 3 ^ 11 * Z (o.payload (t + 1)) := by
        rw [o.z_factor, ← mul_assoc, ← pow_add]
        congr 2
        omega
  have hz : Z (o.payload t) < Z (o.payload (t + 1)) := by
    apply (Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ 11)).mp
    exact hfirst.trans hsecond
  simp [Z] at hz
  omega

/-- The self-writing map does not rescue a finite or ultimately periodic
branch dispatcher.  Any infinite accepted execution must use a genuinely
aperiodic schedule. -/
theorem branch_not_eventually_periodic (o : Orbit) (K p : ℕ) (hp : 0 < p) :
    ¬ EtherCounterAperiodic.EventuallyPeriodicFrom o.branch K p := by
  intro hperiodic
  apply o.toNormalized.branch_not_eventually_periodic K p hp
  intro k
  simpa [toNormalized, ternaryCoreToNormalized, toTernaryCore] using
    congrArg (fun n => n - 1) (hperiodic k)

end Orbit
end SelfWritingKL
end KontoroC

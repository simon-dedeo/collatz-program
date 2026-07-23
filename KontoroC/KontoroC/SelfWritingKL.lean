/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterAperiodic
import KontoroC.EtherCounterStateNoRepeat
import KontoroC.KLDyadicReset

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
def coreModulus : ℕ := 473 * 3 ^ 11
def returnModulus : ℕ := 2 ^ 20

/-- SW1, including both the constant and slope identities. -/
theorem determinant_identity (q : ℕ) :
    3 ^ 11 * Z q + 17 = 2 ^ 20 * W q := by
  simp [Z, W]
  ring

/-- The two moduli selecting the fixed-target odd core are coprime. -/
theorem coreModulus_coprime_returnModulus :
    coreModulus.Coprime returnModulus := by
  norm_num [coreModulus, returnModulus, Nat.Coprime]

/-- Valuation-free CRT interface for QM145g.  Any two requested core
residues select one canonical representative and every other solution is in
the same class modulo the product. -/
theorem exists_unique_core_crt (a b : ℕ) :
    ∃ h : ℕ, h < coreModulus * returnModulus ∧
      Nat.ModEq coreModulus h a ∧ Nat.ModEq returnModulus h b ∧
      ∀ h' : ℕ, Nat.ModEq coreModulus h' a →
        Nat.ModEq returnModulus h' b →
        Nat.ModEq (coreModulus * returnModulus) h' h := by
  let h : ℕ := ↑(Nat.chineseRemainder
    coreModulus_coprime_returnModulus a b)
  refine ⟨h, Nat.chineseRemainder_lt_mul
    coreModulus_coprime_returnModulus a b (by norm_num [coreModulus])
      (by norm_num [returnModulus]), ?_, ?_, ?_⟩
  · exact (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.1
  · exact (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.2
  · intro h' hhA hhB
    apply (Nat.modEq_and_modEq_iff_modEq_mul
      coreModulus_coprime_returnModulus).mp
    exact ⟨hhA.trans (Nat.chineseRemainder
      coreModulus_coprime_returnModulus a b).property.1.symm,
      hhB.trans (Nat.chineseRemainder
        coreModulus_coprime_returnModulus a b).property.2.symm⟩

/-- The source member of a fixed-target CRT family has exactly the dyadic
stride in QM145g. -/
theorem source_stride {m h q : ℕ} (hm : 0 < m)
    (hbase : W q = 2 ^ (8 * m - 5) * h) (t : ℕ) :
    W (q + 2 ^ (8 * m + 15) * t) =
      2 ^ (8 * m - 5) *
        (h + coreModulus * returnModulus * t) := by
  calc
    W (q + 2 ^ (8 * m + 15) * t) =
        W q + 83790531 * 2 ^ (8 * m + 15) * t := by
      simp [W]
      ring
    _ = 2 ^ (8 * m - 5) * h +
        83790531 * 2 ^ (8 * m + 15) * t := by rw [hbase]
    _ = 2 ^ (8 * m - 5) *
        (h + coreModulus * returnModulus * t) := by
      rw [show 8 * m + 15 = (8 * m - 5) + 20 by omega, pow_add]
      norm_num [coreModulus, returnModulus]
      ring

/-- The target member written by the same core lift has exactly the ternary
stride in QM145g. -/
theorem target_stride {m h q' : ℕ}
    (hbase : Z q' = 3 ^ (6 * m) * h) (t : ℕ) :
    Z (q' + 3 ^ (6 * m + 11) * t) =
      3 ^ (6 * m) *
        (h + coreModulus * returnModulus * t) := by
  calc
    Z (q' + 3 ^ (6 * m + 11) * t) =
        Z q' + 495976448 * 3 ^ (6 * m + 11) * t := by
      simp [Z]
      ring
    _ = 3 ^ (6 * m) * h +
        495976448 * 3 ^ (6 * m + 11) * t := by rw [hbase]
    _ = 3 ^ (6 * m) *
        (h + coreModulus * returnModulus * t) := by
      rw [show 6 * m + 11 = 6 * m + 11 by rfl, pow_add]
      norm_num [coreModulus, returnModulus]
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

/-- Packet color zero cannot be acquired at a later positive EC17 step.
The transport multiplier `316` is a unit modulo `473`, so a zero target
color already forces a zero source color.  This is the missing reverse
direction behind the informal statement that a non-packet bare EC17 ray
can never enter the returning-packet component. -/
theorem packetColor_zero_reflects {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hzero' : Nat.ModEq 473 (s' + 291427) 0) :
    Nat.ModEq 473 (s + 291427) 0 := by
  have htransport := packetColor_transport hn hm hs hs' ht
  have hproduct : Nat.ModEq 473 (316 * (s + 291427)) 0 :=
    htransport.symm.trans hzero'
  rw [← ZMod.natCast_eq_natCast_iff] at hproduct ⊢
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hproduct ⊢
  have hunit : IsUnit (316 : ZMod 473) := by
    change IsUnit ((316 : ℕ) : ZMod 473)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  apply hunit.mul_left_inj.mp
  simpa [mul_comm] using hproduct

/-- Packet validity is exactly invariant, in both time directions, along a
positive EC17 transition. -/
theorem packetColor_zero_iff {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Nat.ModEq 473 (s' + 291427) 0 ↔
      Nat.ModEq 473 (s + 291427) 0 :=
  ⟨packetColor_zero_reflects hn hm hs hs' ht,
    packetColor_zero_propagates hn hm hs hs' ht⟩

/-- Contrapositive form consumed by adversarial searches: once the bare
EC17 color is nonzero, every positive successor still fails the packet
gate. -/
theorem packetColor_nonzero_propagates {s s' u u' : ℕ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hs : s = 2 ^ (8 * n - 5) * u)
    (hs' : s' = 2 ^ (8 * m - 5) * u')
    (ht : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17)
    (hnonzero : ¬ Nat.ModEq 473 (s + 291427) 0) :
    ¬ Nat.ModEq 473 (s' + 291427) 0 := by
  exact fun hzero' => hnonzero
    (packetColor_zero_reflects hn hm hs hs' ht hzero')

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

/-! ## Exact promotion from a bare EC17 tail -/

/-- Every core of a bare positive EC17 orbit is odd.  This reuses the exact
finite-prefix parity theorem at a prefix long enough to contain the selected
outgoing transition. -/
theorem bareEC17_core_odd (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    Odd (g.core t) := by
  rw [Nat.odd_iff]
  have h := EtherCounterResidueBound.NaturalPrefix.core_mod_two_eq_one
    (g.toNaturalPrefix (t + 1)) t (by omega)
  simpa [EtherCounterStateNoRepeat.Orbit.toNaturalPrefix] using h

/-- Zero-based ternary-core presentation of an arbitrary bare positive EC17
orbit. -/
def bareEC17ToTernaryCore (g : EtherCounterStateNoRepeat.Orbit) :
    EtherCounterAperiodic.TernaryCoreOrbit where
  level t := g.branch t - 1
  core := g.core
  core_pos := g.core_pos
  balance t := by
    have ht := g.branch_pos t
    have ht1 := g.branch_pos (t + 1)
    rw [show 8 * (g.branch (t + 1) - 1) + 23 =
        8 * g.branch (t + 1) + 15 by omega,
      show 6 * (g.branch t - 1) + 17 =
        6 * g.branch t + 11 by omega]
    exact g.balance t

/-- Every core after the initial one is `1 mod 3`; hence discarding one
state supplies the exact ternary valuation field required by the
self-writing structure. -/
theorem bareEC17_core_next_mod_three
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ) :
    g.core (t + 1) % 3 = 1 := by
  simpa [bareEC17ToTernaryCore] using
    (bareEC17ToTernaryCore g).core_next_mod_three t

/-- Membership of one branch/core state in the affine `Z` payload rail. -/
def OnZRail (n u : ℕ) : Prop :=
  ∃ q, Z q = 3 ^ (6 * n) * u

/-- Divisibility-and-height form of affine rail membership.  This removes
the existential payload from adversarial checks: the centered state must be
at least the rail base and its excess must be divisible by the full stride
`473 * 2^20`, not merely by the packet-color modulus `473`. -/
theorem onZRail_iff (n u : ℕ) :
    OnZRail n u ↔
      494251421 ≤ 3 ^ (6 * n) * u ∧
      495976448 ∣ 3 ^ (6 * n) * u - 494251421 := by
  constructor
  · rintro ⟨q, hq⟩
    constructor
    · rw [← hq]
      simp [Z]
    · use q
      rw [← hq]
      simp [Z]
  · rintro ⟨hle, q, hq⟩
    refine ⟨q, ?_⟩
    simp only [Z]
    omega

theorem zRail_stride_factorization :
    495976448 = 473 * 2 ^ 20 := by norm_num

/-- If every state of a bare EC17 tail lies on the affine `Z` rail, the
entire self-writing orbit is forced.  The `W` factor is not an extra
assumption: it follows from the determinant identity and the bare EC17
balance after cancelling the common factor `2^20`. -/
noncomputable def promoteBareTail
    (g : EtherCounterStateNoRepeat.Orbit)
    (hrail : ∀ t, OnZRail (g.branch (t + 1)) (g.core (t + 1))) :
    SelfWritingKL.Orbit where
  branch t := g.branch (t + 1)
  branch_pos t := g.branch_pos (t + 1)
  core t := g.core (t + 1)
  core_pos t := g.core_pos (t + 1)
  core_odd t := bareEC17_core_odd g (t + 1)
  core_mod_three t := bareEC17_core_next_mod_three g t
  payload t := (hrail t).choose
  z_factor t := (hrail t).choose_spec
  w_factor t := by
    apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ 20)
    calc
      2 ^ 20 * W (hrail t).choose =
          3 ^ 11 * Z (hrail t).choose + 17 :=
        (determinant_identity (hrail t).choose).symm
      _ = 3 ^ (6 * g.branch (t + 1) + 11) *
          g.core (t + 1) + 17 := by
        rw [(hrail t).choose_spec, ← mul_assoc, ← pow_add]
        congr 3
        omega
      _ = 2 ^ (8 * g.branch (t + 2) + 15) * g.core (t + 2) :=
        (g.balance (t + 1)).symm
      _ = 2 ^ 20 *
          (2 ^ (8 * g.branch (t + 2) - 5) * g.core (t + 2)) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        have hpos := g.branch_pos (t + 2)
        omega

/-- Exact promotion criterion.  A bare positive EC17 ray becomes a
self-writing orbit after discarding its first state if and only if every
remaining state belongs to the affine `Z` rail.  Packet color zero is only a
necessary congruence shadow of this stronger all-time rail condition. -/
theorem all_onZRail_iff_exists_selfWriting_tail
    (g : EtherCounterStateNoRepeat.Orbit) :
    (∀ t, OnZRail (g.branch (t + 1)) (g.core (t + 1))) ↔
      ∃ o : SelfWritingKL.Orbit,
        o.branch = (fun t => g.branch (t + 1)) ∧
        o.core = (fun t => g.core (t + 1)) := by
  constructor
  · intro hrail
    exact ⟨promoteBareTail g hrail, rfl, rfl⟩
  · rintro ⟨o, hbranch, hcore⟩
    intro t
    refine ⟨o.payload t, ?_⟩
    simpa [hbranch, hcore] using o.z_factor t

/-- Single-state adversarial consumer.  Failure of the full affine rail at
any time prevents the given bare ray from being the tail of a self-writing
orbit, even if its dyadic address stabilizes and its packet color vanishes. -/
theorem no_selfWriting_tail_of_not_onZRail
    (g : EtherCounterStateNoRepeat.Orbit) (t : ℕ)
    (hfail : ¬ OnZRail (g.branch (t + 1)) (g.core (t + 1))) :
    ¬ ∃ o : SelfWritingKL.Orbit,
      o.branch = (fun j => g.branch (j + 1)) ∧
      o.core = (fun j => g.core (j + 1)) := by
  intro hexists
  have hall := (all_onZRail_iff_exists_selfWriting_tail g).mpr hexists
  exact hfail (hall t)

/-! ## Canonical backward dyadic address -/

/-- The exact reset program read from an arbitrary proposed branch
schedule.  It is defined before assuming that the schedule has an orbit, so
its canonical carries can be audited independently. -/
def resetProgramOfBranch (branch : ℕ → ℕ) (t : ℕ) :
    KLDyadicReset.ResetStep where
  N := 8 * branch (t + 1) + 15
  O := 6 * branch t + 11
  delta := 17

/-- Any nonnegative integer chain following the branch reset program is in
fact strictly positive at every time.  Positivity after time zero follows
from the positive defect.  At time zero, equality with defect `17` rules out
zero because the left side is divisible by two. -/
theorem follows_positive_of_nonnegative
    (branch : ℕ → ℕ) (m : ℕ → ℤ)
    (hm : KLDyadicReset.Follows (resetProgramOfBranch branch) m)
    (h0 : 0 ≤ m 0) : ∀ t, 0 < m t := by
  have hzero_ne : m 0 ≠ 0 := by
    intro hzero
    have hstep := hm 0
    simp only [resetProgramOfBranch] at hstep
    rw [hzero, mul_zero, zero_add] at hstep
    have hpow : (2 : ℤ) ∣ (2 : ℤ) ^ (8 * branch 1 + 15) :=
      dvd_pow_self 2 (by omega)
    have hleft : (2 : ℤ) ∣
        (2 : ℤ) ^ (8 * branch 1 + 15) * m 1 :=
      dvd_mul_of_dvd_left hpow _
    rw [hstep] at hleft
    norm_num at hleft
  have hbase : 0 < m 0 := by omega
  intro t
  induction t with
  | zero => exact hbase
  | succ t ih =>
      have hstep := hm t
      simp only [resetProgramOfBranch] at hstep
      have hrhs : 0 <
          (3 : ℤ) ^ (6 * branch t + 11) * m t + 17 := by
        have hproduct : 0 <
            (3 : ℤ) ^ (6 * branch t + 11) * m t :=
          mul_pos (by positivity) ih
        omega
      have hlhs : 0 <
          (2 : ℤ) ^ (8 * branch (t + 1) + 15) * m (t + 1) := by
        rw [hstep]
        exact hrhs
      have hreordered : 0 <
          m (t + 1) * (2 : ℤ) ^ (8 * branch (t + 1) + 15) := by
        simpa [mul_comm] using hlhs
      exact pos_of_mul_pos_left hreordered (by positivity)

/-- Complete ordinary-address characterization for the bare positive EC17
core recurrence on a prescribed positive branch schedule.  Eventual zero
carry is neither merely necessary nor heuristic: it is equivalent to the
existence of a positive natural EC17 core ray.  Packet color and the affine
`Z/W` self-writing rail remain additional, separate constraints. -/
theorem eventuallyZeroCarry_iff_exists_bareEC17
    (branch : ℕ → ℕ) (hbranch : ∀ t, 0 < branch t) :
    KLDyadicReset.EventuallyZeroCarry (resetProgramOfBranch branch) ↔
      ∃ o : EtherCounterStateNoRepeat.Orbit, o.branch = branch := by
  rw [KLDyadicReset.eventuallyZeroCarry_iff_exists_nonnegative_follows]
  constructor
  · rintro ⟨m, hm, h0⟩
    have hmpos := follows_positive_of_nonnegative branch m hm h0
    let o : EtherCounterStateNoRepeat.Orbit :=
      { branch := branch
        branch_pos := hbranch
        core := fun t => (m t).toNat
        core_pos := fun t => by
          have hcast := Int.toNat_of_nonneg (hmpos t).le
          apply Nat.pos_of_ne_zero
          intro hzero
          have hmzero : m t = 0 := by
            calc
              m t = ((m t).toNat : ℤ) := hcast.symm
              _ = 0 := by simp [hzero]
          exact (ne_of_gt (hmpos t)) hmzero
        balance := fun t => by
          have hstep := hm t
          simp only [resetProgramOfBranch] at hstep
          rw [← Int.toNat_of_nonneg (hmpos t).le,
            ← Int.toNat_of_nonneg (hmpos (t + 1)).le] at hstep
          exact_mod_cast hstep }
    exact ⟨o, rfl⟩
  · rintro ⟨o, rfl⟩
    let m : ℕ → ℤ := fun t => o.core t
    refine ⟨m, ?_, by simp [m]⟩
    intro t
    simp only [resetProgramOfBranch, m]
    exact_mod_cast o.balance t

def resetProgram (o : Orbit) : ℕ → KLDyadicReset.ResetStep :=
  resetProgramOfBranch o.branch

/-- The normalized EC17 cores follow that reset program literally. -/
theorem follows_resetProgram (o : Orbit) :
    KLDyadicReset.Follows o.resetProgram (fun t => (o.core t : ℤ)) := by
  intro t
  simp only [resetProgram, resetProgramOfBranch]
  exact_mod_cast o.balance t

/-- Every self-writing step contributes positive dyadic precision, so the
accumulated reset precision dominates the number of steps. -/
theorem resetPrecision_ge (o : Orbit) (J : ℕ) :
    J ≤ (KLDyadicReset.cumulative o.resetProgram J).S := by
  induction J with
  | zero => simp [KLDyadicReset.cumulative, KLDyadicReset.initialData]
  | succ J ih =>
      rw [KLDyadicReset.cumulative_succ_S]
      have hN : 0 < (o.resetProgram J).N := by
        simp [resetProgram, resetProgramOfBranch]
      omega

/-- The accumulated binary precision of the self-writing reset program is
unbounded. -/
theorem resetPrecision_unbounded (o : Orbit) :
    ∀ L, ∃ J, L ≤ (KLDyadicReset.cumulative o.resetProgram J).S := by
  intro L
  exact ⟨L, o.resetPrecision_ge L⟩

/-- Necessary inverse-limit condition for an ordinary self-writing orbit:
the canonical initial EC17-core residues must eventually become literally
constant at the one natural initial core. -/
theorem initialResidue_eventually_constant (o : Orbit) :
    ∃ J, ∀ K, J ≤ K →
      KLDyadicReset.initialResidue o.resetProgram K = o.core 0 := by
  simpa using KLDyadicReset.initialResidue_eventually_constant_of_follows
    o.resetProgram (fun t => (o.core t : ℤ)) o.follows_resetProgram
      (by positivity) o.resetPrecision_unbounded

/-- Operational version of the same obstruction: all sufficiently late
canonical address carries must vanish. -/
theorem carryDigit_eventually_zero (o : Orbit) :
    ∃ J, ∀ K, J ≤ K →
      KLDyadicReset.carryDigit o.resetProgram K = 0 := by
  exact KLDyadicReset.carryDigit_eventually_zero_of_follows
    o.resetProgram (fun t => (o.core t : ℤ)) o.follows_resetProgram
      (by positivity) o.resetPrecision_unbounded

/-- Ready-made adversarial consumer: infinitely recurring nonzero canonical
carries are incompatible with an ordinary self-writing orbit. -/
theorem false_of_cofinally_nonzero_carries (o : Orbit)
    (hbad : ∀ J, ∃ K, J ≤ K ∧
      KLDyadicReset.carryDigit o.resetProgram K ≠ 0) : False := by
  obtain ⟨J, hzero⟩ := o.carryDigit_eventually_zero
  obtain ⟨K, hJK, hne⟩ := hbad J
  exact hne (hzero K hJK)

/-- Branch-only exclusion interface.  A checker may compute the canonical
carries from a proposed schedule without first constructing any payloads; if
nonzero carries recur cofinally, no self-writing orbit can realize that
schedule. -/
theorem no_orbit_with_branch_of_cofinally_nonzero_carries
    (branch : ℕ → ℕ)
    (hbad : ∀ J, ∃ K, J ≤ K ∧
      KLDyadicReset.carryDigit (resetProgramOfBranch branch) K ≠ 0) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply o.false_of_cofinally_nonzero_carries
  simpa [resetProgram] using hbad

/-- Height-form branch exclusion, useful when a symbolic or morphic analysis
shows the canonical residues themselves escape every ordinary bound. -/
theorem no_orbit_with_branch_of_unbounded_residues
    (branch : ℕ → ℕ)
    (hbad : KLDyadicReset.ResiduesUnbounded
      (resetProgramOfBranch branch)) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply KLDyadicReset.no_nonnegative_follows_of_unbounded_residues
    o.resetProgram (by simpa [resetProgram] using hbad)
  exact ⟨fun t => (o.core t : ℤ), o.follows_resetProgram, by positivity⟩

/-- Change-form branch exclusion: perpetual acquisition of new canonical
high bits also rules out an ordinary orbit. -/
theorem no_orbit_with_branch_of_changes
    (branch : ℕ → ℕ)
    (hbad : KLDyadicReset.ChangesArbitrarilyLate
      (resetProgramOfBranch branch)) :
    ¬ ∃ o : Orbit, o.branch = branch := by
  rintro ⟨o, rfl⟩
  apply KLDyadicReset.no_nonnegative_follows_of_changes
    o.resetProgram o.resetPrecision_unbounded
      (by simpa [resetProgram] using hbad)
  exact ⟨fun t => (o.core t : ℤ), o.follows_resetProgram, by positivity⟩

/-- One branch schedule can select at most one ordinary initial normalized
core. -/
theorem initial_core_unique_of_same_branch (o o' : Orbit)
    (hbranch : o.branch = o'.branch) : o.core 0 = o'.core 0 := by
  have hfollows' : KLDyadicReset.Follows o.resetProgram
      (fun t => (o'.core t : ℤ)) := by
    simpa [resetProgram, hbranch] using o'.follows_resetProgram
  have hint := KLDyadicReset.initial_eq_of_unbounded_cumulative_precision
    o.resetProgram (fun t => (o.core t : ℤ)) (fun t => (o'.core t : ℤ))
      o.follows_resetProgram hfollows' o.resetPrecision_unbounded
  exact_mod_cast hint

/-- Consequently a branch schedule selects at most one initial public
payload in the self-writing coordinate. -/
theorem initial_payload_unique_of_same_branch (o o' : Orbit)
    (hbranch : o.branch = o'.branch) : o.payload 0 = o'.payload 0 := by
  have hcore := initial_core_unique_of_same_branch o o' hbranch
  have hz : Z (o.payload 0) = Z (o'.payload 0) := by
    rw [o.z_factor, o'.z_factor, hcore, hbranch]
  simp [Z] at hz
  omega

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

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.SignedDebrisSemanticNoGo
import KontoroC.OutwardThreeWordBoundaryAmplitude

/-!
# A stationary dyadic boundary rail through the typed debris router

The scalar reproduction equation for the typed signed-debris cofactor is
impossible.  The correct replacement is not another scalar: it is a whole
ordinary dyadic cylinder.  If the base router collision is

`3^a * R_m - 1 = 2^B * W`,

then for every width `w` and ordinary payload `z` one has exactly

`3^a * (R_m + 2^(B+w) z) - 1 = 2^B * (W + 2^w * 3^a z)`.

For positive `w`, the right-hand cofactor remains odd.  Thus the collision
computes its public valuation on one rail while transporting an arbitrary
ordinary boundary amplitude on a second rail.  No new CRT choice is made.

When the requested target label is even, the cofactor is `2 mod 3`, so the
entire output cylinder is a completed boundary `3H-1`.  The final section
proves that any finite three-word address whose dyadic denominator fits in
the retained width transports this free boundary coefficient exactly.

This is a finite stationary interface, not yet an infinite orbit: closure
still requires the public dynamics to regenerate unbounded usable width.
-/

namespace KontoroC
namespace SignedDebrisBoundaryLift

open SignedUnitShuttle SignedDebrisSemanticNoGo
open OutwardThreeWordZeroCarry OutwardThreeWordBoundaryAmplitude

/-- Explicit odd cofactor emitted by the typed router. -/
def typedRouterCofactor (m target : ℕ) : ℕ :=
  (scaledMinusNumerator
    (routerLabel (routerPrecision target) m) m).divMaxPow 2

/-- The base typed collision factors through its exact requested public
binary exponent. -/
theorem typedRouterCofactor_spec
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    scaledMinusNumerator
        (routerLabel (routerPrecision target) m) m =
      2 ^ minusBinary target * typedRouterCofactor m target := by
  let N := scaledMinusNumerator
    (routerLabel (routerPrecision target) m) m
  have hval := typedRouter_padicValNat m target hm hroom
  have hfactor := Nat.pow_padicValNat_mul_divMaxPow 2 N
  change N = 2 ^ minusBinary target * N.divMaxPow 2
  rw [← hval]
  exact hfactor.symm

theorem typedRouterCofactor_pos
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    0 < typedRouterCofactor m target := by
  have hfactor := typedRouterCofactor_spec m target hm hroom
  have hR := plusMinusDebris_pos m
  have hthree : 1 <
      3 ^ minusTernary (routerLabel (routerPrecision target) m) :=
    Nat.one_lt_pow (by simp [minusTernary]) (by norm_num)
  have hNpos : 0 < scaledMinusNumerator
      (routerLabel (routerPrecision target) m) m := by
    dsimp only [scaledMinusNumerator]
    have hprod : 1 <
        3 ^ minusTernary (routerLabel (routerPrecision target) m) *
          plusMinusDebris m := by
      calc
        1 < 3 ^ minusTernary (routerLabel (routerPrecision target) m) := hthree
        _ = 3 ^ minusTernary (routerLabel (routerPrecision target) m) * 1 := by
          ring
        _ ≤ 3 ^ minusTernary (routerLabel (routerPrecision target) m) *
            plusMinusDebris m := Nat.mul_le_mul_left _ hR
    omega
  by_contra hzero
  have hw : typedRouterCofactor m target = 0 := Nat.eq_zero_of_not_pos hzero
  rw [hw, mul_zero] at hfactor
  omega

theorem typedRouterCofactor_odd
    (m target : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    Odd (typedRouterCofactor m target) := by
  have hNpos : 0 < scaledMinusNumerator
      (routerLabel (routerPrecision target) m) m := by
    have hfactor := typedRouterCofactor_spec m target hm hroom
    have hw := typedRouterCofactor_pos m target hm hroom
    rw [hfactor]
    exact Nat.mul_pos (by positivity) hw
  have hnot : ¬2 ∣ typedRouterCofactor m target := by
    exact Nat.not_dvd_divMaxPow (by omega) hNpos.ne'
  simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using hnot

/-- Source cylinder retaining `width` dyadic boundary bits above the public
valuation computed by the router. -/
def boundarySource (m target width z : ℕ) : ℕ :=
  plusMinusDebris m + 2 ^ (minusBinary target + width) * z

/-- Literal numerator obtained by applying the reached sign-negative scale
to a boundary-cylinder source. -/
def boundaryNumerator (m target width z : ℕ) : ℕ :=
  3 ^ minusTernary (routerLabel (routerPrecision target) m) *
      boundarySource m target width z - 1

/-- Exact two-rail identity.  The public valuation is computed on the first
rail; the arbitrary ordinary payload is transported linearly on the second. -/
theorem boundaryNumerator_factorization
    (m target width z : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m) :
    boundaryNumerator m target width z =
      2 ^ minusBinary target *
        (typedRouterCofactor m target +
          2 ^ width *
            3 ^ minusTernary (routerLabel (routerPrecision target) m) * z) := by
  let a := minusTernary (routerLabel (routerPrecision target) m)
  let R := plusMinusDebris m
  let B := minusBinary target
  let W := typedRouterCofactor m target
  have hR : 0 < R := plusMinusDebris_pos m
  have hbase : 3 ^ a * R - 1 = 2 ^ B * W := by
    simpa only [a, R, B, W, scaledMinusNumerator] using
      typedRouterCofactor_spec m target hm hroom
  have hone : 1 ≤ 3 ^ a * R := by
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by positivity) hR)
  let X := 3 ^ a * R
  let Y := 3 ^ a * (2 ^ (B + width) * z)
  have hX : 1 ≤ X := by exact hone
  have hsub : X + Y - 1 = (X - 1) + Y := by
    omega
  dsimp only [boundaryNumerator, boundarySource, a, R, B, W]
  calc
    3 ^ a * (R + 2 ^ (B + width) * z) - 1 =
        (3 ^ a * R - 1) + 3 ^ a * 2 ^ (B + width) * z := by
      simpa only [X, Y, mul_add, mul_assoc] using hsub
    _ = 2 ^ B * W + 3 ^ a * 2 ^ (B + width) * z := by rw [hbase]
    _ = 2 ^ B * (W + 2 ^ width * 3 ^ a * z) := by
      rw [pow_add]
      ring

/-- Positive retained width preserves exact oddness of the emitted cofactor
for every ordinary boundary payload. -/
theorem boundaryOutput_odd
    (m target width z : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m)
    (hwidth : 0 < width) :
    Odd (typedRouterCofactor m target +
      2 ^ width *
        3 ^ minusTernary (routerLabel (routerPrecision target) m) * z) := by
  obtain ⟨k, hk⟩ := typedRouterCofactor_odd m target hm hroom
  have hpowEven : Even (2 ^ width) := even_two.pow_of_ne_zero hwidth.ne'
  obtain ⟨j, hj⟩ := hpowEven.mul_right
    (3 ^ minusTernary (routerLabel (routerPrecision target) m) * z)
  refine ⟨k + j, ?_⟩
  rw [hk, show 2 ^ width *
      3 ^ minusTernary (routerLabel (routerPrecision target) m) * z =
        2 ^ width *
          (3 ^ minusTernary (routerLabel (routerPrecision target) m) * z) by
      ring,
    hj]
  omega

/-- The boundary cylinder retains the same exact public valuation, not only
divisibility, whenever at least one dyadic boundary bit is reserved. -/
theorem boundaryNumerator_padicValNat
    (m target width z : ℕ) (hm : Odd m)
    (hroom : minusBinary target < plusBinary m)
    (hwidth : 0 < width) :
    padicValNat 2 (boundaryNumerator m target width z) =
      minusBinary target := by
  rw [boundaryNumerator_factorization m target width z hm hroom]
  rw [padicValNat_base_pow_mul (by norm_num)
    (boundaryOutput_odd m target width z hm hroom hwidth).pos.ne']
  have hnot : ¬2 ∣ typedRouterCofactor m target +
      2 ^ width *
        3 ^ minusTernary (routerLabel (routerPrecision target) m) * z := by
    simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using
      boundaryOutput_odd m target width z hm hroom hwidth
  rw [padicValNat.eq_zero_of_not_dvd hnot, zero_add]

/-! ## Completed ordinary boundary output -/

private theorem four_pow_mod_three (n : ℕ) : 4 ^ n % 3 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]

/-- At an even requested label the emitted odd cofactor is automatically
`2 mod 3`, exactly the completed-boundary residue. -/
theorem typedRouterCofactor_mod_three_of_even_target
    (m target : ℕ) (hm : Odd m) (htarget : Even target)
    (hroom : minusBinary target < plusBinary m) :
    typedRouterCofactor m target % 3 = 2 := by
  let ell := routerLabel (routerPrecision target) m
  let a := minusTernary ell
  let R := plusMinusDebris m
  let B := minusBinary target
  let W := typedRouterCofactor m target
  have hfactor : 3 ^ a * R - 1 = 2 ^ B * W := by
    simpa only [ell, a, R, B, W, scaledMinusNumerator] using
      typedRouterCofactor_spec m target hm hroom
  have hone : 1 ≤ 3 ^ a * R := by
    exact Nat.succ_le_iff.mpr
      (Nat.mul_pos (by positivity) (plusMinusDebris_pos m))
  have ha0 : a ≠ 0 := by simp [a, ell, minusTernary]
  have hdiv3 : 3 ∣ 3 ^ a * R := by
    exact dvd_mul_of_dvd_left (dvd_pow_self 3 ha0) R
  obtain ⟨k, hk⟩ := hdiv3
  have hkpos : 0 < k := by
    rw [hk] at hone
    omega
  have hleftMod : (3 ^ a * R - 1) % 3 = 2 := by
    have hform : 3 ^ a * R - 1 = 3 * (k - 1) + 2 := by
      rw [hk]
      omega
    rw [hform]
    omega
  obtain ⟨t, ht⟩ := htarget
  have hBform : B = 2 * (23 * t + 27) := by
    dsimp only [B, minusBinary]
    omega
  have hpowB : 2 ^ B % 3 = 1 := by
    calc
      2 ^ B % 3 = (2 ^ 2) ^ (23 * t + 27) % 3 := by
        rw [hBform, pow_mul]
      _ = 4 ^ (23 * t + 27) % 3 := by norm_num
      _ = 1 := four_pow_mod_three _
  have hfactorMod := congrArg (fun n : ℕ => n % 3) hfactor
  rw [hleftMod, Nat.mul_mod, hpowB, one_mul, Nat.mod_mod] at hfactorMod
  exact hfactorMod.symm

/-- Base completed-boundary charge carried by the typed router. -/
def typedRouterBoundaryCharge (m target : ℕ) : ℕ :=
  (typedRouterCofactor m target + 1) / 3

theorem typedRouterCofactor_eq_boundary
    (m target : ℕ) (hm : Odd m) (htarget : Even target)
    (hroom : minusBinary target < plusBinary m) :
    typedRouterCofactor m target =
      3 * typedRouterBoundaryCharge m target - 1 := by
  have hmod := typedRouterCofactor_mod_three_of_even_target
    m target hm htarget hroom
  have hdiv : 3 ∣ typedRouterCofactor m target + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hmul : 3 * typedRouterBoundaryCharge m target =
      typedRouterCofactor m target + 1 := by
    dsimp only [typedRouterBoundaryCharge]
    exact Nat.mul_div_cancel' hdiv
  have hWpos := typedRouterCofactor_pos m target hm hroom
  omega

/-- Completed-boundary charge after transporting a width-`width` ordinary
payload. -/
def boundaryOutputCharge (m target width z : ℕ) : ℕ :=
  typedRouterBoundaryCharge m target +
    2 ^ width *
      3 ^ (minusTernary (routerLabel (routerPrecision target) m) - 1) * z

/-- The complete output cylinder is literally `3H-1`, so it can feed the
ordinary three-word first-passage semantics without a residue conversion. -/
theorem boundaryOutput_eq_completedBoundary
    (m target width z : ℕ) (hm : Odd m) (htarget : Even target)
    (hroom : minusBinary target < plusBinary m) :
    typedRouterCofactor m target +
        2 ^ width *
          3 ^ minusTernary (routerLabel (routerPrecision target) m) * z =
      3 * boundaryOutputCharge m target width z - 1 := by
  let a := minusTernary (routerLabel (routerPrecision target) m)
  let H := typedRouterBoundaryCharge m target
  change typedRouterCofactor m target + 2 ^ width * 3 ^ a * z =
    3 * (H + 2 ^ width * 3 ^ (a - 1) * z) - 1
  have haPos : 0 < a := by simp [a, minusTernary]
  have hpow : 3 ^ a = 3 * 3 ^ (a - 1) := by
    calc
      3 ^ a = 3 ^ ((a - 1) + 1) := by congr 1
      _ = 3 ^ (a - 1) * 3 := by rw [pow_succ]
      _ = 3 * 3 ^ (a - 1) := by rw [mul_comm]
  have hbase := typedRouterCofactor_eq_boundary
    m target hm htarget hroom
  rw [hbase, hpow]
  have hHpos : 0 < typedRouterBoundaryCharge m target := by
    have hWpos := typedRouterCofactor_pos m target hm hroom
    have hmul : 3 * typedRouterBoundaryCharge m target =
        typedRouterCofactor m target + 1 := by
      have hmod := typedRouterCofactor_mod_three_of_even_target
        m target hm htarget hroom
      have hdiv : 3 ∣ typedRouterCofactor m target + 1 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      exact Nat.mul_div_cancel' hdiv
    omega
  let X := 3 * typedRouterBoundaryCharge m target
  let Y := 3 * (2 ^ width * 3 ^ (a - 1) * z)
  have hX : 1 ≤ X := by
    dsimp only [X]
    omega
  have hsub : (X - 1) + Y = X + Y - 1 := by omega
  dsimp only [X, Y] at hsub
  dsimp only [H]
  convert hsub using 1 <;> ring

/-! ## Exact transport by the ordinary three-word map -/

/-- A branch transports an arbitrary linear rail whenever its denominator
divides the incoming coefficient.  This is the local algebraic engine behind
finite cylinder transport: the base charge pays the affine offset, while the
free rail follows the homogeneous branch slope exactly. -/
theorem branchStep_lift_of_dvd
    (b : Branch) {H H' coefficient z : ℕ}
    (hstep : b.Step H H')
    (hdiv : branchDenominator b ∣ coefficient) :
    b.Step
      (H + coefficient * z)
      (H' + branchNumerator b *
        (coefficient / branchDenominator b) * z) := by
  have hbalance := (branch_step_iff_balance b H H').mp hstep
  have hcoefficient :
      branchDenominator b * (coefficient / branchDenominator b) =
        coefficient := Nat.mul_div_cancel' hdiv
  apply (branch_step_iff_balance b _ _).mpr
  calc
    branchDenominator b *
        (H' + branchNumerator b *
          (coefficient / branchDenominator b) * z) =
      branchDenominator b * H' +
        branchNumerator b *
          (branchDenominator b *
            (coefficient / branchDenominator b)) * z := by ring
    _ = branchNumerator b * H + branchOffset b +
        branchNumerator b * coefficient * z := by rw [hbalance, hcoefficient]
    _ = branchNumerator b * (H + coefficient * z) +
        branchOffset b := by ring

/-- Number of dyadic boundary bits consumed by one branch. -/
def branchBits : Branch → ℕ
  | .A => 1
  | .B => 3
  | .C => 6

theorem branchBits_pos (b : Branch) : 0 < branchBits b := by
  cases b <;> norm_num [branchBits]

theorem branchDenominator_eq_two_pow (b : Branch) :
    branchDenominator b = 2 ^ branchBits b := by
  cases b <;> norm_num [branchDenominator, branchBits]

/-- Number of ternary powers gained by the homogeneous part of one branch. -/
def branchTrits : Branch → ℕ
  | .A => 1
  | .B => 2
  | .C => 4

theorem branchNumerator_eq_three_pow (b : Branch) :
    branchNumerator b = 3 ^ branchTrits b := by
  cases b <;> norm_num [branchNumerator, branchTrits]

/-- Total dyadic width consumed by an address prefix. -/
def bitsPrefix (branch : ℕ → Branch) : ℕ → ℕ
  | 0 => 0
  | n + 1 => branchBits (branch n) + bitsPrefix branch n

/-- Total ternary homogeneous gain along an address prefix. -/
def tritsPrefix (branch : ℕ → Branch) : ℕ → ℕ
  | 0 => 0
  | n + 1 => branchTrits (branch n) + tritsPrefix branch n

/-- Every branch consumes at least one bit, so cumulative address cost is at
least its length. -/
theorem le_bitsPrefix (branch : ℕ → Branch) (n : ℕ) :
    n ≤ bitsPrefix branch n := by
  induction n with
  | zero => simp [bitsPrefix]
  | succ n ih =>
      simp only [bitsPrefix]
      have hpos := branchBits_pos (branch n)
      omega

/-- No fixed retained cylinder width can carry an infinite nonempty address.
Consequently every infinite construction using this rail must contain an
autonomous width-regeneration operation. -/
theorem no_fixed_width_covers_all_prefixes
    (branch : ℕ → Branch) (width : ℕ) :
    ¬ ∀ n, bitsPrefix branch n ≤ width := by
  intro h
  have hcost := h (width + 1)
  have hlength := le_bitsPrefix branch (width + 1)
  omega

theorem denominatorPrefix_eq_two_pow
    (branch : ℕ → Branch) (n : ℕ) :
    denominatorPrefix branch n = 2 ^ bitsPrefix branch n := by
  induction n with
  | zero => simp [denominatorPrefix, bitsPrefix]
  | succ n ih =>
      simp only [denominatorPrefix, bitsPrefix, ih,
        branchDenominator_eq_two_pow, pow_add]

theorem numeratorPrefix_eq_three_pow
    (branch : ℕ → Branch) (n : ℕ) :
    numeratorPrefix branch n = 3 ^ tritsPrefix branch n := by
  induction n with
  | zero => simp [numeratorPrefix, tritsPrefix]
  | succ n ih =>
      simp only [numeratorPrefix, tritsPrefix, ih,
        branchNumerator_eq_three_pow, pow_add]

/-- Closed-form resource accounting for one lifted branch: dyadic width is
spent, never approximated, while the homogeneous ternary amplitude grows. -/
theorem branchRailCoefficient_step
    (b : Branch) (width a : ℕ) (hwidth : branchBits b ≤ width) :
    branchNumerator b *
        ((2 ^ width * 3 ^ a) / branchDenominator b) =
      2 ^ (width - branchBits b) * 3 ^ (a + branchTrits b) := by
  have hwidthEq : width = branchBits b + (width - branchBits b) := by omega
  have hpow : 2 ^ width =
      2 ^ branchBits b * 2 ^ (width - branchBits b) := by
    calc
      2 ^ width = 2 ^ (branchBits b + (width - branchBits b)) :=
        congrArg (fun n : ℕ => 2 ^ n) hwidthEq
      _ = 2 ^ branchBits b * 2 ^ (width - branchBits b) := pow_add _ _ _
  have hfactor :
      2 ^ width * 3 ^ a =
        branchDenominator b * (2 ^ (width - branchBits b) * 3 ^ a) := by
    calc
      2 ^ width * 3 ^ a =
          (2 ^ branchBits b * 2 ^ (width - branchBits b)) * 3 ^ a := by
        rw [hpow]
      _ = branchDenominator b *
          (2 ^ (width - branchBits b) * 3 ^ a) := by
        rw [branchDenominator_eq_two_pow]
        ring
  rw [hfactor, Nat.mul_comm (branchDenominator b),
    Nat.mul_div_left _ (branch_denominator_pos b)]
  rw [branchNumerator_eq_three_pow, pow_add]
  ring

/-- Closed-form resource accounting for an arbitrary finite address. -/
theorem prefixRailCoefficient
    (branch : ℕ → Branch) (n width a : ℕ)
    (hwidth : bitsPrefix branch n ≤ width) :
    numeratorPrefix branch n *
        ((2 ^ width * 3 ^ a) / denominatorPrefix branch n) =
      2 ^ (width - bitsPrefix branch n) *
        3 ^ (a + tritsPrefix branch n) := by
  have hwidthEq : width =
      bitsPrefix branch n + (width - bitsPrefix branch n) := by omega
  have hpow : 2 ^ width =
      2 ^ bitsPrefix branch n * 2 ^ (width - bitsPrefix branch n) := by
    calc
      2 ^ width =
          2 ^ (bitsPrefix branch n + (width - bitsPrefix branch n)) :=
        congrArg (fun k : ℕ => 2 ^ k) hwidthEq
      _ = 2 ^ bitsPrefix branch n *
          2 ^ (width - bitsPrefix branch n) := pow_add _ _ _
  have hfactor :
      2 ^ width * 3 ^ a = denominatorPrefix branch n *
        (2 ^ (width - bitsPrefix branch n) * 3 ^ a) := by
    rw [hpow, denominatorPrefix_eq_two_pow]
    ring
  rw [hfactor, Nat.mul_comm (denominatorPrefix branch n),
    Nat.mul_div_left _ (denominatorPrefix_pos branch n)]
  rw [numeratorPrefix_eq_three_pow, pow_add]
  ring

/-- The full affine endpoint equation for a finite address transports an
arbitrary free rail whenever the prefix denominator divides its coefficient. -/
theorem prefix_balance_lift_of_dvd
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hstep : ∀ k, (branch k).Step (charge k) (charge (k + 1)))
    (n coefficient z : ℕ)
    (hdiv : denominatorPrefix branch n ∣ coefficient) :
    denominatorPrefix branch n *
        (charge n + numeratorPrefix branch n *
          (coefficient / denominatorPrefix branch n) * z) =
      numeratorPrefix branch n * (charge 0 + coefficient * z) +
        offsetPrefix branch n := by
  have hbase := prefix_balance charge branch hstep n
  have hcoefficient : denominatorPrefix branch n *
      (coefficient / denominatorPrefix branch n) = coefficient :=
    Nat.mul_div_cancel' hdiv
  calc
    denominatorPrefix branch n *
        (charge n + numeratorPrefix branch n *
          (coefficient / denominatorPrefix branch n) * z) =
      denominatorPrefix branch n * charge n +
        numeratorPrefix branch n *
          (denominatorPrefix branch n *
            (coefficient / denominatorPrefix branch n)) * z := by ring
    _ = numeratorPrefix branch n * charge 0 + offsetPrefix branch n +
        numeratorPrefix branch n * coefficient * z := by
      rw [hbase, hcoefficient]
    _ = numeratorPrefix branch n * (charge 0 + coefficient * z) +
        offsetPrefix branch n := by ring

/-- The transported rail emerging from an even-target router collision. -/
def boundaryRailCoefficient (m target width : ℕ) : ℕ :=
  2 ^ width *
    3 ^ (minusTernary (routerLabel (routerPrecision target) m) - 1)

/-- A branch whose bit cost fits in the retained width divides the free rail.
This is the exact finite resource test; A, B, and C consume respectively
one, three, and six bits. -/
theorem branchDenominator_dvd_boundaryRailCoefficient
    (b : Branch) (m target width : ℕ)
    (hwidth : branchBits b ≤ width) :
    branchDenominator b ∣ boundaryRailCoefficient m target width := by
  rw [branchDenominator_eq_two_pow]
  exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hwidth) _

theorem denominatorPrefix_dvd_boundaryRailCoefficient
    (branch : ℕ → Branch) (n m target width : ℕ)
    (hwidth : bitsPrefix branch n ≤ width) :
    denominatorPrefix branch n ∣ boundaryRailCoefficient m target width := by
  rw [denominatorPrefix_eq_two_pow]
  exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hwidth) _

/-- Any legal base branch lifts uniformly to the full router cylinder while
its dyadic bit cost fits in the retained width.  The conclusion is itself a
literal `Branch.Step`, hence feeds the ordinary execution theorem directly. -/
theorem boundaryOutputCharge_branchStep
    (b : Branch) (m target width z H' : ℕ)
    (hbase : b.Step (typedRouterBoundaryCharge m target) H')
    (hwidth : branchBits b ≤ width) :
    b.Step
      (boundaryOutputCharge m target width z)
      (H' + branchNumerator b *
        (boundaryRailCoefficient m target width /
          branchDenominator b) * z) := by
  simpa only [boundaryOutputCharge, boundaryRailCoefficient] using
    branchStep_lift_of_dvd b hbase
      (branchDenominator_dvd_boundaryRailCoefficient
        b m target width hwidth :
        branchDenominator b ∣ boundaryRailCoefficient m target width)

/-- Arbitrarily long *finite* three-word addresses transport the router's
free ordinary amplitude with exact resource accounting.  The sole condition
is that their cumulative bit cost fit in the initially retained width.  This
is deliberately an endpoint balance, not an infinite-orbit claim. -/
theorem boundaryOutputCharge_prefix_balance
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hstep : ∀ k, (branch k).Step (charge k) (charge (k + 1)))
    (m target width z n : ℕ)
    (hzero : charge 0 = typedRouterBoundaryCharge m target)
    (hwidth : bitsPrefix branch n ≤ width) :
    denominatorPrefix branch n *
        (charge n +
          2 ^ (width - bitsPrefix branch n) *
            3 ^ ((minusTernary
              (routerLabel (routerPrecision target) m) - 1) +
              tritsPrefix branch n) * z) =
      numeratorPrefix branch n *
        boundaryOutputCharge m target width z +
          offsetPrefix branch n := by
  have hdiv := denominatorPrefix_dvd_boundaryRailCoefficient
    branch n m target width hwidth
  have hlift := prefix_balance_lift_of_dvd charge branch hstep n
    (boundaryRailCoefficient m target width) z hdiv
  have hclosed := prefixRailCoefficient branch n width
    (minusTernary (routerLabel (routerPrecision target) m) - 1) hwidth
  dsimp only [boundaryRailCoefficient] at hlift
  rw [hclosed, hzero] at hlift
  simpa only [boundaryOutputCharge] using hlift

/-! ## Why a uniform affine cylinder cannot regenerate width -/

/-- Equality of two affine cylinder parametrizations for every payload forces
equality of their homogeneous coefficients.  Evaluating only at zero and one
is enough; this is a symbolic identity, not a finite search. -/
theorem uniformAffineReembedding_coefficient
    (sourceBase coefficient targetBase exponent offset multiplier : ℕ)
    (hreembed : ∀ z : ℕ,
      sourceBase + coefficient * z =
        targetBase + 2 ^ exponent * (offset + multiplier * z)) :
    coefficient = 2 ^ exponent * multiplier := by
  have hzero := hreembed 0
  have hone := hreembed 1
  simp only [mul_zero, add_zero] at hzero
  simp only [mul_one] at hone
  ring_nf at hzero hone
  have hcoefficient : coefficient = multiplier * 2 ^ exponent := by omega
  simpa only [mul_comm] using hcoefficient

/-- If the new payload multiplier is odd, the alleged new cylinder exponent
is exactly the old coefficient's 2-adic valuation.  Uniform affine
reparametrization can expose existing width but can never manufacture it. -/
theorem uniformAffineReembedding_padicValNat
    (sourceBase coefficient targetBase exponent offset multiplier : ℕ)
    (hreembed : ∀ z : ℕ,
      sourceBase + coefficient * z =
        targetBase + 2 ^ exponent * (offset + multiplier * z))
    (hmultiplier : Odd multiplier) :
    padicValNat 2 coefficient = exponent := by
  rw [uniformAffineReembedding_coefficient sourceBase coefficient targetBase
    exponent offset multiplier hreembed]
  rw [padicValNat_base_pow_mul (by norm_num) hmultiplier.pos.ne']
  have hnot : ¬ 2 ∣ multiplier := by
    simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using hmultiplier
  rw [padicValNat.eq_zero_of_not_dvd hnot]
  simp

end SignedDebrisBoundaryLift
end KontoroC

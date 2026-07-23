/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterStateNoRepeat

/-!
# Gluing bare three-step EC17 replays

This file isolates the construction direction of QM121d.  It has no canonical
residue or pre-existing ray in its hypotheses: compatible positive exact
three-step replays glue to one infinite positive EC17 orbit.
-/

namespace KontoroC
namespace EtherCounterBareGlue

open EtherCounterResidueBound EtherCounterStateNoRepeat

/-- The additive defect in a bare three-step EC17 composition. -/
def threeStepDefect (_n0 n1 n2 : ℕ) : ℕ :=
  17 * (3 ^ ((6 * n1 + 11) + (6 * n2 + 11)) +
    2 ^ (8 * n1 + 15) * 3 ^ (6 * n2 + 11) +
    2 ^ ((8 * n1 + 15) + (8 * n2 + 15)))

/-- Displayed binary exponent of the three transitions beginning at `start`.
The last term uses the branch at `start+3`, as required by the EC17 target
exponent. -/
def threeStepBinaryMass (branch : ℕ → ℕ) (start : ℕ) : ℕ :=
  (8 * branch (start + 1) + 15) +
    (8 * branch (start + 2) + 15) +
    (8 * branch (start + 3) + 15)

/-- Displayed ternary exponent of the three source branches. -/
def threeStepTernaryMass (branch : ℕ → ℕ) (start : ℕ) : ℕ :=
  (6 * branch start + 11) +
    (6 * branch (start + 1) + 11) +
    (6 * branch (start + 2) + 11)

theorem binaryMass_three (branch : ℕ → ℕ) (start : ℕ) :
    binaryMass branch start 3 = threeStepBinaryMass branch start := by
  simp [binaryMass, binaryExponent, threeStepBinaryMass,
    Finset.sum_range_succ]

theorem replayTernaryMass_three (branch : ℕ → ℕ) (start : ℕ) :
    replayTernaryMass branch start 3 = threeStepTernaryMass branch start := by
  simp [replayTernaryMass, ternaryExponent, threeStepTernaryMass,
    Finset.sum_range_succ]

theorem replayOffset_three (branch : ℕ → ℕ) (start : ℕ) :
    replayOffset branch start 3 =
      threeStepDefect (branch start) (branch (start + 1))
        (branch (start + 2)) := by
  have htail2 : replayTernaryMass branch (start + 1) 2 =
      (6 * branch (start + 1) + 11) +
        (6 * branch (start + 2) + 11) := by
    simp [replayTernaryMass, ternaryExponent, Finset.sum_range_succ]
  have htail1 : replayTernaryMass branch (start + 2) 1 =
      6 * branch (start + 2) + 11 := by
    simp [replayTernaryMass, ternaryExponent, Finset.sum_range_succ]
  simp only [replayOffset]
  rw [htail2, htail1]
  simp only [replayTernaryMass_zero, pow_zero, mul_one, mul_zero, add_zero]
  simp only [threeStepDefect, binaryExponent, Nat.add_assoc, Nat.one_add,
    pow_add]
  ring

/-- The compact replay predicate at length three is exactly the displayed
one-cycle affine equation QM121a. -/
theorem composedReplayFactor_three_iff
    (branch : ℕ → ℕ) (start initial terminal : ℕ) :
    ComposedReplayFactor branch start 3 initial terminal ↔
      2 ^ threeStepBinaryMass branch start * terminal =
        3 ^ threeStepTernaryMass branch start * initial +
          threeStepDefect (branch start) (branch (start + 1))
            (branch (start + 2)) := by
  rw [ComposedReplayFactor, binaryMass_three, replayTernaryMass_three,
    replayOffset_three]
  exact eq_comm

/-- A literal zero carry—equality of the next canonical representative and
the exact affine image—produces the compact factor consumed by the gluing
theorem.  No pre-existing orbit is used. -/
theorem composedReplayFactor_of_zeroCarry
    (branch : ℕ → ℕ) (start initial image next : ℕ)
    (haffine :
      2 ^ threeStepBinaryMass branch start * image =
        3 ^ threeStepTernaryMass branch start * initial +
          threeStepDefect (branch start) (branch (start + 1))
            (branch (start + 2)))
    (hzero : next = image) :
    ComposedReplayFactor branch start 3 initial next := by
  rw [composedReplayFactor_three_iff, hzero]
  exact haffine

/-- The elementary defect estimate required by the balanced-precision
construction: the positive three-step defect is strictly smaller than its
full ternary multiplier. -/
theorem threeStepDefect_lt_ternaryMultiplier
    (n0 n1 n2 : ℕ) (hn0 : 0 < n0) :
    threeStepDefect n0 n1 n2 <
      3 ^ ((6 * n0 + 11) + (6 * n1 + 11) + (6 * n2 + 11)) := by
  let a0 := 6 * n0 + 11
  let a1 := 6 * n1 + 11
  let a2 := 6 * n2 + 11
  let b1 := 8 * n1 + 15
  let b2 := 8 * n2 + 15
  let N := 3 ^ (a0 + a1 + a2)
  have ha0 : 51 < 3 ^ a0 := by
    have hpow : 3 ^ 17 ≤ 3 ^ a0 := by
      apply Nat.pow_le_pow_right (by omega)
      dsimp only [a0]
      omega
    exact (by norm_num : 51 < 3 ^ 17).trans_le hpow
  have hb1 : 2 ^ b1 < 3 ^ a1 := by
    simpa [b1, a1] using Orbit.binary_lt_ternary_at_branch n1
  have hb2 : 2 ^ b2 < 3 ^ a2 := by
    simpa [b2, a2] using Orbit.binary_lt_ternary_at_branch n2
  have hfirst : 51 * 3 ^ (a1 + a2) < N := by
    calc
      51 * 3 ^ (a1 + a2) < 3 ^ a0 * 3 ^ (a1 + a2) :=
        Nat.mul_lt_mul_of_pos_right ha0 (by positivity)
      _ = N := by simp [N, pow_add, mul_assoc]
  have hsecondBase : 51 * 2 ^ b1 < 3 ^ a0 * 3 ^ a1 := by
    calc
      51 * 2 ^ b1 < 3 ^ a0 * 2 ^ b1 :=
        Nat.mul_lt_mul_of_pos_right ha0 (by positivity)
      _ < 3 ^ a0 * 3 ^ a1 :=
        Nat.mul_lt_mul_of_pos_left hb1 (by positivity)
  have hsecond : 51 * (2 ^ b1 * 3 ^ a2) < N := by
    calc
      51 * (2 ^ b1 * 3 ^ a2) = (51 * 2 ^ b1) * 3 ^ a2 := by ring
      _ < (3 ^ a0 * 3 ^ a1) * 3 ^ a2 :=
        Nat.mul_lt_mul_of_pos_right hsecondBase (by positivity)
      _ = N := by simp [N, pow_add]
  have hthirdBase : 51 * (2 ^ b1 * 2 ^ b2) <
      3 ^ a0 * (3 ^ a1 * 3 ^ a2) := by
    calc
      51 * (2 ^ b1 * 2 ^ b2) < 3 ^ a0 * (2 ^ b1 * 2 ^ b2) :=
        Nat.mul_lt_mul_of_pos_right ha0 (by positivity)
      _ < 3 ^ a0 * (3 ^ a1 * 2 ^ b2) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
        exact Nat.mul_lt_mul_of_pos_right hb1 (by positivity)
      _ < 3 ^ a0 * (3 ^ a1 * 3 ^ a2) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
        exact Nat.mul_lt_mul_of_pos_left hb2 (by positivity)
  have hthird : 51 * 2 ^ (b1 + b2) < N := by
    rw [pow_add]
    exact hthirdBase.trans_eq (by simp [N, pow_add, mul_assoc])
  have htriple : 3 * threeStepDefect n0 n1 n2 < 3 * N := by
    have hsum :
        51 * 3 ^ (a1 + a2) + 51 * (2 ^ b1 * 3 ^ a2) +
            51 * 2 ^ (b1 + b2) < N + N + N :=
      Nat.add_lt_add (Nat.add_lt_add hfirst hsecond) hthird
    calc
      3 * threeStepDefect n0 n1 n2 =
          51 * 3 ^ (a1 + a2) + 51 * (2 ^ b1 * 3 ^ a2) +
            51 * 2 ^ (b1 + b2) := by
              simp only [threeStepDefect]
              dsimp only [a1, a2, b1, b2]
              ring
      _ < N + N + N := hsum
      _ = 3 * N := by ring
  apply Nat.lt_of_mul_lt_mul_left
  simpa only [N, a0, a1, a2] using htriple

/-- Two canonical high blocks below the ternary modulus have signed
difference strictly inside that modulus. -/
theorem abs_signedCarry_lt
    (A H N : ℕ) (hA : A < N) (hH : H < N) :
    |(A : ℤ) - (H : ℤ)| < (N : ℤ) := by
  rw [abs_lt]
  constructor <;> omega

/-- Within the balanced range, divisibility of the signed carry by the full
ternary modulus is equivalent to literal vanishing. -/
theorem ternary_dvd_signedCarry_iff_zero
    (A H N : ℕ) (hA : A < N) (hH : H < N) :
    (N : ℤ) ∣ (A : ℤ) - (H : ℤ) ↔ (A : ℤ) - (H : ℤ) = 0 := by
  constructor
  · intro hdvd
    exact Int.eq_zero_of_abs_lt_dvd hdvd (abs_signedCarry_lt A H N hA hH)
  · intro hzero
    rw [hzero]
    exact dvd_zero _

/-- Worker-facing balanced congruence.  If the next representative differs
from the exact image by `2^p*C`, then the affine target congruence modulo `N`
is equivalent to `C=0`, provided the binary coefficient is coprime to `N` and
the balanced range has already shown `|C|<N`. -/
theorem worker_modEq_iff_signedCarry_zero
    (m p : ℕ) (N r D y rnext C : ℤ)
    (haffine : (2 : ℤ) ^ m * y = N * r + D)
    (hcarry : rnext = y + (2 : ℤ) ^ p * C)
    (hcoprime : IsCoprime N ((2 : ℤ) ^ (m + p)))
    (hbound : |C| < N) :
    (2 : ℤ) ^ m * rnext ≡ D [ZMOD N] ↔ C = 0 := by
  constructor
  · intro hmod
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hmod
    have hfactor : N ∣ (2 : ℤ) ^ (m + p) * C := by
      refine ⟨-(r + k), ?_⟩
      calc
        (2 : ℤ) ^ (m + p) * C =
            (2 : ℤ) ^ m * ((2 : ℤ) ^ p * C) := by rw [pow_add]; ring
        _ = (2 : ℤ) ^ m * (rnext - y) := by rw [hcarry]; ring
        _ = (2 : ℤ) ^ m * rnext - (2 : ℤ) ^ m * y := by ring
        _ = (2 : ℤ) ^ m * rnext - (N * r + D) := by rw [haffine]
        _ = -(D - (2 : ℤ) ^ m * rnext) - N * r := by ring
        _ = -(N * k) - N * r := by rw [hk]
        _ = N * (-(r + k)) := by ring
    have hdvd : N ∣ C := hcoprime.dvd_of_dvd_mul_left hfactor
    exact Int.eq_zero_of_abs_lt_dvd hdvd hbound
  · intro hzero
    rw [Int.modEq_iff_dvd]
    refine ⟨-r, ?_⟩
    rw [hcarry, hzero, mul_zero, add_zero, haffine]
    ring

/-- The coprimality premise in the worker theorem is automatic for the EC17
ternary modulus and every binary power. -/
theorem isCoprime_three_pow_two_pow (Q e : ℕ) :
    IsCoprime ((3 : ℤ) ^ Q) ((2 : ℤ) ^ e) := by
  have hnat : Nat.Coprime (3 ^ Q) (2 ^ e) :=
    (by norm_num : Nat.Coprime 3 2).pow Q e
  exact Nat.isCoprime_iff_coprime.mpr hnat

/-- Reading a canonical representative in blocks: a value below
`2^(p+ell)` has upper block below `2^ell`. -/
theorem upperBlock_lt_two_pow
    (p ell r s A : ℕ)
    (hrange : r < 2 ^ (p + ell))
    (hdecomp : r = s + 2 ^ p * A) :
    A < 2 ^ ell := by
  have hlower : 2 ^ p * A ≤ r := by omega
  have hscaled : 2 ^ p * A < 2 ^ p * 2 ^ ell := by
    rw [← pow_add]
    exact hlower.trans_lt hrange
  exact Nat.lt_of_mul_lt_mul_left hscaled

/-- The exact EC17 affine image of a canonical source below `2^(m+p)` has
upper `p`-bit quotient below the ternary multiplier, provided the additive
defect is itself below that multiplier. -/
theorem affineImage_upperBlock_lt
    (m p N r D y s H : ℕ)
    (hrange : r < 2 ^ (m + p))
    (hdefect : D < N)
    (haffine : 2 ^ m * y = N * r + D)
    (hdecomp : y = s + 2 ^ p * H) :
    H < N := by
  have hsum : N * r + D < N * 2 ^ (m + p) := by
    calc
      N * r + D < N * r + N := Nat.add_lt_add_left hdefect _
      _ = N * (r + 1) := by ring
      _ ≤ N * 2 ^ (m + p) := by
        exact Nat.mul_le_mul_left N (Nat.succ_le_iff.mpr hrange)
  have hyScaled : 2 ^ m * y < 2 ^ m * (N * 2 ^ p) := by
    rw [haffine]
    convert hsum using 1 <;> rw [pow_add] <;> ring
  have hy : y < N * 2 ^ p := Nat.lt_of_mul_lt_mul_left hyScaled
  have hHlower : 2 ^ p * H ≤ y := by omega
  have hHscaled : 2 ^ p * H < 2 ^ p * N := by
    calc
      2 ^ p * H ≤ y := hHlower
      _ < N * 2 ^ p := hy
      _ = 2 ^ p * N := by ring
  exact Nat.lt_of_mul_lt_mul_left hHscaled

/-- Complete canonical worker gate.  Source and target canonical ranges,
their shared low `p`-bit block, the affine equation, `D<N`, and the exponent
gate `2^ell≤N` make the full ternary congruence equivalent to equality of the
two high blocks—and hence to a literal zero carry. -/
theorem canonical_worker_modEq_iff_upperBlocks_eq
    (m p ell Q r D y rnext s A H : ℕ)
    (hsource : r < 2 ^ (m + p))
    (htarget : rnext < 2 ^ (p + ell))
    (hdefect : D < 3 ^ Q)
    (haffine : 2 ^ m * y = 3 ^ Q * r + D)
    (hnextDecomp : rnext = s + 2 ^ p * A)
    (himageDecomp : y = s + 2 ^ p * H)
    (hgate : 2 ^ ell ≤ 3 ^ Q) :
    (2 : ℤ) ^ m * (rnext : ℤ) ≡ (D : ℤ) [ZMOD (3 : ℤ) ^ Q] ↔ A = H := by
  have hA0 : A < 2 ^ ell :=
    upperBlock_lt_two_pow p ell rnext s A htarget hnextDecomp
  have hA : A < 3 ^ Q := hA0.trans_le hgate
  have hH : H < 3 ^ Q :=
    affineImage_upperBlock_lt m p (3 ^ Q) r D y s H
      hsource hdefect haffine himageDecomp
  have haffineInt :
      (2 : ℤ) ^ m * (y : ℤ) =
        (3 : ℤ) ^ Q * (r : ℤ) + (D : ℤ) := by exact_mod_cast haffine
  have hcarryInt :
      (rnext : ℤ) = (y : ℤ) +
        (2 : ℤ) ^ p * ((A : ℤ) - (H : ℤ)) := by
    have hn : (rnext : ℤ) = (s : ℤ) + (2 : ℤ) ^ p * (A : ℤ) := by
      exact_mod_cast hnextDecomp
    have hi : (y : ℤ) = (s : ℤ) + (2 : ℤ) ^ p * (H : ℤ) := by
      exact_mod_cast himageDecomp
    rw [hn, hi]
    ring
  have hbound : |(A : ℤ) - (H : ℤ)| < ((3 ^ Q : ℕ) : ℤ) :=
    abs_signedCarry_lt A H (3 ^ Q) hA hH
  have hworker := worker_modEq_iff_signedCarry_zero m p
    ((3 : ℤ) ^ Q) (r : ℤ) (D : ℤ) (y : ℤ) (rnext : ℤ)
    ((A : ℤ) - (H : ℤ)) haffineInt hcarryInt
    (isCoprime_three_pow_two_pow Q (m + p)) hbound
  simpa [sub_eq_zero] using hworker

/-- Proof-carrying consecutive three-step replays on a bare branch schedule. -/
structure ThreeReplayChain where
  branch : ℕ → ℕ
  boundary : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  boundary_pos : ∀ q, 0 < boundary q
  replay : ∀ q,
    ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3
  terminal : ∀ q, (replay q).core 3 = boundary (q + 1)

namespace ThreeReplayChain

/-- Select the core in the unique three-step replay cell containing `t`. -/
def core (c : ThreeReplayChain) (t : ℕ) : ℕ :=
  (c.replay (t / 3)).core (t % 3)

theorem core_three_mul (c : ThreeReplayChain) (q : ℕ) :
    c.core (3 * q) = c.boundary q := by
  change (c.replay (3 * q / 3)).core (3 * q % 3) = c.boundary q
  have hdiv : 3 * q / 3 = q := by omega
  have hmod : 3 * q % 3 = 0 := by omega
  rw [hdiv, hmod]
  exact (c.replay q).initial

theorem core_pos (c : ThreeReplayChain) (t : ℕ) : 0 < c.core t := by
  apply (c.replay (t / 3)).core_pos (c.boundary_pos (t / 3))
  exact Nat.le_of_lt (Nat.mod_lt t (by omega))

/-- Consecutive exact cells glue at their common boundary. -/
theorem balance (c : ThreeReplayChain) (t : ℕ) :
    2 ^ binaryExponent c.branch t * c.core (t + 1) =
      3 ^ ternaryExponent c.branch t * c.core t + 17 := by
  generalize hq : t / 3 = q
  generalize hieq : t % 3 = i
  have hi0 : t % 3 < 3 := Nat.mod_lt t (by omega)
  have hi : i < 3 := by simpa only [hieq] using hi0
  have ht : 3 * q + i = t := by
    rw [← hq, ← hieq]
    exact Nat.div_add_mod t 3
  interval_cases i
  · have ht0 : t = 3 * q := by omega
    subst t
    have hdiv0 : 3 * q / 3 = q := by omega
    have hmod0 : 3 * q % 3 = 0 := by omega
    have hdiv1 : (3 * q + 1) / 3 = q := by omega
    have hmod1 : (3 * q + 1) % 3 = 1 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv0, hmod0, hdiv1, hmod1]
    simpa [binaryExponent, ternaryExponent] using
      (c.replay q).balance 0 (by omega)
  · have ht1 : t = 3 * q + 1 := by omega
    subst t
    have hdiv1 : (3 * q + 1) / 3 = q := by omega
    have hmod1 : (3 * q + 1) % 3 = 1 := by omega
    have hdiv2 : (3 * q + 1 + 1) / 3 = q := by omega
    have hmod2 : (3 * q + 1 + 1) % 3 = 2 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv1, hmod1, hdiv2, hmod2]
    simpa [binaryExponent, ternaryExponent] using
      (c.replay q).balance 1 (by omega)
  · have ht2 : t = 3 * q + 2 := by omega
    subst t
    have hlast := (c.replay q).balance 2 (by omega)
    rw [c.terminal q] at hlast
    have hdiv2 : (3 * q + 2) / 3 = q := by omega
    have hmod2 : (3 * q + 2) % 3 = 2 := by omega
    have hdiv3 : (3 * q + 2 + 1) / 3 = q + 1 := by omega
    have hmod3 : (3 * q + 2 + 1) % 3 = 0 := by omega
    simp only [core, Nat.add_zero]
    rw [hdiv2, hmod2, hdiv3, hmod3, (c.replay (q + 1)).initial]
    simpa [binaryExponent, ternaryExponent] using hlast

/-- Gluing a chain of positive exact three-step replays produces a literal
infinite positive EC17 orbit. -/
def toOrbit (c : ThreeReplayChain) : EtherCounterStateNoRepeat.Orbit where
  branch := c.branch
  branch_pos := c.branch_pos
  core := c.core
  core_pos := c.core_pos
  balance t := by
    simpa [binaryExponent, ternaryExponent] using c.balance t

end ThreeReplayChain

/-- A three-step compact factor beginning at time `3*q` decodes to a local
replay whose branch is reindexed from zero. -/
theorem exists_shiftedReplay_of_composedFactor
    (branch : ℕ → ℕ) (boundary : ℕ → ℕ) (q : ℕ)
    (hfactor : ComposedReplayFactor branch (3 * q) 3
      (boundary q) (boundary (q + 1))) :
    ∃ replay : ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3,
      replay.core 3 = boundary (q + 1) := by
  have hshift :
      ComposedReplayFactor (fun i => branch (3 * q + i)) 0 3
        (boundary q) (boundary (q + 1)) := by
    simpa [ComposedReplayFactor, replayTernaryMass_shift,
      replayOffset_shift, binaryMass_shift] using hfactor
  exact exactReplayTo_of_composedReplayFactor
    (fun i => branch (3 * q + i)) (boundary q) (boundary (q + 1)) 3 hshift

/-- Bare positive consecutive compact factors are sufficient to construct an
infinite positive EC17 orbit.  This is the gluing endpoint needed after a
zero-carry argument has supplied the factors. -/
theorem exists_orbit_of_composedReplayFactors
    (branch : ℕ → ℕ) (boundary : ℕ → ℕ)
    (hbranch : ∀ t, 0 < branch t)
    (hboundary : ∀ q, 0 < boundary q)
    (hfactor : ∀ q, ComposedReplayFactor branch (3 * q) 3
      (boundary q) (boundary (q + 1))) :
    ∃ g : EtherCounterStateNoRepeat.Orbit,
      g.branch = branch ∧ ∀ q, g.core (3 * q) = boundary q := by
  classical
  have hexists (q : ℕ) :
      ∃ replay : ExactReplayTo (fun i => branch (3 * q + i)) (boundary q) 3,
        replay.core 3 = boundary (q + 1) :=
    exists_shiftedReplay_of_composedFactor branch boundary q (hfactor q)
  let replay (q : ℕ) := Classical.choose (hexists q)
  have hterminal (q : ℕ) : (replay q).core 3 = boundary (q + 1) :=
    Classical.choose_spec (hexists q)
  let chain : ThreeReplayChain := {
    branch := branch
    boundary := boundary
    branch_pos := hbranch
    boundary_pos := hboundary
    replay := replay
    terminal := hterminal
  }
  refine ⟨chain.toOrbit, rfl, ?_⟩
  intro q
  exact chain.core_three_mul q

/-- End-to-end zero-carry construction interface.  Exact displayed affine
images together with literal zero carries at every cycle produce an infinite
positive EC17 orbit. -/
theorem exists_orbit_of_zeroCarryChain
    (branch boundary image : ℕ → ℕ)
    (hbranch : ∀ t, 0 < branch t)
    (hboundary : ∀ q, 0 < boundary q)
    (haffine : ∀ q,
      2 ^ threeStepBinaryMass branch (3 * q) * image q =
        3 ^ threeStepTernaryMass branch (3 * q) * boundary q +
          threeStepDefect (branch (3 * q)) (branch (3 * q + 1))
            (branch (3 * q + 2)))
    (hzero : ∀ q, boundary (q + 1) = image q) :
    ∃ g : EtherCounterStateNoRepeat.Orbit,
      g.branch = branch ∧ ∀ q, g.core (3 * q) = boundary q := by
  apply exists_orbit_of_composedReplayFactors branch boundary hbranch hboundary
  intro q
  exact composedReplayFactor_of_zeroCarry branch (3 * q)
    (boundary q) (image q) (boundary (q + 1)) (haffine q) (hzero q)

/-- Eventual zero carries are enough: reindex at the first exact cycle and
construct an infinite positive orbit on that tail.  No backward extension to
the original cycle zero is asserted or needed. -/
theorem exists_tailOrbit_of_eventualZeroCarryChain
    (branch boundary image : ℕ → ℕ) (Q0 : ℕ)
    (hbranch : ∀ t, 0 < branch t)
    (hboundary : ∀ q, 0 < boundary q)
    (haffine : ∀ q ≥ Q0,
      2 ^ threeStepBinaryMass branch (3 * q) * image q =
        3 ^ threeStepTernaryMass branch (3 * q) * boundary q +
          threeStepDefect (branch (3 * q)) (branch (3 * q + 1))
            (branch (3 * q + 2)))
    (hzero : ∀ q ≥ Q0, boundary (q + 1) = image q) :
    ∃ g : EtherCounterStateNoRepeat.Orbit,
      (∀ t, g.branch t = branch (3 * Q0 + t)) ∧
        ∀ q, g.core (3 * q) = boundary (Q0 + q) := by
  let tailBranch : ℕ → ℕ := fun t => branch (3 * Q0 + t)
  let tailBoundary : ℕ → ℕ := fun q => boundary (Q0 + q)
  have htailBranch : ∀ t, 0 < tailBranch t := fun t => hbranch _
  have htailBoundary : ∀ q, 0 < tailBoundary q := fun q => hboundary _
  have htailFactor : ∀ q,
      ComposedReplayFactor tailBranch (3 * q) 3
        (tailBoundary q) (tailBoundary (q + 1)) := by
    intro q
    let originalQ := Q0 + q
    have hq : Q0 ≤ originalQ := by simp [originalQ]
    have hfactor := composedReplayFactor_of_zeroCarry branch (3 * originalQ)
      (boundary originalQ) (image originalQ) (boundary (originalQ + 1))
      (haffine originalQ hq) (hzero originalQ hq)
    simpa [tailBranch, tailBoundary, originalQ, ComposedReplayFactor,
      replayTernaryMass_shift, replayOffset_shift, binaryMass_shift,
      Nat.add_assoc,
      show 3 * Q0 + 3 * q = 3 * (Q0 + q) by ring] using hfactor
  obtain ⟨g, hgbranch, hgcore⟩ :=
    exists_orbit_of_composedReplayFactors tailBranch tailBoundary
      htailBranch htailBoundary htailFactor
  refine ⟨g, ?_, hgcore⟩
  intro t
  simpa [tailBranch] using congrFun hgbranch t

end EtherCounterBareGlue
end KontoroC

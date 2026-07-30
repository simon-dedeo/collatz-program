/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnTwoRail

/-!
# A reproducing successor-opcode tail machine

The doubled-opcode two-rail family loses binary parameter width faster than
its odd affine output can replenish it.  This file changes only the opcode
schedule: use the same legal long-return bank, but interpret the boundary
output at opcode `g+1` rather than `2g`.

For six total high cells and `g >= 3`, the boundary coefficient produces more
bits than the complete next source cylinder consumes.  An exact arithmetic
alignment theorem turns the required cylinder restriction into a bouncer
shift rule

`s |-> q + 3^R s`.

This launches a nonlinear successor-quine construction.  It does not produce
an infinite tail orbit or a Collatz counterexample.
-/

namespace KontoroC
namespace LongReturnSuccessorBouncer

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open LongReturnSelfDelimiting
open LongReturnTwoRail

/-- Dividing an odd-to-odd dyadic alignment by two leaves one odd linear
congruence.  After one finite positive lift, the entire surviving tail maps by
an affine rule with odd multiplier `c`. -/
theorem exists_odd_affine_shiftRule
    (xh yh c W : ℕ) (hc : Odd c) (hW : 0 < W) :
    ∃ r q : ℕ,
      (2 * xh + 1) + 2 * c * r = (2 * yh + 1) + 2 ^ W * q ∧
      ∀ s : ℕ,
        (2 * xh + 1) + 2 * c * (r + 2 ^ (W - 1) * s) =
          (2 * yh + 1) + 2 ^ W * (q + c * s) := by
  let m := W - 1
  let M := 2 ^ m
  have hWsplit : W = 1 + m := by dsimp [m]; omega
  obtain ⟨r0, _hr0, hr0mod⟩ :=
    solve_odd_linear_congruence c xh yh m hc
  let r := r0 + M * (yh + 1)
  have hrmod : (xh + c * r) % M = yh % M := by
    have hexpand : xh + c * r =
        xh + c * r0 + (c * (yh + 1)) * M := by
      dsimp [r]
      ring
    rw [hexpand]
    simpa [M] using hr0mod
  have hyhLe : yh ≤ xh + c * r := by
    have hcpos : 0 < c := hc.pos
    have hMpos : 0 < M := by positivity
    have hlarge : yh + 1 ≤ r := by
      dsimp [r]
      have := Nat.le_mul_of_pos_left (yh + 1) hMpos
      omega
    have hrLe : r ≤ c * r := Nat.le_mul_of_pos_left r hcpos
    omega
  have hdvd : M ∣ xh + c * r - yh := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact Nat.sub_mod_eq_zero_of_mod_eq hrmod
  let q := (xh + c * r - yh) / M
  have hhalf : xh + c * r = yh + M * q := by
    have hcancel : M * q = xh + c * r - yh := by
      dsimp only [q]
      exact Nat.mul_div_cancel' hdvd
    omega
  have hpow : 2 ^ W = 2 * M := by
    dsimp [M]
    rw [hWsplit, pow_add]
    norm_num
  refine ⟨r, q, ?_, ?_⟩
  · calc
      (2 * xh + 1) + 2 * c * r = 2 * (xh + c * r) + 1 := by ring
      _ = 2 * (yh + M * q) + 1 := by rw [hhalf]
      _ = (2 * yh + 1) + 2 ^ W * q := by rw [hpow]; ring
  · intro s
    have hmPow : 2 ^ (W - 1) = M := rfl
    calc
      (2 * xh + 1) + 2 * c * (r + 2 ^ (W - 1) * s) =
          2 * (xh + c * r + c * M * s) + 1 := by rw [hmPow]; ring
      _ = 2 * (yh + M * q + c * M * s) + 1 := by rw [hhalf]
      _ = (2 * yh + 1) + 2 ^ W * (q + c * s) := by rw [hpow]; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- The base comparison normalizes exact integers with more than one thousand bits.
set_option exponentiation.threshold 2000 in
/-- Six total high cells at opcode `g` produce more real binary height than
the full six-cell source cylinder at opcode `g+1` consumes, once `g >= 3`.
This is the exact reproduction inequality absent from the doubling ladder. -/
theorem successor_six_gain
    (g : ℕ) (hg : 3 ≤ g) :
    2 ^ S 6 (g + 1) < 3 ^ R 6 g := by
  induction g, hg using Nat.le_induction with
  | base =>
      norm_num [S, P, R, Q]
  | succ g _ ih =>
      have hstep : 2 ^ 138 < 3 ^ 102 := by norm_num
      calc
        2 ^ S 6 (g + 1 + 1) = 2 ^ S 6 (g + 1) * 2 ^ 138 := by
          simp only [S, P]
          rw [show 154 + 6 * (23 * (g + 1 + 1) + 54) =
              (154 + 6 * (23 * (g + 1) + 54)) + 138 by omega,
            pow_add]
        _ < 3 ^ R 6 g * 2 ^ 138 :=
          Nat.mul_lt_mul_of_pos_right ih (by positivity)
        _ < 3 ^ R 6 g * 3 ^ 102 :=
          Nat.mul_lt_mul_of_pos_left hstep (by positivity)
        _ = 3 ^ R 6 (g + 1) := by
          rw [show R 6 (g + 1) = R 6 g + 102 by
              simp only [R, Q]
              omega,
            pow_add]

set_option maxRecDepth 10000 in
/-- Equivalent explicit stride statement: after including the common leading
factor two, current production still exceeds the next cylinder demand. -/
theorem successor_six_stride_surplus
    (g : ℕ) (hg : 3 ≤ g) :
    2 ^ (S 6 (g + 1) + 1) < 2 * 3 ^ R 6 g := by
  have hgain := successor_six_gain g hg
  simpa [pow_succ, mul_comm] using
    (Nat.mul_lt_mul_of_pos_left hgain (by omega : 0 < 2))

/-- The six-cell architecture is a finite phase alphabet, not one fixed
macro.  Any split between base length `k` and intrinsic counter `n` with
`k+n+1=6` consumes the same complete source width. -/
theorem sixPhase_sourceWidth
    {k n : ℕ} (g : ℕ) (hphase : k + n + 1 = 6) :
    twoRailSourceWidth k g n = S 6 g + 1 := by
  simp only [twoRailSourceWidth, S]
  calc
    154 + k * P g + (n + 1) * P g + 1 =
        154 + (k + n + 1) * P g + 1 := by ring
    _ = 154 + 6 * P g + 1 := by rw [hphase]

/-- The same phase split also leaves the boundary-output multiplier
unchanged.  Switching phase can therefore write a different residue word at
zero asymptotic resource cost. -/
theorem sixPhase_boundaryOutputStride
    {k n : ℕ} (g : ℕ) (hphase : k + n + 1 = 6) :
    boundaryOutputStride k g n = 2 * 3 ^ R 6 g := by
  simp only [boundaryOutputStride, R]
  congr 2
  calc
    114 + k * Q g + (n + 1) * Q g =
        114 + (k + n + 1) * Q g := by ring
    _ = 114 + 6 * Q g := by rw [hphase]

/-- Every letter of the six-cell phase alphabet has an ordinary finite code
at every opcode. -/
theorem exists_sixPhase_code
    {k n : ℕ} (g : ℕ) (_hphase : k + n + 1 = 6) :
    ∃ F u : ℕ, 0 < F ∧ TwoRailCode k g n F u :=
  exists_finite_twoRailCode k g n

/-- The successor construction exists as a genuine universal bouncer shift
rule between complete six-cell code families.  The input tail first exposes
the one required low-bit word; every remaining `s` is transported to the next
opcode with the expanding odd affine update `q + 3^R s`. -/
theorem exists_successor_six_shiftRule
    (g : ℕ) (hg : 3 ≤ g) :
    ∃ F u y Fnext unext r q : ℕ,
      TwoRailCode 5 g 0 F u ∧
      TwoRailCode 5 (g + 1) 0 Fnext unext ∧
      Odd y ∧
      (3 ^ Q g - 2 ^ P g) * y =
        (3 ^ Q g) ^ (0 + 1) * u + 2 ^ (P g - 77) ∧
      ∀ s : ℕ,
        let t := r + 2 ^ (twoRailSourceWidth 5 (g + 1) 0 - 1) * s
        let tnext := q + 3 ^ R 6 g * s
        TwoRailStepAt 5 g 0
          (F + twoRailSourceStride 5 g 0 * t)
          (u + 2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R 5 g * t)
          5 (g + 1) 0
          (Fnext + twoRailSourceStride 5 (g + 1) 0 * tnext)
          (unext + 2 * (3 ^ Q (g + 1) - 2 ^ P (g + 1)) *
            3 ^ R 5 (g + 1) * tnext) := by
  obtain ⟨F, u, _hFpos, hcurrent⟩ := exists_finite_twoRailCode 5 g 0
  obtain ⟨Fnext, unext, _hFnextPos, hnext⟩ :=
    exists_finite_twoRailCode 5 (g + 1) 0
  rcases hcurrent with ⟨hu, z, hz, hbase, hfactor⟩
  have hcurrentCode : TwoRailCode 5 g 0 F u :=
    ⟨hu, z, hz, hbase, hfactor⟩
  obtain ⟨out, y, _hsteps, _hexit, hy, _hyFormula, houtput⟩ :=
    exists_selfDelimited_odd_exit_of_coreDefect_factor
      (g := g) (n := 0) (by omega) hz hu hfactor
  have hnextOdd := hnext.source_odd
  rcases hy with ⟨xh, hyEq⟩
  rcases hnextOdd with ⟨yh, hnextEq⟩
  let c := 3 ^ R 6 g
  let W := twoRailSourceWidth 5 (g + 1) 0
  have hc : Odd c := by
    dsimp [c]
    exact Odd.pow (by norm_num : Odd (3 : ℕ))
  have hW : 0 < W := by
    dsimp [W, twoRailSourceWidth]
    simp [S]
  obtain ⟨r, q, _halign, htail⟩ :=
    exists_odd_affine_shiftRule xh yh c W hc hW
  have hcEq : c = 3 ^ (R 5 g + (0 + 1) * Q g) := by
    dsimp [c]
    congr 1
    simp only [R, Q]
    omega
  have hboundary (s : ℕ) :
      y + boundaryOutputStride 5 g 0 *
          (r + 2 ^ (twoRailSourceWidth 5 (g + 1) 0 - 1) * s) =
        Fnext + twoRailSourceStride 5 (g + 1) 0 *
          (q + 3 ^ R 6 g * s) := by
    have hs := htail s
    rw [← hyEq, ← hnextEq] at hs
    simpa [boundaryOutputStride, twoRailSourceStride, W, c, hcEq,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hs
  refine ⟨F, u, y, Fnext, unext, r, q, hcurrentCode, hnext, ?_,
    houtput, ?_⟩
  · exact ⟨xh, hyEq⟩
  · intro s
    dsimp only
    let t := r + 2 ^ (twoRailSourceWidth 5 (g + 1) 0 - 1) * s
    let tnext := q + 3 ^ R 6 g * s
    have hcurLift := twoRailCode_lift (by omega : 0 < g) hcurrentCode t
    have hnextLift := twoRailCode_lift (by omega : 0 < g + 1) hnext tnext
    have houtLift := boundary_output_lift (k := 5) (t := t) houtput
    have hlink :
        y + boundaryOutputStride 5 g 0 * t =
          Fnext + twoRailSourceStride 5 (g + 1) 0 * tnext := by
      simpa [t, tnext] using hboundary s
    rw [hlink] at houtLift
    exact ⟨hcurLift, hnextLift, houtLift⟩

/-- All-level target of the new attempt.  Unlike a schedule of unrelated CRT
solutions, the ordinary boundary output at time `t` is literally the source
field at time `t+1`. -/
structure SuccessorSixRay (g0 : ℕ) where
  source : ℕ → ℕ
  cofactor : ℕ → ℕ
  code : ∀ t : ℕ, TwoRailCode 5 (g0 + t) 0 (source t) (cofactor t)
  link : ∀ t : ℕ,
    (3 ^ Q (g0 + t) - 2 ^ P (g0 + t)) * source (t + 1) =
      (3 ^ Q (g0 + t)) ^ (0 + 1) * cofactor t +
        2 ^ (P (g0 + t) - 77)

namespace SuccessorSixRay

/-- Every linked successor-ray step realizes the complete six-cell algebraic
return at its current opcode. -/
theorem returnBalance
    {g0 : ℕ} (ray : SuccessorSixRay g0) (hg0 : 1 < g0) (t : ℕ) :
    ReturnBalance 6 (g0 + t) (ray.source t) (ray.source (t + 1)) := by
  have hnext : TwoRailCode 5 ((g0 + t) + 1) 0
      (ray.source (t + 1)) (ray.cofactor (t + 1)) := by
    simpa [Nat.add_assoc] using ray.code (t + 1)
  have hstep : TwoRailStepAt 5 (g0 + t) 0
      (ray.source t) (ray.cofactor t)
      5 ((g0 + t) + 1) 0
      (ray.source (t + 1)) (ray.cofactor (t + 1)) :=
    ⟨ray.code t, hnext, ray.link t⟩
  exact (twoRailStepAt_realizes_boundary_return (by omega) hstep).2

/-- Boundary sources in a successor ray are positive ordinary naturals. -/
theorem source_pos
    {g0 : ℕ} (ray : SuccessorSixRay g0) (t : ℕ) : 0 < ray.source t := by
  have hodd := (ray.code t).source_odd
  exact hodd.pos

end SuccessorSixRay

end LongReturnSuccessorBouncer
end KontoroC

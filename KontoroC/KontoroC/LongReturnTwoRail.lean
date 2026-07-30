/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnSelfDelimiting

/-!
# The two-rail arithmetic state of a self-delimited long return

The internal defect cofactor and the ordinary boundary payload are different
registers.  This file records their exact coupling and proves that every
single finite macro shape is arithmetically realizable.  Thus there is no
local congruence obstruction: the remaining counterexample problem is
coherent *forward* realization, where the boundary output of one macro is the
ordinary source of the next macro at the doubled opcode.

These are algebraic long-return balances.  They do not by themselves certify
literal intermediate Collatz cells or an infinite orbit.
-/

namespace KontoroC
namespace LongReturnTwoRail

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open LongReturnSelfDelimiting

/-- The odd multiplier difference in the internal work-register equation. -/
theorem returnCoreDifference_odd (g : ℕ) :
    Odd (3 ^ Q g - 2 ^ P g) := by
  have hlt : 2 ^ P g < 3 ^ Q g :=
    (Nat.pow_lt_pow_right (by norm_num) (by omega)).trans
      (double_two_pow_P_lt_three_pow_Q g)
  apply Nat.Odd.sub_even hlt.le
  · exact Odd.pow (by norm_num : Odd (3 : ℕ))
  · exact even_two.pow_of_ne_zero (by simp [P])

/-- A reattached macro has two public rails: the ordinary source `F` and the
odd residual cofactor `u`.  The work register `z` couples them, but is not the
next ordinary source. -/
def TwoRailCode (k g n F u : ℕ) : Prop :=
  Odd u ∧ ∃ z : ℕ,
    0 < z ∧
    ReturnBalance k g F (2 ^ (P g - 77) * z) ∧
    coreDefect (3 ^ Q g) (2 ^ P g) z =
      2 ^ (n * P g + 77) * u

/-- Every ordinary boundary source of a two-rail code is odd. -/
theorem TwoRailCode.source_odd
    {k g n F u : ℕ} (hcode : TwoRailCode k g n F u) : Odd F := by
  rcases hcode with ⟨_hu, z, _hz, hbase, _hfactor⟩
  have heq := hbase
  simp only [ReturnBalance] at heq
  rw [Nat.odd_iff]
  have hmod := congrArg (fun x : ℕ ↦ x % 2) heq
  simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, S,
    Nat.odd_iff.mp (longReturn_defect_odd k g)] using hmod

/-- Eliminating the work register gives the exact two-rail source equation.
It is deliberately not presented as a scalar recurrence: `F` and `u` carry
independent ternary and dyadic constraints. -/
theorem twoRail_source_balance
    {k g n F u : ℕ} (hcode : TwoRailCode k g n F u) :
    (3 ^ Q g - 2 ^ P g) * (3 ^ R k g * F) =
      (3 ^ Q g - 2 ^ P g) * defect k g +
        2 ^ (S k g + (P g - 77)) *
          (1 + 2 ^ (n * P g + 77) * u) := by
  rcases hcode with ⟨_hu, z, hz, hbase, hfactor⟩
  let D := 3 ^ Q g - 2 ^ P g
  have hDz := coreDefect_decomp (return_core_gap g) hz
  change D * z = 1 + coreDefect (3 ^ Q g) (2 ^ P g) z at hDz
  rw [hfactor] at hDz
  simp only [ReturnBalance] at hbase
  calc
    D * (3 ^ R k g * F) =
        D * (defect k g + 2 ^ S k g *
          (2 ^ (P g - 77) * z)) := by rw [hbase]
    _ = D * defect k g +
        2 ^ (S k g + (P g - 77)) * (D * z) := by
          rw [pow_add]
          ring
    _ = D * defect k g +
        2 ^ (S k g + (P g - 77)) *
          (1 + 2 ^ (n * P g + 77) * u) := by rw [hDz]

/-- Binary width of the complete source cylinder for a fixed macro shape.
The extra bit records that the residual cofactor is odd, not merely integral. -/
def twoRailSourceWidth (k g n : ℕ) : ℕ :=
  S k g + (n + 1) * P g + 1

/-- Natural affine stride of the complete source family. -/
def twoRailSourceStride (k g n : ℕ) : ℕ :=
  2 ^ twoRailSourceWidth k g n

/-- Corresponding stride of the boundary output when the source-family
parameter is incremented once. -/
def boundaryOutputStride (k g n : ℕ) : ℕ :=
  2 * 3 ^ (R k g + (n + 1) * Q g)

/-- A fixed macro code carries a full ordinary affine tail.  The source tail
is dyadic, the cofactor tail is twice an odd multiplier, and both preserve the
exact odd-cofactor condition. -/
theorem twoRailCode_lift
    {k g n F u : ℕ} (hg : 0 < g) (hcode : TwoRailCode k g n F u)
    (t : ℕ) :
    TwoRailCode k g n
      (F + twoRailSourceStride k g n * t)
      (u + 2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t) := by
  rcases hcode with ⟨hu, z, hz, hbase, hfactor⟩
  let L := n * P g + 77
  let W := L + 1
  let znext := z + 2 ^ W * 3 ^ R k g * t
  let unext := u + 2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t
  have hP := seventy_seven_le_P hg
  have hwidth :
      S k g + (P g - 77) + W = twoRailSourceWidth k g n := by
    simp only [twoRailSourceWidth]
    dsimp [W, L]
    rw [Nat.add_mul, one_mul]
    omega
  have hbaseNext :
      ReturnBalance k g
        (F + twoRailSourceStride k g n * t)
        (2 ^ (P g - 77) * znext) := by
    simp only [ReturnBalance] at hbase ⊢
    rw [mul_add, hbase]
    dsimp [twoRailSourceStride]
    rw [← hwidth, pow_add, pow_add]
    dsimp [znext]
    ring
  have hfactorNext :
      coreDefect (3 ^ Q g) (2 ^ P g) znext =
        2 ^ (n * P g + 77) * unext := by
    let D := 3 ^ Q g - 2 ^ P g
    have hDdecomp := coreDefect_decomp (return_core_gap g) hz
    change D * z = 1 + coreDefect (3 ^ Q g) (2 ^ P g) z at hDdecomp
    rw [hfactor] at hDdecomp
    have hpowW : 2 ^ W = 2 ^ L * 2 := by
      simpa [W] using (pow_succ 2 L)
    have hznextPos : 0 < znext := by dsimp [znext]; omega
    have hnextDecomp := coreDefect_decomp (return_core_gap g) hznextPos
    change D * znext =
      1 + coreDefect (3 ^ Q g) (2 ^ P g) znext at hnextDecomp
    have hDznext : D * znext = 1 + 2 ^ L * unext := by
      calc
        D * znext = D * z + D * (2 ^ W * 3 ^ R k g * t) := by
          dsimp [znext]
          ring
        _ = (1 + 2 ^ L * u) +
            D * (2 ^ W * 3 ^ R k g * t) := by rw [hDdecomp]
        _ = 1 + 2 ^ L * unext := by
          rw [hpowW]
          dsimp [unext]
          ring
    rw [hDznext] at hnextDecomp
    dsimp [L] at hnextDecomp ⊢
    omega
  have hunext : Odd unext := by
    dsimp [unext]
    have heven : Even
        (2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t) := by
      rw [show 2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t =
          2 * ((3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t) by ring]
      exact even_two.mul_right _
    exact hu.add_even heven
  refine ⟨?_, znext, ?_, hbaseNext, hfactorNext⟩
  · simpa [unext] using hunext
  · dsimp [znext]
    omega

/-- The displayed output stride is exactly the one induced by the cofactor
tail in `twoRailCode_lift`. -/
theorem boundary_output_lift
    {k g n u y t : ℕ}
    (houtput :
      (3 ^ Q g - 2 ^ P g) * y =
        (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77)) :
    (3 ^ Q g - 2 ^ P g) *
        (y + boundaryOutputStride k g n * t) =
      (3 ^ Q g) ^ (n + 1) *
          (u + 2 * (3 ^ Q g - 2 ^ P g) * 3 ^ R k g * t) +
        2 ^ (P g - 77) := by
  rw [mul_add, houtput]
  have hstride : boundaryOutputStride k g n =
      2 * 3 ^ R k g * (3 ^ Q g) ^ (n + 1) := by
    simp only [boundaryOutputStride]
    rw [pow_add, show (n + 1) * Q g = Q g * (n + 1) by
        exact Nat.mul_comm _ _,
      ← pow_mul]
    ring
  rw [hstride]
  ring

/-- A complete next-stage source cylinder can never divide the current
one-parameter output stride.  The former contains many binary bits; the
latter contains exactly one.  Hence a whole one-parameter bouncer language
cannot be forward-invariant under this macro. -/
theorem next_sourceStride_not_dvd_boundaryOutputStride
    (k g n knext nnext : ℕ) :
    ¬ twoRailSourceStride knext (2 * g) nnext ∣
      boundaryOutputStride k g n := by
  have hwidth : 2 ≤ twoRailSourceWidth knext (2 * g) nnext := by
    simp only [twoRailSourceWidth, S]
    omega
  have hfour : 4 ∣ twoRailSourceStride knext (2 * g) nnext := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hwidth
  have hodd : Odd (3 ^ (R k g + (n + 1) * Q g)) :=
    Odd.pow (by norm_num : Odd (3 : ℕ))
  have hnotFour : ¬4 ∣ boundaryOutputStride k g n := by
    intro hdvd
    obtain ⟨q, hq⟩ := hdvd
    simp only [boundaryOutputStride] at hq
    have heq :
        3 ^ (R k g + (n + 1) * Q g) = 2 * q := by
      omega
    have heven : Even (3 ^ (R k g + (n + 1) * Q g)) :=
      ⟨q, by simpa [two_mul] using heq⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  intro hdvd
  exact hnotFour (hfour.trans hdvd)

/-- There is no one-stage arithmetic obstruction.  For every positive opcode,
return length and intrinsic counter value, one can solve the dyadic exact-
valuation condition and the independent ternary entrance condition
simultaneously. -/
theorem exists_finite_twoRailCode
    (k g n : ℕ) :
    ∃ F u : ℕ, 0 < F ∧ TwoRailCode k g n F u := by
  let D := 3 ^ Q g - 2 ^ P g
  let L := n * P g + 77
  let W := L + 1
  let E := S k g + (P g - 77)
  let M2 := 2 ^ W
  let M3 := 3 ^ R k g
  have hDodd : Odd D := by
    simpa [D] using returnCoreDifference_odd g
  have hLpos : 0 < L := by dsimp [L]; omega
  have hM2 : M2 = 2 ^ L * 2 := by
    simpa [M2, W] using (pow_succ 2 L)
  have htargetLt : 1 + 2 ^ L < M2 := by
    have hpowPos : 1 < 2 ^ L := one_lt_pow₀ (by norm_num) hLpos.ne'
    rw [hM2]
    omega
  obtain ⟨r, _hrLt, hrmod⟩ :=
    solve_odd_linear_congruence D 0 (1 + 2 ^ L) W hDodd
  have hrmodExact : (D * r) % M2 = 1 + 2 ^ L := by
    simpa [M2, Nat.mod_eq_of_lt htargetLt] using hrmod
  have hrpos : 0 < r := by
    by_contra hnot
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hrzero, mul_zero, Nat.zero_mod] at hrmodExact
    have htargetPos : 0 < 1 + 2 ^ L := by positivity
    omega
  let q := (D * r) / M2
  have hrEq : D * r = 1 + 2 ^ L + M2 * q := by
    calc
      D * r = (D * r) % M2 + M2 * ((D * r) / M2) :=
        (Nat.mod_add_div _ _).symm
      _ = 1 + 2 ^ L + M2 * q := by rw [hrmodExact]
  let base := defect k g + 2 ^ E * r
  let coeff := 2 ^ (E + W)
  have hcop : Nat.Coprime coeff M3 := by
    dsimp [coeff, M3]
    exact Nat.Coprime.pow (E + W) (R k g) (by norm_num)
  obtain ⟨t, _htLt, htmod⟩ :=
    solve_coprime_linear_congruence coeff base 0 M3
      (by positivity) hcop
  have htmodZero : (base + coeff * t) % M3 = 0 := by
    simpa using htmod
  let z := r + M2 * t
  have hnumerator :
      defect k g + 2 ^ E * z = base + coeff * t := by
    dsimp [z, base, coeff, M2]
    rw [pow_add]
    ring
  have hentrance : EntranceCompatible k g z := by
    simp only [EntranceCompatible]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [show 3 ^ R k g = M3 by rfl]
    rw [show S k g + (P g - 77) = E by rfl, hnumerator]
    exact htmodZero
  let u := 1 + 2 * q + 2 * D * t
  have hu : Odd u := by
    dsimp [u]
    rw [Nat.odd_iff]
    simp [Nat.add_mod, Nat.mul_mod]
  have hDz : D * z = 1 + 2 ^ L * u := by
    calc
      D * z = D * r + D * (M2 * t) := by dsimp [z]; ring
      _ = (1 + 2 ^ L + M2 * q) + D * (M2 * t) := by rw [hrEq]
      _ = 1 + 2 ^ L * u := by
        rw [hM2]
        dsimp [u]
        ring
  have hz : 0 < z := by dsimp [z]; omega
  have hfactor :
      coreDefect (3 ^ Q g) (2 ^ P g) z = 2 ^ L * u := by
    change D * z - 1 = 2 ^ L * u
    omega
  obtain ⟨F, hbase⟩ :=
    entranceCompatible_iff_exists_returnBalance.mp hentrance
  have hdefectPos : 0 < defect k g := by
    apply Nat.add_pos_left
    exact Nat.mul_pos (by positivity) (by dsimp [b0]; positivity)
  have hFpos : 0 < F := by
    by_contra hnot
    have hFzero : F = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [ReturnBalance] at hbase
    rw [hFzero, mul_zero] at hbase
    omega
  refine ⟨F, u, hFpos, hu, z, hz, hbase, ?_⟩
  simpa [L] using hfactor

/-- The exact forward-link predicate at an arbitrary next opcode.  The next
stage receives the boundary
payload `Fnext`; its new work register remains existentially packaged inside
the next `TwoRailCode`.  This prevents the unsound scalar identification
`Fnext = znext`. -/
def TwoRailStepAt
    (k g n F u knext gnext nnext Fnext unext : ℕ) : Prop :=
  TwoRailCode k g n F u ∧
  TwoRailCode knext gnext nnext Fnext unext ∧
  (3 ^ Q g - 2 ^ P g) * Fnext =
    (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77)

/-- Doubled-opcode specialization retained for the original architecture. -/
def DoubledTwoRailStep
    (k g n F u knext nnext Fnext unext : ℕ) : Prop :=
  TwoRailStepAt k g n F u knext (2 * g) nnext Fnext unext

/-- A forward-linked two-rail step really reattaches the complete current
macro to the next ordinary boundary source.  No retroactive source lift is
used in this theorem. -/
theorem twoRailStepAt_realizes_boundary_return
    {k g n F u knext gnext nnext Fnext unext : ℕ} (hg : 1 < g)
    (hstep :
      TwoRailStepAt k g n F u knext gnext nnext Fnext unext) :
    0 < Fnext ∧ ReturnBalance (k + n + 1) g F Fnext := by
  rcases hstep with ⟨hcurrent, hnext, houtput⟩
  rcases hcurrent with ⟨hu, z, hz, hbase, hfactor⟩
  obtain ⟨out, y, hsteps, hexit, _hy, _hyFormula, hclosed⟩ :=
    exists_selfDelimited_odd_exit_of_coreDefect_factor hg hz hu hfactor
  have hDpos : 0 < 3 ^ Q g - 2 ^ P g := by
    exact Nat.sub_pos_of_lt
      ((Nat.pow_lt_pow_right (by norm_num) (by omega)).trans
        (double_two_pow_P_lt_three_pow_Q g))
  have hyEq : y = Fnext := by
    apply Nat.eq_of_mul_eq_mul_left hDpos
    exact hclosed.trans houtput.symm
  have hreturn :=
    returnBalance_exit_of_returnLengthCoreSteps (by omega)
      hbase hsteps hexit
  have hFnextPos : 0 < Fnext := by
    rcases hnext with ⟨_hunext, znext, _hznext, hnextBase, _hnextFactor⟩
    have hdefectPos : 0 < defect knext gnext := by
      apply Nat.add_pos_left
      exact Nat.mul_pos (by positivity) (by dsimp [b0]; positivity)
    by_contra hnot
    have hzero : Fnext = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [ReturnBalance] at hnextBase
    rw [hzero, mul_zero] at hnextBase
    omega
  rw [hyEq] at hreturn
  exact ⟨hFnextPos, hreturn⟩

/-- The generic consumer specializes back to the doubled-opcode step. -/
theorem doubledTwoRailStep_realizes_boundary_return
    {k g n F u knext nnext Fnext unext : ℕ} (hg : 1 < g)
    (hstep :
      DoubledTwoRailStep k g n F u knext nnext Fnext unext) :
    0 < Fnext ∧ ReturnBalance (k + n + 1) g F Fnext :=
  twoRailStepAt_realizes_boundary_return hg hstep

end LongReturnTwoRail
end KontoroC

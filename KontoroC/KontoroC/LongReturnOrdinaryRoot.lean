/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnLengthHensel
import KontoroC.OutwardCodeCompactness

/-!
# The ordinary-root gate for adjacent long returns

The unconditional splice in `LongReturnLengthHensel` obtains the next pair by
lifting the current source through a positive dyadic tail.  Iterating that
construction generally produces a compatible 2-adic source rather than one
fixed ordinary natural.

This file isolates the exact alternative needed for an ordinary
counterexample.  First, it characterizes the sources of adjacent return pairs
by one explicit dyadic congruence and one Archimedean lower bound.  Second, it
proves that a monotone tower of retroactive source lifts stabilizes at an
ordinary root exactly when the lift tails are eventually zero.  Consequently
the constructive target is an eventual *forward zero-lift chain*: the longer
endpoint itself must satisfy the next source congruence, without changing any
earlier source.

These are reductions, not an infinite orbit.  Literal intermediate-cell
semantics remain a separate gate.
-/

namespace KontoroC
namespace LongReturnOrdinaryRoot

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open OutwardCodeCompactness

/-- A source supports the two consecutive algebraic return lengths `k` and
`k+1`. -/
def AdjacentSource (k g F : ℕ) : Prop :=
  ∃ X Y : ℕ,
    ReturnBalance k g F X ∧ ReturnBalance (k + 1) g F Y

/-- The complete dyadic source precision consumed by an adjacent pair. -/
def sourceWidth (k g : ℕ) : ℕ := S k g + P g

/-- The marker bit sits exactly 77 places below the source modulus. -/
def markerWidth (k g : ℕ) : ℕ := S k g + (P g - 77)

/-- Exact source-cylinder characterization.  Apart from positivity of the
residual numerator, supporting an adjacent pair is one dyadic congruence.
The coefficient is odd, hence this is one residue class modulo
`2^(S(k,g)+P(g))`. -/
theorem adjacentSource_iff_mod
    {k g F : ℕ} (hg : 0 < g) :
    AdjacentSource k g F ↔
      defect k g < 3 ^ R k g * F ∧
      (3 ^ (Q g + R k g) * F) % 2 ^ sourceWidth k g =
        (3 ^ Q g * defect k g + 2 ^ markerWidth k g) %
          2 ^ sourceWidth k g := by
  let e := P g - 77
  let E := S k g + e
  let W := S k g + P g
  let modulus := 2 ^ W
  let ternary := 3 ^ Q g
  let slope := 3 ^ R k g
  let forcing := defect k g
  have hP := seventy_seven_le_P hg
  have hPsplit : P g = e + 77 := by dsimp [e]; omega
  have hWsplit : W = E + 77 := by
    dsimp [W, E]
    omega
  have hmarkerLt : 2 ^ E < modulus := by
    dsimp [modulus]
    rw [hWsplit]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  constructor
  · rintro ⟨X, Y, hbase, hnext⟩
    have houtput := (returnBalance_succ_iff hg hbase).mp hnext
    have hforcingLt : forcing < slope * F := by
      simp only [ReturnBalance] at hbase
      change slope * F = forcing + 2 ^ S k g * X at hbase
      rw [hbase]
      have hXPos : 0 < X := by
        have hmarkerPos : 0 < 2 ^ (P g - 77) := by positivity
        by_contra hnot
        have hXzero : X = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hXzero, mul_zero] at houtput
        omega
      exact Nat.lt_add_of_pos_right
        (Nat.mul_pos (by positivity) hXPos)
    refine ⟨hforcingLt, ?_⟩
    have heq : ternary * slope * F =
        ternary * forcing + 2 ^ E + modulus * Y := by
      have hbaseLocal :
          slope * F = forcing + 2 ^ S k g * X := by
        simpa [ReturnBalance, slope, forcing] using hbase
      calc
        ternary * slope * F = ternary * (slope * F) := by ring
        _ = ternary * (forcing + 2 ^ S k g * X) := by
          rw [hbaseLocal]
        _ = ternary * forcing + 2 ^ S k g * (ternary * X) := by
          ring
        _ = ternary * forcing +
            2 ^ S k g * (2 ^ (P g - 77) + 2 ^ P g * Y) := by
          rw [houtput]
        _ = ternary * forcing + 2 ^ E + modulus * Y := by
          dsimp [modulus, W, E, e]
          rw [pow_add, pow_add]
          ring
    have hlocal : (ternary * slope * F) % modulus =
        (ternary * forcing + 2 ^ E) % modulus := by
      rw [heq]
      simp
    simpa [sourceWidth, markerWidth, ternary, slope, forcing, modulus,
      W, E, pow_add] using hlocal
  · rintro ⟨hforcingLt, hmod⟩
    change forcing < slope * F at hforcingLt
    let N := slope * F - forcing
    have hdecomp : slope * F = forcing + N := by
      dsimp [N]
      omega
    have hmodLocal : (ternary * slope * F) % modulus =
        (ternary * forcing + 2 ^ E) % modulus := by
      simpa [sourceWidth, markerWidth, ternary, slope, forcing, modulus,
        W, E, pow_add] using hmod
    have hmodEq :
        ternary * slope * F ≡ ternary * forcing + 2 ^ E
          [MOD modulus] := hmodLocal
    have hleft :
        ternary * slope * F = ternary * forcing + ternary * N := by
      calc
        ternary * slope * F = ternary * (slope * F) := by ring
        _ = ternary * (forcing + N) := by rw [hdecomp]
        _ = ternary * forcing + ternary * N := by ring
    rw [hleft] at hmodEq
    have hNModEq : ternary * N ≡ 2 ^ E [MOD modulus] :=
      Nat.ModEq.add_left_cancel
        (Nat.ModEq.refl (ternary * forcing)) hmodEq
    have hNmod : (ternary * N) % modulus = 2 ^ E := by
      rw [Nat.ModEq] at hNModEq
      simpa [Nat.mod_eq_of_lt hmarkerLt] using hNModEq
    let Y := (ternary * N) / modulus
    have hTN : ternary * N = 2 ^ E + modulus * Y := by
      calc
        ternary * N = (ternary * N) % modulus +
            modulus * ((ternary * N) / modulus) :=
          (Nat.mod_add_div _ _).symm
        _ = 2 ^ E + modulus * Y := by rw [hNmod]
    have hdvdProd : 2 ^ E ∣ ternary * N := by
      refine ⟨1 + 2 ^ 77 * Y, ?_⟩
      rw [hTN]
      dsimp [modulus]
      rw [hWsplit, pow_add]
      ring
    have hcop : Nat.Coprime (2 ^ E) ternary := by
      dsimp [ternary]
      exact Nat.Coprime.pow E (Q g) (by norm_num)
    have hdvd : 2 ^ E ∣ N := hcop.dvd_of_dvd_mul_left hdvdProd
    obtain ⟨z, hz⟩ := hdvd
    let X := 2 ^ e * z
    have hNoutput : N = 2 ^ S k g * X := by
      dsimp [X, E] at hz ⊢
      rw [hz, pow_add]
      ring
    have hbase : ReturnBalance k g F X := by
      simp only [ReturnBalance]
      change slope * F = forcing + 2 ^ S k g * X
      rw [hdecomp, hNoutput]
    have hcell : HenselStep g z Y := by
      simp only [HenselStep]
      change ternary * z = 1 + 2 ^ 77 * Y
      have hfactor :
          2 ^ E * (ternary * z) =
            2 ^ E * (1 + 2 ^ 77 * Y) := by
        calc
          2 ^ E * (ternary * z) = ternary * N := by rw [hz]; ring
          _ = 2 ^ E + modulus * Y := hTN
          _ = 2 ^ E * (1 + 2 ^ 77 * Y) := by
            dsimp [modulus]
            rw [hWsplit, pow_add]
            ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ E) hfactor
    have hnext : ReturnBalance (k + 1) g F Y := by
      apply (returnBalance_succ_iff_hensel hg hbase).2
      refine ⟨z, henselStep_odd hcell, ?_, hcell⟩
      rfl
    exact ⟨X, Y, hbase, hnext⟩

/-- The odd coefficient makes the source congruence solvable at every finite
length. -/
theorem exists_sourceResidue (k g : ℕ) :
    ∃ r : ℕ, r < 2 ^ sourceWidth k g ∧
      (3 ^ (Q g + R k g) * r) % 2 ^ sourceWidth k g =
        (3 ^ Q g * defect k g + 2 ^ markerWidth k g) %
          2 ^ sourceWidth k g := by
  have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
  obtain ⟨r, hr, hmod⟩ := solve_odd_linear_congruence
    (3 ^ (Q g + R k g)) 0
    (3 ^ Q g * defect k g + 2 ^ markerWidth k g)
    (sourceWidth k g) (Odd.pow (n := Q g + R k g) hthree)
  exact ⟨r, hr, by simpa using hmod⟩

/-- Canonical least representative of the unique adjacent-source cylinder. -/
noncomputable def sourceResidue (k g : ℕ) : ℕ :=
  Nat.find (exists_sourceResidue k g)

theorem sourceResidue_spec (k g : ℕ) :
    sourceResidue k g < 2 ^ sourceWidth k g ∧
      (3 ^ (Q g + R k g) * sourceResidue k g) %
          2 ^ sourceWidth k g =
        (3 ^ Q g * defect k g + 2 ^ markerWidth k g) %
          2 ^ sourceWidth k g :=
  Nat.find_spec (exists_sourceResidue k g)

/-- Uniqueness of the adjacent-source residue. -/
theorem source_mod_eq_sourceResidue_of_congruence
    {k g F : ℕ}
    (hmod :
      (3 ^ (Q g + R k g) * F) % 2 ^ sourceWidth k g =
        (3 ^ Q g * defect k g + 2 ^ markerWidth k g) %
          2 ^ sourceWidth k g) :
    F % 2 ^ sourceWidth k g = sourceResidue k g := by
  let coeff := 3 ^ (Q g + R k g)
  let modulus := 2 ^ sourceWidth k g
  let target := 3 ^ Q g * defect k g + 2 ^ markerWidth k g
  have hF : coeff * F ≡ target [MOD modulus] := by
    rw [Nat.ModEq]
    simpa [coeff, modulus, target] using hmod
  have hr : coeff * sourceResidue k g ≡ target [MOD modulus] := by
    rw [Nat.ModEq]
    simpa [coeff, modulus, target] using (sourceResidue_spec k g).2
  have hcancelInput :
      coeff * F ≡ coeff * sourceResidue k g [MOD modulus] :=
    hF.trans hr.symm
  have hcop : Nat.Coprime modulus coeff := by
    dsimp [modulus, coeff]
    exact Nat.Coprime.pow (sourceWidth k g) (Q g + R k g) (by norm_num)
  have hcancel : F ≡ sourceResidue k g [MOD modulus] :=
    Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hcancelInput
  exact Nat.mod_eq_of_modEq hcancel (sourceResidue_spec k g).1

/-- Fully explicit version of the source-cylinder test. -/
theorem adjacentSource_iff_sourceResidue
    {k g F : ℕ} (hg : 0 < g) :
    AdjacentSource k g F ↔
      defect k g < 3 ^ R k g * F ∧
        F % 2 ^ sourceWidth k g = sourceResidue k g := by
  rw [adjacentSource_iff_mod hg]
  constructor
  · rintro ⟨hpos, hmod⟩
    exact ⟨hpos, source_mod_eq_sourceResidue_of_congruence hmod⟩
  · rintro ⟨hpos, hresidue⟩
    refine ⟨hpos, ?_⟩
    let coeff := 3 ^ (Q g + R k g)
    let modulus := 2 ^ sourceWidth k g
    calc
      (3 ^ (Q g + R k g) * F) % 2 ^ sourceWidth k g =
          (coeff * (F % modulus)) % modulus := by
            simp [coeff, modulus, Nat.mul_mod]
      _ = (coeff * sourceResidue k g) % modulus := by rw [hresidue]
      _ = (3 ^ Q g * defect k g + 2 ^ markerWidth k g) %
          2 ^ sourceWidth k g := by
            simpa [coeff, modulus] using (sourceResidue_spec k g).2

/-- Once the source modulus exceeds an ordinary source, adjacency forces
literal equality with the canonical representative, not merely congruence. -/
theorem source_eq_sourceResidue_of_adjacentSource_of_lt
    {k g F : ℕ} (hg : 0 < g) (hsource : AdjacentSource k g F)
    (hlt : F < 2 ^ sourceWidth k g) :
    F = sourceResidue k g := by
  have hmod := (adjacentSource_iff_sourceResidue hg).mp hsource |>.2
  rw [Nat.mod_eq_of_lt hlt] at hmod
  exact hmod

/-- Elementary affine-division obstruction.  If `A` is more than twice `B`
and coprime to it, no natural sequence can satisfy
`A*z_n = 1+B*z_(n+1)` forever.  Conjugating by the rational fixed point makes
`B^n` divide one fixed positive integer for every `n`. -/
theorem no_supercritical_affine_division_chain
    {A B : ℕ} (hBone : 1 < B) (htwo : 2 * B < A)
    (hcop : Nat.Coprime B A) :
    ¬ ∃ z : ℕ → ℕ, ∀ n, A * z n = 1 + B * z (n + 1) := by
  rintro ⟨z, hz⟩
  let D := A - B
  have hBpos : 0 < B := by omega
  have hDone : 1 < D := by
    dsimp [D]
    omega
  have hDadd : D + B = A := by
    dsimp [D]
    omega
  have hzpos : ∀ n, 0 < z n := by
    intro n
    by_contra hnot
    have hzero : z n = 0 := Nat.eq_zero_of_not_pos hnot
    have hn := hz n
    rw [hzero, mul_zero] at hn
    have hBnext : 0 ≤ B * z (n + 1) := Nat.zero_le _
    omega
  let w : ℕ → ℕ := fun n => D * z n - 1
  have hwdecomp : ∀ n, D * z n = 1 + w n := by
    intro n
    dsimp [w]
    have hprod : 0 < D * z n := Nat.mul_pos (by omega) (hzpos n)
    omega
  have hwpos : ∀ n, 0 < w n := by
    intro n
    have hprod : 1 < D * z n := by
      have hzOne : 1 ≤ z n := hzpos n
      exact lt_of_lt_of_le hDone (Nat.le_mul_of_pos_right D (hzpos n))
    dsimp [w]
    omega
  have hwrec : ∀ n, B * w (n + 1) = A * w n := by
    intro n
    have hscaled := congrArg (fun x : ℕ => D * x) (hz n)
    have hn := hwdecomp n
    have hnext := hwdecomp (n + 1)
    nlinarith
  have hiterate : ∀ n, B ^ n * w n = A ^ n * w 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          B ^ (n + 1) * w (n + 1) =
              B ^ n * (B * w (n + 1)) := by rw [pow_succ]; ring
          _ = B ^ n * (A * w n) := by rw [hwrec n]
          _ = A * (B ^ n * w n) := by ring
          _ = A * (A ^ n * w 0) := by rw [ih]
          _ = A ^ (n + 1) * w 0 := by rw [pow_succ]; ring
  have hdvd : ∀ n, B ^ n ∣ w 0 := by
    intro n
    have hdvdProduct : B ^ n ∣ A ^ n * w 0 :=
      ⟨w n, (hiterate n).symm⟩
    exact (hcop.pow n n).dvd_of_dvd_mul_left hdvdProduct
  let n := w 0 + 1
  have hlarge : w 0 < B ^ n := by
    change w 0 < B ^ (w 0 + 1)
    exact (Nat.lt_succ_self (w 0)).trans (Nat.lt_pow_self hBone)
  have hsmall : B ^ n ≤ w 0 :=
    Nat.le_of_dvd (hwpos 0) (hdvd n)
  omega

/-- At one fixed opcode, consuming adjacent return lengths forever is
impossible over ordinary naturals.  The Hensel recurrence is supercritical:
`3^Q z_n = 1+2^P z_(n+1)`. -/
theorem no_infinite_fixed_opcode_hensel_chain (g : ℕ) :
    ¬ ∃ z : ℕ → ℕ, ∀ n,
      3 ^ Q g * z n = 1 + 2 ^ P g * z (n + 1) := by
  apply no_supercritical_affine_division_chain
  · have hPpos : 0 < P g := by simp [P]
    exact one_lt_pow₀ (by norm_num) hPpos.ne'
  · have hgain := double_two_pow_P_lt_three_pow_Q g
    rw [pow_succ] at hgain
    simpa [mul_comm] using hgain
  · exact Nat.Coprime.pow (P g) (Q g) (by norm_num)

/-- Adjacent-source cylinders are nested as the return length grows.  In fact
one return of length `k+1` already reconstructs the shorter sibling at `k`;
the appended defect is exactly the marker term required by the Hensel
equation. -/
theorem adjacentSource_of_succ
    {k g F : ℕ} (hg : 0 < g) :
    AdjacentSource (k + 1) g F → AdjacentSource k g F := by
  rintro ⟨Xnext, Ynext, hnext, _hlonger⟩
  let e := P g - 77
  let E := S k g + e
  let slope := 3 ^ R k g
  let forcing := defect k g
  let ternary := 3 ^ Q g
  have hP := seventy_seven_le_P hg
  have hPsplit : P g = e + 77 := by dsimp [e]; omega
  have hR := R_succ_eq k g
  have hS := S_succ_eq k g
  have hdefect := defect_succ k g
  have happended := appended_defect_exponent_eq k g hg
  have hscaled :
      ternary * (slope * F) =
        ternary * forcing + 2 ^ E +
          2 ^ (S k g + P g) * Xnext := by
    simp only [ReturnBalance] at hnext
    calc
      ternary * (slope * F) = 3 ^ R (k + 1) g * F := by
        dsimp [ternary, slope]
        rw [hR, pow_add]
        ring
      _ = defect (k + 1) g + 2 ^ S (k + 1) g * Xnext := hnext
      _ = ternary * forcing + 2 ^ E +
          2 ^ (S k g + P g) * Xnext := by
        rw [hdefect, hS]
        dsimp [ternary, forcing, E, e]
        rw [happended]
  have hforcingLt : forcing < slope * F := by
    by_contra hnot
    have hle : slope * F ≤ forcing := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_left ternary hle
    rw [hscaled] at hmul
    have hmarkerPos : 0 < 2 ^ E := by positivity
    omega
  let N := slope * F - forcing
  have hdecomp : slope * F = forcing + N := by
    dsimp [N]
    omega
  have hNscaled :
      ternary * N = 2 ^ E + 2 ^ (S k g + P g) * Xnext := by
    nlinarith
  have hdvdProd : 2 ^ S k g ∣ ternary * N := by
    refine ⟨2 ^ e + 2 ^ P g * Xnext, ?_⟩
    rw [hNscaled]
    dsimp [E]
    rw [pow_add, pow_add]
    ring
  have hcop : Nat.Coprime (2 ^ S k g) ternary := by
    dsimp [ternary]
    exact Nat.Coprime.pow (S k g) (Q g) (by norm_num)
  have hdvd : 2 ^ S k g ∣ N := hcop.dvd_of_dvd_mul_left hdvdProd
  obtain ⟨X, hX⟩ := hdvd
  have hbase : ReturnBalance k g F X := by
    simp only [ReturnBalance]
    change slope * F = forcing + 2 ^ S k g * X
    rw [hdecomp, hX]
  have houtput :
      ternary * X = 2 ^ e + 2 ^ P g * Xnext := by
    have hfactor :
        2 ^ S k g * (ternary * X) =
          2 ^ S k g * (2 ^ e + 2 ^ P g * Xnext) := by
      calc
        2 ^ S k g * (ternary * X) = ternary * N := by rw [hX]; ring
        _ = 2 ^ E + 2 ^ (S k g + P g) * Xnext := hNscaled
        _ = 2 ^ S k g * (2 ^ e + 2 ^ P g * Xnext) := by
          dsimp [E]
          rw [pow_add, pow_add]
          ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hfactor
  have hnext' : ReturnBalance (k + 1) g F Xnext := by
    apply (returnBalance_succ_iff hg hbase).2
    simpa [ternary, e] using houtput
  exact ⟨X, Xnext, hbase, hnext'⟩

/-- Hence any unbounded collection of supported return lengths at one fixed
source would force support at every length. -/
theorem adjacentSource_of_exists_ge
    {g F k : ℕ} (hg : 0 < g)
    (hcofinal : ∀ bound, ∃ j, bound ≤ j ∧ AdjacentSource j g F) :
    AdjacentSource k g F := by
  obtain ⟨j, hkj, hj⟩ := hcofinal k
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  clear hkj
  induction d with
  | zero => exact hj
  | succ d ih =>
      apply ih
      exact adjacentSource_of_succ hg hj

/-- Fixed source plus unbounded adaptive return length is impossible.  This
closes the tempting escape of camping at one opcode and using `k` as an
unbounded counter; a genuine ordinary construction must keep moving through
opcode levels. -/
theorem no_fixed_source_cofinal_adjacent_lengths
    {g F : ℕ} (hg : 0 < g) :
    ¬ (∀ bound, ∃ k, bound ≤ k ∧ AdjacentSource k g F) := by
  intro hcofinal
  have hall : ∀ k, AdjacentSource k g F := fun k =>
    adjacentSource_of_exists_ge hg hcofinal
  classical
  choose X Y hbase hnext using hall
  have hYeq : ∀ k, Y k = X (k + 1) := by
    intro k
    have hleft := hnext k
    have hright := hbase (k + 1)
    simp only [ReturnBalance] at hleft hright
    have hmul : 2 ^ S (k + 1) g * Y k =
        2 ^ S (k + 1) g * X (k + 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hzexists : ∀ k, ∃ z : ℕ,
      X k = 2 ^ (P g - 77) * z ∧ HenselStep g z (Y k) := by
    intro k
    obtain ⟨z, _hzOdd, hX, hcell⟩ :=
      (returnBalance_succ_iff_hensel hg (hbase k)).mp (hnext k)
    exact ⟨z, hX, hcell⟩
  choose z hX hcell using hzexists
  apply no_infinite_fixed_opcode_hensel_chain g
  refine ⟨z, fun k ↦ ?_⟩
  have hcellEq := hcell k
  simp only [HenselStep] at hcellEq
  calc
    3 ^ Q g * z k = 1 + 2 ^ 77 * Y k := hcellEq
    _ = 1 + 2 ^ 77 * X (k + 1) := by rw [hYeq k]
    _ = 1 + 2 ^ P g * z (k + 1) := by
      rw [hX (k + 1)]
      have hP := seventy_seven_le_P hg
      have hpPow : 2 ^ 77 * 2 ^ (P g - 77) = 2 ^ P g := by
        rw [← pow_add]
        congr 1
        omega
      calc
        1 + 2 ^ 77 * (2 ^ (P g - 77) * z (k + 1)) =
            1 + (2 ^ 77 * 2 ^ (P g - 77)) * z (k + 1) := by ring
        _ = 1 + 2 ^ P g * z (k + 1) := by rw [hpPow]

/-- A literal forward adjacent splice: the longer endpoint is the next source,
with no retroactive change to the current source. -/
def ForwardAdjacentSplice (k g source nextSource : ℕ) : Prop :=
  ∃ shorter : ℕ,
    ReturnBalance k g source shorter ∧
      ReturnBalance (k + 1) g source nextSource

theorem forwardAdjacentSplice_gives_adjacentSource
    {k g source nextSource : ℕ}
    (h : ForwardAdjacentSplice k g source nextSource) :
    AdjacentSource k g source := by
  obtain ⟨shorter, hshort, hlong⟩ := h
  exact ⟨shorter, nextSource, hshort, hlong⟩

/-- The exact zero-lift test for the next doubled opcode. -/
theorem zeroLiftExtension_iff_mod
    {knext g endpoint : ℕ} (hg : 0 < g) :
    AdjacentSource knext (2 * g) endpoint ↔
      defect knext (2 * g) < 3 ^ R knext (2 * g) * endpoint ∧
      (3 ^ (Q (2 * g) + R knext (2 * g)) * endpoint) %
          2 ^ sourceWidth knext (2 * g) =
        (3 ^ Q (2 * g) * defect knext (2 * g) +
          2 ^ markerWidth knext (2 * g)) %
            2 ^ sourceWidth knext (2 * g) := by
  exact adjacentSource_iff_mod (by omega)

/-- A retroactive lift is the exact source update appearing in
`adjacent_return_realization_lift`. -/
def RetroactiveLift (k g source tail nextSource : ℕ) : Prop :=
  nextSource = source + 2 ^ (S k g + P g) * tail

/-- In a tower built by the unconditional splice, the ordinary source
stabilizes exactly when the retroactive tail is eventually zero.  Thus an
ordinary counterexample from this architecture must eventually become a
genuine forward zero-lift chain. -/
theorem eventuallyConstant_iff_eventuallyZero_retroactiveTail
    (k g source tail : ℕ → ℕ)
    (hlift : ∀ n, RetroactiveLift (k n) (g n) (source n) (tail n)
      (source (n + 1))) :
    EventuallyConstant source ↔
      ∃ K, ∀ n, K ≤ n → tail n = 0 := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun n hn ↦ ?_⟩
    have hstep : source (n + 1) = source n := by
      rw [hK n hn, hK (n + 1) (by omega)]
    have hu := hlift n
    simp only [RetroactiveLift] at hu
    rw [hstep] at hu
    have hpow : 0 < 2 ^ (S (k n) (g n) + P (g n)) := by positivity
    nlinarith
  · rintro ⟨K, hzero⟩
    have hstep : ∀ n, K ≤ n → source (n + 1) = source n := by
      intro n hn
      have hu := hlift n
      simp only [RetroactiveLift, hzero n hn, mul_zero, add_zero] at hu
      exact hu
    refine ⟨K, fun n hn ↦ ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction d with
    | zero => rfl
    | succ d ih =>
        rw [Nat.add_succ, hstep (K + d) (Nat.le_add_right K d),
          ih (Nat.le_add_right K d)]

end LongReturnOrdinaryRoot
end KontoroC

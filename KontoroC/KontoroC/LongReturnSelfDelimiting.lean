/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongReturnOrdinaryRoot

/-!
# Adaptive return length is an intrinsic finite counter

The adjacent-long-return construction exposed the recurrence

`A*z = 1 + B*z'`,

where `A = 3^Q(g)` and `B = 2^P(g)`.  This file proves that the number of
successive legal cells is not an external instruction.  It is exactly the
binary valuation of the positive fixed-point defect

`(A-B)*z-1`,

measured in blocks of width `P(g)`.  Thus the payload itself supplies a
self-delimiting unary counter: continue while one complete block remains and
exit at the first failed block.

This removes the external return-length schedule, but it does not construct
the required doubled-opcode zero-lift chain or an ordinary Collatz orbit.
-/

namespace KontoroC
namespace LongReturnSelfDelimiting

open LongDoublingQuineThreshold
open LongReturnLengthHensel
open LongReturnOrdinaryRoot

theorem longReturn_defect_odd (k g : ℕ) : Odd (defect k g) := by
  rw [Nat.odd_iff]
  simp [defect, b0, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- Every source supporting an adjacent long-return pair is odd.  Therefore
the longer endpoint used as the next source must leave the 77-bit Hensel
division with an odd quotient. -/
theorem adjacentSource_odd {k g F : ℕ} (h : AdjacentSource k g F) : Odd F := by
  obtain ⟨X, _Y, hbase, _hnext⟩ := h
  have heq := hbase
  simp only [ReturnBalance] at heq
  rw [Nat.odd_iff]
  have hmod := congrArg (fun n : ℕ ↦ n % 2) heq
  simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, S,
    Nat.odd_iff.mp (longReturn_defect_odd k g)] using hmod

/-- One affine Hensel-core cell. -/
def CoreStep (A B z znext : ℕ) : Prop :=
  A * z = 1 + B * znext

/-- A finite sequence of `n` affine Hensel-core cells. -/
inductive CoreSteps (A B : ℕ) : ℕ → ℕ → ℕ → Prop
  | zero (z : ℕ) : CoreSteps A B 0 z z
  | succ {n z znext out : ℕ} :
      CoreStep A B z znext → CoreSteps A B n znext out →
        CoreSteps A B (n + 1) z out

/-- Positive defect from the (negative) rational fixed point of the cell. -/
def coreDefect (A B z : ℕ) : ℕ :=
  (A - B) * z - 1

theorem coreDefect_decomp
    {A B z : ℕ} (hgap : 1 < A - B) (hz : 0 < z) :
    (A - B) * z = 1 + coreDefect A B z := by
  simp only [coreDefect]
  have hprod : 0 < (A - B) * z := Nat.mul_pos (by omega) hz
  omega

/-- Conjugating one affine cell by its rational fixed point makes it
homogeneous. -/
theorem coreStep_defect_balance
    {A B z znext : ℕ} (hB : 0 < B) (hgap : 1 < A - B)
    (hz : 0 < z) (hstep : CoreStep A B z znext) :
    B * coreDefect A B znext = A * coreDefect A B z := by
  have hAB : B < A := by omega
  have hnext : 0 < znext := by
    simp only [CoreStep] at hstep
    by_contra hnot
    have hznext : znext = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hznext, mul_zero, add_zero] at hstep
    have hAz : 1 < A * z := by
      have hA : 2 < A := by omega
      have hAz' := hA.trans_le (Nat.le_mul_of_pos_right A hz)
      omega
    omega
  have hzDecomp := coreDefect_decomp hgap hz
  have hnextDecomp := coreDefect_decomp hgap hnext
  simp only [CoreStep] at hstep
  have hsum : B + (A - B) = A := by omega
  have hshift (u : ℕ) : B * u + A = B * (1 + u) + (A - B) := by
    calc
      B * u + A = B * u + (B + (A - B)) :=
        congrArg (fun x : ℕ ↦ B * u + x) hsum.symm
      _ = B * (1 + u) + (A - B) := by ring
  have hplus :
      B * coreDefect A B znext + A =
        A * coreDefect A B z + A := by
    calc
      B * coreDefect A B znext + A =
          B * (1 + coreDefect A B znext) + (A - B) := by
            exact hshift _
      _ = B * ((A - B) * znext) + (A - B) := by
            rw [hnextDecomp]
      _ = (A - B) * (1 + B * znext) := by ring
      _ = (A - B) * (A * z) := by rw [← hstep]
      _ = A * ((A - B) * z) := by ring
      _ = A * (1 + coreDefect A B z) := by rw [hzDecomp]
      _ = A * coreDefect A B z + A := by ring
  omega

/-- Iterating the fixed-point conjugacy gives a pure multiplicative balance. -/
theorem coreSteps_defect_balance
    {A B n z out : ℕ} (hB : 0 < B) (hgap : 1 < A - B)
    (hz : 0 < z) (hsteps : CoreSteps A B n z out) :
    B ^ n * coreDefect A B out = A ^ n * coreDefect A B z := by
  induction hsteps with
  | zero z => simp
  | @succ n z znext out hstep htail ih =>
      have hnext : 0 < znext := by
        simp only [CoreStep] at hstep
        by_contra hnot
        have hznext : znext = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hznext, mul_zero, add_zero] at hstep
        have hA : 2 < A := by omega
        have hAz' := hA.trans_le (Nat.le_mul_of_pos_right A hz)
        have hAz : 1 < A * z := by omega
        omega
      have hlocal := coreStep_defect_balance hB hgap hz hstep
      have htailBalance := ih hnext
      calc
        B ^ (n + 1) * coreDefect A B out =
            B * (B ^ n * coreDefect A B out) := by
              rw [pow_succ]
              ring
        _ = B * (A ^ n * coreDefect A B znext) := by
              rw [htailBalance]
        _ = A ^ n * (B * coreDefect A B znext) := by ring
        _ = A ^ n * (A * coreDefect A B z) := by rw [hlocal]
        _ = A ^ (n + 1) * coreDefect A B z := by
              rw [pow_succ]
              ring

/-- Exact finite-capacity theorem.  A source supports `n` cells iff the
fixed-point defect contains `n` complete factors of `B`. -/
theorem exists_coreSteps_iff_pow_dvd_coreDefect
    {A B n z : ℕ} (hB : 0 < B) (hgap : 1 < A - B)
    (hcop : Nat.Coprime A B) (hz : 0 < z) :
    (∃ out, CoreSteps A B n z out) ↔ B ^ n ∣ coreDefect A B z := by
  constructor
  · rintro ⟨out, hsteps⟩
    have hbalance := coreSteps_defect_balance hB hgap hz hsteps
    have hdvdProduct : B ^ n ∣ A ^ n * coreDefect A B z :=
      ⟨coreDefect A B out, hbalance.symm⟩
    exact (hcop.pow n n).symm.dvd_of_dvd_mul_left hdvdProduct
  · intro hdvd
    induction n generalizing z with
    | zero => exact ⟨z, CoreSteps.zero z⟩
    | succ n ih =>
        obtain ⟨t, ht⟩ := hdvd
        let znext := z + B ^ n * t
        have hpow : B ^ (n + 1) = B * B ^ n := by
          rw [pow_succ]
          ring
        have hdefectDecomp := coreDefect_decomp hgap hz
        have hsum : B + (A - B) = A := by omega
        have hstep : CoreStep A B z znext := by
          simp only [CoreStep]
          calc
            A * z = (B + (A - B)) * z := by rw [hsum]
            _ = B * z + (A - B) * z := by ring
            _ = B * z + (1 + coreDefect A B z) := by
                  rw [hdefectDecomp]
            _ = B * z + (1 + B ^ (n + 1) * t) := by rw [ht]
            _ = 1 + B * znext := by
                  dsimp [znext]
                  rw [hpow]
                  ring
        have hnextPos : 0 < znext := by
          dsimp [znext]
          omega
        have hnextDefect :
            coreDefect A B znext = B ^ n * (A * t) := by
          have hznextDecomp := coreDefect_decomp hgap hnextPos
          have hexpanded :
              coreDefect A B znext =
                coreDefect A B z + (A - B) * (B ^ n * t) := by
            have hplus :
                1 + coreDefect A B znext =
                  1 + (coreDefect A B z +
                    (A - B) * (B ^ n * t)) := by
              calc
                1 + coreDefect A B znext = (A - B) * znext :=
                  hznextDecomp.symm
                _ = (A - B) * z + (A - B) * (B ^ n * t) := by
                  dsimp [znext]
                  ring
                _ = (1 + coreDefect A B z) +
                    (A - B) * (B ^ n * t) := by rw [hdefectDecomp]
                _ = 1 + (coreDefect A B z +
                    (A - B) * (B ^ n * t)) := by ring
            omega
          calc
            coreDefect A B znext =
                coreDefect A B z + (A - B) * (B ^ n * t) := hexpanded
            _ = B ^ (n + 1) * t + (A - B) * (B ^ n * t) := by
                  rw [ht]
            _ = B ^ n * ((B + (A - B)) * t) := by
                  rw [hpow]
                  ring
            _ = B ^ n * (A * t) := by rw [hsum]
        have hnextDvd : B ^ n ∣ coreDefect A B znext := by
          rw [hnextDefect]
          exact dvd_mul_right _ _
        obtain ⟨out, htail⟩ := ih hnextPos hnextDvd
        exact ⟨out, CoreSteps.succ hstep htail⟩

/-- The core recurrence generated by consecutive long-return lengths. -/
def ReturnLengthCoreStep (g z znext : ℕ) : Prop :=
  CoreStep (3 ^ Q g) (2 ^ P g) z znext

/-- `n` consecutive high cells at one opcode. -/
def ReturnLengthCoreSteps (g n z out : ℕ) : Prop :=
  CoreSteps (3 ^ Q g) (2 ^ P g) n z out

/-- Intrinsic number of complete high-cell blocks stored by the payload. -/
def selfCellCapacity (g z : ℕ) : ℕ :=
  padicValNat 2 (coreDefect (3 ^ Q g) (2 ^ P g) z) / P g

theorem return_core_gap (g : ℕ) :
    1 < 3 ^ Q g - 2 ^ P g := by
  have hgain := double_two_pow_P_lt_three_pow_Q g
  have hBpos : 0 < 2 ^ P g := by positivity
  omega

theorem return_core_defect_ne_zero {g z : ℕ} (hz : 0 < z) :
    coreDefect (3 ^ Q g) (2 ^ P g) z ≠ 0 := by
  have hdecomp := coreDefect_decomp (return_core_gap g) hz
  have hprod : 1 < (3 ^ Q g - 2 ^ P g) * z :=
    (return_core_gap g).trans_le
      (Nat.le_mul_of_pos_right (3 ^ Q g - 2 ^ P g) hz)
  rw [hdecomp] at hprod
  omega

/-- An odd Hensel endpoint uses exactly the terminal 77 bits of the
fixed-point defect.  The strict hypothesis excludes the exceptional opcode
`g=1`, where `P(g)=77` and the high block can interfere at the same scale. -/
theorem padicVal_coreDefect_eq_seventy_seven_of_henselStep_odd
    {g z y : ℕ} (hg : 1 < g) (hz : 0 < z)
    (hstep : HenselStep g z y) (hy : Odd y) :
    padicValNat 2 (coreDefect (3 ^ Q g) (2 ^ P g) z) = 77 := by
  let A0 := 3 ^ Q g
  let B0 := 2 ^ P g
  let w := coreDefect A0 B0 z
  let q := 2 ^ (P g - 77) * z
  have hP : 77 < P g := by simp [P]; omega
  have hPsplit : P g = 77 + (P g - 77) := by omega
  have hdecomp := coreDefect_decomp (return_core_gap g) hz
  have hsum : B0 + (A0 - B0) = A0 := by
    dsimp [A0, B0]
    have hBlt : 2 ^ P g < 3 ^ Q g := by
      exact (Nat.pow_lt_pow_right (by norm_num) (by omega)).trans
        (double_two_pow_P_lt_three_pow_Q g)
    exact Nat.add_sub_of_le hBlt.le
  have hAz : A0 * z = B0 * z + (A0 - B0) * z := by
    calc
      A0 * z = (B0 + (A0 - B0)) * z := by rw [hsum]
      _ = B0 * z + (A0 - B0) * z := by ring
  have hmain : 2 ^ 77 * y = B0 * z + w := by
    simp only [HenselStep] at hstep
    change A0 * z = 1 + 2 ^ 77 * y at hstep
    change (A0 - B0) * z = 1 + w at hdecomp
    rw [hAz, hdecomp] at hstep
    omega
  have hBfactor : B0 * z = 2 ^ 77 * q := by
    dsimp [B0, q]
    have hpow : 2 ^ P g = 2 ^ 77 * 2 ^ (P g - 77) := by
      rw [← pow_add, Nat.add_sub_of_le hP.le]
    rw [hpow]
    ring
  have hqle : q ≤ y := by
    rw [hBfactor] at hmain
    nlinarith
  let u := y - q
  have hfactor : w = 2 ^ 77 * u := by
    rw [hBfactor] at hmain
    dsimp [u]
    calc
      w = 2 ^ 77 * y - 2 ^ 77 * q := by omega
      _ = 2 ^ 77 * (y - q) := by rw [Nat.mul_sub_left_distrib]
  have hqEven : Even q := by
    have hexp : 0 < P g - 77 := by omega
    dsimp [q]
    rw [even_iff_two_dvd]
    exact (pow_dvd_pow 2 (by omega : 1 ≤ P g - 77)).trans
      (dvd_mul_right _ _)
  have huOdd : Odd u := by
    dsimp [u]
    exact Nat.Odd.sub_even hqle hy hqEven
  have huNe : u ≠ 0 := huOdd.pos.ne'
  dsimp [w, A0, B0] at hfactor
  rw [hfactor]
  change padicValNat 2 (2 ^ 77 * u) = 77
  rw [padicValNat_base_pow_mul (by norm_num) huNe]
  have hnotTwo : ¬2 ∣ u := by
    simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr huOdd)
  rw [padicValNat.eq_zero_of_not_dvd hnotTwo]

/-- Positivity propagates through a finite core trace. -/
theorem coreSteps_out_pos
    {A B n z out : ℕ} (_hB : 0 < B) (hA : 1 < A) (hz : 0 < z)
    (hsteps : CoreSteps A B n z out) : 0 < out := by
  induction hsteps with
  | zero z => exact hz
  | @succ n z znext out hstep htail ih =>
      have hnext : 0 < znext := by
        simp only [CoreStep] at hstep
        by_contra hnot
        have hznext : znext = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hznext, mul_zero, add_zero] at hstep
        have hAz := hA.trans_le (Nat.le_mul_of_pos_right A hz)
        omega
      exact ih hnext

/-- Hence an odd exit after `n` complete high cells forces the source defect
to contain exactly `n*P(g)+77` binary digits.  This is the endogenous
return-length law. -/
theorem padicVal_source_coreDefect_of_coreSteps_odd_exit
    {g n z out y : ℕ} (hg : 1 < g) (hz : 0 < z)
    (hsteps : ReturnLengthCoreSteps g n z out)
    (hexit : HenselStep g out y) (hy : Odd y) :
    padicValNat 2 (coreDefect (3 ^ Q g) (2 ^ P g) z) =
      n * P g + 77 := by
  have hout : 0 < out := coreSteps_out_pos
    (by positivity) (one_lt_pow₀ (by norm_num) (by simp [Q])) hz hsteps
  have hbalance := coreSteps_defect_balance
    (A := 3 ^ Q g) (B := 2 ^ P g)
    (by positivity) (return_core_gap g) hz hsteps
  have hsourceNe := return_core_defect_ne_zero (g := g) hz
  have houtNe := return_core_defect_ne_zero (g := g) hout
  have hleftPow : (2 ^ P g) ^ n = 2 ^ (n * P g) := by
    rw [mul_comm, pow_mul]
  have hrightPow : (3 ^ Q g) ^ n = 3 ^ (n * Q g) := by
    rw [mul_comm, pow_mul]
  have hval := congrArg (padicValNat 2) hbalance
  have hthreeOdd : Odd (3 ^ (n * Q g)) :=
    Odd.pow (n := n * Q g) (by norm_num)
  have hthreeNotTwo : ¬2 ∣ 3 ^ (n * Q g) := by
    simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hthreeOdd)
  rw [hleftPow, hrightPow,
    padicValNat.mul (by positivity) houtNe,
    padicValNat.mul (by positivity) hsourceNe,
    padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hthreeNotTwo,
    zero_add] at hval
  rw [padicVal_coreDefect_eq_seventy_seven_of_henselStep_odd hg hout
    hexit hy] at hval
  omega

/-- In particular the return length is recovered, rather than selected, from
the current payload. -/
theorem selfCellCapacity_eq_of_coreSteps_odd_exit
    {g n z out y : ℕ} (hg : 1 < g) (hz : 0 < z)
    (hsteps : ReturnLengthCoreSteps g n z out)
    (hexit : HenselStep g out y) (hy : Odd y) :
    selfCellCapacity g z = n := by
  have hval := padicVal_source_coreDefect_of_coreSteps_odd_exit
    hg hz hsteps hexit hy
  simp only [selfCellCapacity, hval]
  have hPpos : 0 < P g := by simp [P]
  have hsmall : 77 < P g := by simp [P]; omega
  rw [show n * P g + 77 = 77 + n * P g by omega,
    Nat.mul_comm n (P g),
    Nat.add_mul_div_left 77 n hPpos, Nat.div_eq_of_lt hsmall,
    zero_add]

/-- Zero-retroactive-lift compatibility at the doubled opcode forces the
same intrinsic valuation law: the next adjacent source is odd, so the final
77-bit division is exact and self-delimiting. -/
theorem padicVal_source_coreDefect_of_doubled_adjacent_exit
    {g n z out y knext : ℕ} (hg : 1 < g) (hz : 0 < z)
    (hsteps : ReturnLengthCoreSteps g n z out)
    (hexit : HenselStep g out y)
    (hnext : AdjacentSource knext (2 * g) y) :
    padicValNat 2 (coreDefect (3 ^ Q g) (2 ^ P g) z) =
      n * P g + 77 :=
  padicVal_source_coreDefect_of_coreSteps_odd_exit
    hg hz hsteps hexit (adjacentSource_odd hnext)

/-- A core cell is not merely a recurrence on an auxiliary register.  After
restoring the forced zero block, it is exactly the Hensel instruction which
advances the same ordinary-source return balance by one cell. -/
theorem henselStep_scaled_of_returnLengthCoreStep
    {g z znext : ℕ} (hg : 0 < g)
    (hstep : ReturnLengthCoreStep g z znext) :
    HenselStep g z (2 ^ (P g - 77) * znext) := by
  have hP := seventy_seven_le_P hg
  have hsplit : P g = 77 + (P g - 77) := by omega
  have hpow : 2 ^ P g = 2 ^ 77 * 2 ^ (P g - 77) := by
    calc
      2 ^ P g = 2 ^ (77 + (P g - 77)) := congrArg (2 ^ ·) hsplit
      _ = 2 ^ 77 * 2 ^ (P g - 77) := pow_add 2 77 (P g - 77)
  simp only [ReturnLengthCoreStep, CoreStep] at hstep
  simp only [HenselStep]
  calc
    3 ^ Q g * z = 1 + 2 ^ P g * znext := hstep
    _ = 1 + 2 ^ 77 * (2 ^ (P g - 77) * znext) := by
      rw [hpow]
      ring

/-- Reattachment theorem for a finite core trace.  If the initial work
register occurs as the forced-zero output of one return balance, all core
cells advance the return length while keeping the ordinary source literally
unchanged. -/
theorem returnBalance_add_of_returnLengthCoreSteps
    {k g F n z out : ℕ} (hg : 0 < g)
    (hbase : ReturnBalance k g F (2 ^ (P g - 77) * z))
    (hsteps : ReturnLengthCoreSteps g n z out) :
    ReturnBalance (k + n) g F (2 ^ (P g - 77) * out) := by
  induction hsteps generalizing k F with
  | zero z => simpa using hbase
  | @succ n z znext out hstep htail ih =>
      have hcell := henselStep_scaled_of_returnLengthCoreStep hg hstep
      have hnext :
          ReturnBalance (k + 1) g F (2 ^ (P g - 77) * znext) :=
        (returnBalance_succ_iff_hensel hg hbase).2
          ⟨z, henselStep_odd hcell, rfl, hcell⟩
      have hrest := ih (k := k + 1) (F := F) hnext
      simpa [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using hrest

/-- Appending the terminal 77-bit exit to a reattached core trace gives the
longer return balance whose output is the actual next ordinary payload. -/
theorem returnBalance_exit_of_returnLengthCoreSteps
    {k g F n z out y : ℕ} (hg : 0 < g)
    (hbase : ReturnBalance k g F (2 ^ (P g - 77) * z))
    (hsteps : ReturnLengthCoreSteps g n z out)
    (hexit : HenselStep g out y) :
    ReturnBalance (k + n + 1) g F y := by
  have hlast := returnBalance_add_of_returnLengthCoreSteps hg hbase hsteps
  exact (returnBalance_succ_iff_hensel hg hlast).2
    ⟨out, henselStep_odd hexit, rfl, hexit⟩

/-- Exact ternary entrance condition for using `z` as the internal work
register without changing it by a retroactive Hensel lift. -/
def EntranceCompatible (k g z : ℕ) : Prop :=
  3 ^ R k g ∣
    defect k g + 2 ^ (S k g + (P g - 77)) * z

/-- Entrance compatibility is exactly the existence of an ordinary source
whose length-`k` return has the required forced-zero output.  This is the
ternary gate that an internal core trace cannot supply by itself. -/
theorem entranceCompatible_iff_exists_returnBalance
    {k g z : ℕ} :
    EntranceCompatible k g z ↔
      ∃ F : ℕ,
        ReturnBalance k g F (2 ^ (P g - 77) * z) := by
  simp only [EntranceCompatible, ReturnBalance]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨F, ?_⟩
    calc
      3 ^ R k g * F =
          defect k g + 2 ^ (S k g + (P g - 77)) * z := hF.symm
      _ = defect k g +
          2 ^ S k g * (2 ^ (P g - 77) * z) := by
            rw [pow_add]
            ring
  · rintro ⟨F, hF⟩
    refine ⟨F, ?_⟩
    calc
      defect k g + 2 ^ (S k g + (P g - 77)) * z =
          defect k g + 2 ^ S k g * (2 ^ (P g - 77) * z) := by
            rw [pow_add]
            ring
      _ = 3 ^ R k g * F := hF.symm

/-- The exact source factorization is also sufficient.  Its odd cofactor
executes all `n` complete cells and then becomes an odd terminal endpoint by
one final 77-bit Hensel division. -/
theorem exists_selfDelimited_odd_exit_of_coreDefect_factor
    {g n z u : ℕ} (hg : 1 < g) (hz : 0 < z) (hu : Odd u)
    (hfactor :
      coreDefect (3 ^ Q g) (2 ^ P g) z =
        2 ^ (n * P g + 77) * u) :
    ∃ out y : ℕ,
      ReturnLengthCoreSteps g n z out ∧
      HenselStep g out y ∧ Odd y ∧
      y = 2 ^ (P g - 77) * out + (3 ^ Q g) ^ n * u ∧
      (3 ^ Q g - 2 ^ P g) * y =
        (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77) := by
  have hpowB : (2 ^ P g) ^ n = 2 ^ (n * P g) := by
    rw [mul_comm, pow_mul]
  have hdvd : (2 ^ P g) ^ n ∣
      coreDefect (3 ^ Q g) (2 ^ P g) z := by
    rw [hfactor, hpowB, pow_add]
    refine ⟨2 ^ 77 * u, ?_⟩
    ring
  obtain ⟨out, hsteps⟩ :=
    (exists_coreSteps_iff_pow_dvd_coreDefect
      (A := 3 ^ Q g) (B := 2 ^ P g)
      (by positivity) (return_core_gap g)
      (Nat.Coprime.pow (Q g) (P g) (by norm_num)) hz).2 hdvd
  have hout : 0 < out := coreSteps_out_pos
    (by positivity) (one_lt_pow₀ (by norm_num) (by simp [Q])) hz hsteps
  have hbalance := coreSteps_defect_balance
    (A := 3 ^ Q g) (B := 2 ^ P g)
    (by positivity) (return_core_gap g) hz hsteps
  have houtFactor :
      coreDefect (3 ^ Q g) (2 ^ P g) out =
        2 ^ 77 * ((3 ^ Q g) ^ n * u) := by
    rw [hfactor, hpowB, pow_add] at hbalance
    have hcancel :
        2 ^ (n * P g) * coreDefect (3 ^ Q g) (2 ^ P g) out =
          2 ^ (n * P g) * (2 ^ 77 * ((3 ^ Q g) ^ n * u)) := by
      calc
        2 ^ (n * P g) * coreDefect (3 ^ Q g) (2 ^ P g) out =
            (3 ^ Q g) ^ n *
              (2 ^ (n * P g) * (2 ^ 77 * u)) := by
                simpa only [mul_assoc] using hbalance
        _ = 2 ^ (n * P g) * (2 ^ 77 * ((3 ^ Q g) ^ n * u)) := by
          ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hcancel
  let y := 2 ^ (P g - 77) * out + (3 ^ Q g) ^ n * u
  have hP : 77 < P g := by simp [P]; omega
  have hPsplit : P g = 77 + (P g - 77) := by omega
  have hsum : 2 ^ P g + (3 ^ Q g - 2 ^ P g) = 3 ^ Q g := by
    have hlt : 2 ^ P g < 3 ^ Q g :=
      (Nat.pow_lt_pow_right (by norm_num) (by omega)).trans
        (double_two_pow_P_lt_three_pow_Q g)
    exact Nat.add_sub_of_le hlt.le
  have houtDecomp := coreDefect_decomp (return_core_gap g) hout
  have hexit : HenselStep g out y := by
    simp only [HenselStep]
    have hAout :
        3 ^ Q g * out =
          2 ^ P g * out + (3 ^ Q g - 2 ^ P g) * out := by
      calc
        3 ^ Q g * out =
            (2 ^ P g + (3 ^ Q g - 2 ^ P g)) * out := by rw [hsum]
        _ = 2 ^ P g * out + (3 ^ Q g - 2 ^ P g) * out := by ring
    rw [hAout, houtDecomp, houtFactor]
    dsimp [y]
    have hpPow : 2 ^ P g = 2 ^ 77 * 2 ^ (P g - 77) := by
      rw [← pow_add, Nat.add_sub_of_le hP.le]
    rw [hpPow]
    ring
  have hfirstEven : Even (2 ^ (P g - 77) * out) := by
    rw [even_iff_two_dvd]
    exact (pow_dvd_pow 2 (by omega : 1 ≤ P g - 77)).trans
      (dvd_mul_right _ _)
  have hsecondOdd : Odd ((3 ^ Q g) ^ n * u) := by
    exact (Odd.pow (n := n) (Odd.pow (n := Q g) (by norm_num))).mul hu
  have hyOdd : Odd y := by
    dsimp [y]
    exact hfirstEven.add_odd hsecondOdd
  have hclosed :
      (3 ^ Q g - 2 ^ P g) * y =
        (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77) := by
    have houtEq :
        (3 ^ Q g - 2 ^ P g) * out =
          1 + 2 ^ 77 * ((3 ^ Q g) ^ n * u) := by
      calc
        (3 ^ Q g - 2 ^ P g) * out =
            1 + coreDefect (3 ^ Q g) (2 ^ P g) out :=
              (coreDefect_decomp (return_core_gap g) hout)
        _ = 1 + 2 ^ 77 * ((3 ^ Q g) ^ n * u) := by rw [houtFactor]
    dsimp [y]
    have hpPow : 2 ^ P g = 2 ^ (P g - 77) * 2 ^ 77 := by
      rw [← pow_add, Nat.sub_add_cancel hP.le]
    have hsum' : (3 ^ Q g - 2 ^ P g) + 2 ^ P g = 3 ^ Q g := by
      exact Nat.sub_add_cancel
        ((Nat.pow_lt_pow_right (by norm_num) (by omega)).trans
          (double_two_pow_P_lt_three_pow_Q g)).le
    calc
      (3 ^ Q g - 2 ^ P g) *
          (2 ^ (P g - 77) * out + (3 ^ Q g) ^ n * u) =
        2 ^ (P g - 77) * ((3 ^ Q g - 2 ^ P g) * out) +
          (3 ^ Q g - 2 ^ P g) * ((3 ^ Q g) ^ n * u) := by ring
      _ = 2 ^ (P g - 77) *
          (1 + 2 ^ 77 * ((3 ^ Q g) ^ n * u)) +
          (3 ^ Q g - 2 ^ P g) * ((3 ^ Q g) ^ n * u) := by rw [houtEq]
      _ = ((3 ^ Q g - 2 ^ P g) + 2 ^ P g) *
          ((3 ^ Q g) ^ n * u) + 2 ^ (P g - 77) := by
            rw [hpPow]
            ring
      _ = (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77) := by
            rw [hsum', pow_succ]
            ring
  exact ⟨out, y, hsteps, hexit, hyOdd, rfl, hclosed⟩

/-- The fully reattached finite compiler.  The ternary entrance congruence
and the dyadic defect factorization are independent rails: together they
produce one positive ordinary source, the entire self-delimited core trace,
and the final longer return balance without altering that source. -/
theorem exists_reattached_selfDelimited_macro
    {k g n z u : ℕ} (hg : 1 < g) (hz : 0 < z) (hu : Odd u)
    (hentrance : EntranceCompatible k g z)
    (hfactor :
      coreDefect (3 ^ Q g) (2 ^ P g) z =
        2 ^ (n * P g + 77) * u) :
    ∃ F out y : ℕ,
      0 < F ∧
      ReturnBalance k g F (2 ^ (P g - 77) * z) ∧
      ReturnLengthCoreSteps g n z out ∧
      HenselStep g out y ∧ Odd y ∧
      ReturnBalance (k + n + 1) g F y ∧
      y = 2 ^ (P g - 77) * out + (3 ^ Q g) ^ n * u ∧
      (3 ^ Q g - 2 ^ P g) * y =
        (3 ^ Q g) ^ (n + 1) * u + 2 ^ (P g - 77) := by
  obtain ⟨F, hbase⟩ :=
    entranceCompatible_iff_exists_returnBalance.mp hentrance
  obtain ⟨out, y, hsteps, hexit, hy, hyFormula, hclosed⟩ :=
    exists_selfDelimited_odd_exit_of_coreDefect_factor hg hz hu hfactor
  have hdefectPos : 0 < defect k g := by
    apply Nat.add_pos_left
    exact Nat.mul_pos (by positivity) (by dsimp [b0]; positivity)
  have hFpos : 0 < F := by
    by_contra hnot
    have hFzero : F = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [ReturnBalance] at hbase
    rw [hFzero, mul_zero] at hbase
    omega
  have hfinal :=
    returnBalance_exit_of_returnLengthCoreSteps (by omega) hbase hsteps hexit
  exact ⟨F, out, y, hFpos, hbase, hsteps, hexit, hy, hfinal,
    hyFormula, hclosed⟩

/-- Main self-delimiting-counter theorem: exactly `n` further high cells are
available precisely when `n` does not exceed the intrinsic capacity. -/
theorem exists_returnLengthCoreSteps_iff_le_capacity
    {g n z : ℕ} (hz : 0 < z) :
    (∃ out, ReturnLengthCoreSteps g n z out) ↔
      n ≤ selfCellCapacity g z := by
  rw [show (∃ out, ReturnLengthCoreSteps g n z out) ↔
      (2 ^ P g) ^ n ∣ coreDefect (3 ^ Q g) (2 ^ P g) z by
    exact exists_coreSteps_iff_pow_dvd_coreDefect
      (by positivity) (return_core_gap g)
      (Nat.Coprime.pow (Q g) (P g) (by norm_num)) hz]
  have hdefect := return_core_defect_ne_zero (g := g) hz
  have hPpos : 0 < P g := by simp [P]
  rw [← pow_mul]
  rw [Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdefect]
  constructor
  · intro h
    apply (Nat.le_div_iff_mul_le hPpos).2
    simpa [mul_comm] using h
  · intro h
    have hmul := (Nat.le_div_iff_mul_le hPpos).1 h
    simpa [mul_comm] using hmul

/-- The intrinsic capacity is attainable. -/
theorem exists_capacity_many_returnLengthCoreSteps
    {g z : ℕ} (hz : 0 < z) :
    ∃ out, ReturnLengthCoreSteps g (selfCellCapacity g z) z out :=
  (exists_returnLengthCoreSteps_iff_le_capacity hz).2 le_rfl

/-- The very next cell after the intrinsic capacity is impossible.  This is
the exact autonomous exit signal. -/
theorem no_more_than_capacity_returnLengthCoreSteps
    {g z : ℕ} (hz : 0 < z) :
    ¬ ∃ out, ReturnLengthCoreSteps g (selfCellCapacity g z + 1) z out := by
  rw [exists_returnLengthCoreSteps_iff_le_capacity hz]
  omega

end LongReturnSelfDelimiting
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.FiniteCompiler

/-!
# Exact separated-packet delay lines

The state `1 + p * 2^J` transports its high packet by two binary positions
per accelerated step while multiplying the payload by three.  This file
proves the whole parametrized wire, rather than replaying a large instance.
-/

namespace KontoroC

/-- One low bit separated from an arbitrary high payload by a dyadic gap. -/
def delayState (p J : ℕ) : ℕ :=
  1 + p * 2 ^ J

theorem delayState_pos (p J : ℕ) : 0 < delayState p J := by
  simp [delayState]

theorem delayState_odd {p J : ℕ} (hJ : 0 < J) : Odd (delayState p J) := by
  rw [delayState]
  apply odd_one.add_even
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ)
  rw [pow_succ]
  apply even_iff_two_dvd.mpr
  exact ⟨p * 2 ^ j, by ring⟩

/-- One exact wire tick.  A gap of at least three makes the valuation exactly
two and leaves another positive odd separated-packet state. -/
theorem delayState_step {p J : ℕ} (hJ : 3 ≤ J) :
    LegalInstruction (delayState p J) 2 ∧
      oddStep (delayState p J) = delayState (3 * p) (J - 2) := by
  apply legalInstruction_of_step_equation
  · exact delayState_pos p J
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · exact Nat.odd_iff.mp (delayState_odd (p := 3 * p) (by omega))
  · have hsplit : J - 2 + 2 = J := by omega
    rw [delayState, delayState]
    rw [← hsplit, pow_add]
    norm_num
    ring

/-- `n` exact valuation-two ticks through a delay line.  The inequality keeps
the terminal state odd and leaves a residual gap of at least two. -/
theorem delayState_word {p J n : ℕ}
    (hp : 0 < p) (hpOdd : Odd p) (hroom : 2 * n + 2 ≤ J) :
    WordLegal (delayState p J) (List.replicate n 2) ∧
      runWord (delayState p J) (List.replicate n 2) =
        delayState (3 ^ n * p) (J - 2 * n) := by
  induction n generalizing p J with
  | zero =>
      constructor
      · trivial
      · simp [delayState]
  | succ n ih =>
      have hJ : 3 ≤ J := by omega
      have hstep := delayState_step (p := p) hJ
      have hp' : 0 < 3 * p := by positivity
      have hpOdd' : Odd (3 * p) := (by norm_num : Odd 3).mul hpOdd
      have hroom' : 2 * n + 2 ≤ J - 2 := by omega
      have htail := ih hp' hpOdd' hroom'
      rw [List.replicate_succ, WordLegal, runWord_cons, hstep.2]
      constructor
      · exact ⟨hstep.1, htail.1⟩
      · rw [htail.2]
        congr 1
        · rw [pow_succ]
          ring
        · omega

/-- Closed-form endpoint of the exact wire, separated from the legality
statement for convenient rewriting. -/
theorem runWord_delayState {p J n : ℕ}
    (hp : 0 < p) (hpOdd : Odd p) (hroom : 2 * n + 2 ≤ J) :
    runWord (delayState p J) (List.replicate n 2) =
      delayState (3 ^ n * p) (J - 2 * n) :=
  (delayState_word hp hpOdd hroom).2

/-- The exact long wire exposed by the order-ten Colussi header.  The proof
uses the parametric theorem above; it does not construct or replay a
19,673-element proof term. -/
theorem colussiOrderTen_delay :
    WordLegal (delayState 1 39348) (List.replicate 19673 2) ∧
      runWord (delayState 1 39348) (List.replicate 19673 2) =
        1 + 4 * 3 ^ 19673 := by
  have h := delayState_word
    (p := 1) (J := 39348) (n := 19673)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h.1, h.2.trans ?_⟩
  change 1 + (3 ^ 19673 * 1) * 2 ^ (39348 - 2 * 19673) =
    1 + 4 * 3 ^ 19673
  rw [show 39348 - 2 * 19673 = 2 by norm_num]
  norm_num only [pow_two, mul_one]
  rw [mul_comm (3 ^ 19673) 4]

/-- Formula-generated order-ten Colussi seed.  Its decimal expansion is not
stored in the certificate. -/
def colussiOrderTenSeed : ℕ :=
  (4 ^ 19683 - 1) / 3 ^ 10

def colussiOrderTenHeader : List ℕ :=
  [1, 1, 2, 1, 1, 1, 5, 1, 4, 1]

theorem div_mod_of_mod_mul_eq_mul {N d M r : ℕ}
    (hd : 0 < d) (hr : r < M) (hmod : N % (d * M) = d * r) :
    (N / d) % M = r := by
  let q := N / (d * M)
  have hN : d * (M * q + r) = N := by
    calc
      d * (M * q + r) = (d * M) * q + d * r := by ring
      _ = (d * M) * (N / (d * M)) + N % (d * M) := by
        rw [hmod]
      _ = N := Nat.div_add_mod N (d * M)
  have hdiv : N / d = M * q + r := by
    rw [← hN, Nat.mul_comm d, Nat.mul_div_left _ hd]
  rw [hdiv]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- A kernel-checked low-address fact about the 11,846-digit formula value. -/
theorem colussiOrderTenSeed_mod_twoPow19 :
    colussiOrderTenSeed % 2 ^ 19 = 189031 := by
  have hmod :
      (4 ^ 19683 - 1) % (59049 * 524288) = 59049 * 189031 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 20000 in
      decide
  set_option maxRecDepth 100000 in
  set_option exponentiation.threshold 20000 in
    change ((4 ^ 19683 - 1) / 59049) % 524288 = 189031
  set_option maxRecDepth 100000 in
    exact div_mod_of_mod_mul_eq_mul
      (N := 4 ^ 19683 - 1) (d := 59049) (M := 524288) (r := 189031)
      (by norm_num) (by norm_num) hmod

theorem colussiOrderTenHeader_positive :
    PositiveWord colussiOrderTenHeader := by
  norm_num [PositiveWord, colussiOrderTenHeader]

theorem colussiOrderTenResidue_finalCongruence :
    FinalCongruence 189031 colussiOrderTenHeader := by
  norm_num [FinalCongruence, colussiOrderTenHeader, totalValuation,
    affineOffset]

/-- The compact header is literally legal at the formula-generated seed.
Only its 19-bit address is needed to certify all ten exact valuations. -/
theorem colussiOrderTenHeader_legal :
    WordLegal colussiOrderTenSeed colussiOrderTenHeader := by
  have hmod19 : colussiOrderTenSeed ≡ 189031 [MOD 2 ^ 19] := by
    change colussiOrderTenSeed % 2 ^ 19 = 189031 % 2 ^ 19
    rw [colussiOrderTenSeed_mod_twoPow19]
    norm_num
  have hmod : colussiOrderTenSeed ≡ 189031
      [MOD 2 ^ (totalValuation colussiOrderTenHeader + 1)] := by
    simpa [colussiOrderTenHeader, totalValuation] using hmod19
  have hfinal : FinalCongruence colussiOrderTenSeed colussiOrderTenHeader :=
    FinalCongruence.of_modEq colussiOrderTenHeader hmod.symm
      colussiOrderTenResidue_finalCongruence
  exact (finalCongruence_iff_wordLegal colussiOrderTenSeed
    colussiOrderTenHeader colussiOrderTenHeader_positive).mp hfinal |>.1

/-- Kernel reduction checks the one large affine balance.  This uses `decide`,
not `native_decide`: no compiler execution enters the trusted proof. -/
theorem colussiOrderTenHeader_affine_balance :
    59049 * colussiOrderTenSeed + 262145 =
      262144 * (1 + 2 ^ 39348) := by
  set_option maxRecDepth 100000 in
  set_option exponentiation.threshold 40000 in
    decide

/-- End-to-end kernel theorem for the formula-generated 11,846-digit header. -/
theorem colussiOrderTenHeader_endpoint :
    runWord colussiOrderTenSeed colussiOrderTenHeader =
      delayState 1 39348 := by
  have h := valuationWord_affine_identity colussiOrderTenHeader_legal
  simp only [colussiOrderTenHeader, totalValuation, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil, affineOffset_cons,
    affineOffset_nil, pow_zero, mul_zero, add_zero] at h
  norm_num only [pow_zero, pow_one] at h
  have hbalance := colussiOrderTenHeader_affine_balance
  rw [hbalance] at h
  have hout :
      runWord colussiOrderTenSeed [1, 1, 2, 1, 1, 1, 5, 1, 4, 1] =
        1 + 2 ^ 39348 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 262144) h
  change runWord colussiOrderTenSeed [1, 1, 2, 1, 1, 1, 5, 1, 4, 1] =
    1 + 1 * 2 ^ 39348
  simpa only [one_mul] using hout

end KontoroC

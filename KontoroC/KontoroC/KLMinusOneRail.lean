/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Syracuse
import KontoroC.TwoRailGate

/-!
# The pure KL class-8 rail exhausts a finite dyadic counter

In the translated coordinate `z = x + 1`, a class-8 predecessor refinement
is multiplication by `2/3`; its forward reversal is multiplication by `3/2`.
The corresponding natural-number segment is the minus-one rail

`x_j = 3^j * 2^(L-j) * t - 1`.

The exact Syracuse calculation below shows that every finite segment exists,
but the splicing identity strictly consumes the two-adic valuation of its
payload.  Hence pure class-8 segments cannot be spliced forever from one
ordinary natural.  Mixed schedules can evade the theorem only by recharging
that valuation.
-/

namespace KontoroC
namespace KLMinusOneRail

open CleanLean.Collatz

/-- The `j`th point of a length-`L` pure class-8 rail. -/
def railState (L t j : ℕ) : ℕ :=
  3 ^ j * 2 ^ (L - j) * t - 1

theorem railState_pos {L t j : ℕ} (ht : 0 < t) (hj : j < L) :
    0 < railState L t j := by
  have hgap : 0 < L - j := by omega
  simpa [railState, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (twoPow_mul_sub_one_pos_odd (m := L - j) (h := 3 ^ j * t)
      hgap (by positivity : 0 < 3 ^ j * t)).1

/-- Before the endpoint, the rail point is odd, so the Syracuse map takes
its odd branch. -/
theorem railState_odd {L t j : ℕ} (ht : 0 < t) (hj : j < L) :
    railState L t j % 2 = 1 := by
  have hgap : 0 < L - j := by omega
  simpa [railState, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (twoPow_mul_sub_one_pos_odd (m := L - j) (h := 3 ^ j * t)
      hgap (by positivity : 0 < 3 ^ j * t)).2

/-- One literal Syracuse shortcut moves one step along the rail. -/
theorem syracuseStep_railState {L t j : ℕ} (ht : 0 < t) (hj : j < L) :
    syracuseStep (railState L t j) = railState L t (j + 1) := by
  let a := 3 ^ j * 2 ^ (L - (j + 1)) * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hsource : railState L t j = 2 * a - 1 := by
    simp only [railState, a]
    have hgap : L - j = (L - (j + 1)) + 1 := by omega
    congr 1
    rw [hgap, pow_succ]
    ring
  have htarget : railState L t (j + 1) = 3 * a - 1 := by
    simp only [railState, a]
    congr 1
    rw [pow_succ]
    ring
  rw [syracuseStep, if_neg]
  · rw [hsource, htarget]
    omega
  · rw [railState_odd ht hj]
    norm_num

/-- Every intermediate point is strictly larger than its predecessor. -/
theorem railState_strictMono {L t j : ℕ} (ht : 0 < t) (hj : j < L) :
    railState L t j < railState L t (j + 1) := by
  let a := 3 ^ j * 2 ^ (L - (j + 1)) * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hsource : railState L t j = 2 * a - 1 := by
    simp only [railState, a]
    have hgap : L - j = (L - (j + 1)) + 1 := by omega
    congr 1
    rw [hgap, pow_succ]
    ring
  have htarget : railState L t (j + 1) = 3 * a - 1 := by
    simp only [railState, a]
    congr 1
    rw [pow_succ]
    ring
  rw [hsource, htarget]
  omega

/-- QM128a: a length-`L` pure class-8 segment runs from
`2^L*t-1` to `3^L*t-1`. -/
theorem syracuse_iterate_railState {L t j : ℕ} (ht : 0 < t)
    (hj : j ≤ L) :
    syracuseStep^[j] (railState L t 0) = railState L t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact syracuseStep_railState ht (by omega)

theorem syracuse_iterate_minusOne_rail {L t : ℕ} (ht : 0 < t) :
    syracuseStep^[L] (2 ^ L * t - 1) = 3 ^ L * t - 1 := by
  simpa [railState] using syracuse_iterate_railState (L := L) (t := t) ht
    (le_refl L)

/-- A splice of two pure rails consumes exactly the next rail length from
the payload's two-adic valuation.  Additive form avoids truncated subtraction. -/
theorem splice_valuation_balance {L M t u : ℕ}
    (ht : 0 < t) (hu : 0 < u)
    (hsplice : 3 ^ L * t = 2 ^ M * u) :
    M + padicValNat 2 u = padicValNat 2 t := by
  have hleft : padicValNat 2 (3 ^ L * t) = padicValNat 2 t := by
    rw [padicValNat.mul (by positivity) ht.ne', padicValNat.pow]
    norm_num [padicValNat.eq_zero_of_not_dvd]
  have hright : padicValNat 2 (2 ^ M * u) = M + padicValNat 2 u := by
    rw [padicValNat.mul (by positivity) hu.ne', padicValNat.prime_pow]
  rw [← hleft, hsplice, hright]

theorem splice_strictly_consumes {L M t u : ℕ}
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < u)
    (hsplice : 3 ^ L * t = 2 ^ M * u) :
    padicValNat 2 u < padicValNat 2 t := by
  have hbalance := splice_valuation_balance ht hu hsplice
  omega

/-- QM128c: no infinite chain of positive pure class-8 rails can splice.
The proof exposes the finite counter explicitly: after `n` splices, at least
`n` units have been consumed from the initial dyadic valuation. -/
theorem no_infinite_positive_splice_chain
    (length payload : ℕ → ℕ)
    (hlength : ∀ i, 0 < length i)
    (hpayload : ∀ i, 0 < payload i)
    (hsplice : ∀ i,
      3 ^ (length i) * payload i =
        2 ^ (length (i + 1)) * payload (i + 1)) : False := by
  have hcounter (i : ℕ) :
      i + padicValNat 2 (payload i) ≤ padicValNat 2 (payload 0) := by
    induction i with
    | zero => simp
    | succ i ih =>
        have hdrop := splice_strictly_consumes
          (hlength (i + 1)) (hpayload i) (hpayload (i + 1)) (hsplice i)
        omega
  have h := hcounter (padicValNat 2 (payload 0) + 1)
  omega

/-! ## The same obstruction as a rational affine fixed-point theorem -/

/-- The class-8 predecessor branch in the original affine coordinate. -/
def r8 (x : ℚ) : ℚ := (2 * x - 1) / 3

theorem r8_add_one (x : ℚ) :
    r8 x + 1 = (2 / 3 : ℚ) * (x + 1) := by
  simp [r8]
  ring

/-- Translation by the exceptional point `-1` conjugates every iterate of
the class-8 branch to multiplication by `(2/3)^L`. -/
theorem r8_iterate_add_one (L : ℕ) (x : ℚ) :
    r8^[L] x + 1 = (2 / 3 : ℚ) ^ L * (x + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Function.iterate_succ_apply', r8_add_one, ih, pow_succ]
      ring

/-- The negative Collatz fixed point is the only rational periodic point of
the pure class-8 predecessor branch. -/
theorem r8_periodic_only_minusOne {L : ℕ} {x : ℚ}
    (hL : 0 < L) (hperiod : r8^[L] x = x) : x = -1 := by
  have htranslated := r8_iterate_add_one L x
  rw [hperiod] at htranslated
  have hpow : (2 / 3 : ℚ) ^ L < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hL.ne'
  nlinarith

/-! ## Ordinary naturals cannot remain on the 3-adic spine -/

/-- Matching the `-1` residue at precision `3^k` already forces exponential
ordinary size. -/
theorem minusOne_residue_forces_scale {n k : ℕ}
    (hresidue : n % 3 ^ k = 3 ^ k - 1) :
    3 ^ k ≤ n + 1 := by
  have hle := Nat.mod_le n (3 ^ k)
  rw [hresidue] at hle
  omega

/-- A fixed ordinary natural eventually differs from `-1` at every finer
ternary precision.  Thus the exact exceptional spine is genuinely 3-adic;
only a growing diagonal sequence of naturals can chase it. -/
theorem ordinary_eventually_avoids_minusOne_spine (n : ℕ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → n % 3 ^ k ≠ 3 ^ k - 1 := by
  refine ⟨n + 1, ?_⟩
  intro k hk hresidue
  have hscale := minusOne_residue_forces_scale hresidue
  have hbase : n + 1 < 3 ^ (n + 1) := Nat.lt_pow_self (by omega)
  have hmono : 3 ^ (n + 1) ≤ 3 ^ k :=
    Nat.pow_le_pow_right (by omega) hk
  omega

/-- In particular, no single ordinary natural represents the all-`2`
ternary address at every precision. -/
theorem no_ordinary_minusOne_inverseLimit_address (n : ℕ) :
    ¬∀ k : ℕ, n % 3 ^ k = 3 ^ k - 1 := by
  intro hall
  obtain ⟨K, hK⟩ := ordinary_eventually_avoids_minusOne_spine n
  exact hK K (le_refl K) (hall K)

end KLMinusOneRail
end KontoroC

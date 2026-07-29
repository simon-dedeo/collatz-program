/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.LongDoublingQuineThreshold

/-!
# Denominator collapse for every long doubling quine

For a degree-`k` doubling equation, reducedness gives the reverse denominator
divisibility

`Q(kappa * X^2) ∣ X^k Q(X)`.

Degree alone only says `deg Q <= k`.  The missing one-line invariant is the
order of vanishing at zero.  Both the top degree and the trailing degree
double under the squaring substitution.  Comparing both across the same
quotient forces `natTrailingDegree Q = natDegree Q`; hence `Q` is a monomial.

This rules out every nonzero rational pole for every return length at once.
It is strictly stronger than enumerating the degree-two denominator shapes.
-/

namespace KontoroC
namespace LongDoublingQuineRationalNoGo

open Polynomial
open SuccessorQuineRationalNoGo
open DoublingQuineRationalNoGo

theorem natTrailingDegree_scale {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    (scale c p).natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · subst p
    simp [scale]
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [scale_coeff]
    exact mul_ne_zero (coeff_natTrailingDegree_ne_zero.mpr hp)
      (pow_ne_zero _ hc)
  · apply le_natTrailingDegree (scale_ne_zero hc hp)
    intro n hn
    rw [scale_coeff, coeff_eq_zero_of_lt_natTrailingDegree hn, zero_mul]

theorem natTrailingDegree_expand_two (p : ℚ[X]) :
    (Polynomial.expand ℚ 2 p).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases hp : p = 0
  · subst p
    simp
  let a := p.natTrailingDegree
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_expand (by norm_num)]
    simp only [dvd_mul_right, ↓reduceIte]
    simpa [Nat.mul_div_right] using coeff_natTrailingDegree_ne_zero.mpr hp
  · apply le_natTrailingDegree (expand_ne_zero (by norm_num) |>.2 hp)
    intro n hn
    rw [coeff_expand (by norm_num)]
    split_ifs with hdiv
    · apply coeff_eq_zero_of_lt_natTrailingDegree
      have htwice : 2 * (n / 2) = n := Nat.mul_div_cancel' hdiv
      omega
    · rfl

theorem natTrailingDegree_squareScale {kappa : ℚ} (hkappa : kappa ≠ 0)
    (p : ℚ[X]) :
    (squareScale kappa p).natTrailingDegree = 2 * p.natTrailingDegree := by
  rw [show squareScale kappa p =
      Polynomial.expand ℚ 2 (scale kappa p) by
    rw [squareScale, scale, expand_eq_comp_X_pow, comp_assoc]
    simp]
  rw [natTrailingDegree_expand_two, natTrailingDegree_scale hkappa]

/-- Reverse squaring divisibility alone forces a monomial denominator, for
every shift degree `k`. -/
theorem denom_eq_monomial_of_reverse
    {kappa : ℚ} (hkappa : kappa ≠ 0) {k : ℕ}
    {Q : ℚ[X]} (hQ : Q ≠ 0)
    (hreverse : squareScale kappa Q ∣ X ^ k * Q) :
    ∃ q : ℚ, q ≠ 0 ∧ Q = C q * X ^ Q.natDegree := by
  obtain ⟨T, hT⟩ := hreverse
  have hscale : squareScale kappa Q ≠ 0 := squareScale_ne_zero hkappa hQ
  have hleft : X ^ k * Q ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  have hTne : T ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hT
    exact hleft hT
  have hdegree := congrArg Polynomial.natDegree hT
  have htrail := congrArg Polynomial.natTrailingDegree hT
  rw [natDegree_X_pow_mul k hQ, natDegree_mul hscale hTne,
    natDegree_squareScale hkappa] at hdegree
  rw [show X ^ k * Q = Q * X ^ k by ring,
    natTrailingDegree_mul_X_pow hQ,
    natTrailingDegree_mul hscale hTne,
    natTrailingDegree_squareScale hkappa] at htrail
  have hleT := natTrailingDegree_le_natDegree T
  have hkd : k = Q.natDegree + T.natDegree := by omega
  have hkt : k = Q.natTrailingDegree + T.natTrailingDegree := by omega
  have heq : Q.natTrailingDegree = Q.natDegree := by
    have hqa := natTrailingDegree_le_natDegree Q
    omega
  let q := Q.leadingCoeff
  have hq : q ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  let M := Q * C q⁻¹
  have hMmonic : M.Monic := monic_mul_leadingCoeff_inv hQ
  have hMdegree : M.natDegree = Q.natDegree := by
    dsimp only [M, q]
    rw [natDegree_mul_C (inv_ne_zero hq)]
  have hMtrail : M.natTrailingDegree = Q.natTrailingDegree := by
    dsimp only [M, q]
    rw [natTrailingDegree_mul hQ (C_ne_zero.mpr (inv_ne_zero hq))]
    simp
  have hM : M = X ^ M.natDegree :=
    (hMmonic.eq_X_pow_iff_natTrailingDegree_eq_natDegree).2 (by
      rw [hMdegree, hMtrail, heq])
  refine ⟨q, hq, ?_⟩
  let d := M.natDegree
  have hMd : M = X ^ d := hM
  have hd : d = Q.natDegree := hMdegree
  have hrecover : M * C q = Q := by
    dsimp only [M]
    rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hq, C_1, mul_one]
  have hshape : Q = C q * X ^ d := by
    calc
    Q = M * C q := hrecover.symm
    _ = X ^ d * C q := by rw [hMd]
    _ = C q * X ^ d := by ring
  have hpow : C q * X ^ d = C q * X ^ Q.natDegree :=
    congrArg (fun n : ℕ => C q * X ^ n) hd
  exact hshape.trans hpow

end LongDoublingQuineRationalNoGo
end KontoroC

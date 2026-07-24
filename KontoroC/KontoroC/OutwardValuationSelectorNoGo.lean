/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardWriterDecoderLiteral

/-!
# Obstruction to ternary valuation-recursive writer--decoder selectors

The last-nonzero-ternary-digit hierarchy partitions the ordinary naturals
above a center into exact layers

`n = center + 3^depth * digit (mod 3^(depth+1))`, `digit=1,2`.

A recursive selector may choose a different writer--decoder chart on every
such layer.  Nevertheless, each individual layer is a full ternary cylinder,
so the coarse dyadic-hole theorem produces arbitrarily large ordinary points
of that same exact valuation and primitive digit where the chosen chart is
illegal.  Thus valuation recursion alone cannot make the writer--decoder
architecture total.  A surviving selector must impose genuinely mixed
dyadic restrictions inside every regular ternary layer.
-/

namespace KontoroC
namespace OutwardValuationSelectorNoGo

open OutwardCoarseHole OutwardWriterDecoderSemantics
  OutwardWriterDecoderLiteral

/-- One exact layer of the last-nonzero-ternary-digit hierarchy. -/
def TernaryPrimitiveLayer
    (center depth digit n : ℕ) : Prop :=
  n ≡ center + 3 ^ depth * digit [MOD 3 ^ (depth + 1)]

/-- Membership in a primitive layer with digit `1` or `2` really fixes the
three-adic valuation of the displacement. -/
theorem padicValNat_sub_eq_depth_of_primitiveLayer
    {center depth digit n : ℕ}
    (hdigit_pos : 0 < digit) (hdigit_lt : digit < 3)
    (hnlarge : center < n)
    (hlayer : TernaryPrimitiveLayer center depth digit n) :
    padicValNat 3 (n - center) = depth := by
  have hcenterRight : center ≤ center + 3 ^ depth * digit := by omega
  have hdiff :
      n - center ≡ 3 ^ depth * digit [MOD 3 ^ (depth + 1)] := by
    simpa [TernaryPrimitiveLayer] using
      Nat.ModEq.sub hnlarge.le hcenterRight hlayer (Nat.ModEq.refl center)
  have hpowFactor : 3 ^ (depth + 1) = 3 ^ depth * 3 := by
    rw [pow_succ]
  have hdepthDvdModulus : 3 ^ depth ∣ 3 ^ (depth + 1) :=
    pow_dvd_pow 3 (by omega)
  have hdepthDvdRight : 3 ^ depth ∣ 3 ^ depth * digit :=
    dvd_mul_right _ _
  have hdepthDvd : 3 ^ depth ∣ n - center :=
    (hdiff.dvd_iff hdepthDvdModulus).mpr hdepthDvdRight
  have hnextNotRight : ¬3 ^ (depth + 1) ∣ 3 ^ depth * digit := by
    intro hdvd
    have hpositive : 0 < 3 ^ depth * digit := by positivity
    have hsmall : 3 ^ depth * digit < 3 ^ (depth + 1) := by
      rw [hpowFactor]
      exact Nat.mul_lt_mul_of_pos_left hdigit_lt (by positivity)
    exact (Nat.not_dvd_of_pos_of_lt hpositive hsmall) hdvd
  have hnextNot : ¬3 ^ (depth + 1) ∣ n - center := by
    intro hdvd
    exact hnextNotRight
      ((hdiff.dvd_iff (dvd_refl (3 ^ (depth + 1)))).mp hdvd)
  have hdiffNe : n - center ≠ 0 := by omega
  have hlower : depth ≤ padicValNat 3 (n - center) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiffNe).mp hdepthDvd
  have hupper : ¬depth + 1 ≤ padicValNat 3 (n - center) := by
    intro hle
    exact hnextNot
      ((Nat.pow_dvd_iff_le_padicValNat (by norm_num) hdiffNe).mpr hle)
  omega

/-- Even after choosing an arbitrary separate chart for this valuation depth
and primitive digit, there are arbitrarily large ordinary members of the
same layer where the exact literal cell data do not exist. -/
theorem exists_large_failure_in_primitiveLayer
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride)
    (center depth digit B : ℕ) :
    ∃ n,
      B < n ∧
      TernaryPrimitiveLayer center depth digit n ∧
      ¬ LiteralWriterDecoderCandidate g q stride correction n := by
  obtain ⟨n, hnB, hnlayer, hncoarse⟩ :=
    exists_large_not_coarseWriterDecoderLegal
      (3 ^ (g + 2)) q stride correction (threePow_odd _) hstride
      (depth + 1) (center + 3 ^ depth * digit) B
  exact ⟨n, hnB, hnlayer, fun hliteral =>
    hncoarse (literalWriterDecoderCandidate_coarse hliteral)⟩

/-- Last-nonzero-digit form: the counterexample parameter can be chosen in
the exact requested valuation layer, not merely in its enclosing cylinder. -/
theorem exists_large_failure_with_exact_valuation
    (g q stride : ℕ) (correction : ℕ → ℕ)
    (hstride : Odd stride)
    (center depth digit B : ℕ)
    (hdigit_pos : 0 < digit) (hdigit_lt : digit < 3) :
    ∃ n,
      max B center < n ∧
      padicValNat 3 (n - center) = depth ∧
      TernaryPrimitiveLayer center depth digit n ∧
      ¬ LiteralWriterDecoderCandidate g q stride correction n := by
  obtain ⟨n, hnlarge, hnlayer, hnillegal⟩ :=
    exists_large_failure_in_primitiveLayer g q stride correction hstride
      center depth digit (max B center)
  exact ⟨n, hnlarge,
    padicValNat_sub_eq_depth_of_primitiveLayer hdigit_pos hdigit_lt
      (lt_of_le_of_lt (Nat.le_max_right B center) hnlarge) hnlayer,
    hnlayer, hnillegal⟩

/-- A recursive ternary selector may vary its chart arbitrarily with the
valuation depth and primitive digit; it still cannot cover even one complete
regular layer. -/
theorem no_primitiveLayer_forces_selectedChart
    (g q stride : ℕ → ℕ → ℕ)
    (correction : ℕ → ℕ → ℕ → ℕ)
    (hstride : ∀ depth digit, Odd (stride depth digit))
    (center depth digit : ℕ)
    (hdigit_pos : 0 < digit) (hdigit_lt : digit < 3) :
    ¬ ∀ n, TernaryPrimitiveLayer center depth digit n →
      LiteralWriterDecoderCandidate
        (g depth digit) (q depth digit) (stride depth digit)
        (correction depth digit) n := by
  intro htotal
  obtain ⟨n, _, _, hnlayer, hnillegal⟩ :=
    exists_large_failure_with_exact_valuation
      (g depth digit) (q depth digit) (stride depth digit)
      (correction depth digit) (hstride depth digit)
      center depth digit center hdigit_pos hdigit_lt
  exact hnillegal (htotal n hnlayer)

end OutwardValuationSelectorNoGo
end KontoroC

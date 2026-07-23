/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Fixed-chart rank obstruction for outward recharge graphs

This file formalizes the finite-graph part of QM162.  It deliberately starts
from the leading-coefficient valuation balance which a concrete symbolic
chart edge must prove.  It does not identify semantically equal expressions
on finite parameter domains, and it does not apply to chart *types* carrying
an unbounded runtime denominator.
-/

namespace KontoroC
namespace OutwardChartRankNoGo

/-- Integer-valued dyadic chart rank from the leading coefficient valuation
and the displayed denominator depth.  Integer subtraction is essential. -/
def chartRank (leadingV2 denominatorBits : ℕ) : ℤ :=
  (leadingV2 : ℤ) - (denominatorBits : ℤ)

/-- Taking `v2` of a certified leading-coefficient identity gives this
balance.  The rank therefore drops by exactly the word length plus drain. -/
theorem chartRank_drop_of_leading_balance
    {sourceV2 targetV2 sourceDenominator targetDenominator S a : ℕ}
    (hbalance :
      targetDenominator + sourceV2 =
        sourceDenominator + S + a + targetV2) :
    chartRank targetV2 targetDenominator =
      chartRank sourceV2 sourceDenominator - (S + a : ℕ) := by
  simp only [chartRank]
  omega

/-- A nonempty recharge has positive cost, so the preceding exact rank law is
strict. -/
theorem chartRank_strictly_drops
    {sourceV2 targetV2 sourceDenominator targetDenominator S a : ℕ}
    (hbalance :
      targetDenominator + sourceV2 =
        sourceDenominator + S + a + targetV2)
    (hcost : 0 < S + a) :
    chartRank targetV2 targetDenominator <
      chartRank sourceV2 sourceDenominator := by
  rw [chartRank_drop_of_leading_balance hbalance]
  omega

/-- No finite nonempty directed graph can have a strictly rank-decreasing
outgoing edge from every node.  Branching does not help: choose a node of
minimum rank and follow any one of its promised edges. -/
theorem no_finite_total_strict_descent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (rank : ι → ℤ) (edge : ι → ι → Prop)
    (hout : ∀ i, ∃ j, edge i j)
    (hdown : ∀ i j, edge i j → rank j < rank i) : False := by
  classical
  let ranks : Finset ℤ := Finset.univ.image rank
  have hranks : ranks.Nonempty := by
    simp [ranks]
  let minimum : ℤ := ranks.min' hranks
  have hminimumMem : minimum ∈ ranks := by
    exact Finset.min'_mem ranks hranks
  obtain ⟨i, _hi, hirank⟩ := Finset.mem_image.mp hminimumMem
  obtain ⟨j, hij⟩ := hout i
  have hjrank : rank j ∈ ranks := by
    simp [ranks]
  have hminimumLe : minimum ≤ rank j :=
    Finset.min'_le ranks (rank j) hjrank
  have hstrict : rank j < minimum := by
    simpa [hirank] using hdown i j hij
  exact (not_lt_of_ge hminimumLe) hstrict

/-- QM162 graph consequence.  Each certified edge supplies a positive
recharge cost and the corresponding exact chart-rank equation. -/
theorem no_finite_total_fixedChart_recharge
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (rank : ι → ℤ) (edge : ι → ι → Prop)
    (hout : ∀ i, ∃ j, edge i j)
    (hedge : ∀ i j, edge i j →
      ∃ cost : ℕ, 0 < cost ∧ rank j = rank i - (cost : ℤ)) : False := by
  apply no_finite_total_strict_descent rank edge hout
  intro i j hij
  obtain ⟨cost, hcost, hrank⟩ := hedge i j hij
  rw [hrank]
  omega

end OutwardChartRankNoGo
end KontoroC

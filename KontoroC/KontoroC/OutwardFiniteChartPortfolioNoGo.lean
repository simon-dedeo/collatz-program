/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardValuationSelectorNoGo

/-!
# Finite portfolios of writer--decoder charts leave dyadic holes

One literal writer--decoder chart occupies at most fifty residue classes
modulo `2^54`.  This file records the finite-union consequence: a portfolio
of charts still misses a dyadic class whenever its total row budget is less
than `2^54`.  CRT then places arbitrarily large ordinary parameters from
every prescribed ternary cylinder in that common hole.

This is an architecture obstruction, not a no-go theorem for arbitrary
dispatchers.  A mixed recursive selector may impose new dyadic information
after every step, and a sufficiently large or unbounded chart family is not
covered by the finite budget hypothesis below.
-/

namespace KontoroC
namespace OutwardFiniteChartPortfolioNoGo

open OutwardCoarseHole OutwardWriterDecoderSemantics
  OutwardWriterDecoderLiteral

variable {ι : Type*}

/-- The union of the dyadic residue covers used by a finite chart portfolio. -/
def portfolioCover (charts : Finset ι) (cover : ι → Finset ℕ) : Finset ℕ :=
  charts.biUnion cover

/-- If every chart uses at most fifty rows, the portfolio uses at most fifty
times its number of charts.  Overlap can only improve this bound. -/
theorem portfolioCover_card_le
    (charts : Finset ι) (cover : ι → Finset ℕ)
    (hcover : ∀ i ∈ charts, (cover i).card ≤ 50) :
    (portfolioCover charts cover).card ≤ 50 * charts.card := by
  calc
    (portfolioCover charts cover).card ≤
        ∑ i ∈ charts, (cover i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ charts, 50 := by
      exact Finset.sum_le_sum fun i hi ↦ hcover i hi
    _ = 50 * charts.card := by simp [Nat.mul_comm]

/-- A finite portfolio accepts a parameter when at least one retained chart
accepts it. -/
def PortfolioLegal (charts : Finset ι) (Legal : ι → ℕ → Prop)
    (n : ℕ) : Prop :=
  ∃ i ∈ charts, Legal i n

/-- Generic finite-portfolio hole theorem.  Each chart may have a completely
different legality predicate and a different set of dyadic rows. -/
theorem exists_large_illegal_for_portfolio
    (charts : Finset ι) (Legal : ι → ℕ → Prop)
    (cover : ι → Finset ℕ) (k a B : ℕ)
    (hcover : ∀ i ∈ charts, (cover i).card ≤ 50)
    (hbudget : 50 * charts.card < 2 ^ 54)
    (hnecessary : ∀ i ∈ charts, ∀ n,
      Legal i n → n % 2 ^ 54 ∈ cover i) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ∀ i ∈ charts, ¬Legal i n := by
  let combinedCover := portfolioCover charts cover
  have hcombinedCard : combinedCover.card < 2 ^ 54 :=
    (portfolioCover_card_le charts cover hcover).trans_lt hbudget
  obtain ⟨n, hnB, hn3, hnlegal⟩ :=
    exists_large_illegal_in_every_ternary_cylinder
      (PortfolioLegal charts Legal) combinedCover 54 k a B
      hcombinedCard (by
        intro n hn
        rcases hn with ⟨i, hi, hin⟩
        exact Finset.mem_biUnion.mpr
          ⟨i, hi, hnecessary i hi n hin⟩)
  refine ⟨n, hnB, hn3, fun i hi hin ↦ ?_⟩
  exact hnlegal ⟨i, hi, hin⟩

/-- Open-tail form of the generic portfolio obstruction. -/
theorem exists_positive_open_tail_illegal_for_portfolio
    (charts : Finset ι) (Legal : ι → ℕ → Prop)
    (cover : ι → Finset ℕ) (k u₀ : ℕ)
    (hcover : ∀ i ∈ charts, (cover i).card ≤ 50)
    (hbudget : 50 * charts.card < 2 ^ 54)
    (hnecessary : ∀ i ∈ charts, ∀ n,
      Legal i n → n % 2 ^ 54 ∈ cover i) :
    ∃ m, 0 < m ∧
      ∀ i ∈ charts, ¬Legal i (u₀ + 3 ^ k * m) := by
  obtain ⟨n, hnu₀, hn3, hnlegal⟩ :=
    exists_large_illegal_for_portfolio charts Legal cover k u₀ u₀
      hcover hbudget hnecessary
  have hu₀n : u₀ ≤ n := hnu₀.le
  have hdvd : 3 ^ k ∣ n - u₀ :=
    (Nat.modEq_iff_dvd' hu₀n).mp hn3.symm
  obtain ⟨m, hm⟩ := hdvd
  have hn : n = u₀ + 3 ^ k * m := by omega
  have hmpos : 0 < m := by
    by_contra hmzero
    have hm0 : m = 0 := by omega
    subst m
    simp at hn
    omega
  refine ⟨m, hmpos, fun i hi hin ↦ ?_⟩
  exact hnlegal i hi (by simpa [← hn] using hin)

/-! ## Literal writer--decoder specialization -/

/-- The canonical fifty-row cover attached to one literal chart. -/
noncomputable def literalChartCover
    (g q stride : ℕ) (correction : ℕ → ℕ) : Finset ℕ :=
  fiftyClassCover
    (smallCounterRow (3 ^ (g + 2)) q stride correction)
    (largeCounterTail (3 ^ (g + 2)) q stride)

theorem literalChartCover_card_le
    (g q stride : ℕ) (correction : ℕ → ℕ) :
    (literalChartCover g q stride correction).card ≤ 50 := by
  exact fiftyClassCover_card_le _ _

/-- Every exact literal candidate lies in its chart's canonical fifty-row
dyadic cover. -/
theorem literalCandidate_mem_chartCover
    {g q stride n : ℕ} {correction : ℕ → ℕ}
    (hstride : Odd stride)
    (h : LiteralWriterDecoderCandidate g q stride correction n) :
    n % 2 ^ 54 ∈ literalChartCover g q stride correction := by
  apply mem_fiftyClassCover_of_classified
    (CoarseWriterDecoderLegal (3 ^ (g + 2)) q stride correction)
    (smallCounterRow (3 ^ (g + 2)) q stride correction)
    (largeCounterTail (3 ^ (g + 2)) q stride) n
  · intro x hx
    exact coarseWriterDecoderLegal_classified (threePow_odd _) hstride hx
  · exact literalWriterDecoderCandidate_coarse h

/-- Main literal consequence: below the exact row budget, every ternary
parameter cylinder contains arbitrarily large ordinary coefficients rejected
by every chart in the finite portfolio. -/
theorem exists_large_without_literalCandidate_in_portfolio
    (charts : Finset ι)
    (g q stride : ι → ℕ)
    (correction : ι → ℕ → ℕ)
    (hstride : ∀ i ∈ charts, Odd (stride i))
    (hbudget : 50 * charts.card < 2 ^ 54)
    (k a B : ℕ) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ∀ i ∈ charts,
        ¬LiteralWriterDecoderCandidate
          (g i) (q i) (stride i) (correction i) n := by
  apply exists_large_illegal_for_portfolio charts
    (fun i n ↦ LiteralWriterDecoderCandidate
      (g i) (q i) (stride i) (correction i) n)
    (fun i ↦ literalChartCover (g i) (q i) (stride i) (correction i))
    k a B
  · intro i _
    exact literalChartCover_card_le _ _ _ _
  · exact hbudget
  · intro i hi n hn
    exact literalCandidate_mem_chartCover (hstride i hi) hn

/-- The same theorem in the open-tail parameterization produced after a
finite exact edge prefix. -/
theorem exists_positive_open_tail_without_literalCandidate_in_portfolio
    (charts : Finset ι)
    (g q stride : ι → ℕ)
    (correction : ι → ℕ → ℕ)
    (hstride : ∀ i ∈ charts, Odd (stride i))
    (hbudget : 50 * charts.card < 2 ^ 54)
    (k u₀ : ℕ) :
    ∃ m, 0 < m ∧
      ∀ i ∈ charts,
        ¬LiteralWriterDecoderCandidate
          (g i) (q i) (stride i) (correction i)
          (u₀ + 3 ^ k * m) := by
  apply exists_positive_open_tail_illegal_for_portfolio charts
    (fun i n ↦ LiteralWriterDecoderCandidate
      (g i) (q i) (stride i) (correction i) n)
    (fun i ↦ literalChartCover (g i) (q i) (stride i) (correction i))
    k u₀
  · intro i _
    exact literalChartCover_card_le _ _ _ _
  · exact hbudget
  · intro i hi n hn
    exact literalCandidate_mem_chartCover (hstride i hi) hn

/-- A convenient decimal form of the exact `2^54 / 50` budget. -/
theorem fifty_mul_card_lt_twoPow_fiftyFour
    {charts : Finset ι}
    (hcard : charts.card ≤ 360287970189) :
    50 * charts.card < 2 ^ 54 := by
  calc
    50 * charts.card ≤ 50 * 360287970189 :=
      Nat.mul_le_mul_left 50 hcard
    _ < 2 ^ 54 := by norm_num

/-- Decimal-budget specialization of the main literal portfolio theorem. -/
theorem exists_large_without_literalCandidate_in_portfolio_of_card_le
    (charts : Finset ι)
    (g q stride : ι → ℕ)
    (correction : ι → ℕ → ℕ)
    (hstride : ∀ i ∈ charts, Odd (stride i))
    (hcard : charts.card ≤ 360287970189)
    (k a B : ℕ) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ∀ i ∈ charts,
        ¬LiteralWriterDecoderCandidate
          (g i) (q i) (stride i) (correction i) n := by
  exact exists_large_without_literalCandidate_in_portfolio
    charts g q stride correction hstride
      (fifty_mul_card_lt_twoPow_fiftyFour hcard) k a B

/-- Decimal-budget open-tail specialization. -/
theorem exists_positive_open_tail_without_literalCandidate_in_portfolio_of_card_le
    (charts : Finset ι)
    (g q stride : ι → ℕ)
    (correction : ι → ℕ → ℕ)
    (hstride : ∀ i ∈ charts, Odd (stride i))
    (hcard : charts.card ≤ 360287970189)
    (k u₀ : ℕ) :
    ∃ m, 0 < m ∧
      ∀ i ∈ charts,
        ¬LiteralWriterDecoderCandidate
          (g i) (q i) (stride i) (correction i)
          (u₀ + 3 ^ k * m) := by
  exact exists_positive_open_tail_without_literalCandidate_in_portfolio
    charts g q stride correction hstride
      (fifty_mul_card_lt_twoPow_fiftyFour hcard) k u₀

end OutwardFiniteChartPortfolioNoGo
end KontoroC

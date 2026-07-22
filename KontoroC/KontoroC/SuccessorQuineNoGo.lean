/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.Laurent

/-!
# No finite Laurent solution for the successor return quine

For the legal unit route `1 -> 1 -> g -> g -> 1`, the successor ansatz
normalizes to

`A*r(z) - D*z^2*r(c*z) = b0 + b1*z + b2*z^2`.

A finite Laurent series `r = ∑ r_n z^n` would therefore obey

`A*r_n = B_n + D*c^(n-2)*r_(n-2)`.

This file proves that no finitely supported coefficient function can satisfy
that recurrence when `A`, `D`, `c`, and `b1` are nonzero.  The proof uses the
least negative exponent to exclude a principal part, then the greatest
remaining exponent to exclude positive degree.  The coefficient at one
finally excludes a constant.

This kernel-closes the Laurent-polynomial part of the successor-quine no-go.
The additional statement that every rational-function solution would have to
be Laurent polynomial is a separate denominator/pole theorem and is not
assumed here.
-/

namespace KontoroC

namespace SuccessorQuineNoGo

/-- Coefficients of the quadratic forcing term. -/
def forcing (b0 b1 b2 : ℚ) (n : ℤ) : ℚ :=
  if n = 0 then b0 else if n = 1 then b1 else if n = 2 then b2 else 0

/-- A finite Laurent solution cannot have a nonzero coefficient at a negative
exponent: choose the least such exponent and inspect its recurrence. -/
theorem negative_coefficient_eq_zero
    {A D c b0 b1 b2 : ℚ} (hA : A ≠ 0)
    (r : ℤ →₀ ℚ)
    (heq : ∀ n : ℤ,
      A * r n = forcing b0 b1 b2 n +
        D * c ^ (n - 2) * r (n - 2))
    {n : ℤ} (hn : n < 0) : r n = 0 := by
  by_contra hn0
  have hsne : r.support.Nonempty :=
    ⟨n, Finsupp.mem_support_iff.mpr hn0⟩
  let m := r.support.min' hsne
  have hmmem : m ∈ r.support := Finset.min'_mem _ _
  have hmne : r m ≠ 0 := Finsupp.mem_support_iff.mp hmmem
  have hmle : m ≤ n :=
    Finset.min'_le _ n (Finsupp.mem_support_iff.mpr hn0)
  have hmneg : m < 0 := lt_of_le_of_lt hmle hn
  have hm2zero : r (m - 2) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hm2mem
    have hle : m ≤ m - 2 := Finset.min'_le _ _ hm2mem
    omega
  have h := heq m
  rw [hm2zero] at h
  simp [forcing, show m ≠ 0 by omega, show m ≠ 1 by omega,
    show m ≠ 2 by omega] at h
  exact h.elim hA hmne

/-- Generic finite-Laurent obstruction.  Only four nonvanishing facts about
the coefficients are needed. -/
theorem no_finiteLaurent_solution
    {A D c b0 b1 b2 : ℚ}
    (hA : A ≠ 0) (hD : D ≠ 0) (hc : c ≠ 0) (hb1 : b1 ≠ 0) :
    ¬ ∃ r : ℤ →₀ ℚ, ∀ n : ℤ,
      A * r n = forcing b0 b1 b2 n +
        D * c ^ (n - 2) * r (n - 2) := by
  rintro ⟨r, heq⟩
  have hrneg : r (-1) = 0 :=
    negative_coefficient_eq_zero hA r heq (by omega)
  have hr1 : r 1 ≠ 0 := by
    intro hr
    have h := heq 1
    rw [hr] at h
    norm_num [forcing, hrneg] at h
    exact hb1 h.symm
  have hsne : r.support.Nonempty :=
    ⟨1, Finsupp.mem_support_iff.mpr hr1⟩
  let d := r.support.max' hsne
  have hdmem : d ∈ r.support := Finset.max'_mem _ _
  have hdne : r d ≠ 0 := Finsupp.mem_support_iff.mp hdmem
  have hdge : 1 ≤ d :=
    Finset.le_max' _ 1 (Finsupp.mem_support_iff.mpr hr1)
  have hd2zero : r (d + 2) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hd2mem
    have hle : d + 2 ≤ d := Finset.le_max' _ _ hd2mem
    omega
  have h := heq (d + 2)
  rw [hd2zero, show d + 2 - 2 = d by omega] at h
  simp [forcing, show d + 2 ≠ 0 by omega,
    show d + 2 ≠ 1 by omega, show d + 2 ≠ 2 by omega] at h
  have hz : c ^ d ≠ 0 := zpow_ne_zero d hc
  exact h.elim (fun hdc ↦ hdc.elim hD hz) hdne

def A : ℚ := 3 ^ 114
def D : ℚ := 2 ^ 154
def c : ℚ := 2 ^ 23 / 3 ^ 17
def b0 : ℚ := 3 ^ 57 + 2 ^ 77
def b1 : ℚ := 2 ^ 77
def b2 : ℚ := 2 ^ 77

/-- Exact successor-quine specialization: RQ3 has no finite Laurent-
polynomial solution over the rationals. -/
theorem no_successor_quine_finiteLaurent :
    ¬ ∃ r : ℤ →₀ ℚ, ∀ n : ℤ,
      A * r n = forcing b0 b1 b2 n +
        D * c ^ (n - 2) * r (n - 2) := by
  apply no_finiteLaurent_solution
  · norm_num [A]
  · norm_num [D]
  · norm_num [c]
  · norm_num [b1]

end SuccessorQuineNoGo

end KontoroC

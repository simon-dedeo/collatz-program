/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeDriftCertificate
import KontoroC.OutwardLiteralMacroOrbit

/-!
# Recurrent finite symbols require unbounded ordinary-charge fibers

An infinite literal recharge orbit has strictly increasing ordinary boundary
charges.  If an arbitrary finite symbolic quotient labels that orbit, some
symbol recurs infinitely often.  The charges lying over that one recurrent
symbol are then unbounded.

This is the precise semantic cost of recurrence in a finite first-passage
quotient.  A recurrent symbolic state cannot decode to one ordinary charge,
or even to any fixed finite set of charges.  A viable construction must
supply an unbounded fiber/cocycle together with coherent literal replay.
-/

namespace KontoroC
namespace OutwardRecurrentFiberNoGo

open OutwardInvariantBridge OutwardLiteralMacroOrbit

/-- A symbol occurs arbitrarily late in an infinite schedule. -/
def RecurrentSymbol {Symbol : Type*} (state : ℕ → Symbol)
    (symbol : Symbol) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ state n = symbol

/-- Every schedule over a finite type has a recurrent symbol. -/
theorem exists_recurrentSymbol
    {Symbol : Type*} [Finite Symbol] (state : ℕ → Symbol) :
    ∃ symbol, RecurrentSymbol state symbol := by
  obtain ⟨symbol, hinfinite⟩ := Finite.exists_infinite_fiber state
  have hset : ({n : ℕ | state n = symbol} : Set ℕ).Infinite := by
    rw [show {n : ℕ | state n = symbol} =
        state ⁻¹' ({symbol} : Set Symbol) by ext n; simp]
    exact Set.infinite_coe_iff.mp hinfinite
  refine ⟨symbol, fun N ↦ ?_⟩
  obtain ⟨n, hnmem, hn⟩ := hset.exists_gt N
  exact ⟨n, hn.le, hnmem⟩

/-- Later macro indices have strictly larger ordinary charges. -/
theorem charge_lt_of_index_lt
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    {m n : ℕ} (hmn : m < n) :
    charge m < charge n :=
  orbit_strictMono charge words hmacro hmn

/-- If one quotient symbol recurs, the ordinary charges represented by that
single symbol are unbounded. -/
theorem recurrentSymbol_charge_unbounded
    {Symbol : Type*}
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (state : ℕ → Symbol) (symbol : Symbol)
    (hrecurrent : RecurrentSymbol state symbol) :
    ∀ bound, ∃ n, state n = symbol ∧ bound < charge n := by
  intro bound
  obtain ⟨n, hn, hstate⟩ := hrecurrent (bound + 1)
  have hescape := orbit_linear_escape charge words hmacro n
  exact ⟨n, hstate, by omega⟩

/-- A recurrent quotient symbol cannot represent only a fixed finite set of
ordinary boundary charges. -/
theorem no_finite_chargeFiber_of_recurrentSymbol
    {Symbol : Type*}
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (state : ℕ → Symbol) (symbol : Symbol)
    (hrecurrent : RecurrentSymbol state symbol)
    (fiber : Finset ℕ)
    (hfiber : ∀ n, state n = symbol → charge n ∈ fiber) :
    False := by
  let bound := ∑ H ∈ fiber, H
  obtain ⟨n, hstate, hn⟩ :=
    recurrentSymbol_charge_unbounded charge words hmacro
      state symbol hrecurrent bound
  have hmem : charge n ∈ fiber := hfiber n hstate
  have hle : charge n ≤ bound := by
    dsimp only [bound]
    exact Finset.single_le_sum
      (fun H _ ↦ Nat.zero_le H) hmem
  omega

/-- Any finite labeling of an infinite literal recharge orbit has at least
one symbolic fiber carrying unbounded ordinary charges. -/
theorem exists_symbol_with_unbounded_chargeFiber
    {Symbol : Type*} [Finite Symbol]
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (state : ℕ → Symbol) :
    ∃ symbol, ∀ bound, ∃ n,
      state n = symbol ∧ bound < charge n := by
  obtain ⟨symbol, hrecurrent⟩ := exists_recurrentSymbol state
  exact ⟨symbol,
    recurrentSymbol_charge_unbounded charge words hmacro
      state symbol hrecurrent⟩

/-- Consequently no finite-state quotient can cover every visit by assigning
each symbolic state a fixed finite set of possible ordinary charges. -/
theorem no_finite_chargeFiber_decoder
    {Symbol : Type*} [Finite Symbol]
    (charge : ℕ → ℕ) (words : ℕ → List (List Bool))
    (hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n))
    (state : ℕ → Symbol) (fiber : Symbol → Finset ℕ)
    (hdecode : ∀ n, charge n ∈ fiber (state n)) :
    False := by
  obtain ⟨symbol, hrecurrent⟩ := exists_recurrentSymbol state
  exact no_finite_chargeFiber_of_recurrentSymbol
    charge words hmacro state symbol hrecurrent (fiber symbol)
    (fun n hstate ↦ by simpa [hstate] using hdecode n)

end OutwardRecurrentFiberNoGo
end KontoroC

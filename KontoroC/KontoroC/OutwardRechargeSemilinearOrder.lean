/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteGroupDriftNoGo

/-!
# Recharge reachability is a semilinear order

Adjoin equality to literal positive `RechargeEdge`.  The resulting relation
is a partial order.  More specifically, every principal upper cone is a
chain: two charges reachable from one ordinary source are themselves
comparable by literal recharge.  On such a cone the reachability order agrees
exactly with the usual numerical order on naturals.

Thus a finite ordinary-charge search can sort all retained descendants of one
source and replay the literal suffix between every consecutive pair.  Any
additional branching exists only in symbolic annotations, not in the
ordinary first-passage dynamics itself.
-/

namespace KontoroC
namespace OutwardRechargeSemilinearOrder

open OutwardDirectedPathExpansion OutwardRechargeChain

/-- Reflexive closure of literal positive recharge. -/
def RechargeReachable (H K : ℕ) : Prop :=
  H = K ∨ RechargeEdge H K

@[refl] theorem RechargeReachable.refl (H : ℕ) :
    RechargeReachable H H :=
  Or.inl rfl

theorem RechargeReachable.of_edge {H K : ℕ} (h : RechargeEdge H K) :
    RechargeReachable H K :=
  Or.inr h

/-- Reachability is transitive, using literal concatenation in the
edge--edge case. -/
@[trans] theorem RechargeReachable.trans {H K L : ℕ}
    (hHK : RechargeReachable H K) (hKL : RechargeReachable K L) :
    RechargeReachable H L := by
  rcases hHK with rfl | hHK
  · exact hKL
  rcases hKL with rfl | hKL
  · exact Or.inr hHK
  · exact Or.inr (RechargeEdge.trans hHK hKL)

/-- Positive recharge forbids a nontrivial cycle, so reflexive reachability
is antisymmetric. -/
theorem RechargeReachable.antisymm {H K : ℕ}
    (hHK : RechargeReachable H K) (hKH : RechargeReachable K H) :
    H = K := by
  rcases hHK with hEq | hHK
  · exact hEq
  rcases hKH with hEq | hKH
  · exact hEq.symm
  · exact (not_lt_of_ge hKH.lt.le hHK.lt).elim

/-- Reachability always respects ordinary numerical order. -/
theorem RechargeReachable.le {H K : ℕ} (h : RechargeReachable H K) :
    H ≤ K := by
  rcases h with rfl | h
  · exact le_rfl
  · exact h.lt.le

/-- Semilinearity: every principal upper cone of literal recharge
reachability is totally ordered. -/
theorem upperCone_total {H K L : ℕ}
    (hHK : RechargeReachable H K) (hHL : RechargeReachable H L) :
    RechargeReachable K L ∨ RechargeReachable L K := by
  rcases hHK with rfl | hHK
  · exact Or.inl hHL
  rcases hHL with rfl | hHL
  · exact Or.inr (Or.inr hHK)
  rcases RechargeEdge.eq_or_between_of_common_source hHK hHL with
      hEq | hKL | hLK
  · exact Or.inl (Or.inl hEq)
  · exact Or.inl (Or.inr hKL)
  · exact Or.inr (Or.inr hLK)

/-- On descendants of one common source, the literal reachability order is
exactly the ordinary numerical order. -/
theorem between_iff_le_of_common_source
    {H K L : ℕ} (hHK : RechargeReachable H K)
    (hHL : RechargeReachable H L) :
    RechargeReachable K L ↔ K ≤ L := by
  constructor
  · exact RechargeReachable.le
  · intro hKL
    rcases upperCone_total hHK hHL with hforward | hbackward
    · exact hforward
    · have hLK := hbackward.le
      have hEq : K = L := Nat.le_antisymm hKL hLK
      exact Or.inl hEq

/-- Strict numerical order between common descendants is exactly a positive
literal recharge edge. -/
theorem edge_iff_lt_of_common_source
    {H K L : ℕ} (hHK : RechargeReachable H K)
    (hHL : RechargeReachable H L) :
    RechargeEdge K L ↔ K < L := by
  constructor
  · exact RechargeEdge.lt
  · intro hKL
    have hreachable : RechargeReachable K L :=
      (between_iff_le_of_common_source hHK hHL).mpr hKL.le
    rcases hreachable with hEq | hedge
    · exact (Nat.ne_of_lt hKL hEq).elim
    · exact hedge

end OutwardRechargeSemilinearOrder
end KontoroC

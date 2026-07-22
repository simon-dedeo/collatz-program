/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.NegativeShadow

/-!
# The `-1` (Mersenne) shadow grammar

This is the exact Lean endpoint for `search_mersenne_shadow.py`.  The signed
fixed point `-1` and its valuation word `[1]` are built into the interface;
all actual orbit states and valuation legality remain natural-number data.
-/

namespace KontoroC

/-- The worker's word at counter level `m` with final collision extra `e`.
It is deliberately defined through the general negative-shadow grammar, so
the generic endpoint and growth theorems apply without a second proof. -/
def mersenneMacroWord (m e : ℕ) : List ℕ :=
  shadowMacroWord [1] m e

@[simp] theorem repeatWord_singleton (k m : ℕ) :
    repeatWord [k] m = List.replicate m k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [repeatWord_succ, ih]
      calc
        List.replicate m k ++ [k] =
            List.replicate m k ++ List.replicate 1 k := by simp
        _ = List.replicate (m + 1) k :=
          (List.replicate_add m 1 k).symm

theorem bumpLast_append_singleton (u : List ℕ) (k e : ℕ) :
    bumpLast e (u ++ [k]) = u ++ [k + e] := by
  induction u with
  | nil => simp [bumpLast]
  | cons a u ih =>
      cases u with
      | nil => simp [bumpLast]
      | cons b bs =>
          change a :: bumpLast e ((b :: bs) ++ [k]) =
            a :: ((b :: bs) ++ [k + e])
          exact congrArg (List.cons a) ih

/-- Syntactic bridge to the Python worker's
`(1,) * (level - 1) + (1 + extra,)` representation. -/
theorem mersenneMacroWord_eq (m e : ℕ) (hm : 0 < m) :
    mersenneMacroWord m e =
      List.replicate (m - 1) 1 ++ [1 + e] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [mersenneMacroWord, shadowMacroWord, repeatWord_singleton]
  have hr : List.replicate (n + 1) 1 =
      List.replicate n 1 ++ [1] := by
    calc
      List.replicate (n + 1) 1 =
          List.replicate n 1 ++ List.replicate 1 1 :=
        List.replicate_add n 1 1
      _ = List.replicate n 1 ++ [1] := by simp
  rw [hr, bumpLast_append_singleton]
  simp

/-- Exact special case used by the Mersenne worker:
`x = 2^m h - 1` is sent to `(3^m h - 1) / 2^e`. -/
theorem mersenneShadow_endpoint {h x m e : ℕ} (hm : 0 < m)
    (hx : (x : ℤ) = -1 + (2 : ℤ) ^ m * h)
    (hlegal : WordLegal x (mersenneMacroWord m e)) :
    (2 ^ e : ℤ) * runWord x (mersenneMacroWord m e) =
      -1 + (3 : ℤ) ^ m * h := by
  have hfix : (2 ^ totalValuation [1] : ℤ) * (-1) =
      (3 ^ [1].length : ℤ) * (-1) + affineOffset [1] := by
    norm_num [totalValuation, affineOffset]
  simpa [mersenneMacroWord, totalValuation] using
    (negativeShadow_endpoint (c := (-1 : ℤ)) (h := (h : ℤ))
      (w := [1]) (x := x) (m := m) (e := e) (by simp) hm hfix hx hlegal)

/-- An infinite exact renewal program around the negative fixed point `-1`.
`packet_odd` and `extra_pos` preserve the search artifact's exact-coordinate
semantics, although the final soundness proof needs only positivity, legality,
renewal, and the uniform extra bound. -/
structure MersenneShadowOrbit where
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  extraBound : ℕ
  level0_pos : 0 < level0
  extra_pos : ∀ t, 0 < extra t
  packet_pos : ∀ t, 0 < packet t
  packet_odd : ∀ t, Odd (packet t)
  extra_le : ∀ t, extra t ≤ extraBound
  coordinate : ∀ t, (state t : ℤ) =
    -1 + (2 : ℤ) ^ (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (mersenneMacroWord (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) =
    -1 + (3 : ℤ) ^ (level0 + t) * packet t

namespace MersenneShadowOrbit

/-- Forget the `-1`-specific presentation and obtain the general bounded
phase-shadow certificate. -/
def toBoundedPhaseShadowOrbit (g : MersenneShadowOrbit) :
    BoundedPhaseShadowOrbit where
  controller := fun _ => -1
  word := fun _ => [1]
  level0 := g.level0
  extra := g.extra
  packet := g.packet
  state := g.state
  numerator := 3
  denominator := 2
  extraBound := g.extraBound
  controller_neg := by simp
  word_nonempty := by simp
  level0_pos := g.level0_pos
  packet_pos := g.packet_pos
  denominator_pos := by norm_num
  supercritical := by norm_num
  common_shape := by simp [totalValuation]
  extra_le := g.extra_le
  fixed_affine := by simp [totalValuation, affineOffset]
  coordinate := by
    intro t
    simpa [totalValuation] using g.coordinate t
  legal := by
    intro t
    simpa [mersenneMacroWord] using g.legal t
  renewal := by
    intro t
    simpa using g.renewal t

/-- An infinite bounded-extra Mersenne renewal is a literal counterexample to
the ordinary Collatz conjecture formalized in `CleanLean`. -/
theorem not_conjecture (g : MersenneShadowOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toBoundedPhaseShadowOrbit.not_conjecture

end MersenneShadowOrbit

end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EventualGlider
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Positive orbits shadowing a negative affine controller

A negative accelerated cycle is used here only as a finite controller.  The
actual Collatz states and legality premises remain positive naturals.
-/

namespace KontoroC

/-- Concatenate `m` copies of one controller word. -/
def repeatWord (w : List ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => repeatWord w m ++ w

@[simp] theorem repeatWord_zero (w : List ℕ) : repeatWord w 0 = [] := rfl

@[simp] theorem repeatWord_succ (w : List ℕ) (m : ℕ) :
    repeatWord w (m + 1) = repeatWord w m ++ w := rfl

@[simp] theorem repeatWord_length (w : List ℕ) (m : ℕ) :
    (repeatWord w m).length = m * w.length := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih, Nat.succ_mul]

@[simp] theorem repeatWord_totalValuation (w : List ℕ) (m : ℕ) :
    totalValuation (repeatWord w m) = m * totalValuation w := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih, totalValuation_append, Nat.succ_mul]

/-- Increase only the final requested valuation. -/
def bumpLast (e : ℕ) : List ℕ → List ℕ
  | [] => []
  | [k] => [k + e]
  | k :: j :: ks => k :: bumpLast e (j :: ks)

theorem bumpLast_length {w : List ℕ} (hw : w ≠ []) (e : ℕ) :
    (bumpLast e w).length = w.length := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons k ks ih =>
      cases ks with
      | nil => simp [bumpLast]
      | cons j js => simp [bumpLast, ih (by simp)]

theorem bumpLast_totalValuation {w : List ℕ} (hw : w ≠ []) (e : ℕ) :
    totalValuation (bumpLast e w) = totalValuation w + e := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons k ks ih =>
      cases ks with
      | nil => simp [bumpLast]
      | cons j js => simp [bumpLast, ih (by simp), Nat.add_assoc]

/-- The last valuation never occurs in the affine offset, so increasing it
does not change that offset. -/
theorem bumpLast_affineOffset {w : List ℕ} (hw : w ≠ []) (e : ℕ) :
    affineOffset (bumpLast e w) = affineOffset w := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons k ks ih =>
      cases ks with
      | nil => simp [bumpLast]
      | cons j js =>
          simp [bumpLast, bumpLast_length (w := j :: js) (by simp),
            ih (by simp)]

theorem bumpLast_ne_nil {w : List ℕ} (hw : w ≠ []) (e : ℕ) :
    bumpLast e w ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [bumpLast_length hw e] at hlen
  exact hw (List.length_eq_zero_iff.mp (by simpa using hlen))

/-- The exact valuation word used by the negative-shadow worker. -/
def shadowMacroWord (w : List ℕ) (m e : ℕ) : List ℕ :=
  bumpLast e (repeatWord w m)

theorem repeatWord_ne_nil {w : List ℕ} (hw : w ≠ []) {m : ℕ} (hm : 0 < m) :
    repeatWord w m ≠ [] := by
  cases m with
  | zero => omega
  | succ m => simp [repeatWord, hw]

/-- A signed affine fixed point remains fixed under every repeated block.
No claim about negative Collatz dynamics is hidden here: signed legality of a
controller must be checked separately by the search side. -/
theorem signed_affine_fixed_repeat {c : ℤ} {w : List ℕ}
    (hfix : (2 ^ totalValuation w : ℤ) * c =
      (3 ^ w.length : ℤ) * c + affineOffset w) (m : ℕ) :
    (2 ^ totalValuation (repeatWord w m) : ℤ) * c =
      (3 ^ (repeatWord w m).length : ℤ) * c +
        affineOffset (repeatWord w m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [repeatWord_succ, totalValuation_append, List.length_append,
        affineOffset_append]
      push_cast
      calc
        (2 : ℤ) ^ (totalValuation (repeatWord w m) + totalValuation w) * c =
            (2 : ℤ) ^ totalValuation (repeatWord w m) *
              ((2 : ℤ) ^ totalValuation w * c) := by
                rw [pow_add]
                ring
        _ = (2 : ℤ) ^ totalValuation (repeatWord w m) *
              ((3 : ℤ) ^ w.length * c + affineOffset w) +
              0 := by rw [hfix]; ring
        _ = (3 : ℤ) ^ w.length *
              ((2 : ℤ) ^ totalValuation (repeatWord w m) * c) +
              (2 : ℤ) ^ totalValuation (repeatWord w m) * affineOffset w := by
                ring
        _ = (3 : ℤ) ^ w.length *
              ((3 : ℤ) ^ (repeatWord w m).length * c +
                affineOffset (repeatWord w m)) +
              (2 : ℤ) ^ totalValuation (repeatWord w m) * affineOffset w := by
                rw [ih]
        _ = (3 : ℤ) ^ ((repeatWord w m).length + w.length) * c +
              ((3 : ℤ) ^ w.length * affineOffset (repeatWord w m) +
                (2 : ℤ) ^ totalValuation (repeatWord w m) * affineOffset w) := by
                  rw [pow_add]
                  ring

/-- Exact shifted-coordinate macro identity.  If the positive macro word is
literally legal, its endpoint is the controller shadow divided by precisely
the extra final valuation. -/
theorem negativeShadow_endpoint {c h : ℤ} {x m e : ℕ} {w : List ℕ}
    (hw : w ≠ []) (hm : 0 < m)
    (hfix : (2 ^ totalValuation w : ℤ) * c =
      (3 ^ w.length : ℤ) * c + affineOffset w)
    (hx : (x : ℤ) = c + (2 ^ totalValuation w : ℤ) ^ m * h)
    (hlegal : WordLegal x (shadowMacroWord w m e)) :
    (2 ^ e : ℤ) * runWord x (shadowMacroWord w m e) =
      c + (3 ^ w.length : ℤ) ^ m * h := by
  let u := repeatWord w m
  have hu : u ≠ [] := repeatWord_ne_nil hw hm
  have hidNat := valuationWord_affine_identity hlegal
  have hid : (2 ^ totalValuation (shadowMacroWord w m e) : ℤ) *
      runWord x (shadowMacroWord w m e) =
      (3 ^ (shadowMacroWord w m e).length : ℤ) * x +
        affineOffset (shadowMacroWord w m e) := by
    exact_mod_cast hidNat
  have hfixed := signed_affine_fixed_repeat hfix m
  have hlen : (shadowMacroWord w m e).length = u.length := by
    exact bumpLast_length hu e
  have htotal : totalValuation (shadowMacroWord w m e) =
      totalValuation u + e := bumpLast_totalValuation hu e
  have hoffset : affineOffset (shadowMacroWord w m e) = affineOffset u :=
    bumpLast_affineOffset hu e
  have hQ : (2 ^ totalValuation u : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hQ
  calc
    (2 ^ totalValuation u : ℤ) *
        ((2 ^ e : ℤ) * runWord x (shadowMacroWord w m e)) =
        (2 ^ totalValuation (shadowMacroWord w m e) : ℤ) *
          runWord x (shadowMacroWord w m e) := by rw [htotal, pow_add]; ring
    _ = (3 ^ (shadowMacroWord w m e).length : ℤ) * x +
          affineOffset (shadowMacroWord w m e) := hid
    _ = (3 ^ u.length : ℤ) * x + affineOffset u := by rw [hlen, hoffset]
    _ = (2 ^ totalValuation u : ℤ) *
          (c + (3 ^ w.length : ℤ) ^ m * h) := by
            have hQpow : (2 ^ totalValuation u : ℤ) =
                (2 ^ totalValuation w : ℤ) ^ m := by
              dsimp [u]
              rw [repeatWord_totalValuation, mul_comm, pow_mul]
            have hPpow : (3 ^ u.length : ℤ) =
                (3 ^ w.length : ℤ) ^ m := by
              dsimp [u]
              rw [repeatWord_length, mul_comm, pow_mul]
            calc
              (3 ^ u.length : ℤ) * x + affineOffset u =
                  (3 ^ u.length : ℤ) *
                    (c + (2 ^ totalValuation w : ℤ) ^ m * h) +
                    affineOffset u := by rw [hx]
              _ = (3 ^ u.length : ℤ) * c + affineOffset u +
                    (3 ^ u.length : ℤ) *
                      ((2 ^ totalValuation w : ℤ) ^ m * h) := by ring
              _ = (2 ^ totalValuation u : ℤ) * c +
                    (3 ^ u.length : ℤ) *
                      ((2 ^ totalValuation w : ℤ) ^ m * h) := by rw [hfixed]
              _ = (2 ^ totalValuation u : ℤ) *
                    (c + (3 ^ w.length : ℤ) ^ m * h) := by
                      rw [hQpow, hPpow]
                      ring

/-- Division form of `negativeShadow_endpoint`, matching the worker's exact
integer formula. -/
theorem negativeShadow_endpoint_ediv {c h : ℤ} {x m e : ℕ} {w : List ℕ}
    (hw : w ≠ []) (hm : 0 < m)
    (hfix : (2 ^ totalValuation w : ℤ) * c =
      (3 ^ w.length : ℤ) * c + affineOffset w)
    (hx : (x : ℤ) = c + (2 ^ totalValuation w : ℤ) ^ m * h)
    (hlegal : WordLegal x (shadowMacroWord w m e)) :
    (runWord x (shadowMacroWord w m e) : ℤ) =
      (c + (3 ^ w.length : ℤ) ^ m * h) / 2 ^ e := by
  symm
  apply Int.ediv_eq_of_eq_mul_left (by positivity)
  simpa [mul_comm] using (negativeShadow_endpoint hw hm hfix hx hlegal).symm

/-- A supercritical shadow macro is strictly outward whenever its multiplier
beats the bounded collision cost at that level. -/
theorem negativeShadow_strict_growth
    {c : ℤ} {P Q m e h x y : ℕ}
    (hc : c < 0) (hh : 0 < h)
    (hx : (x : ℤ) = c + (Q : ℤ) ^ m * h)
    (hy : (2 ^ e : ℤ) * y = c + (P : ℤ) ^ m * h)
    (hratio : 2 ^ e * Q ^ m < P ^ m) : x < y := by
  have hcscale : (2 ^ e : ℤ) * c ≤ c := by
    have hone : (1 : ℤ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
    simpa using mul_le_mul_of_nonpos_right hone hc.le
  have hratioInt : (2 ^ e : ℤ) * Q ^ m * h < (P : ℤ) ^ m * h := by
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hratio) (by exact_mod_cast hh)
  have hscaled : (2 ^ e : ℤ) * x < (2 ^ e : ℤ) * y := by
    rw [hx, hy]
    nlinarith
  have hxyInt : (x : ℤ) < y := lt_of_mul_lt_mul_left hscaled (by positivity)
  exact_mod_cast hxyInt

/-- If `P>Q>0`, every collision bound `e≤E` is eventually dominated by the
supercritical ratio. -/
theorem eventually_twoPow_mul_pow_lt_pow {P Q E : ℕ}
    (hQ : 0 < Q) (hPQ : Q < P) :
    ∃ N, ∀ m, N ≤ m → ∀ e, e ≤ E → 2 ^ e * Q ^ m < P ^ m := by
  let r : ℝ := P / Q
  have hr : 1 < r := by
    dsimp [r]
    exact (one_lt_div (by exact_mod_cast hQ)).2 (by exact_mod_cast hPQ)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((2 : ℝ) ^ E) hr
  refine ⟨N, fun m hm e he ↦ ?_⟩
  have hepow : (2 : ℝ) ^ e ≤ 2 ^ E :=
    pow_le_pow_right₀ (by norm_num) he
  have hrpow : r ^ N ≤ r ^ m := pow_le_pow_right₀ hr.le hm
  have hclock : (2 : ℝ) ^ e < r ^ m := hepow.trans_lt (hN.trans_le hrpow)
  have hQpow : 0 < (Q : ℝ) ^ m := pow_pos (by exact_mod_cast hQ) _
  have hmul := mul_lt_mul_of_pos_right hclock hQpow
  have hreal : (2 : ℝ) ^ e * Q ^ m < P ^ m := by
    calc
      (2 : ℝ) ^ e * Q ^ m < r ^ m * Q ^ m := hmul
      _ = P ^ m := by
        dsimp [r]
        rw [div_pow]
        field_simp
  exact_mod_cast hreal

/-- An all-level renewal certificate built from one negative affine
controller.  The controller is signed, while every actual state and exact
valuation word is natural. -/
structure NegativeShadowRenewal where
  controller : ℤ
  word : List ℕ
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  controller_neg : controller < 0
  word_nonempty : word ≠ []
  level0_pos : 0 < level0
  start_large : 4 < state 0
  packet_pos : ∀ t, 0 < packet t
  fixed_affine : (2 ^ totalValuation word : ℤ) * controller =
    (3 ^ word.length : ℤ) * controller + affineOffset word
  coordinate : ∀ t, (state t : ℤ) = controller +
    (2 ^ totalValuation word : ℤ) ^ (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (shadowMacroWord word (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) = controller +
    (3 ^ word.length : ℤ) ^ (level0 + t) * packet t
  ratio : ∀ t,
    2 ^ extra t * (2 ^ totalValuation word) ^ (level0 + t) <
      (3 ^ word.length) ^ (level0 + t)

namespace NegativeShadowRenewal

/-- Every exact renewal certificate instantiates the generic macro-glider
interface. -/
def toMacroGlider (g : NegativeShadowRenewal) : MacroGlider where
  state := g.state
  word := fun t => shadowMacroWord g.word (g.level0 + t) (g.extra t)
  start_large := g.start_large
  word_nonempty := fun t => by
    apply bumpLast_ne_nil
    exact repeatWord_ne_nil g.word_nonempty (Nat.add_pos_left g.level0_pos t)
  legal := g.legal
  transition := fun t => by
    have hend := negativeShadow_endpoint g.word_nonempty
      (Nat.add_pos_left g.level0_pos t)
      g.fixed_affine (g.coordinate t) (g.legal t)
    have heq : (runWord (g.state t)
        (shadowMacroWord g.word (g.level0 + t) (g.extra t)) : ℤ) =
        g.state (t + 1) := by
      apply mul_left_cancel₀ (show (2 ^ g.extra t : ℤ) ≠ 0 by positivity)
      exact hend.trans (g.renewal t).symm
    exact_mod_cast heq
  grows := fun t =>
    negativeShadow_strict_growth g.controller_neg (g.packet_pos t)
      (g.coordinate t) (g.renewal t) (g.ratio t)

/-- End-to-end soundness of an infinite exact negative-shadow renewal. -/
theorem not_conjecture (g : NegativeShadowRenewal) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end NegativeShadowRenewal

/-- Phase-changing variant: the negative controller and its rotated word may
change at every renewal.  This matches `search_phase_shadow.py`; no theorem
assumes that a finite compatible phase path extends indefinitely. -/
structure PhaseShadowRenewal where
  controller : ℕ → ℤ
  word : ℕ → List ℕ
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  controller_neg : ∀ t, controller t < 0
  word_nonempty : ∀ t, word t ≠ []
  level0_pos : 0 < level0
  start_large : 4 < state 0
  packet_pos : ∀ t, 0 < packet t
  fixed_affine : ∀ t,
    (2 ^ totalValuation (word t) : ℤ) * controller t =
      (3 ^ (word t).length : ℤ) * controller t + affineOffset (word t)
  coordinate : ∀ t, (state t : ℤ) = controller t +
    (2 ^ totalValuation (word t) : ℤ) ^ (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (shadowMacroWord (word t) (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) = controller t +
    (3 ^ (word t).length : ℤ) ^ (level0 + t) * packet t
  ratio : ∀ t,
    2 ^ extra t * (2 ^ totalValuation (word t)) ^ (level0 + t) <
      (3 ^ (word t).length) ^ (level0 + t)

namespace PhaseShadowRenewal

/-- A phase-changing all-level renewal is still a literal macro-glider. -/
def toMacroGlider (g : PhaseShadowRenewal) : MacroGlider where
  state := g.state
  word := fun t => shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)
  start_large := g.start_large
  word_nonempty := fun t => by
    apply bumpLast_ne_nil
    exact repeatWord_ne_nil (g.word_nonempty t)
      (Nat.add_pos_left g.level0_pos t)
  legal := g.legal
  transition := fun t => by
    have hend := negativeShadow_endpoint (g.word_nonempty t)
      (Nat.add_pos_left g.level0_pos t)
      (g.fixed_affine t) (g.coordinate t) (g.legal t)
    have heq : (runWord (g.state t)
        (shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)) : ℤ) =
        g.state (t + 1) := by
      apply mul_left_cancel₀ (show (2 ^ g.extra t : ℤ) ≠ 0 by positivity)
      exact hend.trans (g.renewal t).symm
    exact_mod_cast heq
  grows := fun t =>
    negativeShadow_strict_growth (g.controller_neg t) (g.packet_pos t)
      (g.coordinate t) (g.renewal t) (g.ratio t)

theorem not_conjecture (g : PhaseShadowRenewal) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end PhaseShadowRenewal

/-- Exact all-level phase-shadow data with a common supercritical multiplier
and a uniform collision bound.  Unlike `PhaseShadowRenewal`, growth and a
large starting state are consequences rather than fields. -/
structure BoundedPhaseShadowOrbit where
  controller : ℕ → ℤ
  word : ℕ → List ℕ
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  numerator : ℕ
  denominator : ℕ
  extraBound : ℕ
  controller_neg : ∀ t, controller t < 0
  word_nonempty : ∀ t, word t ≠ []
  level0_pos : 0 < level0
  packet_pos : ∀ t, 0 < packet t
  denominator_pos : 0 < denominator
  supercritical : denominator < numerator
  common_shape : ∀ t,
    3 ^ (word t).length = numerator ∧
      2 ^ totalValuation (word t) = denominator
  extra_le : ∀ t, extra t ≤ extraBound
  fixed_affine : ∀ t,
    (2 ^ totalValuation (word t) : ℤ) * controller t =
      (3 ^ (word t).length : ℤ) * controller t + affineOffset (word t)
  coordinate : ∀ t, (state t : ℤ) = controller t +
    (2 ^ totalValuation (word t) : ℤ) ^ (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (shadowMacroWord (word t) (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) = controller t +
    (3 ^ (word t).length : ℤ) ^ (level0 + t) * packet t

namespace BoundedPhaseShadowOrbit

theorem macroWord_nonempty (g : BoundedPhaseShadowOrbit) (t : ℕ) :
    shadowMacroWord (g.word t) (g.level0 + t) (g.extra t) ≠ [] := by
  apply bumpLast_ne_nil
  exact repeatWord_ne_nil (g.word_nonempty t)
    (Nat.add_pos_left g.level0_pos t)

theorem state_pos (g : BoundedPhaseShadowOrbit) (t : ℕ) : 0 < g.state t := by
  have hlegal := g.legal t
  have hne := g.macroWord_nonempty t
  generalize hw : shadowMacroWord (g.word t) (g.level0 + t) (g.extra t) = w at hlegal hne
  cases w with
  | nil => exact (hne rfl).elim
  | cons k ks => exact hlegal.1.1

theorem transition (g : BoundedPhaseShadowOrbit) (t : ℕ) :
    runWord (g.state t)
      (shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)) =
        g.state (t + 1) := by
  have hend := negativeShadow_endpoint (g.word_nonempty t)
    (Nat.add_pos_left g.level0_pos t)
    (g.fixed_affine t) (g.coordinate t) (g.legal t)
  have heq : (runWord (g.state t)
      (shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)) : ℤ) =
      g.state (t + 1) := by
    apply mul_left_cancel₀ (show (2 ^ g.extra t : ℤ) ≠ 0 by positivity)
    exact hend.trans (g.renewal t).symm
  exact_mod_cast heq

/-- Beyond the Archimedean threshold, bounded collision valuations cannot
overcome the common supercritical multiplier. -/
theorem eventually_grows (g : BoundedPhaseShadowOrbit) :
    ∃ N, ∀ t, N ≤ t → g.state t < g.state (t + 1) := by
  obtain ⟨N, hN⟩ := eventually_twoPow_mul_pow_lt_pow
    g.denominator_pos g.supercritical (E := g.extraBound)
  refine ⟨N, fun t ht ↦ ?_⟩
  have hratio0 := hN (g.level0 + t)
    (ht.trans (Nat.le_add_left t g.level0)) (g.extra t) (g.extra_le t)
  have hshape := g.common_shape t
  have hratio :
      2 ^ g.extra t * (2 ^ totalValuation (g.word t)) ^ (g.level0 + t) <
        (3 ^ (g.word t).length) ^ (g.level0 + t) := by
    simpa [hshape.1, hshape.2] using hratio0
  exact negativeShadow_strict_growth (g.controller_neg t) (g.packet_pos t)
    (g.coordinate t) (g.renewal t) hratio

/-- Bounded exact renewal data automatically supplies an eventual glider.
Four extra strict steps after a positive state make the shifted start exceed
`4`. -/
theorem exists_eventualMacroGlider (g : BoundedPhaseShadowOrbit) :
    ∃ eg : EventualMacroGlider,
      eg.state = g.state ∧
      eg.word = (fun t =>
        shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)) := by
  obtain ⟨N, hN⟩ := g.eventually_grows
  have hg0 := hN N (Nat.le_refl N)
  have hg1 := hN (N + 1) (by omega)
  have hg2 := hN (N + 2) (by omega)
  have hg3 := hN (N + 3) (by omega)
  have hg1' : g.state (N + 1) < g.state (N + 2) := by
    convert hg1 using 1
  have hg2' : g.state (N + 2) < g.state (N + 3) := by
    convert hg2 using 1
  have hg3' : g.state (N + 3) < g.state (N + 4) := by
    convert hg3 using 1
  have hlarge : 4 < g.state (N + 4) := by
    have hp := g.state_pos N
    omega
  let eg : EventualMacroGlider :=
    { state := g.state
      word := fun t => shadowMacroWord (g.word t) (g.level0 + t) (g.extra t)
      tailStart := N + 4
      start_large := hlarge
      word_nonempty := fun t _ht => g.macroWord_nonempty t
      legal := fun t _ht => g.legal t
      transition := fun t _ht => g.transition t
      grows := fun t ht => hN t ((by omega : N ≤ N + 4).trans ht) }
  exact ⟨eg, rfl, rfl⟩

/-- End-to-end bounded-renewal consumer.  No separate growth premise or large
starting state is required. -/
theorem not_conjecture (g : BoundedPhaseShadowOrbit) :
    ¬CleanLean.Collatz.Conjecture := by
  obtain ⟨eg, _hstate, _hword⟩ := g.exists_eventualMacroGlider
  exact eg.not_conjecture

end BoundedPhaseShadowOrbit

end KontoroC

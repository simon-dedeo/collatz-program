/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardWriterDecoderSemantics

/-!
# Symbolic literal semantics for resonant decoders

This file proves the all-parameter execution part of QM164.  The old
`OutwardResonance` module checks one fixed word of length seventeen; here the
zero and one runs are handled by induction, so the result applies to every
resonance identity and does not expand a large parity word.
-/

namespace KontoroC
namespace OutwardResonantDecoder

open ShortcutParityPeriodicNoGo OutwardCodeCompactness OutwardFirstPassage

/-- A block of `z` even shortcut instructions removes an exact factor
`2^z`. -/
theorem executes_replicate_false (z x : ℕ) :
    Executes (List.replicate z false) (2 ^ z * x) x := by
  induction z with
  | zero => simp [Executes]
  | succ z ih =>
      rw [List.replicate_succ]
      simp only [Executes, Bool.false_eq_true, ↓reduceIte]
      refine ⟨2 ^ z * x, ?_, ih⟩
      rw [pow_succ]
      ring

/-- A block of `o` odd shortcut instructions maps `2^o*x-1` to
`3^o*x-1`.  The positivity hypothesis keeps the natural subtractions honest. -/
theorem executes_replicate_true (o x : ℕ) (hx : 0 < x) :
    Executes (List.replicate o true) (2 ^ o * x - 1) (3 ^ o * x - 1) := by
  induction o generalizing x with
  | zero => simp [Executes]
  | succ o ih =>
      rw [List.replicate_succ]
      simp only [Executes, ↓reduceIte]
      refine ⟨2 ^ o * (3 * x) - 1, ?_, ?_⟩
      · rw [pow_succ]
        have ha : 0 < 2 ^ o * x := Nat.mul_pos (by positivity) hx
        have hrewrite : 2 ^ o * (3 * x) = 3 * (2 ^ o * x) := by ring
        rw [hrewrite]
        rw [show 2 ^ o * 2 * x = 2 * (2 ^ o * x) by ring]
        omega
      · have h3x : 0 < 3 * x := by positivity
        convert ih (3 * x) h3x using 1
        rw [pow_succ]
        ring

/-- The general resonant decoder parity word `0^z 1^o`. -/
def resonantDecoderWord (z o : ℕ) : List Bool :=
  List.replicate z false ++ List.replicate o true

@[simp] theorem resonantDecoderWord_length (z o : ℕ) :
    (resonantDecoderWord z o).length = z + o := by
  simp [resonantDecoderWord]

@[simp] theorem count_true_replicate_false (z : ℕ) :
    (List.replicate z false).count true = 0 := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, ih]

@[simp] theorem resonantDecoderWord_oddCount (z o : ℕ) :
    (resonantDecoderWord z o).count true = o := by
  simp [resonantDecoderWord]

/-- Moving left along the final run of ones can only decrease the outward
slope ratio. -/
theorem threePow_le_twoPow_shift_of_le
    {z j m : ℕ} (hjm : j ≤ m)
    (hm : 3 ^ m ≤ 2 ^ (z + m)) :
    3 ^ j ≤ 2 ^ (z + j) := by
  by_contra hnot
  have hbad : 2 ^ (z + j) < 3 ^ j := by omega
  let r := m - j
  have hmjr : m = j + r := by
    dsimp [r]
    omega
  have h23 : 2 ^ r ≤ 3 ^ r := by
    exact Nat.pow_le_pow_left (by omega) r
  have hcontr : 2 ^ (z + m) < 3 ^ m := by
    calc
      2 ^ (z + m) = 2 ^ (z + j) * 2 ^ r := by
        rw [hmjr, show z + (j + r) = (z + j) + r by omega, pow_add]
      _ ≤ 2 ^ (z + j) * 3 ^ r :=
        Nat.mul_le_mul_left _ h23
      _ < 3 ^ j * 3 ^ r :=
        Nat.mul_lt_mul_of_pos_right hbad (by positivity)
      _ = 3 ^ m := by rw [hmjr, pow_add]
  omega

/-- The usual two adjacent slope inequalities make `0^z 1^o` a genuine
first-passage word. -/
theorem resonantDecoder_firstPassage
    {z o : ℕ} (hz : 0 < z) (ho : 0 < o)
    (hprevious : 3 ^ (o - 1) ≤ 2 ^ (z + o - 1))
    (houtward : 2 ^ (z + o) < 3 ^ o) :
    FirstPassage (resonantDecoderWord z o) := by
  constructor
  · simpa [WordOutward] using houtward
  · intro u hu
    have hlen : u.length < z + o := by
      simpa using properPrefix_length_lt hu
    have hprefix := hu.1
    rw [List.prefix_iff_eq_take] at hprefix
    rw [hprefix]
    by_cases hn : u.length ≤ z
    · have htake :
          (resonantDecoderWord z o).take u.length =
            List.replicate u.length false := by
        simp [resonantDecoderWord, List.take_append, hn]
      rw [htake]
      simp [WordOutward]
    · let j := u.length - z
      have hjpos : 0 < j := by dsimp [j]; omega
      have hjlt : j < o := by dsimp [j]; omega
      have hj : j ≤ o - 1 := by omega
      have hprev' : 3 ^ (o - 1) ≤ 2 ^ (z + (o - 1)) := by
        have hexponent : z + o - 1 = z + (o - 1) := by omega
        rw [← hexponent]
        exact hprevious
      have hslope : 3 ^ j ≤ 2 ^ (z + j) :=
        threePow_le_twoPow_shift_of_le hj hprev'
      have hzle : z ≤ u.length := by omega
      have htake :
          (resonantDecoderWord z o).take u.length =
            List.replicate z false ++ List.replicate j true := by
        simp [resonantDecoderWord, List.take_append,
          min_eq_right hzle, min_eq_left hjlt.le, j]
      rw [htake]
      simp only [WordOutward, List.length_append, List.length_replicate,
        List.count_append, count_true_replicate_false]
      simp only [List.count_replicate, Bool.true_eq, ↓reduceIte,
        zero_add]
      exact Nat.not_lt_of_ge hslope

/-- Exact literal decoder execution in a subtraction-free source interface.
The hypotheses are precisely the resonance identity and encoded payload
identity. -/
theorem resonantDecoder_executes
    {c z o d u q : ℕ}
    (hu : 0 < u) (hq : 0 < q)
    (hresonance : 2 ^ z = 1 + 3 ^ (c + 1) * d)
    (hpayload : u + d = 2 ^ (z + o) * q) :
    Executes (resonantDecoderWord z o)
      (3 * (3 ^ c * u) - 1)
      (3 * (3 ^ (c + o) * q) - 1) := by
  let x := 3 ^ (c + 1) * 2 ^ o * q
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsource :
      3 * (3 ^ c * u) - 1 = 2 ^ z * (x - 1) := by
    have hpowc : 3 ^ (c + 1) = 3 * 3 ^ c := by
      rw [pow_succ]
      ring
    have hpowzo : 2 ^ (z + o) = 2 ^ z * 2 ^ o := pow_add 2 z o
    have hxone : 1 ≤ x := hx
    have hbalance :
        3 * (3 ^ c * u) + 2 ^ z = 2 ^ z * x + 1 := by
      calc
        3 * (3 ^ c * u) + 2 ^ z =
            3 ^ (c + 1) * u + (1 + 3 ^ (c + 1) * d) := by
              rw [hresonance, hpowc]
              ring
        _ = 3 ^ (c + 1) * (u + d) + 1 := by ring
        _ = 3 ^ (c + 1) * (2 ^ (z + o) * q) + 1 := by
              rw [hpayload]
        _ = 2 ^ z * x + 1 := by
              dsimp [x]
              rw [hpowzo]
              ring
    rw [Nat.mul_sub_left_distrib]
    omega
  have hmiddle := executes_replicate_false z (x - 1)
  have hones := executes_replicate_true o (3 ^ (c + 1) * q) (by positivity)
  have hmiddleEq : x - 1 =
      2 ^ o * (3 ^ (c + 1) * q) - 1 := by
    dsimp [x]
    ring
  have htargetEq : 3 ^ o * (3 ^ (c + 1) * q) - 1 =
      3 * (3 ^ (c + o) * q) - 1 := by
    rw [show c + 1 = 1 + c by omega, pow_add, pow_add]
    ring
  rw [resonantDecoderWord, executes_append, hsource]
  refine ⟨x - 1, hmiddle, ?_⟩
  simpa [hmiddleEq, htargetEq] using hones

end OutwardResonantDecoder
end KontoroC

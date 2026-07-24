/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardStrictKraftGap
import KontoroC.OutwardSemanticAliasNoGo

/-!
# Exponential Kraft decay for the full iterated first-passage language

The universal `17/20` Kraft defect is not a finite-state phenomenon.  A
finite family of schedules containing exactly `n` first-passage blocks has
total dyadic mass at most `(17/20)^n` after flattening.

The proof uses two structural facts.  First-passage prefix-freeness gives
unique parsing, so flattened equal-depth schedules remain prefix-free.
Second, the tilted letter weight gains one factor `20/17` on every block.
The ordinary weighted Kraft inequality then supplies exponential decay.

This is a rarity theorem only.  It does not exclude a single measure-zero
infinite schedule and it makes no ordinary-root inference.
-/

namespace KontoroC
namespace OutwardIteratedKraftGap

open scoped BigOperators
open ShortcutParityPeriodicNoGo PrefixKraft OutwardFirstPassage
  OutwardCodeCompactness OutwardOddSlice OutwardStrictKraftGap
  OutwardSemanticAliasNoGo

/-- Flatten all block schedules in a finite family, identifying only equal
literal parity words. -/
def flattenedSchedules
    (schedules : Finset (List (List Bool))) : Finset (List Bool) :=
  schedules.image flattenWords

theorem mem_flattenedSchedules_iff
    {schedules : Finset (List (List Bool))} {w : List Bool} :
    w ∈ flattenedSchedules schedules ↔
      ∃ words ∈ schedules, flattenWords words = w := by
  simp [flattenedSchedules, eq_comm]

theorem wordWeight_append (q : Bool → ℝ) (u v : List Bool) :
    wordWeight q (u ++ v) = wordWeight q u * wordWeight q v := by
  simp [wordWeight]

theorem dyadicWeight_append (u v : List Bool) :
    dyadicWeight (u ++ v) = dyadicWeight u * dyadicWeight v := by
  simp [dyadicWeight, pow_add]

theorem wordWeight_nonneg (q : Bool → ℝ)
    (hq : ∀ b, 0 ≤ q b) (w : List Bool) :
    0 ≤ wordWeight q w := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [wordWeight_cons]
      exact mul_nonneg (hq b) ih

theorem dyadicWeight_nonneg (w : List Bool) :
    0 ≤ dyadicWeight w := by
  exact pow_nonneg (by norm_num) _

/-- Every first-passage block in a schedule contributes a separate tilt
factor. -/
theorem bias_pow_mul_dyadicWeight_flatten_le
    {words : List (List Bool)}
    (hwords : WordsIn FirstPassageCode words) :
    biasBase ^ words.length * dyadicWeight (flattenWords words) ≤
      wordWeight biasedLetter (flattenWords words) := by
  induction words with
  | nil => norm_num [flattenWords, dyadicWeight]
  | cons w words ih =>
      have hwfirst : FirstPassage w := hwords w (by simp)
      have htail : WordsIn FirstPassageCode words := by
        intro v hv
        exact hwords v (by simp [hv])
      have hw := biasBase_mul_dyadicWeight_le_of_outward hwfirst.1
      have hi := ih htail
      calc
        biasBase ^ (w :: words).length *
              dyadicWeight (flattenWords (w :: words)) =
            (biasBase * dyadicWeight w) *
              (biasBase ^ words.length *
                dyadicWeight (flattenWords words)) := by
                  simp only [List.length_cons, pow_succ, flattenWords,
                    dyadicWeight_append]
                  ring
        _ ≤ wordWeight biasedLetter w *
              wordWeight biasedLetter (flattenWords words) := by
                exact mul_le_mul hw hi
                  (mul_nonneg (pow_nonneg (by norm_num [biasBase]) _)
                    (dyadicWeight_nonneg _))
                  (wordWeight_nonneg biasedLetter biasedLetter_nonneg _)
        _ = wordWeight biasedLetter (flattenWords (w :: words)) := by
              rw [flattenWords, wordWeight_append]

/-- Equal-depth first-passage schedules have prefix-free flattened parity
words.  This is the unique-decoding step which prevents double-counting. -/
theorem flattenedSchedules_prefixFree
    (schedules : Finset (List (List Bool))) (n : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hlength : ∀ words ∈ schedules, words.length = n) :
    PrefixFree (flattenedSchedules schedules : Set (List Bool)) := by
  intro u hu v hv huv
  rcases mem_flattenedSchedules_iff.mp hu with
    ⟨left, hleft, rfl⟩
  rcases mem_flattenedSchedules_iff.mp hv with
    ⟨right, hright, rfl⟩
  have hp : left <+: right :=
    wordsIn_prefix_of_flatten_prefix
      (hwords left hleft) (hwords right hright) huv
  obtain ⟨suffix, hsuffix⟩ := hp
  have hsuffixLength : suffix.length = 0 := by
    have hlen := congrArg List.length hsuffix
    simp only [List.length_append] at hlen
    rw [hlength left hleft, hlength right hright] at hlen
    omega
  have hsuffixNil : suffix = [] :=
    List.eq_nil_of_length_eq_zero hsuffixLength
  subst suffix
  simpa using congrArg flattenWords hsuffix

/-- At fixed macro depth, first-passage parsing makes flattening injective. -/
theorem flattenWords_injOn_equalDepth
    (schedules : Finset (List (List Bool))) (n : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hlength : ∀ words ∈ schedules, words.length = n) :
    Set.InjOn flattenWords (schedules : Set (List (List Bool))) := by
  intro left hleft right hright heq
  have hpFlat : flattenWords left <+: flattenWords right := by
    rw [heq]
  have hp : left <+: right :=
    wordsIn_prefix_of_flatten_prefix
      (hwords left hleft) (hwords right hright) hpFlat
  obtain ⟨suffix, hsuffix⟩ := hp
  have hsuffixLength : suffix.length = 0 := by
    have hlen := congrArg List.length hsuffix
    simp only [List.length_append] at hlen
    rw [hlength left hleft, hlength right hright] at hlen
    omega
  have hsuffixNil : suffix = [] :=
    List.eq_nil_of_length_eq_zero hsuffixLength
  subst suffix
  simpa using hsuffix

theorem flattenedSchedules_card_eq
    (schedules : Finset (List (List Bool))) (n : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hlength : ∀ words ∈ schedules, words.length = n) :
    (flattenedSchedules schedules).card = schedules.card := by
  exact Finset.card_image_iff.mpr
    (flattenWords_injOn_equalDepth schedules n hwords hlength)

/-- Main theorem: the full `n`-fold first-passage language has exponential
dyadic Kraft decay, with no finite grammar or state space in the statement. -/
theorem finite_nMacro_dyadicMass_le
    (schedules : Finset (List (List Bool))) (n : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hlength : ∀ words ∈ schedules, words.length = n) :
    ∑ w ∈ flattenedSchedules schedules, dyadicWeight w ≤
      ((17 : ℝ) / 20) ^ n := by
  let C := flattenedSchedules schedules
  have hpf : PrefixFree (C : Set (List Bool)) :=
    flattenedSchedules_prefixFree schedules n hwords hlength
  have hpoint :
      ∑ w ∈ C, biasBase ^ n * dyadicWeight w ≤
        ∑ w ∈ C, wordWeight biasedLetter w := by
    apply Finset.sum_le_sum
    intro w hw
    rcases mem_flattenedSchedules_iff.mp hw with
      ⟨words, hmem, hflat⟩
    rw [← hflat, ← hlength words hmem]
    exact bias_pow_mul_dyadicWeight_flatten_le (hwords words hmem)
  have hkraft :
      ∑ w ∈ C, wordWeight biasedLetter w ≤ 1 :=
    weightedKraft_finite biasedLetter biasedLetter_nonneg
      biasedLetter_sum_le_one C hpf
  have htotal :
      biasBase ^ n * ∑ w ∈ C, dyadicWeight w ≤ 1 := by
    rw [Finset.mul_sum]
    exact hpoint.trans hkraft
  have hb : 0 < biasBase ^ n := by
    exact pow_pos (by norm_num [biasBase]) _
  have hdiv :
      ∑ w ∈ C, dyadicWeight w ≤ 1 / biasBase ^ n := by
    apply (le_div_iff₀ hb).2
    simpa [mul_comm] using htotal
  have hinverse : 1 / biasBase ^ n = ((17 : ℝ) / 20) ^ n := by
    rw [one_div, ← inv_pow]
    congr 1
    norm_num [biasBase]
  simpa [C, hinverse] using hdiv

/-- In particular, at every positive macro depth the total mass is strictly
less than one. -/
theorem finite_nMacro_dyadicMass_lt_one
    (schedules : Finset (List (List Bool))) (n : ℕ)
    (hn : 0 < n)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hlength : ∀ words ∈ schedules, words.length = n) :
    ∑ w ∈ flattenedSchedules schedules, dyadicWeight w < 1 := by
  exact (finite_nMacro_dyadicMass_le schedules n hwords hlength).trans_lt
    (by
      have hbase : (17 : ℝ) / 20 < 1 := by norm_num
      exact pow_lt_one₀ (by norm_num) hbase hn.ne')

/-- Exact finite residue-count form.  If every flattened schedule has bit
length `L`, then the number of distinct `n`-macro schedules is at most
`(17/20)^n` of all `2^L` Boolean words. -/
theorem finite_nMacro_card_bound_of_fixed_bitLength
    (schedules : Finset (List (List Bool))) (n L : ℕ)
    (hwords : ∀ words ∈ schedules,
      WordsIn FirstPassageCode words)
    (hmacroLength : ∀ words ∈ schedules, words.length = n)
    (hbitLength : ∀ words ∈ schedules,
      (flattenWords words).length = L) :
    20 ^ n * schedules.card ≤ 17 ^ n * 2 ^ L := by
  let C := flattenedSchedules schedules
  have hCbit : ∀ w ∈ C, w.length = L := by
    intro w hw
    rcases mem_flattenedSchedules_iff.mp hw with
      ⟨words, hmem, hflat⟩
    rw [← hflat]
    exact hbitLength words hmem
  have hmass := finite_nMacro_dyadicMass_le
    schedules n hwords hmacroLength
  have hmassEq :
      ∑ w ∈ C, dyadicWeight w =
        (C.card : ℝ) / (2 : ℝ) ^ L := by
    calc
      ∑ w ∈ C, dyadicWeight w =
          ∑ _w ∈ C, (2 : ℝ)⁻¹ ^ L := by
            apply Finset.sum_congr rfl
            intro w hw
            simp [dyadicWeight, hCbit w hw]
      _ = (C.card : ℝ) * (2 : ℝ)⁻¹ ^ L := by simp
      _ = (C.card : ℝ) / (2 : ℝ) ^ L := by
            rw [div_eq_mul_inv, inv_pow]
  have hratio :
      (C.card : ℝ) / (2 : ℝ) ^ L ≤
        (17 : ℝ) ^ n / (20 : ℝ) ^ n := by
    rw [← hmassEq]
    simpa [div_pow] using hmass
  have hcross :
      (C.card : ℝ) * (20 : ℝ) ^ n ≤
        (17 : ℝ) ^ n * (2 : ℝ) ^ L :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mp hratio
  have hcardEq := flattenedSchedules_card_eq
    schedules n hwords hmacroLength
  dsimp [C] at hcardEq hcross
  rw [hcardEq] at hcross
  have hcross' :
      (20 : ℝ) ^ n * (schedules.card : ℝ) ≤
        (17 : ℝ) ^ n * (2 : ℝ) ^ L := by
    simpa [mul_comm] using hcross
  exact_mod_cast hcross'

end OutwardIteratedKraftGap
end KontoroC

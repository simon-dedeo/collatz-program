/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahUniformMorphismNoGo

/-!
# Affine rigidity for variable-width YAH morphisms

This file develops the exact affine invariant needed to audit the proposed
all-width, marker-fixed morphism rigidity argument.  The final rigidity
theorem is built from finite simulations of the eleven pinned rules.
-/

namespace KontoroC
namespace YahVariableMorphismRigidity

open YahRewriteSystem
open YahRewriteSystem.Symbol

def symbolSlope : Symbol → ℕ
  | bin0 | bin1 => 2
  | tri0 | tri1 | tri2 => 3
  | slash => 0
  | dot => 1

def wordSlope (w : Word) : ℕ := (w.map symbolSlope).prod

def wordIntercept (w : Word) : ℕ := mixedEvalFrom 0 w

theorem symbolAction_affine (s : Symbol) (x : ℕ) :
    symbolAction s x = symbolSlope s * x + symbolAction s 0 := by
  cases s <;> simp [symbolAction, symbolSlope]

theorem mixedEvalFrom_affine (x : ℕ) (w : Word) :
    mixedEvalFrom x w = wordSlope w * x + wordIntercept w := by
  induction w generalizing x with
  | nil => simp [mixedEvalFrom, wordSlope, wordIntercept]
  | cons s rest ih =>
      change mixedEvalFrom (symbolAction s x) rest =
        (symbolSlope s * wordSlope rest) * x +
          mixedEvalFrom (symbolAction s 0) rest
      rw [ih, ih, symbolAction_affine]
      ring

theorem wordSlope_append (u v : Word) :
    wordSlope (u ++ v) = wordSlope u * wordSlope v := by
  simp [wordSlope, List.map_append, List.prod_append]

theorem wordIntercept_append (u v : Word) :
    wordIntercept (u ++ v) =
      wordSlope v * wordIntercept u + wordIntercept v := by
  change mixedEvalFrom 0 (u ++ v) =
    wordSlope v * mixedEvalFrom 0 u + mixedEvalFrom 0 v
  rw [show mixedEvalFrom 0 (u ++ v) =
      mixedEvalFrom (mixedEvalFrom 0 u) v by
    simp [mixedEvalFrom, List.foldl_append]]
  rw [mixedEvalFrom_affine]
  rfl

/-- A delimiter-free finite simulation preserves both coefficients of the
represented affine map. -/
theorem affine_eq_of_delimiter_free_trace {u v : Word}
    (h : Relation.TransGen Step u v)
    (hslash : u.count slash = 0) (hdot : u.count dot = 0) :
    wordSlope u = wordSlope v ∧ wordIntercept u = wordIntercept v := by
  have h0 := transGen_mixedEvalFrom_eq_of_delimiter_free h hslash hdot 0
  have h1 := transGen_mixedEvalFrom_eq_of_delimiter_free h hslash hdot 1
  rw [mixedEvalFrom_affine, mixedEvalFrom_affine] at h0 h1
  constructor <;> omega

theorem digitOnly_append {u v : Word} (hu : DigitOnly u) (hv : DigitOnly v) :
    DigitOnly (u ++ v) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hu x hx
  · exact hv x hx

theorem digitOnly_wordMap_pair (sigma : Symbol → Word) (a b : Symbol)
    (ha : DigitOnly (sigma a)) (hb : DigitOnly (sigma b)) :
    DigitOnly (YahContextGlider.wordMap sigma [a, b]) := by
  simpa [YahContextGlider.wordMap] using digitOnly_append ha hb

theorem affine_eq_of_basic_simulation (sigma : Symbol → Word)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma)
    {lhs rhs : Word} (rule : BasicRule lhs rhs)
    (hlhs : DigitOnly (YahContextGlider.wordMap sigma lhs)) :
    wordSlope (YahContextGlider.wordMap sigma lhs) =
        wordSlope (YahContextGlider.wordMap sigma rhs) ∧
      wordIntercept (YahContextGlider.wordMap sigma lhs) =
        wordIntercept (YahContextGlider.wordMap sigma rhs) := by
  apply affine_eq_of_delimiter_free_trace (hsim rule)
  · exact digitOnly_slash_count _ hlhs
  · exact digitOnly_dot_count _ hlhs

/-- Variable-width, marker-fixed, nonerasing digit morphisms. -/
structure MarkerFixedDigitMorphism (sigma : Symbol → Word) : Prop where
  slash_fixed : sigma slash = [slash]
  dot_fixed : sigma dot = [dot]
  bin0_digits : DigitOnly (sigma bin0)
  bin1_digits : DigitOnly (sigma bin1)
  tri0_digits : DigitOnly (sigma tri0)
  tri1_digits : DigitOnly (sigma tri1)
  tri2_digits : DigitOnly (sigma tri2)
  bin0_nonempty : sigma bin0 ≠ []
  bin1_nonempty : sigma bin1 ≠ []
  tri0_nonempty : sigma tri0 ≠ []
  tri1_nonempty : sigma tri1 ≠ []
  tri2_nonempty : sigma tri2 ≠ []

theorem wordSlope_pos (w : Word) (hw : DigitOnly w) : 0 < wordSlope w := by
  induction w with
  | nil => simp [wordSlope]
  | cons s rest ih =>
      have hs := hw s (by simp)
      have hrest : DigitOnly rest := by
        intro x hx
        exact hw x (by simp [hx])
      have hi := ih hrest
      cases s <;> simp [IsDigit] at hs
      all_goals
        simp only [wordSlope, List.map_cons, List.prod_cons, symbolSlope]
        positivity

theorem one_lt_wordSlope (w : Word) (hw : DigitOnly w) (hne : w ≠ []) :
    1 < wordSlope w := by
  cases w with
  | nil => contradiction
  | cons s rest =>
      have hs := hw s (by simp)
      have hrest : DigitOnly rest := by
        intro x hx
        exact hw x (by simp [hx])
      have hpos := wordSlope_pos rest hrest
      have hge : 1 ≤ wordSlope rest := hpos
      have hss : 2 ≤ symbolSlope s := by
        cases s <;> simp_all [IsDigit, symbolSlope]
      change 1 < symbolSlope s * wordSlope rest
      exact lt_of_lt_of_le (by omega : 1 < 2 * 1)
        (Nat.mul_le_mul hss hge)

/-- MR1, now without any common-width assumption. -/
theorem bin0_image_forced_variable (sigma : Symbol → Word)
    (hm : MarkerFixedDigitMorphism sigma)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma) :
    sigma bin0 = List.replicate (sigma bin0).length bin0 := by
  have hdt0 := hsim BasicRule.dt0
  have hreduction : Relation.TransGen Step (sigma bin0 ++ [dot]) [dot] := by
    simpa [YahContextGlider.wordMap, hm.dot_fixed] using hdt0
  exact digit_word_reducing_to_dot_all_bin0 _ hm.bin0_digits hreduction

private theorem pairAffine (sigma : Symbol → Word)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma)
    (a b c d : Symbol) (ha : DigitOnly (sigma a))
    (hb : DigitOnly (sigma b)) (rule : BasicRule [a, b] [c, d]) :
    wordSlope (sigma a ++ sigma b) = wordSlope (sigma c ++ sigma d) ∧
      wordIntercept (sigma a ++ sigma b) =
        wordIntercept (sigma c ++ sigma d) := by
  have h := affine_eq_of_basic_simulation sigma hsim rule
    (digitOnly_wordMap_pair sigma a b ha hb)
  simpa [YahContextGlider.wordMap] using h

set_option maxHeartbeats 800000 in
-- Expanding the six affine word equations creates large nonlinear-normalization terms.
-- The theorem derives the nine coefficient identities forced by the six A-rules.
theorem mr2_of_simulation (sigma : Symbol → Word)
    (hm : MarkerFixedDigitMorphism sigma)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma) :
    let α := wordSlope (sigma bin0)
    let β := wordSlope (sigma bin1)
    let ε := wordSlope (sigma tri0)
    let φ := wordSlope (sigma tri1)
    let γ := wordSlope (sigma tri2)
    let b := wordIntercept (sigma bin1)
    let e := wordIntercept (sigma tri0)
    let f := wordIntercept (sigma tri1)
    let g := wordIntercept (sigma tri2)
    e = 0 ∧ α * φ = β * ε ∧ f = b ∧ γ = φ ∧
      g = α * b ∧ ε = φ ∧ b * ε = b * (β + 1) ∧
      β = α ∧ b * (φ + 1) = b * α ^ 2 ∧
      b * (φ + α) = b * (α ^ 2 + 1) := by
  dsimp
  have h00 := pairAffine sigma hsim bin0 tri0 tri0 bin0
    hm.bin0_digits hm.tri0_digits BasicRule.a00
  have h01 := pairAffine sigma hsim bin0 tri1 tri0 bin1
    hm.bin0_digits hm.tri1_digits BasicRule.a01
  have h02 := pairAffine sigma hsim bin0 tri2 tri1 bin0
    hm.bin0_digits hm.tri2_digits BasicRule.a02
  have h10 := pairAffine sigma hsim bin1 tri0 tri1 bin1
    hm.bin1_digits hm.tri0_digits BasicRule.a10
  have h11 := pairAffine sigma hsim bin1 tri1 tri2 bin0
    hm.bin1_digits hm.tri1_digits BasicRule.a11
  have h12 := pairAffine sigma hsim bin1 tri2 tri2 bin1
    hm.bin1_digits hm.tri2_digits BasicRule.a12
  simp only [wordSlope_append, wordIntercept_append] at h00 h01 h02 h10 h11 h12
  have hA := bin0_image_forced_variable sigma hm hsim
  have hA0 : wordIntercept (sigma bin0) = 0 := by
    rw [hA]
    unfold wordIntercept
    rw [YahUniformMorphismNoGo.mixedEvalFrom_replicate_bin0]
    simp
  simp only [hA0, mul_zero, zero_add] at h00 h01 h02 h10 h11 h12
  have hα : 1 < wordSlope (sigma bin0) :=
    one_lt_wordSlope _ hm.bin0_digits hm.bin0_nonempty
  have hβ : 1 < wordSlope (sigma bin1) :=
    one_lt_wordSlope _ hm.bin1_digits hm.bin1_nonempty
  have hφ : 1 < wordSlope (sigma tri1) :=
    one_lt_wordSlope _ hm.tri1_digits hm.tri1_nonempty
  have he : wordIntercept (sigma tri0) = 0 := by
    nlinarith [h00.2]
  have hsf : wordSlope (sigma bin0) * wordSlope (sigma tri1) =
      wordSlope (sigma bin1) * wordSlope (sigma tri0) := by
    simpa [mul_comm] using h01.1
  have hf : wordIntercept (sigma tri1) = wordIntercept (sigma bin1) := by
    nlinarith [h01.2]
  have hgamma : wordSlope (sigma tri2) = wordSlope (sigma tri1) := by
    nlinarith [h02.1]
  have hg : wordIntercept (sigma tri2) =
      wordSlope (sigma bin0) * wordIntercept (sigma bin1) := by
    nlinarith [h02.2]
  have heps : wordSlope (sigma tri0) = wordSlope (sigma tri1) := by
    nlinarith [h10.1]
  have hbeps : wordIntercept (sigma bin1) * wordSlope (sigma tri0) =
      wordIntercept (sigma bin1) * (wordSlope (sigma bin1) + 1) := by
    nlinarith [h10.2]
  have hbeta : wordSlope (sigma bin1) = wordSlope (sigma bin0) := by
    nlinarith [h11.1]
  have hbphi : wordIntercept (sigma bin1) *
      (wordSlope (sigma tri1) + 1) =
      wordIntercept (sigma bin1) * wordSlope (sigma bin0) ^ 2 := by
    nlinarith [h11.2]
  have hblast : wordIntercept (sigma bin1) *
      (wordSlope (sigma tri1) + wordSlope (sigma bin0)) =
      wordIntercept (sigma bin1) * (wordSlope (sigma bin0) ^ 2 + 1) := by
    nlinarith [h12.2]
  exact ⟨he, hsf, hf, hgamma, hg, heps, hbeps, hbeta, hbphi, hblast⟩

/-- The positive-intercept branch of MR2 has only the slopes 2 and 3. -/
theorem mr2_positive_branch
    (α β ε φ γ b e f g : ℕ) (hα : 2 ≤ α) (hb : 0 < b)
    (h : e = 0 ∧ α * φ = β * ε ∧ f = b ∧ γ = φ ∧
      g = α * b ∧ ε = φ ∧ b * ε = b * (β + 1) ∧
      β = α ∧ b * (φ + 1) = b * α ^ 2 ∧
      b * (φ + α) = b * (α ^ 2 + 1)) :
    α = 2 ∧ β = 2 ∧ ε = 3 ∧ φ = 3 ∧ γ = 3 ∧
      e = 0 ∧ f = b ∧ g = 2 * b := by
  rcases h with ⟨he, _, hf, hγ, hg, hε, hbε, hβ, hbφ, hbLast⟩
  have hφa : φ = α + 1 := by
    nlinarith
  have hsq : φ + 1 = α ^ 2 := by
    nlinarith
  have hα2 : α = 2 := by
    nlinarith
  subst α
  simp_all

theorem digit_word_singleton_of_slope_le_three (w : Word)
    (hw : DigitOnly w) (hne : w ≠ []) (hslope : wordSlope w ≤ 3) :
    ∃ s, w = [s] := by
  cases w with
  | nil => contradiction
  | cons s rest =>
      have hs := hw s (by simp)
      have hrest : DigitOnly rest := by
        intro x hx
        exact hw x (by simp [hx])
      have hss : 2 ≤ symbolSlope s := by
        cases s <;> simp_all [IsDigit, symbolSlope]
      by_cases hr : rest = []
      · subst rest
        exact ⟨s, rfl⟩
      · have hrs : 2 ≤ wordSlope rest :=
          one_lt_wordSlope rest hrest hr
        change symbolSlope s * wordSlope rest ≤ 3 at hslope
        nlinarith

theorem digit_word_eq_bin0_of_signature (w : Word) (hw : DigitOnly w)
    (hne : w ≠ []) (hs : wordSlope w = 2) (hi : wordIntercept w = 0) :
    w = [bin0] := by
  obtain ⟨s, rfl⟩ := digit_word_singleton_of_slope_le_three w hw hne (by omega)
  cases s <;> simp_all [IsDigit, wordSlope, symbolSlope, wordIntercept,
    mixedEvalFrom, symbolAction]

theorem digit_word_eq_bin1_of_signature (w : Word) (hw : DigitOnly w)
    (hne : w ≠ []) (hs : wordSlope w = 2) (hi : 0 < wordIntercept w) :
    w = [bin1] := by
  obtain ⟨s, rfl⟩ := digit_word_singleton_of_slope_le_three w hw hne (by omega)
  cases s <;> simp_all [IsDigit, wordSlope, symbolSlope, wordIntercept,
    mixedEvalFrom, symbolAction]

theorem digit_word_eq_tri0_of_signature (w : Word) (hw : DigitOnly w)
    (hne : w ≠ []) (hs : wordSlope w = 3) (hi : wordIntercept w = 0) :
    w = [tri0] := by
  obtain ⟨s, rfl⟩ := digit_word_singleton_of_slope_le_three w hw hne (by omega)
  cases s <;> simp_all [IsDigit, wordSlope, symbolSlope, wordIntercept,
    mixedEvalFrom, symbolAction]

theorem digit_word_eq_tri1_of_signature (w : Word) (hw : DigitOnly w)
    (hne : w ≠ []) (hs : wordSlope w = 3) (hi : wordIntercept w = 1) :
    w = [tri1] := by
  obtain ⟨s, rfl⟩ := digit_word_singleton_of_slope_le_three w hw hne (by omega)
  cases s <;> simp_all [IsDigit, wordSlope, symbolSlope, wordIntercept,
    mixedEvalFrom, symbolAction]

theorem digit_word_eq_tri2_of_signature (w : Word) (hw : DigitOnly w)
    (hne : w ≠ []) (hs : wordSlope w = 3) (hi : wordIntercept w = 2) :
    w = [tri2] := by
  obtain ⟨s, rfl⟩ := digit_word_singleton_of_slope_le_three w hw hne (by omega)
  cases s <;> simp_all [IsDigit, wordSlope, symbolSlope, wordIntercept,
    mixedEvalFrom, symbolAction]

/-- In the positive-intercept branch, the morphism is already the identity on
all five digit symbols. -/
theorem identity_on_digits_of_bin1_intercept_pos (sigma : Symbol → Word)
    (hm : MarkerFixedDigitMorphism sigma)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma)
    (hb : 0 < wordIntercept (sigma bin1)) :
    sigma bin0 = [bin0] ∧ sigma bin1 = [bin1] ∧
      sigma tri0 = [tri0] ∧ sigma tri1 = [tri1] ∧ sigma tri2 = [tri2] := by
  have hmr := mr2_of_simulation sigma hm hsim
  have hα : 2 ≤ wordSlope (sigma bin0) :=
    one_lt_wordSlope _ hm.bin0_digits hm.bin0_nonempty
  have hp := mr2_positive_branch
    (wordSlope (sigma bin0)) (wordSlope (sigma bin1))
    (wordSlope (sigma tri0)) (wordSlope (sigma tri1))
    (wordSlope (sigma tri2)) (wordIntercept (sigma bin1))
    (wordIntercept (sigma tri0)) (wordIntercept (sigma tri1))
    (wordIntercept (sigma tri2)) hα hb hmr
  rcases hp with ⟨hA, hB, hE, hF, hG, he, hf, hg⟩
  have eA0 : wordIntercept (sigma bin0) = 0 := by
    rw [bin0_image_forced_variable sigma hm hsim]
    unfold wordIntercept
    rw [YahUniformMorphismNoGo.mixedEvalFrom_replicate_bin0]
    simp
  have eA := digit_word_eq_bin0_of_signature _ hm.bin0_digits
    hm.bin0_nonempty hA eA0
  have eB := digit_word_eq_bin1_of_signature _ hm.bin1_digits
    hm.bin1_nonempty hB hb
  have hbOne : wordIntercept (sigma bin1) = 1 := by
    rw [eB]
    rfl
  have eE := digit_word_eq_tri0_of_signature _ hm.tri0_digits
    hm.tri0_nonempty hE he
  have eF := digit_word_eq_tri1_of_signature _ hm.tri1_digits
    hm.tri1_nonempty hF (by omega)
  have eG := digit_word_eq_tri2_of_signature _ hm.tri2_digits
    hm.tri2_nonempty hG (by omega)
  exact ⟨eA, eB, eE, eF, eG⟩

def ZeroDigitOnly (w : Word) : Prop :=
  ∀ s ∈ w, s = bin0 ∨ s = tri0

theorem zeroDigitOnly_of_intercept_zero (w : Word) (hw : DigitOnly w)
    (hi : wordIntercept w = 0) : ZeroDigitOnly w := by
  induction w with
  | nil => simp [ZeroDigitOnly]
  | cons s rest ih =>
      have hs := hw s (by simp)
      have hrest : DigitOnly rest := by
        intro x hx
        exact hw x (by simp [hx])
      have hintercept : wordSlope rest * symbolAction s 0 +
          wordIntercept rest = 0 := by
        change mixedEvalFrom 0 (s :: rest) = 0 at hi
        change mixedEvalFrom (symbolAction s 0) rest = 0 at hi
        rw [mixedEvalFrom_affine] at hi
        exact hi
      have hs0 : symbolAction s 0 = 0 := by
        have hpos := wordSlope_pos rest hrest
        nlinarith
      have hr0 : wordIntercept rest = 0 := by omega
      have hir := ih hrest hr0
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · cases x <;> simp_all [IsDigit, symbolAction]
      · exact hir x hx

theorem tri0_dvd_wordSlope_of_mem (w : Word) (hmem : tri0 ∈ w) :
    3 ∣ wordSlope w := by
  unfold wordSlope
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨tri0, hmem, by simp [symbolSlope]⟩

theorem all_bin0_of_zero_digits_and_two_power_slope (w : Word) (n : ℕ)
    (hz : ZeroDigitOnly w) (hs : wordSlope w = 2 ^ n) :
    w = List.replicate w.length bin0 := by
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  intro s hsMem
  rcases hz s hsMem with rfl | rfl
  · rfl
  · exfalso
    have hdvd : 3 ∣ 2 ^ n := by
      rw [← hs]
      exact tri0_dvd_wordSlope_of_mem w hsMem
    have hcop : Nat.Coprime 3 (2 ^ n) :=
      Nat.Coprime.pow_right n (by decide)
    have : (3 : ℕ) = 1 := hcop.eq_one_of_dvd hdvd
    omega

/-- Zero ternary count and zero binary-one count form a forward-invariant
region for slash-free rewriting.  In that region only terminal zero deletion
and the harmless zero-digit commutation can occur. -/
theorem step_zero_counts_closed {u v : Word} (h : Step u v)
    (hslash : u.count slash = 0) (hternary : ternaryCount u = 0)
    (hbin1 : u.count bin1 = 0) :
    ternaryCount v = 0 ∧ v.count bin1 = 0 := by
  cases h with
  | context left right rule =>
      cases rule <;>
        simp_all [ternaryCount, List.count_append] <;> omega

theorem transGen_zero_counts_closed {u v : Word}
    (h : Relation.TransGen Step u v)
    (hslash : u.count slash = 0) (hternary : ternaryCount u = 0)
    (hbin1 : u.count bin1 = 0) :
    ternaryCount v = 0 ∧ v.count bin1 = 0 := by
  induction h with
  | single huv => exact step_zero_counts_closed huv hslash hternary hbin1
  | tail hab hbc ih =>
      have hbslash : _ := transGen_slash_count hab
      exact step_zero_counts_closed hbc (by omega) ih.1 ih.2

theorem step_source_active {u v : Word} (h : Step u v) :
    0 < u.count slash + u.count dot + ternaryCount u + u.count bin1 := by
  cases h with
  | context left right rule =>
      cases rule <;>
        simp_all [ternaryCount, List.count_append] <;> omega

theorem no_step_all_bin0 (n : ℕ) (v : Word) :
    ¬ Step (List.replicate n bin0) v := by
  intro h
  have hactive := step_source_active h
  simp only [List.count_replicate, ternaryCount] at hactive
  have hs : (bin0 == slash) = false := by decide
  have hd : (bin0 == dot) = false := by decide
  have h0 : (bin0 == tri0) = false := by decide
  have h1 : (bin0 == tri1) = false := by decide
  have h2 : (bin0 == tri2) = false := by decide
  have hb : (bin0 == bin1) = false := by decide
  simp [hs, hd, h0, h1, h2, hb] at hactive

theorem transGen_exists_head {u v : Word} (h : Relation.TransGen Step u v) :
    ∃ z, Step u z := by
  induction h using Relation.TransGen.head_induction_on with
  | single huv => exact ⟨_, huv⟩
  | head huv _ _ => exact ⟨_, huv⟩

theorem no_transGen_from_all_bin0 (n : ℕ) (v : Word) :
    ¬ Relation.TransGen Step (List.replicate n bin0) v := by
  intro h
  obtain ⟨z, hz⟩ := transGen_exists_head h
  exact no_step_all_bin0 n z hz

theorem wordSlope_replicate_bin0 (n : ℕ) :
    wordSlope (List.replicate n bin0) = 2 ^ n := by
  simp [wordSlope, symbolSlope]

/-- The zero-intercept branch is impossible: it makes every digit image an
all-zero word, so the simulated A00 rule would be a nonempty derivation out of
an irreducible all-zero word. -/
theorem bin1_intercept_ne_zero (sigma : Symbol → Word)
    (hm : MarkerFixedDigitMorphism sigma)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma) :
    wordIntercept (sigma bin1) ≠ 0 := by
  intro hb0
  have hmr := mr2_of_simulation sigma hm hsim
  rcases hmr with ⟨he, _, hf, hgamma, hg, heps, _, hbeta, _, _⟩
  have hA := bin0_image_forced_variable sigma hm hsim
  let m := (sigma bin0).length
  have hAslope : wordSlope (sigma bin0) = 2 ^ m := by
    rw [hA]
    exact wordSlope_replicate_bin0 m
  have hBint : wordIntercept (sigma bin1) = 0 := hb0
  have hBzero := zeroDigitOnly_of_intercept_zero _ hm.bin1_digits hBint
  have hBslope : wordSlope (sigma bin1) = 2 ^ m := by omega
  have hB := all_bin0_of_zero_digits_and_two_power_slope
    (sigma bin1) m hBzero hBslope
  have hdt1 := hsim BasicRule.dt1
  have htrace : Relation.TransGen Step
      (sigma bin1 ++ [dot]) (sigma tri2 ++ [dot]) := by
    simpa [YahContextGlider.wordMap, hm.dot_fixed] using hdt1
  have hsourceSlash : (sigma bin1 ++ [dot]).count slash = 0 := by
    simp [digitOnly_slash_count _ hm.bin1_digits]
  have hsourceTernary : ternaryCount (sigma bin1 ++ [dot]) = 0 := by
    rw [hB]
    simp only [ternaryCount, List.count_append, List.count_replicate]
    have h0 : (bin0 == tri0) = false := by decide
    have h1 : (bin0 == tri1) = false := by decide
    have h2 : (bin0 == tri2) = false := by decide
    simp [h0, h1, h2]
  have hsourceBin1 : (sigma bin1 ++ [dot]).count bin1 = 0 := by
    rw [hB]
    simp only [List.count_append, List.count_replicate]
    have h0 : (bin0 == bin1) = false := by decide
    simp [h0]
  have htarget := transGen_zero_counts_closed htrace hsourceSlash
    hsourceTernary hsourceBin1
  have hGternary : ternaryCount (sigma tri2) = 0 := by
    simpa [ternaryCount, List.count_append] using htarget.1
  have hGbin1 : (sigma tri2).count bin1 = 0 := by
    simpa [List.count_append] using htarget.2
  have hG := digitOnly_eq_bin0_of_counts_zero _ hm.tri2_digits
    hGternary hGbin1
  let r := (sigma tri2).length
  have hGslope : wordSlope (sigma tri2) = 2 ^ r := by
    rw [hG]
    exact wordSlope_replicate_bin0 r
  have hFint : wordIntercept (sigma tri1) = 0 := by omega
  have hEint : wordIntercept (sigma tri0) = 0 := he
  have hFzero := zeroDigitOnly_of_intercept_zero _ hm.tri1_digits hFint
  have hEzero := zeroDigitOnly_of_intercept_zero _ hm.tri0_digits hEint
  have hFslope : wordSlope (sigma tri1) = 2 ^ r := by omega
  have hEslope : wordSlope (sigma tri0) = 2 ^ r := by omega
  have hF := all_bin0_of_zero_digits_and_two_power_slope
    (sigma tri1) r hFzero hFslope
  have hE := all_bin0_of_zero_digits_and_two_power_slope
    (sigma tri0) r hEzero hEslope
  have hAm : sigma bin0 = List.replicate m bin0 := by
    simpa [m] using hA
  have hEpow : 2 ^ (sigma tri0).length = 2 ^ r := by
    rw [← wordSlope_replicate_bin0, ← hE]
    exact hEslope
  have hElen : (sigma tri0).length = r :=
    Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) hEpow
  have hEr : sigma tri0 = List.replicate r bin0 := by
    simpa [hElen] using hE
  have ha00 := hsim BasicRule.a00
  have ha00' : Relation.TransGen Step
      (sigma bin0 ++ sigma tri0) (sigma tri0 ++ sigma bin0) := by
    simpa [YahContextGlider.wordMap] using ha00
  rw [hAm, hEr] at ha00'
  have hcomm : List.replicate r bin0 ++ List.replicate m bin0 =
      List.replicate m bin0 ++ List.replicate r bin0 := by
    rw [← List.replicate_add, ← List.replicate_add, Nat.add_comm]
  rw [hcomm] at ha00'
  have hzeroTrace : Relation.TransGen Step
      (List.replicate (m + r) bin0) (List.replicate (m + r) bin0) := by
    simpa only [List.replicate_add, Nat.add_comm] using ha00'
  exact no_transGen_from_all_bin0 (m + r) _ hzeroTrace

/-- Identity is the unique productive nonerasing digit-word morphism fixing
the two delimiters, with no common-width assumption. -/
theorem marker_fixed_digit_morphism_eq_identity (sigma : Symbol → Word)
    (hm : MarkerFixedDigitMorphism sigma)
    (hsim : YahUniformMorphismNoGo.BasicSimulation sigma) :
    sigma = fun s => [s] := by
  have hb : 0 < wordIntercept (sigma bin1) :=
    Nat.pos_of_ne_zero (bin1_intercept_ne_zero sigma hm hsim)
  rcases identity_on_digits_of_bin1_intercept_pos sigma hm hsim hb with
    ⟨h0, h1, ht0, ht1, ht2⟩
  funext s
  cases s with
  | bin0 => exact h0
  | bin1 => exact h1
  | slash => exact hm.slash_fixed
  | dot => exact hm.dot_fixed
  | tri0 => exact ht0
  | tri1 => exact ht1
  | tri2 => exact ht2


end YahVariableMorphismRigidity
end KontoroC

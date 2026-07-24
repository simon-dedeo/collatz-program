/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteStateKraftGap

/-!
# A uniform Kraft gap for outward first-passage words

This file extracts a quantitative scarcity consequence from outwardness.
The elementary rational comparison `3^3 < 2^5` implies that every outward
Boolean word has strictly fewer than `2/3` as many false letters as true
letters.  A slightly biased subprobability on the two letters can therefore
dominate ordinary dyadic mass by a fixed factor on every outward word.

The weighted Kraft lemma below is proved directly for arbitrary finite
prefix-free Boolean families.  It does not appeal to a probabilistic model or
to any Collatz orbit realization.
-/

namespace KontoroC
namespace OutwardStrictKraftGap

open scoped BigOperators
open ShortcutParityPeriodicNoGo PrefixKraft OutwardFirstPassage

/-- Exact integral slope consequence of outwardness. -/
theorem outward_false_true_slope {w : List Bool} (hout : WordOutward w) :
    3 * w.count false < 2 * w.count true := by
  have hodd : 0 < w.count true := by
    by_contra h
    have hz : w.count true = 0 := Nat.eq_zero_of_not_pos h
    simp only [WordOutward, hz, pow_zero] at hout
    have : 1 ≤ 2 ^ w.length := Nat.one_le_pow w.length 2 (by omega)
    omega
  by_contra hnot
  have h2 : 2 * w.count true ≤ 3 * w.count false := by omega
  have hlen := List.count_true_add_count_false w
  have hexp : 5 * w.count true ≤ 3 * w.length := by omega
  have hraise := Nat.pow_lt_pow_left hout (by omega : 3 ≠ 0)
  have hbase : 3 ^ 3 < 2 ^ 5 := by norm_num
  have hbaseRaise := Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hodd)
  have hmono : 2 ^ (5 * w.count true) ≤ 2 ^ (3 * w.length) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hbaseRaise' :
      3 ^ (3 * w.count true) < 2 ^ (5 * w.count true) := by
    simpa [pow_mul] using hbaseRaise
  have hraise' :
      2 ^ (3 * w.length) < 3 ^ (3 * w.count true) := by
    simpa [pow_mul, Nat.mul_comm] using hraise
  exact (lt_irrefl _ (hbaseRaise'.trans (hmono.trans_lt hraise')))

/-- Product weight of a Boolean word. -/
def wordWeight (q : Bool → ℝ) (w : List Bool) : ℝ :=
  (w.map q).prod

@[simp] theorem wordWeight_nil (q : Bool → ℝ) :
    wordWeight q [] = 1 := rfl

@[simp] theorem wordWeight_cons (q : Bool → ℝ) (b : Bool) (w : List Bool) :
    wordWeight q (b :: w) = q b * wordWeight q w := by
  simp [wordWeight]

/-- Tails of the members of `C` whose first letter is `b`. -/
def branch (C : Finset (List Bool)) (b : Bool) : Finset (List Bool) :=
  (C.filter fun w => w.head? = some b).image List.tail

theorem mem_branch_iff {C : Finset (List Bool)} {b : Bool} {u : List Bool} :
    u ∈ branch C b ↔ b :: u ∈ C := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, htail⟩
    have hwC := (Finset.mem_filter.mp hw).1
    have hhead := (Finset.mem_filter.mp hw).2
    obtain ⟨v, rfl⟩ := List.head?_eq_some_iff.mp hhead
    simp only [List.tail_cons] at htail
    subst u
    simpa using hwC
  · intro hu
    apply Finset.mem_image.mpr
    refine ⟨b :: u, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨hu, by simp⟩

theorem branch_prefixFree {C : Finset (List Bool)}
    (hpf : PrefixFree (C : Set (List Bool))) (b : Bool) :
    PrefixFree (branch C b : Set (List Bool)) := by
  intro u hu v hv huv
  have hbu : b :: u ∈ C := mem_branch_iff.mp hu
  have hbv : b :: v ∈ C := mem_branch_iff.mp hv
  have hcons : b :: u <+: b :: v := List.prefix_cons_inj b |>.mpr huv
  have := hpf hbu hbv hcons
  simpa using this

theorem branch_length_le {C : Finset (List Bool)} {L : ℕ}
    (hlen : ∀ w ∈ C, w.length ≤ L + 1) (b : Bool) :
    ∀ u ∈ branch C b, u.length ≤ L := by
  intro u hu
  have hbu : b :: u ∈ C := mem_branch_iff.mp hu
  simpa using hlen (b :: u) hbu

theorem sum_head_branch (q : Bool → ℝ) (C : Finset (List Bool)) (b : Bool) :
    (∑ w ∈ C.filter fun w => w.head? = some b, wordWeight q w) =
      q b * ∑ u ∈ branch C b, wordWeight q u := by
  classical
  let S := C.filter fun w => w.head? = some b
  have hinj : Set.InjOn List.tail (S : Set (List Bool)) := by
    intro u hu v hv huv
    have huhead := (Finset.mem_filter.mp hu).2
    have hvhead := (Finset.mem_filter.mp hv).2
    obtain ⟨ut, rfl⟩ := List.head?_eq_some_iff.mp huhead
    obtain ⟨vt, rfl⟩ := List.head?_eq_some_iff.mp hvhead
    simpa using huv
  have himage := Finset.sum_image (f := wordWeight q) hinj
  change (∑ w ∈ S, wordWeight q w) =
    q b * ∑ u ∈ S.image List.tail, wordWeight q u
  rw [himage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hhead := (Finset.mem_filter.mp hw).2
  obtain ⟨u, rfl⟩ := List.head?_eq_some_iff.mp hhead
  simp

/-- Bounded-length induction behind the finite weighted Kraft inequality. -/
theorem weightedKraft_finite_aux
    (q : Bool → ℝ)
    (hqnonneg : ∀ b, 0 ≤ q b)
    (hqsum : q false + q true ≤ 1)
    (L : ℕ)
    (C : Finset (List Bool))
    (hlen : ∀ w ∈ C, w.length ≤ L)
    (hpf : PrefixFree (C : Set (List Bool))) :
    ∑ w ∈ C, wordWeight q w ≤ 1 := by
  classical
  induction L generalizing C with
  | zero =>
      have hC : C ⊆ {[]} := by
        intro w hw
        have := hlen w hw
        have hwlen : w.length = 0 := by omega
        cases w with
        | nil => simp
        | cons b w => simp at hwlen
      have : C = ∅ ∨ C = {[]} := by
        by_cases hnil : [] ∈ C
        · right
          apply Finset.Subset.antisymm hC
          simpa using hnil
        · left
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          have hw0 : w = [] := by simpa using hC hw
          subst w
          exact hnil hw
      rcases this with rfl | rfl <;> simp
  | succ L ih =>
      by_cases hnil : [] ∈ C
      · have hC : C = {[]} := by
          apply Finset.ext
          intro w
          constructor
          · intro hw
            have heq := hpf hnil hw List.nil_prefix
            simpa [heq]
          · intro hw
            have : w = [] := by simpa using hw
            subst w
            exact hnil
        simp [hC]
      · let Cfalse := branch C false
        let Ctrue := branch C true
        have hfalse := ih Cfalse
          (branch_length_le hlen false)
          (branch_prefixFree hpf false)
        have htrue := ih Ctrue
          (branch_length_le hlen true)
          (branch_prefixFree hpf true)
        have hpartition :
            C.filter (fun w => ¬w.head? = some false) =
              C.filter (fun w => w.head? = some true) := by
          ext w
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hw, hnfalse⟩
            have hwne : w ≠ [] := by
              intro hw0
              exact hnil (hw0 ▸ hw)
            cases hhead : w.head? with
            | none =>
                cases w with
                | nil => exact (hwne rfl).elim
                | cons b w => simp at hhead
            | some b =>
                cases b <;> simp_all
          · rintro ⟨hw, htrue⟩
            exact ⟨hw, by simp [htrue]⟩
        have hsplit := Finset.sum_filter_add_sum_filter_not C
          (fun w => w.head? = some false) (wordWeight q)
        rw [hpartition] at hsplit
        rw [← hsplit, sum_head_branch, sum_head_branch]
        calc
          q false * ∑ u ∈ Cfalse, wordWeight q u +
              q true * ∑ u ∈ Ctrue, wordWeight q u ≤
              q false * 1 + q true * 1 := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hfalse (hqnonneg false))
                  (mul_le_mul_of_nonneg_left htrue (hqnonneg true))
          _ ≤ 1 := by simpa using hqsum

/-- Finite weighted Kraft inequality for a two-letter subprobability. -/
theorem weightedKraft_finite
    (q : Bool → ℝ)
    (hqnonneg : ∀ b, 0 ≤ q b)
    (hqsum : q false + q true ≤ 1)
    (C : Finset (List Bool))
    (hpf : PrefixFree (C : Set (List Bool))) :
    ∑ w ∈ C, wordWeight q w ≤ 1 := by
  classical
  apply weightedKraft_finite_aux q hqnonneg hqsum (C.sup List.length) C
  · intro w hw
    exact Finset.le_sup hw
  · exact hpf

/-- The small rational tilt used to obtain a strict uniform defect. -/
noncomputable def biasBase : ℝ := 20 / 17

/-- A subprobability on the Boolean alphabet.  Relative to a fair bit, a
true letter earns `biasBase^2` and a false letter pays
`biasBase^(-3)`. -/
noncomputable def biasedLetter (b : Bool) : ℝ :=
  if b then biasBase ^ 2 * (2 : ℝ)⁻¹
  else (biasBase⁻¹) ^ 3 * (2 : ℝ)⁻¹

/-- Ordinary fair-bit cylinder weight. -/
noncomputable def dyadicWeight (w : List Bool) : ℝ :=
  (2 : ℝ)⁻¹ ^ w.length

theorem wordWeight_eq_counts (q : Bool → ℝ) (w : List Bool) :
    wordWeight q w =
      q true ^ w.count true * q false ^ w.count false := by
  induction w with
  | nil => simp
  | cons b w ih =>
      cases b <;> simp [ih, pow_succ] <;> ring

theorem biasedLetter_nonneg : ∀ b, 0 ≤ biasedLetter b := by
  intro b
  cases b <;> simp [biasedLetter, biasBase] <;> positivity

/-- The tilted letter weights leave positive unused mass. -/
theorem biasedLetter_sum_le_one :
    biasedLetter false + biasedLetter true ≤ 1 := by
  norm_num [biasedLetter, biasBase]

theorem biasedWeight_eq (w : List Bool) :
    wordWeight biasedLetter w = dyadicWeight w *
      (biasBase ^ (2 * w.count true) *
        (biasBase⁻¹) ^ (3 * w.count false)) := by
  rw [wordWeight_eq_counts]
  rw [show biasedLetter true = biasBase ^ 2 * (2 : ℝ)⁻¹ by
        simp [biasedLetter],
      show biasedLetter false = (biasBase⁻¹) ^ 3 * (2 : ℝ)⁻¹ by
        simp [biasedLetter]]
  simp only [dyadicWeight]
  rw [show w.length = w.count true + w.count false by
    simpa using List.count_true_add_count_false w]
  rw [pow_add, pow_mul, pow_mul]
  ring

/-- Every outward word gains the fixed factor `20/17` under the tilted
subprobability. -/
theorem biasBase_mul_dyadicWeight_le_of_outward
    {w : List Bool} (hout : WordOutward w) :
    biasBase * dyadicWeight w ≤ wordWeight biasedLetter w := by
  have hslope := outward_false_true_slope hout
  have hexp : 3 * w.count false + 1 ≤ 2 * w.count true := by omega
  have hp := pow_le_pow_right₀
    (show (1 : ℝ) ≤ biasBase by norm_num [biasBase]) hexp
  have hmul := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ (biasBase⁻¹) ^ (3 * w.count false) by
      apply pow_nonneg
      exact inv_nonneg.mpr (by norm_num [biasBase]))
  have hleft :
      biasBase ^ (3 * w.count false + 1) *
          (biasBase⁻¹) ^ (3 * w.count false) = biasBase := by
    rw [pow_succ]
    calc
      biasBase ^ (3 * w.count false) * biasBase *
          biasBase⁻¹ ^ (3 * w.count false) =
          biasBase * (biasBase ^ (3 * w.count false) *
            biasBase⁻¹ ^ (3 * w.count false)) := by ring
      _ = biasBase * (biasBase * biasBase⁻¹) ^
          (3 * w.count false) := by rw [mul_pow]
      _ = biasBase := by simp [biasBase]
  rw [hleft] at hmul
  rw [biasedWeight_eq]
  have hd : 0 ≤ dyadicWeight w := by
    exact pow_nonneg (by norm_num) _
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hmul hd

/-- Universal strict Kraft bound for any finite prefix-free outward family. -/
theorem finite_outward_dyadicMass_le
    (C : Finset (List Bool))
    (hpf : PrefixFree (C : Set (List Bool)))
    (hout : ∀ w ∈ C, WordOutward w) :
    ∑ w ∈ C, dyadicWeight w ≤ (17 : ℝ) / 20 := by
  have hpoint :
      ∑ w ∈ C, biasBase * dyadicWeight w ≤
        ∑ w ∈ C, wordWeight biasedLetter w :=
    Finset.sum_le_sum fun w hw =>
      biasBase_mul_dyadicWeight_le_of_outward (hout w hw)
  have hkraft := weightedKraft_finite biasedLetter biasedLetter_nonneg
    biasedLetter_sum_le_one C hpf
  have htotal : biasBase * ∑ w ∈ C, dyadicWeight w ≤ 1 := by
    rw [Finset.mul_sum]
    exact hpoint.trans hkraft
  have hr : 0 < biasBase := by norm_num [biasBase]
  have hdiv : ∑ w ∈ C, dyadicWeight w ≤ 1 / biasBase := by
    apply (le_div_iff₀ hr).2
    simpa [mul_comm] using htotal
  simpa [biasBase] using hdiv

/-- First-passage prefix-freeness supplies the hypotheses of the uniform
outward bound automatically. -/
theorem finite_firstPassage_dyadicMass_le
    (C : Finset (List Bool))
    (hfirst : ∀ w ∈ C, FirstPassage w) :
    ∑ w ∈ C, dyadicWeight w ≤ (17 : ℝ) / 20 := by
  apply finite_outward_dyadicMass_le C
  · intro u hu v hv huv
    exact OutwardFirstPassage.prefixFree (hfirst u hu) (hfirst v hv) huv
  · intro w hw
    exact (hfirst w hw).1

theorem finite_firstPassage_dyadicMass_lt_one
    (C : Finset (List Bool))
    (hfirst : ∀ w ∈ C, FirstPassage w) :
    ∑ w ∈ C, dyadicWeight w < 1 := by
  exact (finite_firstPassage_dyadicMass_le C hfirst).trans_lt (by norm_num)

/-- Dyadic mass function supported on the complete set of first-passage
words. -/
noncomputable def firstPassageWeight (w : List Bool) : ℝ :=
  by
    classical
    exact if FirstPassage w then dyadicWeight w else 0

theorem firstPassageWeight_nonneg (w : List Bool) :
    0 ≤ firstPassageWeight w := by
  classical
  simp only [firstPassageWeight]
  split_ifs
  · exact pow_nonneg (by norm_num) _
  · exact le_rfl

theorem finite_firstPassageWeight_sum_le (U : Finset (List Bool)) :
    ∑ w ∈ U, firstPassageWeight w ≤ (17 : ℝ) / 20 := by
  classical
  let C := U.filter FirstPassage
  have hfirst : ∀ w ∈ C, FirstPassage w := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hbound := finite_firstPassage_dyadicMass_le C hfirst
  simpa [C, firstPassageWeight, Finset.sum_filter] using hbound

/-- The complete countable first-passage code is summable. -/
theorem summable_firstPassageWeight : Summable firstPassageWeight := by
  apply summable_of_sum_le firstPassageWeight_nonneg
  exact finite_firstPassageWeight_sum_le

/-- Uniform strict defect for the full countable first-passage code. -/
theorem tsum_firstPassageWeight_le :
    ∑' w : List Bool, firstPassageWeight w ≤ (17 : ℝ) / 20 := by
  exact summable_firstPassageWeight.tsum_le_of_sum_le
    finite_firstPassageWeight_sum_le

theorem tsum_firstPassageWeight_lt_one :
    ∑' w : List Bool, firstPassageWeight w < 1 := by
  exact tsum_firstPassageWeight_le.trans_lt (by norm_num)

/-! ## Finite-depth survivor counts -/

open OutwardFiniteStateKraftGap.FirstPassageGrammar

/-- Boolean words of length at most `L`. -/
def boolWordsUpTo (L : ℕ) : Finset (List Bool) :=
  (Finset.range (L + 1)).biUnion binaryWords

theorem mem_boolWordsUpTo_iff {L : ℕ} {w : List Bool} :
    w ∈ boolWordsUpTo L ↔ w.length ≤ L := by
  constructor
  · intro hw
    rcases Finset.mem_biUnion.mp hw with ⟨n, hn, hwn⟩
    have hnlt : n < L + 1 := Finset.mem_range.mp hn
    have hlen : w.length = n := mem_binaryWords_iff.mp hwn
    omega
  · intro hw
    apply Finset.mem_biUnion.mpr
    exact ⟨w.length, Finset.mem_range.mpr (by omega),
      mem_binaryWords_iff.mpr rfl⟩

/-- All first-passage words visible by depth `L`. -/
noncomputable def firstPassageWordsUpTo (L : ℕ) : Finset (List Bool) := by
  classical
  exact (boolWordsUpTo L).filter FirstPassage

theorem mem_firstPassageWordsUpTo_iff {L : ℕ} {w : List Bool} :
    w ∈ firstPassageWordsUpTo L ↔ FirstPassage w ∧ w.length ≤ L := by
  classical
  rw [firstPassageWordsUpTo, Finset.mem_filter, mem_boolWordsUpTo_iff]
  tauto

/-- Length-`L` cylinders caught by a finite prefix family. -/
def coveredAtDepth (C : Finset (List Bool)) (L : ℕ) :
    Finset (List Bool) :=
  C.biUnion fun w => extensions w (L - w.length)

theorem coveredAtDepth_subset_binaryWords
    (C : Finset (List Bool)) (L : ℕ)
    (hlen : ∀ w ∈ C, w.length ≤ L) :
    coveredAtDepth C L ⊆ binaryWords L := by
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨w, hw, hzw⟩
  rcases Finset.mem_image.mp hzw with ⟨tail, htail, rfl⟩
  have htailLen : tail.length = L - w.length :=
    mem_binaryWords_iff.mp htail
  have hwlen := hlen w hw
  apply mem_binaryWords_iff.mpr
  simp only [List.length_append, htailLen]
  omega

/-- Quantitative finite-depth form of the strict Kraft gap. -/
theorem coveredAtDepth_card_bound
    (C : Finset (List Bool)) (L : ℕ)
    (hlen : ∀ w ∈ C, w.length ≤ L)
    (hpf : PrefixFree (C : Set (List Bool)))
    (hout : ∀ w ∈ C, WordOutward w) :
    20 * (coveredAtDepth C L).card ≤ 17 * 2 ^ L := by
  have hmass := finite_outward_dyadicMass_le C hpf hout
  have hscaled : ∀ w ∈ C,
      dyadicWeight w = (2 ^ (L - w.length) : ℝ) / 2 ^ L := by
    intro w hw
    have hq := dyadicWeight_eq_scaled w L (hlen w hw)
    have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
    norm_num at hr
    simpa [dyadicWeight, one_div] using hr
  have hmass' :
      (∑ w ∈ C, (2 ^ (L - w.length) : ℝ)) / 2 ^ L ≤
        (17 : ℝ) / 20 := by
    rw [Finset.sum_div]
    calc
      (∑ w ∈ C, (2 ^ (L - w.length) : ℝ) / 2 ^ L) =
          ∑ w ∈ C, dyadicWeight w := by
            apply Finset.sum_congr rfl
            intro w hw
            exact (hscaled w hw).symm
      _ ≤ (17 : ℝ) / 20 := hmass
  have hden : (0 : ℝ) < 2 ^ L := by positivity
  have hcross := (div_le_iff₀ hden).mp hmass'
  have hsumR :
      (20 : ℝ) * (∑ w ∈ C, (2 ^ (L - w.length) : ℝ)) ≤
        17 * 2 ^ L := by
    nlinarith
  have hsumN :
      20 * (∑ w ∈ C, 2 ^ (L - w.length)) ≤ 17 * 2 ^ L := by
    exact_mod_cast hsumR
  have hcard :
      (coveredAtDepth C L).card ≤ ∑ w ∈ C, 2 ^ (L - w.length) := by
    calc
      (coveredAtDepth C L).card ≤
          ∑ w ∈ C, (extensions w (L - w.length)).card :=
        Finset.card_biUnion_le
      _ = ∑ w ∈ C, 2 ^ (L - w.length) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [card_extensions]
  omega

/-- At every depth, at least a `3/20` fraction of Boolean words avoid all
outward first-passage cylinders visible by that depth. -/
theorem firstPassage_uncovered_card_lower_bound (L : ℕ) :
    3 * 2 ^ L ≤ 20 *
      (binaryWords L \ coveredAtDepth (firstPassageWordsUpTo L) L).card := by
  let C := firstPassageWordsUpTo L
  have hlen : ∀ w ∈ C, w.length ≤ L := by
    intro w hw
    exact (mem_firstPassageWordsUpTo_iff.mp hw).2
  have hpf : PrefixFree (C : Set (List Bool)) := by
    intro u hu v hv huv
    exact OutwardFirstPassage.prefixFree
      (mem_firstPassageWordsUpTo_iff.mp hu).1
      (mem_firstPassageWordsUpTo_iff.mp hv).1 huv
  have hout : ∀ w ∈ C, WordOutward w := by
    intro w hw
    exact (mem_firstPassageWordsUpTo_iff.mp hw).1.1
  have hcovered := coveredAtDepth_card_bound C L hlen hpf hout
  have hsubset := coveredAtDepth_subset_binaryWords C L hlen
  rw [Finset.card_sdiff_of_subset hsubset, card_binaryWords]
  have hcard := Finset.card_le_card hsubset
  rw [card_binaryWords] at hcard
  omega

/-- Membership in the uncovered family has the intended prefix semantics:
no prefix has yet become outward. -/
theorem no_outward_prefix_of_mem_uncovered
    {L : ℕ} {z : List Bool}
    (hz : z ∈ binaryWords L \
      coveredAtDepth (firstPassageWordsUpTo L) L) :
    ∀ u, u <+: z → ¬ WordOutward u := by
  intro u huz huout
  have hzlen : z.length = L := mem_binaryWords_iff.mp
    (Finset.mem_sdiff.mp hz).1
  obtain ⟨v, hvu, hvfirst⟩ := exists_firstPassage_prefix u huout
  have hvz : v <+: z := hvu.trans huz
  have hvlen : v.length ≤ L := hvz.length_le.trans_eq hzlen
  have hvC : v ∈ firstPassageWordsUpTo L :=
    mem_firstPassageWordsUpTo_iff.mpr ⟨hvfirst, hvlen⟩
  rcases hvz with ⟨tail, htail⟩
  have htailLen : tail.length = L - v.length := by
    have hlength := congrArg List.length htail
    simp only [List.length_append] at hlength
    omega
  have htailMem : tail ∈ binaryWords (L - v.length) :=
    mem_binaryWords_iff.mpr htailLen
  have hzCovered : z ∈ coveredAtDepth (firstPassageWordsUpTo L) L := by
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hvC, Finset.mem_image.mpr ⟨tail, htailMem, ?_⟩⟩
    exact htail
  exact (Finset.mem_sdiff.mp hz).2 hzCovered

/-! ## Consequences for finite first-passage grammars -/

open OutwardFiniteStateKraftGap

variable {State Edge : Type*}
variable [Fintype State] [Nonempty State] [DecidableEq State]
variable [Fintype Edge] [DecidableEq Edge]

/-- Every state of every finite first-passage grammar has the same universal
rational Kraft defect.  No transfer supersolution is needed. -/
theorem FirstPassageGrammar.outMass_le_seventeen_div_twenty
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i ≤ (17 : ℚ) / 20 := by
  rw [G.outMass_eq_sum_outgoingWords i]
  have hfirst : ∀ w ∈ G.outgoingWords i, FirstPassage w := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨e, _, rfl⟩
    exact G.firstPassage e
  have h := finite_firstPassage_dyadicMass_le (G.outgoingWords i) hfirst
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  norm_num
  simpa [dyadicWeight] using h

/- Compatibility corollaries retaining the earlier weaker public constants. -/
theorem FirstPassageGrammar.outMass_le_twenty_five_div_twenty_six
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i ≤ (25 : ℚ) / 26 := by
  exact (FirstPassageGrammar.outMass_le_seventeen_div_twenty G i).trans
    (by norm_num)

theorem FirstPassageGrammar.outMass_le_hundred_div_one_hundred_one
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i ≤ (100 : ℚ) / 101 := by
  exact (FirstPassageGrammar.outMass_le_seventeen_div_twenty G i).trans
    (by norm_num)

theorem FirstPassageGrammar.outMass_lt_one_uniform
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i < 1 := by
  exact (FirstPassageGrammar.outMass_le_seventeen_div_twenty G i).trans_lt
    (by norm_num)

/-- Consequently every state misses a concrete fixed-depth binary cylinder,
without any Perron or finite-state contraction certificate. -/
theorem FirstPassageGrammar.exists_uncovered_word_uniform
    (G : FirstPassageGrammar State Edge) (i : State) :
    ∃ z,
      z.length = (G.outgoingWords i).sup List.length ∧
      ∀ w ∈ G.outgoingWords i, ¬w <+: z := by
  exact G.exists_uncovered_word_of_outMass_lt_one i
    (FirstPassageGrammar.outMass_lt_one_uniform G i)

end OutwardStrictKraftGap
end KontoroC

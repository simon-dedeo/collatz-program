/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardInvariantBridge

/-!
# Coarse dyadic holes inside every ternary parameter cylinder

This file isolates the topology/CRT conclusion of QM170 from its
writer--decoder arithmetic premise.  If all legal parameters lie in fewer
than `2^d` residue classes modulo `2^d`, then every ternary cylinder contains
arbitrarily large illegal parameters.  No bounded computation is used.

The writer-specific assertion that its full unbounded target alphabet is
covered by at most fifty classes modulo `2^54` remains a separate premise.
-/

namespace KontoroC
namespace OutwardCoarseHole

/-! ## The one-class mechanism -/

/-- An affine gate whose parameter coefficient is `2` times an odd number
has at most one solution class modulo `2^d` when tested modulo `2^(d+1)`.
This is the abstract uniqueness step behind each row of the coarse cover. -/
theorem twoAdic_linear_gate_right_unique
    {d constant coefficient n n' : ℕ}
    (hodd : Odd coefficient)
    (hn : constant + 2 * coefficient * n ≡ 0 [MOD 2 ^ (d + 1)])
    (hn' : constant + 2 * coefficient * n' ≡ 0 [MOD 2 ^ (d + 1)]) :
    n ≡ n' [MOD 2 ^ d] := by
  have hboth :
      constant + 2 * coefficient * n ≡
        constant + 2 * coefficient * n' [MOD 2 ^ (d + 1)] :=
    hn.trans hn'.symm
  have hmul :
      2 * (coefficient * n) ≡ 2 * (coefficient * n')
        [MOD 2 * 2 ^ d] := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      Nat.ModEq.add_left_cancel' constant hboth
  have hcoefficient :
      coefficient * n ≡ coefficient * n' [MOD 2 ^ d] :=
    Nat.ModEq.mul_left_cancel' (by norm_num) hmul
  have hcop : Nat.Coprime (2 ^ d) coefficient :=
    (hodd.coprime_two_left).pow_left d
  exact hcoefficient.cancel_left_of_coprime hcop.gcd_eq_one

/-- Once the writer counter is at least `51`, every correction term carrying
the factor `2^(p+4)` disappears at coarse precision `2^55`. -/
theorem large_writer_correction_mod_twoPow
    (p q : ℕ) (hp : 51 ≤ p) :
    7 + 2 ^ (p + 4) * q ≡ 7 [MOD 2 ^ 55] := by
  have hpow : 2 ^ 55 ∣ 2 ^ (p + 4) :=
    Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.ModEq]
  rw [Nat.add_mod]
  rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpow q)]
  simp

/-- The forty-nine individual writer counters `p=2,...,50`, together with
one common tail class for `p≥51`, produce at most fifty coarse classes. -/
noncomputable def fiftyClassCover
    (row : Fin 49 → ℕ) (tail : ℕ) : Finset ℕ :=
  insert tail (Finset.univ.image row)

theorem fiftyClassCover_card_le
    (row : Fin 49 → ℕ) (tail : ℕ) :
    (fiftyClassCover row tail).card ≤ 50 := by
  classical
  unfold fiftyClassCover
  calc
    (insert tail (Finset.univ.image row)).card ≤
        (Finset.univ.image row).card + 1 := Finset.card_insert_le _ _
    _ ≤ Finset.univ.card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = 50 := by simp

/-- A semantic classifier into the forty-nine small-counter rows or the one
large-counter tail supplies the exact finite-cover premise. -/
theorem mem_fiftyClassCover_of_classified
    (Legal : ℕ → Prop) (row : Fin 49 → ℕ) (tail n : ℕ)
    (hclassify : ∀ x, Legal x →
      (∃ i, x % 2 ^ 54 = row i) ∨ x % 2 ^ 54 = tail)
    (hn : Legal n) :
    n % 2 ^ 54 ∈ fiftyClassCover row tail := by
  classical
  rcases hclassify n hn with ⟨i, hi⟩ | htail
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  · exact Finset.mem_insert.mpr (Or.inl htail)

/-! ## A writer--decoder affine gate model -/

/-- The coarse divisibility condition seen by a fixed target writer counter.
`A` and `stride` are odd in the writer--decoder application. -/
def AffineCoarseGate
    (A q stride correction n : ℕ) : Prop :=
  A * (q + 2 * stride * n) + correction ≡ 0 [MOD 2 ^ 55]

theorem AffineCoarseGate.right_unique
    {A q stride correction n n' : ℕ}
    (hA : Odd A) (hstride : Odd stride)
    (hn : AffineCoarseGate A q stride correction n)
    (hn' : AffineCoarseGate A q stride correction n') :
    n ≡ n' [MOD 2 ^ 54] := by
  have hn0 :
      A * q + correction + 2 * (A * stride) * n ≡ 0
        [MOD 2 ^ (54 + 1)] := by
    change A * (q + 2 * stride * n) + correction ≡ 0
      [MOD 2 ^ 55] at hn
    rw [show 54 + 1 = 55 by omega]
    convert hn using 1
    ring
  have hn0' :
      A * q + correction + 2 * (A * stride) * n' ≡ 0
        [MOD 2 ^ (54 + 1)] := by
    change A * (q + 2 * stride * n') + correction ≡ 0
      [MOD 2 ^ 55] at hn'
    rw [show 54 + 1 = 55 by omega]
    convert hn' using 1
    ring
  exact twoAdic_linear_gate_right_unique (hA.mul hstride) hn0 hn0'

/-- A canonical residue for a gate, chosen only when a solution exists. -/
noncomputable def affineCoarseGateRepresentative
    (A q stride correction : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, AffineCoarseGate A q stride correction n then
    Classical.choose h
  else
    0

theorem AffineCoarseGate.modEq_representative
    {A q stride correction n : ℕ}
    (hA : Odd A) (hstride : Odd stride)
    (hn : AffineCoarseGate A q stride correction n) :
    n ≡ affineCoarseGateRepresentative A q stride correction
      [MOD 2 ^ 54] := by
  classical
  unfold affineCoarseGateRepresentative
  split_ifs with hex
  · exact hn.right_unique hA hstride (Classical.choose_spec hex)
  · exact (hex ⟨n, hn⟩).elim

/-- The necessary coarse legality relation: small target counters use their
individual decoder correction, while all counters `p≥51` use the common
writer correction `7`. -/
def CoarseWriterDecoderLegal
    (A q stride : ℕ) (correction : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ p, 2 ≤ p ∧
    if p < 51 then
      AffineCoarseGate A q stride (correction p) n
    else
      AffineCoarseGate A q stride 7 n

noncomputable def smallCounterRow
    (A q stride : ℕ) (correction : ℕ → ℕ) (i : Fin 49) : ℕ :=
  affineCoarseGateRepresentative A q stride (correction (i + 2)) % 2 ^ 54

noncomputable def largeCounterTail
    (A q stride : ℕ) : ℕ :=
  affineCoarseGateRepresentative A q stride 7 % 2 ^ 54

/-- The full unbounded counter alphabet of the coarse gate is classified by
the promised forty-nine individual rows and one common tail row. -/
theorem coarseWriterDecoderLegal_classified
    {A q stride : ℕ} {correction : ℕ → ℕ}
    (hA : Odd A) (hstride : Odd stride)
    {n : ℕ} (hn : CoarseWriterDecoderLegal A q stride correction n) :
    (∃ i, n % 2 ^ 54 = smallCounterRow A q stride correction i) ∨
      n % 2 ^ 54 = largeCounterTail A q stride := by
  rcases hn with ⟨p, hp, hgate⟩
  by_cases hsmall : p < 51
  · simp only [hsmall, if_true] at hgate
    let i : Fin 49 := ⟨p - 2, by omega⟩
    have hip : (i : ℕ) + 2 = p := by
      dsimp [i]
      omega
    left
    refine ⟨i, ?_⟩
    have hmod := hgate.modEq_representative hA hstride
    rw [Nat.ModEq] at hmod
    simpa [smallCounterRow, hip] using hmod
  · simp only [hsmall, if_false] at hgate
    right
    have hmod := hgate.modEq_representative hA hstride
    rw [Nat.ModEq] at hmod
    simpa [largeCounterTail] using hmod

/-- A finite set with fewer than `M` elements misses a canonical residue in
`[0,M)`. -/
theorem exists_residue_not_mem {M : ℕ} (cover : Finset ℕ)
    (hcard : cover.card < M) :
    ∃ r, r < M ∧ r ∉ cover := by
  by_contra hnone
  push Not at hnone
  have hsubset : Finset.range M ⊆ cover := by
    intro r hr
    exact hnone r (Finset.mem_range.mp hr)
  have hle := Finset.card_le_card hsubset
  simp only [Finset.card_range] at hle
  omega

/-- CRT plus an arbitrary positive product lift: every ternary class meets
every dyadic class above every prescribed height. -/
theorem exists_large_in_ternary_and_dyadic_classes
    (k d a r B : ℕ) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      n ≡ r [MOD 2 ^ d] := by
  have hcop : Nat.Coprime (3 ^ k) (2 ^ d) :=
    Nat.Coprime.pow_right d <|
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 2)
  let cr := Nat.chineseRemainder hcop a r
  let c : ℕ := cr
  let modulus := 3 ^ k * 2 ^ d
  let n := c + modulus * (B + 1)
  have hmodulus : 0 < modulus := by
    dsimp [modulus]
    positivity
  have hnlarge : B < n := by
    dsimp [n]
    have hone : 1 ≤ modulus := hmodulus
    nlinarith
  have hnbase : n ≡ c [MOD modulus] := by
    dsimp [n]
    simp
  refine ⟨n, hnlarge, ?_, ?_⟩
  · exact (hnbase.of_mul_right (2 ^ d)).trans cr.property.1
  · exact (hnbase.of_mul_left (3 ^ k)).trans cr.property.2

/-- Main coarse-hole theorem: fewer than all dyadic residue classes leave an
arbitrarily large hole inside every ternary cylinder. -/
theorem exists_large_outside_dyadic_cover
    (cover : Finset ℕ) (d k a B : ℕ)
    (hcard : cover.card < 2 ^ d) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      n % 2 ^ d ∉ cover := by
  obtain ⟨r, hrlt, hrnot⟩ := exists_residue_not_mem cover hcard
  obtain ⟨n, hnB, hn3, hn2⟩ :=
    exists_large_in_ternary_and_dyadic_classes k d a r B
  refine ⟨n, hnB, hn3, ?_⟩
  have hrmod : r % 2 ^ d = r := Nat.mod_eq_of_lt hrlt
  have hnrem : n % 2 ^ d = r := by
    rw [Nat.ModEq] at hn2
    exact hn2.trans hrmod
  simpa [hnrem] using hrnot

/-- Direct open-tail form: a ternary affine progression cannot stay inside a
proper finite collection of dyadic classes.  The witness has a strictly
positive ordinary parameter, not merely a `3`-adic address. -/
theorem exists_positive_parameter_outside_dyadic_cover
    (cover : Finset ℕ) (d k u₀ : ℕ)
    (hcard : cover.card < 2 ^ d) :
    ∃ m, 0 < m ∧
      (u₀ + 3 ^ k * m) % 2 ^ d ∉ cover := by
  obtain ⟨n, hnu₀, hn3, hncover⟩ :=
    exists_large_outside_dyadic_cover cover d k u₀ u₀ hcard
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
  exact ⟨m, hmpos, by simpa [← hn] using hncover⟩

/-- A legality predicate supported on a proper finite dyadic cover cannot
contain even one complete ternary cylinder. -/
theorem exists_large_illegal_in_every_ternary_cylinder
    (Legal : ℕ → Prop) (cover : Finset ℕ) (d k a B : ℕ)
    (hcard : cover.card < 2 ^ d)
    (hnecessary : ∀ n, Legal n → n % 2 ^ d ∈ cover) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ¬ Legal n := by
  obtain ⟨n, hnB, hn3, hncover⟩ :=
    exists_large_outside_dyadic_cover cover d k a B hcard
  exact ⟨n, hnB, hn3, fun hnLegal => hncover (hnecessary n hnLegal)⟩

/-- The numerical specialization used by the writer--decoder proposal. -/
theorem fifty_lt_two_pow_fiftyFour : 50 < 2 ^ 54 := by
  norm_num

/-- QM170f's topological consequence, conditional only on the advertised
fifty-class necessary cover. -/
theorem exists_large_illegal_of_fifty_class_cover
    (Legal : ℕ → Prop) (cover : Finset ℕ) (k a B : ℕ)
    (hcard : cover.card ≤ 50)
    (hnecessary : ∀ n, Legal n → n % 2 ^ 54 ∈ cover) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ¬ Legal n := by
  apply exists_large_illegal_in_every_ternary_cylinder
    Legal cover 54 k a B
  · exact hcard.trans_lt fifty_lt_two_pow_fiftyFour
  · exact hnecessary

/-- QM170f in its forty-nine-rows-plus-tail interface.  Once the
writer-specific classification is proved, the arbitrarily large hole follows
without any further arithmetic assumptions. -/
theorem exists_large_illegal_of_fifty_class_classification
    (Legal : ℕ → Prop) (row : Fin 49 → ℕ) (tail k a B : ℕ)
    (hclassify : ∀ n, Legal n →
      (∃ i, n % 2 ^ 54 = row i) ∨ n % 2 ^ 54 = tail) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ¬ Legal n := by
  apply exists_large_illegal_of_fifty_class_cover
    Legal (fiftyClassCover row tail) k a B
  · exact fiftyClassCover_card_le row tail
  · intro n hn
    exact mem_fiftyClassCover_of_classified Legal row tail n hclassify hn

/-- The precise open-tail corollary used after a finite prescribed edge
prefix: the remaining `3^k`-scaled ordinary parameter can be chosen positive
so that the next writer--decoder cell is illegal. -/
theorem exists_positive_open_tail_failure_of_fifty_class_cover
    (Legal : ℕ → Prop) (cover : Finset ℕ) (k u₀ : ℕ)
    (hcard : cover.card ≤ 50)
    (hnecessary : ∀ n, Legal n → n % 2 ^ 54 ∈ cover) :
    ∃ m, 0 < m ∧ ¬Legal (u₀ + 3 ^ k * m) := by
  obtain ⟨m, hmpos, hmcover⟩ :=
    exists_positive_parameter_outside_dyadic_cover
      cover 54 k u₀ (hcard.trans_lt fifty_lt_two_pow_fiftyFour)
  exact ⟨m, hmpos, fun hmLegal =>
    hmcover (hnecessary _ hmLegal)⟩

/-- Unconditional coarse-gate obstruction: for odd chart coefficients, no
ternary cylinder can consist entirely of parameters satisfying some target
counter gate, even though the target counter is allowed to be unbounded. -/
theorem exists_large_not_coarseWriterDecoderLegal
    (A q stride : ℕ) (correction : ℕ → ℕ)
    (hA : Odd A) (hstride : Odd stride)
    (k a B : ℕ) :
    ∃ n,
      B < n ∧
      n ≡ a [MOD 3 ^ k] ∧
      ¬ CoarseWriterDecoderLegal A q stride correction n := by
  apply exists_large_illegal_of_fifty_class_classification
    (CoarseWriterDecoderLegal A q stride correction)
    (smallCounterRow A q stride correction)
    (largeCounterTail A q stride) k a B
  intro n hn
  exact coarseWriterDecoderLegal_classified hA hstride hn

/-- Directly in the worker's open-tail parameterization. -/
theorem exists_positive_open_tail_not_coarseWriterDecoderLegal
    (A q stride : ℕ) (correction : ℕ → ℕ)
    (hA : Odd A) (hstride : Odd stride)
    (k u₀ : ℕ) :
    ∃ m, 0 < m ∧
      ¬ CoarseWriterDecoderLegal A q stride correction
        (u₀ + 3 ^ k * m) := by
  let row := smallCounterRow A q stride correction
  let tail := largeCounterTail A q stride
  let cover := fiftyClassCover row tail
  apply exists_positive_open_tail_failure_of_fifty_class_cover
    (CoarseWriterDecoderLegal A q stride correction) cover k u₀
  · dsimp [cover]
    exact fiftyClassCover_card_le row tail
  · intro n hn
    apply mem_fiftyClassCover_of_classified
      (CoarseWriterDecoderLegal A q stride correction) row tail n
    · intro x hx
      exact coarseWriterDecoderLegal_classified hA hstride hx
    · exact hn

/-- Contradiction form: no single ternary cylinder, and therefore no
nonempty finite union built from such cylinders, can force legality. -/
theorem no_ternary_cylinder_forces_legal_of_fifty_class_cover
    (Legal : ℕ → Prop) (cover : Finset ℕ) (k a : ℕ)
    (hcard : cover.card ≤ 50)
    (hnecessary : ∀ n, Legal n → n % 2 ^ 54 ∈ cover) :
    ¬ ∀ n, n ≡ a [MOD 3 ^ k] → Legal n := by
  intro hforces
  obtain ⟨n, _, hn3, hnillegal⟩ :=
    exists_large_illegal_of_fifty_class_cover
      Legal cover k a 0 hcard hnecessary
  exact hnillegal (hforces n hn3)

end OutwardCoarseHole
end KontoroC

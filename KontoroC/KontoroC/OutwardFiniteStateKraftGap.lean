/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFirstPassage

/-!
# A finite-state Kraft gap for first-passage macro grammars

This module isolates a certificate-friendly version of the finite transition
matrix idea. Every edge carries a first-passage Boolean word, hence a dyadic
weight `2^(-word.length)`. If a positive rational vector is a strict
subeigenvector for the resulting transfer operator, then at least one state's
outgoing prefix code has Kraft mass strictly below one.

The theorem is an architecture filter. It does not assert that an arbitrary
recursive first-passage invariant has finitely many states, and it does not
construct a Collatz counterexample.
-/

namespace KontoroC
namespace OutwardFiniteStateKraftGap

open scoped BigOperators
open PrefixKraft OutwardFirstPassage

/-- A finite first-passage macro grammar. Two distinct edges from the same
state may not carry the same word; edges from different states may. -/
structure FirstPassageGrammar (State Edge : Type*)
    [Fintype State] [Fintype Edge] where
  source : Edge → State
  target : Edge → State
  word : Edge → List Bool
  firstPassage : ∀ e, FirstPassage (word e)
  word_injective_on_source :
    ∀ {e f}, source e = source f → word e = word f → e = f

variable {State Edge : Type*}
variable [Fintype State] [Nonempty State] [DecidableEq State]
variable [Fintype Edge] [DecidableEq Edge]

namespace FirstPassageGrammar

/-! ## Finite dyadic covering lemma -/

/-- All Boolean words of one fixed length. -/
def binaryWords (n : ℕ) : Finset (List Bool) :=
  Finset.univ.image (fun f : Fin n → Bool => List.ofFn f)

theorem mem_binaryWords_iff {n : ℕ} {w : List Bool} :
    w ∈ binaryWords n ↔ w.length = n := by
  constructor
  · intro hw
    rcases Finset.mem_image.mp hw with ⟨f, _, rfl⟩
    simp
  · intro hw
    subst n
    apply Finset.mem_image.mpr
    refine ⟨fun i : Fin w.length => w.get i, Finset.mem_univ _, ?_⟩
    exact List.ofFn_get w

theorem card_binaryWords (n : ℕ) : (binaryWords n).card = 2 ^ n := by
  classical
  rw [binaryWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- Length-`w.length+n` words extending `w`. -/
def extensions (w : List Bool) (n : ℕ) : Finset (List Bool) :=
  (binaryWords n).image fun tail => w ++ tail

theorem card_extensions (w : List Bool) (n : ℕ) :
    (extensions w n).card = 2 ^ n := by
  classical
  rw [extensions, Finset.card_image_of_injective _
    (List.append_right_injective w), card_binaryWords]

/-- Every fixed-length word is caught by a prefix from `C`. -/
def CoversAtDepth (C : Finset (List Bool)) (L : ℕ) : Prop :=
  ∀ z, z.length = L → ∃ w ∈ C, w <+: z

theorem binaryWords_subset_extensions_biUnion
    (C : Finset (List Bool)) (L : ℕ)
    (hcover : CoversAtDepth C L) :
    binaryWords L ⊆
      C.biUnion fun w => extensions w (L - w.length) := by
  intro z hz
  have hzlen : z.length = L := mem_binaryWords_iff.mp hz
  obtain ⟨w, hw, hwz⟩ := hcover z hzlen
  have hwlen : w.length ≤ L := hwz.length_le.trans_eq hzlen
  rcases hwz with ⟨tail, htail⟩
  have htaillen : tail.length = L - w.length := by
    have hlength := congrArg List.length htail
    simp only [List.length_append] at hlength
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨w, hw, Finset.mem_image.mpr ⟨tail, ?_, ?_⟩⟩
  · exact mem_binaryWords_iff.mpr htaillen
  · exact htail

/-- A finite fixed-depth prefix cover has cleared Kraft mass at least the
full binary level. -/
theorem twoPow_le_sum_twoPow_sub_length_of_coversAtDepth
    (C : Finset (List Bool)) (L : ℕ)
    (hcover : CoversAtDepth C L) :
    2 ^ L ≤ ∑ w ∈ C, 2 ^ (L - w.length) := by
  calc
    2 ^ L = (binaryWords L).card := (card_binaryWords L).symm
    _ ≤ (C.biUnion fun w => extensions w (L - w.length)).card :=
      Finset.card_le_card (binaryWords_subset_extensions_biUnion C L hcover)
    _ ≤ ∑ w ∈ C, (extensions w (L - w.length)).card :=
      Finset.card_biUnion_le
    _ = ∑ w ∈ C, 2 ^ (L - w.length) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [card_extensions]

theorem dyadicWeight_eq_scaled (w : List Bool) (L : ℕ)
    (hlen : w.length ≤ L) :
    (1 / 2 : ℚ) ^ w.length =
      (2 ^ (L - w.length) : ℚ) / 2 ^ L := by
  rw [show L = (L - w.length) + w.length by omega, pow_add]
  rw [div_pow]
  norm_num
  field_simp

/-- For a finite prefix family, fixed-depth coverage forces Kraft mass at
least one.  Prefix-freeness is not needed for this direction. -/
theorem one_le_dyadicMass_of_coversAtDepth
    (C : Finset (List Bool)) (L : ℕ)
    (hlen : ∀ w ∈ C, w.length ≤ L)
    (hcover : CoversAtDepth C L) :
    1 ≤ ∑ w ∈ C, (1 / 2 : ℚ) ^ w.length := by
  have hcount :=
    twoPow_le_sum_twoPow_sub_length_of_coversAtDepth C L hcover
  have hcountQ :
      (2 ^ L : ℚ) ≤ ∑ w ∈ C, (2 ^ (L - w.length) : ℚ) := by
    exact_mod_cast hcount
  calc
    1 ≤ (∑ w ∈ C, (2 ^ (L - w.length) : ℚ)) / 2 ^ L := by
      apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ L)).2
      simpa using hcountQ
    _ = ∑ w ∈ C, (1 / 2 : ℚ) ^ w.length := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w hw
      exact (dyadicWeight_eq_scaled w L (hlen w hw)).symm

/-- The exact dyadic cylinder mass of one edge. -/
noncomputable def edgeWeight
    (G : FirstPassageGrammar State Edge) (e : Edge) : ℚ :=
  (1 / 2 : ℚ) ^ (G.word e).length

/-- Edges leaving a specified state. -/
def outgoing (G : FirstPassageGrammar State Edge) (i : State) : Finset Edge :=
  Finset.univ.filter fun e => G.source e = i

/-- Kraft mass of all edge words leaving one state. -/
noncomputable def outMass
    (G : FirstPassageGrammar State Edge) (i : State) : ℚ :=
  ∑ e ∈ G.outgoing i, G.edgeWeight e

/-- The rational weighted transfer operator associated to the grammar. -/
noncomputable def transfer
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (i : State) : ℚ :=
  ∑ e ∈ G.outgoing i, G.edgeWeight e * v (G.target e)

/-- The exact finite weighted adjacency matrix.  This is the object whose
Perron supersolutions can be exported as rational certificates. -/
noncomputable def adjacency
    (G : FirstPassageGrammar State Edge) : Matrix State State ℚ :=
  fun i j => ∑ e ∈ G.outgoing i with G.target e = j, G.edgeWeight e

theorem transfer_eq_adjacency_mulVec
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (i : State) :
    G.transfer v i = G.adjacency.mulVec v i := by
  classical
  simp only [transfer, adjacency, Matrix.mulVec, dotProduct]
  symm
  calc
    (∑ j, (∑ e ∈ G.outgoing i with G.target e = j,
        G.edgeWeight e) * v j) =
        ∑ j, ∑ e ∈ G.outgoing i with G.target e = j,
          G.edgeWeight e * v j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ j, ∑ e ∈ G.outgoing i with G.target e = j,
          G.edgeWeight e * v (G.target e) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro e he
            rw [(Finset.mem_filter.mp he).2]
    _ = ∑ e ∈ G.outgoing i, G.edgeWeight e * v (G.target e) :=
      Finset.sum_fiberwise (G.outgoing i) G.target
        (fun e => G.edgeWeight e * v (G.target e))

theorem edgeWeight_pos (G : FirstPassageGrammar State Edge) (e : Edge) :
    0 < G.edgeWeight e := by
  simp only [edgeWeight]
  positivity

theorem edgeWeight_nonneg (G : FirstPassageGrammar State Edge) (e : Edge) :
    0 ≤ G.edgeWeight e := (G.edgeWeight_pos e).le

/-- The words used at one state, with duplicate edge labels removed. -/
def outgoingWords
    (G : FirstPassageGrammar State Edge) (i : State) : Finset (List Bool) :=
  (G.outgoing i).image G.word

theorem word_injective_on_outgoing
    (G : FirstPassageGrammar State Edge) (i : State)
    {e f : Edge} (he : e ∈ G.outgoing i) (hf : f ∈ G.outgoing i)
    (heq : G.word e = G.word f) : e = f := by
  apply G.word_injective_on_source
  · have hes : G.source e = i := by simpa [outgoing] using he
    have hfs : G.source f = i := by simpa [outgoing] using hf
    exact hes.trans hfs.symm
  · exact heq

theorem outMass_eq_sum_outgoingWords
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i =
      ∑ w ∈ G.outgoingWords i, (1 / 2 : ℚ) ^ w.length := by
  classical
  rw [outMass, outgoingWords, Finset.sum_image]
  · rfl
  · intro e he f hf heq
    exact G.word_injective_on_outgoing i he hf heq

theorem outgoingWords_prefixFree
    (G : FirstPassageGrammar State Edge) (i : State) :
    PrefixFree (G.outgoingWords i : Set (List Bool)) := by
  intro u hu v hv huv
  rcases Finset.mem_image.mp hu with ⟨e, he, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨f, hf, rfl⟩
  exact OutwardFirstPassage.prefixFree (G.firstPassage e)
    (G.firstPassage f) huv

theorem nil_not_mem_outgoingWords
    (G : FirstPassageGrammar State Edge) (i : State) :
    [] ∉ (G.outgoingWords i : Set (List Bool)) := by
  intro hnil
  rcases Finset.mem_image.mp hnil with ⟨e, _, he⟩
  exact firstPassage_ne_nil (G.firstPassage e) he

/-- First-passage prefix-freeness makes every local outgoing mass at most
one. This is proved using mathlib's Kraft--McMillan theorem. -/
theorem outMass_le_one
    (G : FirstPassageGrammar State Edge) (i : State) :
    G.outMass i ≤ 1 := by
  rw [G.outMass_eq_sum_outgoingWords i]
  have hk := InformationTheory.kraft_mcmillan_inequality
    (PrefixKraft.uniquelyDecodable_of_prefixFree
      (G.outgoingWords_prefixFree i) (G.nil_not_mem_outgoingWords i))
  norm_num at hk
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  norm_num
  exact hk

/-- Strict local Kraft defect is witnessed by a finite dyadic cylinder: at
the maximum outgoing word length there is a Boolean word having no outgoing
edge word as a prefix. -/
theorem exists_uncovered_word_of_outMass_lt_one
    (G : FirstPassageGrammar State Edge) (i : State)
    (hmass : G.outMass i < 1) :
    ∃ z,
      z.length = (G.outgoingWords i).sup List.length ∧
      ∀ w ∈ G.outgoingWords i, ¬w <+: z := by
  classical
  let L := (G.outgoingWords i).sup List.length
  by_contra hnone
  push Not at hnone
  have hcover : CoversAtDepth (G.outgoingWords i) L := by
    intro z hz
    obtain ⟨w, hw, hpref⟩ := hnone z hz
    exact ⟨w, hw, hpref⟩
  have hlen : ∀ w ∈ G.outgoingWords i, w.length ≤ L := by
    intro w hw
    exact Finset.le_sup hw
  have hone := one_le_dyadicMass_of_coversAtDepth
    (G.outgoingWords i) L hlen hcover
  rw [← G.outMass_eq_sum_outgoingWords i] at hone
  exact (not_lt_of_ge hone) hmass

/-- Exact finite arithmetic certificate for a transfer contraction. -/
def HasRationalKraftGap
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (r : ℚ) : Prop :=
  (∀ i, 0 < v i) ∧ 0 ≤ r ∧ r < 1 ∧
    ∀ i, G.transfer v i ≤ r * v i

/-- A positive strict transfer supersolution forces a local Kraft defect.
The proof chooses a state of minimum certificate weight; no spectral-radius
library or floating-point eigenvalue is used. -/
theorem exists_state_outMass_lt_one_of_rationalKraftGap
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (r : ℚ)
    (hgap : G.HasRationalKraftGap v r) :
    ∃ i, G.outMass i < 1 := by
  classical
  rcases hgap with ⟨hvpos, _, hrlt, hsuper⟩
  let values : Finset ℚ := Finset.univ.image v
  have hvalues : values.Nonempty := by simp [values]
  let minimum : ℚ := values.min' hvalues
  have hminimumMem : minimum ∈ values := Finset.min'_mem values hvalues
  obtain ⟨i, _, hirank⟩ := Finset.mem_image.mp hminimumMem
  have hmin : ∀ j, v i ≤ v j := by
    intro j
    have hj : v j ∈ values := by simp [values]
    have hle := Finset.min'_le values (v j) hj
    simpa [hirank] using hle
  refine ⟨i, ?_⟩
  by_contra hnot
  have hmass : 1 ≤ G.outMass i := le_of_not_gt hnot
  have hweighted : v i * G.outMass i ≤ G.transfer v i := by
    simp only [outMass, transfer, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    calc
      v i * G.edgeWeight e = G.edgeWeight e * v i := by ring
      _ ≤ G.edgeWeight e * v (G.target e) :=
        mul_le_mul_of_nonneg_left (hmin (G.target e))
          (G.edgeWeight_nonneg e)
  have hself : v i ≤ v i * G.outMass i := by
    nlinarith [hvpos i]
  have hcontract : r * v i < v i := by
    nlinarith [hvpos i]
  exact (not_lt_of_ge (hself.trans (hweighted.trans (hsuper i)))) hcontract

/-- Full finite-depth architecture filter: a rational transfer gap produces
a state and an explicit-length dyadic subcylinder missed by every outgoing
first-passage macro. -/
theorem exists_state_and_uncovered_word_of_rationalKraftGap
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (r : ℚ)
    (hgap : G.HasRationalKraftGap v r) :
    ∃ i z,
      z.length = (G.outgoingWords i).sup List.length ∧
      ∀ w ∈ G.outgoingWords i, ¬w <+: z := by
  obtain ⟨i, hi⟩ :=
    G.exists_state_outMass_lt_one_of_rationalKraftGap v r hgap
  obtain ⟨z, hzlen, hz⟩ := G.exists_uncovered_word_of_outMass_lt_one i hi
  exact ⟨i, z, hzlen, hz⟩

/-- In particular a strict rational transfer gap is incompatible with Kraft
completeness at every state. -/
theorem no_every_state_outMass_eq_one_of_rationalKraftGap
    (G : FirstPassageGrammar State Edge) (v : State → ℚ) (r : ℚ)
    (hgap : G.HasRationalKraftGap v r) :
    ¬ ∀ i, G.outMass i = 1 := by
  intro hcomplete
  obtain ⟨i, hi⟩ :=
    G.exists_state_outMass_lt_one_of_rationalKraftGap v r hgap
  rw [hcomplete i] at hi
  exact (lt_irrefl 1) hi

end FirstPassageGrammar
end OutwardFiniteStateKraftGap
end KontoroC

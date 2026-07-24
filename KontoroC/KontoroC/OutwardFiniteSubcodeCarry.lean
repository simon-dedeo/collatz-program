/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteHeight
import KontoroC.OutwardCodeCounterexample
import Mathlib.Order.KonigLemma
import Mathlib.Data.Fin.Tuple.Take

/-!
# Carry compactness for finite first-passage subcodes

This file gives an exact arithmetic coordinate for extending a canonical
dyadic cylinder by one literal first-passage block.  It then packages the
finite-alphabet compactness criterion: one ordinary natural executes a
finite subcode forever exactly when finite schedules of every depth can be
found with one uniform bound on the sum of their extension carries.

No finite subcode or carry bound is constructed here.
-/

namespace KontoroC
namespace OutwardFiniteSubcodeCarry

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardCylinderRenewal OutwardFirstPassage

noncomputable section

/-- Total literal bit length of a block schedule. -/
def scheduleLength (u : List (List Bool)) : ℕ := (flattenWords u).length

/-- Canonical dyadic source residue of the flattened block schedule. -/
def scheduleResidue (u : List (List Bool)) : ℕ :=
  (canonicalExecution (flattenWords u)).1

/-- The unweighted natural carry introduced by extending `u` by `w`. -/
def extensionCarry (u : List (List Bool)) (w : List Bool) : ℕ :=
  scheduleResidue (u ++ [w]) / 2 ^ scheduleLength u

theorem flattenWords_append (u v : List (List Bool)) :
    flattenWords (u ++ v) = flattenWords u ++ flattenWords v := by
  induction u with
  | nil => rfl
  | cons w u ih => simp [flattenWords, ih, List.append_assoc]

theorem scheduleLength_append (u v : List (List Bool)) :
    scheduleLength (u ++ v) = scheduleLength u + scheduleLength v := by
  simp [scheduleLength, flattenWords_append]

theorem scheduleLength_append_singleton (u : List (List Bool)) (w : List Bool) :
    scheduleLength (u ++ [w]) = scheduleLength u + w.length := by
  rw [scheduleLength_append]
  simp [scheduleLength, flattenWords]

/-- The canonical source of an extended schedule reduces to the canonical
source of its prefix modulo the prefix cylinder modulus. -/
theorem scheduleResidue_append_mod (u v : List (List Bool)) :
    scheduleResidue (u ++ v) % 2 ^ scheduleLength u = scheduleResidue u := by
  let full := canonicalExecution (flattenWords (u ++ v))
  obtain ⟨middle, hprefix, _⟩ :=
    (executes_append (flattenWords u) (flattenWords v)).mp <| by
      simpa [flattenWords_append] using
        (canonicalExecution_spec (flattenWords (u ++ v))).2.2
  have hmod := executes_source_modEq (flattenWords u) hprefix
    (canonicalExecution_spec (flattenWords u)).2.2
  have hleft : scheduleResidue (u ++ v) % 2 ^ scheduleLength u =
      scheduleResidue u % 2 ^ scheduleLength u := by
    simpa only [scheduleResidue, scheduleLength, flattenWords_append,
      Nat.ModEq] using hmod
  rw [hleft, Nat.mod_eq_of_lt]
  simpa [scheduleResidue, scheduleLength] using
    (canonicalExecution_spec (flattenWords u)).1

/-- QM173a, exact extension identity. -/
theorem scheduleResidue_append_singleton (u : List (List Bool)) (w : List Bool) :
    scheduleResidue (u ++ [w]) = scheduleResidue u +
      2 ^ scheduleLength u * extensionCarry u w := by
  rw [extensionCarry, ← scheduleResidue_append_mod u [w]]
  exact (Nat.mod_add_div (scheduleResidue (u ++ [w]))
    (2 ^ scheduleLength u)).symm

/-- QM173a, the new carry fits in the newly appended dyadic digits. -/
theorem extensionCarry_lt_twoPow (u : List (List Bool)) (w : List Bool) :
    extensionCarry u w < 2 ^ w.length := by
  rw [extensionCarry]
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ scheduleLength u)).2
  have hcanonical := (canonicalExecution_spec (flattenWords (u ++ [w]))).1
  change scheduleResidue (u ++ [w]) < 2 ^ scheduleLength (u ++ [w]) at hcanonical
  rw [scheduleLength_append_singleton] at hcanonical
  simpa [scheduleResidue, scheduleLength, pow_add, mul_comm] using hcanonical

/-- The carry in QM173a is unique. -/
theorem extensionCarry_unique (u : List (List Bool)) (w : List Bool) {q : ℕ}
    (hq : scheduleResidue (u ++ [w]) =
      scheduleResidue u + 2 ^ scheduleLength u * q) :
    q = extensionCarry u w := by
  have hcanonical := scheduleResidue_append_singleton u w
  have : 2 ^ scheduleLength u * q =
      2 ^ scheduleLength u * extensionCarry u w := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) this

/-- Sum of the successive unweighted extension carries in a schedule, from
an already fixed prefix. -/
def carrySumFrom : List (List Bool) → List (List Bool) → ℕ
  | _, [] => 0
  | pre, w :: ws =>
      extensionCarry pre w + carrySumFrom (pre ++ [w]) ws

/-- Total extension-carry budget of a schedule starting at the root. -/
def carrySum (u : List (List Bool)) : ℕ := carrySumFrom [] u

theorem carrySumFrom_append (pre u v : List (List Bool)) :
    carrySumFrom pre (u ++ v) =
      carrySumFrom pre u + carrySumFrom (pre ++ u) v := by
  induction u generalizing pre with
  | nil => simp [carrySumFrom]
  | cons w u ih =>
      simp only [List.cons_append, carrySumFrom]
      rw [ih]
      simp [List.append_assoc, Nat.add_assoc]

theorem carrySum_append (u v : List (List Bool)) :
    carrySum (u ++ v) = carrySum u + carrySumFrom u v := by
  simpa [carrySum] using carrySumFrom_append [] u v

theorem carrySum_mono_prefix {u v : List (List Bool)} (huv : u <+: v) :
    carrySum u ≤ carrySum v := by
  obtain ⟨tail, rfl⟩ := huv
  rw [carrySum_append]
  exact Nat.le_add_right _ _

/-! ## A finite type of schedules and its restriction maps -/

/-- A length-`n` schedule whose letters belong to the finite subcode `F`. -/
def SubcodeSchedule (F : Finset (List Bool)) (n : ℕ) :=
  Fin n → {w : List Bool // w ∈ F}

instance (F : Finset (List Bool)) (n : ℕ) : Finite (SubcodeSchedule F n) :=
  by
    unfold SubcodeSchedule
    infer_instance

/-- Forget the finite-subcode membership proofs and expose a literal list. -/
def SubcodeSchedule.words {F : Finset (List Bool)} {n : ℕ}
    (u : SubcodeSchedule F n) : List (List Bool) :=
  List.ofFn fun i ↦ (u i).1

theorem SubcodeSchedule.length_words {F : Finset (List Bool)} {n : ℕ}
    (u : SubcodeSchedule F n) : u.words.length = n := by
  simp [SubcodeSchedule.words]

theorem SubcodeSchedule.wordsIn {F : Finset (List Bool)} {n : ℕ}
    (u : SubcodeSchedule F n) : WordsIn (↑F : Set (List Bool)) u.words := by
  intro w hw
  rw [SubcodeSchedule.words, List.mem_ofFn] at hw
  obtain ⟨i, rfl⟩ := hw
  exact (u i).2

/-- Restrict a schedule to an earlier depth. -/
def SubcodeSchedule.restrict {F : Finset (List Bool)} {i j : ℕ}
    (hij : i ≤ j) (u : SubcodeSchedule F j) : SubcodeSchedule F i :=
  Fin.take i hij u

theorem SubcodeSchedule.words_restrict {F : Finset (List Bool)} {i j : ℕ}
    (hij : i ≤ j) (u : SubcodeSchedule F j) :
    (u.restrict hij).words = u.words.take i := by
  exact Fin.ofFn_take_eq_take_ofFn hij (fun k ↦ (u k).1)

theorem SubcodeSchedule.restrict_refl {F : Finset (List Bool)} {n : ℕ}
    (u : SubcodeSchedule F n) : u.restrict rfl.le = u := by
  funext i
  rfl

theorem SubcodeSchedule.restrict_trans {F : Finset (List Bool)}
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : SubcodeSchedule F k) :
    (u.restrict hjk).restrict hij = u.restrict (hij.trans hjk) := by
  funext x
  rfl

/-- A finite-subcode schedule whose total carry is at most `K`. -/
def BoundedSchedule (F : Finset (List Bool)) (K n : ℕ) :=
  {u : SubcodeSchedule F n // carrySum u.words ≤ K}

instance (F : Finset (List Bool)) (K n : ℕ) : Finite (BoundedSchedule F K n) :=
  by
    exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Prefix restriction preserves a carry budget. -/
def BoundedSchedule.restrict {F : Finset (List Bool)} {K i j : ℕ}
    (hij : i ≤ j) (u : BoundedSchedule F K j) : BoundedSchedule F K i :=
  ⟨u.1.restrict hij, by
    rw [SubcodeSchedule.words_restrict]
    exact (carrySum_mono_prefix (List.take_prefix i u.1.words)).trans u.2⟩

theorem BoundedSchedule.restrict_refl {F : Finset (List Bool)} {K n : ℕ}
    (u : BoundedSchedule F K n) : u.restrict rfl.le = u := by
  apply Subtype.ext
  exact SubcodeSchedule.restrict_refl u.1

theorem BoundedSchedule.restrict_trans {F : Finset (List Bool)} {K i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (u : BoundedSchedule F K k) :
    (u.restrict hjk).restrict hij = u.restrict (hij.trans hjk) := by
  apply Subtype.ext
  exact SubcodeSchedule.restrict_trans hij hjk u.1

/-- Turn the usual list presentation of a finite-subcode schedule into the
finite function presentation used by Kőnig compactness. -/
def SubcodeSchedule.ofWords {F : Finset (List Bool)} {n : ℕ}
    (u : List (List Bool)) (hlen : u.length = n)
    (hwords : WordsIn (↑F : Set (List Bool)) u) : SubcodeSchedule F n :=
  fun i ↦
    let j : Fin u.length := Fin.cast hlen.symm i
    ⟨u.get j, hwords (u.get j) (List.get_mem u j)⟩

theorem SubcodeSchedule.words_ofWords {F : Finset (List Bool)} {n : ℕ}
    (u : List (List Bool)) (hlen : u.length = n)
    (hwords : WordsIn (↑F : Set (List Bool)) u) :
    (SubcodeSchedule.ofWords u hlen hwords).words = u := by
  apply List.ext_get
  · simp [SubcodeSchedule.length_words, hlen]
  · intro i hi h'i
    simp [SubcodeSchedule.words, SubcodeSchedule.ofWords]

/-- List-form witnesses at every depth make the finite types of bounded
schedules nonempty at every grade. -/
theorem boundedSchedule_nonempty_of_lists
    {F : Finset (List Bool)} {K n : ℕ}
    (h : ∃ u : List (List Bool), u.length = n ∧
      WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K) :
    Nonempty (BoundedSchedule F K n) := by
  obtain ⟨u, hlen, hwords, hcarry⟩ := h
  let schedule := SubcodeSchedule.ofWords u hlen hwords
  refine ⟨⟨schedule, ?_⟩⟩
  simpa [schedule, SubcodeSchedule.words_ofWords] using hcarry

/-- Kőnig compactness for the prefix-closed finite tree of schedules with
carry budget `K`. -/
theorem exists_coherent_boundedSchedules
    {F : Finset (List Bool)} {K : ℕ}
    (h : ∀ n, ∃ u : List (List Bool), u.length = n ∧
      WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K) :
    ∃ f : (n : ℕ) → BoundedSchedule F K n,
      ∀ {i j : ℕ} (hij : i ≤ j), (f j).restrict hij = f i := by
  letI (n : ℕ) : Nonempty (BoundedSchedule F K n) :=
    boundedSchedule_nonempty_of_lists (h n)
  refine exists_seq_forall_proj_of_forall_finite
    (α := fun n ↦ BoundedSchedule F K n)
    (fun {_ _} hij u ↦ BoundedSchedule.restrict hij u) ?_ ?_ ?_
  · intro i u
    exact BoundedSchedule.restrict_refl u
  · intro i j k hij hjk u
    exact BoundedSchedule.restrict_trans hij hjk u
  · intro i u
    exact Set.toFinite _

/-! ## Arithmetic control of schedules -/

theorem carrySum_append_singleton (u : List (List Bool)) (w : List Bool) :
    carrySum (u ++ [w]) = carrySum u + extensionCarry u w := by
  rw [carrySum_append]
  simp [carrySumFrom]

/-- The unweighted carry sum is bounded by the resulting canonical source
residue.  Each positive carry contributes at least its unweighted value to
the dyadically weighted source increment. -/
theorem carrySum_le_scheduleResidue (u : List (List Bool)) :
    carrySum u ≤ scheduleResidue u := by
  induction u using List.reverseRecOn with
  | nil => simp [carrySum, carrySumFrom, scheduleResidue, flattenWords,
      canonicalExecution]
  | append_singleton u w ih =>
      rw [carrySum_append_singleton, scheduleResidue_append_singleton]
      have hpow : 1 ≤ 2 ^ scheduleLength u :=
        Nat.one_le_pow (scheduleLength u) 2 (by omega)
      have hq : extensionCarry u w ≤
          2 ^ scheduleLength u * extensionCarry u w := by
        simpa [mul_comm] using
          Nat.mul_le_mul_right (extensionCarry u w) hpow
      omega

/-- Any literal execution starts at a lift of the canonical source, so its
unweighted carry sum is no larger than the ordinary starting value. -/
theorem carrySum_le_of_executesBlocks {u : List (List Bool)} {start : ℕ}
    (hexec : ExecutesBlocks u start) : carrySum u ≤ start := by
  obtain ⟨finish, hflat⟩ := (executesBlocks_iff u start).mp hexec
  obtain ⟨t, hstart, _⟩ :=
    (executes_iff_canonical_family (flattenWords u)).mp hflat
  calc
    carrySum u ≤ scheduleResidue u := carrySum_le_scheduleResidue u
    _ ≤ start := by simp [scheduleResidue, hstart]

/-- The letter at position `n` in the coherent Kőnig branch. -/
def coherentWord {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) (n : ℕ) : List Bool :=
  ((f (n + 1)).1 ⟨n, by omega⟩).1

/-- The first `n` letters of the coherent Kőnig branch. -/
def coherentPrefix {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) (n : ℕ) :
    List (List Bool) :=
  List.ofFn fun i : Fin n ↦ coherentWord f i

theorem coherentPrefix_succ {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) (n : ℕ) :
    coherentPrefix f (n + 1) = coherentPrefix f n ++ [coherentWord f n] := by
  simpa [coherentPrefix, coherentWord] using
    (List.ofFn_succ' (fun i : Fin (n + 1) ↦ coherentWord f i))

theorem coherentPrefix_eq_words {F : Finset (List Bool)} {K : ℕ}
    {f : (n : ℕ) → BoundedSchedule F K n}
    (hf : ∀ {i j : ℕ} (hij : i ≤ j), (f j).restrict hij = f i)
    (n : ℕ) : coherentPrefix f n = (f n).1.words := by
  apply List.ext_get
  · simp [coherentPrefix, SubcodeSchedule.length_words]
  · intro i hi h'i
    have hiN : i < n := by
      simpa [SubcodeSchedule.length_words] using h'i
    have hin : i + 1 ≤ n := by omega
    have hcoh := hf hin
    have hfun : ((f n).1.restrict hin) ⟨i, by omega⟩ =
        (f (i + 1)).1 ⟨i, by omega⟩ := by
      exact congrFun (congrArg Subtype.val hcoh) ⟨i, by omega⟩
    change (f n).1 ⟨i, hiN⟩ = (f (i + 1)).1 ⟨i, by omega⟩ at hfun
    simpa [coherentPrefix, coherentWord, SubcodeSchedule.words,
      SubcodeSchedule.restrict] using congrArg Subtype.val hfun.symm

theorem coherentPrefix_wordsIn {F : Finset (List Bool)} {K : ℕ}
    {f : (n : ℕ) → BoundedSchedule F K n}
    (hf : ∀ {i j : ℕ} (hij : i ≤ j), (f j).restrict hij = f i)
    (n : ℕ) : WordsIn (↑F : Set (List Bool)) (coherentPrefix f n) := by
  rw [coherentPrefix_eq_words hf n]
  exact (f n).1.wordsIn

theorem coherentPrefix_carry_le {F : Finset (List Bool)} {K : ℕ}
    {f : (n : ℕ) → BoundedSchedule F K n}
    (hf : ∀ {i j : ℕ} (hij : i ≤ j), (f j).restrict hij = f i)
    (n : ℕ) : carrySum (coherentPrefix f n) ≤ K := by
  rw [coherentPrefix_eq_words hf n]
  exact (f n).2

theorem coherentPrefix_length {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) (n : ℕ) :
    (coherentPrefix f n).length = n := by
  simp [coherentPrefix]

theorem coherentPrefix_take {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) {i j : ℕ} (hij : i ≤ j) :
    (coherentPrefix f j).take i = coherentPrefix f i := by
  calc
    (coherentPrefix f j).take i =
        List.ofFn (Fin.take i hij (fun k : Fin j ↦ coherentWord f k)) := by
      simpa [coherentPrefix] using
        (Fin.ofFn_take_eq_take_ofFn hij
          (fun k : Fin j ↦ coherentWord f k)).symm
    _ = coherentPrefix f i := by
      simp only [coherentPrefix]
      congr 1

theorem coherentPrefix_prefix {F : Finset (List Bool)} {K : ℕ}
    (f : (n : ℕ) → BoundedSchedule F K n) {i j : ℕ} (hij : i ≤ j) :
    coherentPrefix f i <+: coherentPrefix f j := by
  rw [List.prefix_iff_eq_take]
  simpa [coherentPrefix_length f i, hij] using (coherentPrefix_take f hij).symm

/-- A coherent branch with a uniform unweighted carry budget has an ordinary
positive source executing every finite prefix.  The key discrete point is
that the bounded increasing carry sum eventually stops, so every later edge
carry is zero and the canonical source residue stabilizes. -/
theorem coherent_boundedSchedules_give_infiniteExecution
    {F : Finset (List Bool)} {K : ℕ}
    (hfirst : ∀ w ∈ F, FirstPassage w)
    {f : (n : ℕ) → BoundedSchedule F K n}
    (hf : ∀ {i j : ℕ} (hij : i ≤ j), (f j).restrict hij = f i) :
    ∃ start, InfiniteExecution (↑F : Set (List Bool)) start := by
  let c : ℕ → ℕ := fun n ↦ carrySum (coherentPrefix f n)
  have hcMono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [c]
    rw [coherentPrefix_succ]
    exact carrySum_mono_prefix (List.prefix_append _ _)
  have hcBound : BoundedRange c :=
    ⟨K, fun n ↦ coherentPrefix_carry_le hf n⟩
  obtain ⟨N, hN⟩ :=
    (eventuallyConstant_iff_boundedRange_of_monotone hcMono).2 hcBound
  let N' := max N 1
  have hNN' : N ≤ N' := Nat.le_max_left _ _
  have hN'pos : 1 ≤ N' := Nat.le_max_right _ _
  have hcarryZero : ∀ n, N' ≤ n →
      extensionCarry (coherentPrefix f n) (coherentWord f n) = 0 := by
    intro n hn
    have hnN : N ≤ n := hNN'.trans hn
    have hsnN : N ≤ n + 1 := hnN.trans (by omega)
    have heq : c (n + 1) = c n := (hN (n + 1) hsnN).trans (hN n hnN).symm
    dsimp [c] at heq
    rw [coherentPrefix_succ, carrySum_append_singleton] at heq
    omega
  let r : ℕ → ℕ := fun n ↦ scheduleResidue (coherentPrefix f n)
  have hrMono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [r]
    rw [coherentPrefix_succ, scheduleResidue_append_singleton]
    exact Nat.le_add_right _ _
  have hrStable : ∀ n, N' ≤ n → r n = r N' := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
        dsimp [r] at ih ⊢
        rw [coherentPrefix_succ, scheduleResidue_append_singleton,
          hcarryZero n hn, Nat.mul_zero, Nat.add_zero, ih]
  let start := r N'
  have hword0 : coherentWord f 0 ∈ F := by
    exact ((f 1).1 ⟨0, by omega⟩).2
  have hfirst0 : FirstPassage (coherentWord f 0) :=
    hfirst _ hword0
  have hrOnePos : 0 < r 1 := by
    simpa [r, coherentPrefix_succ, coherentPrefix, coherentWord,
      scheduleResidue, flattenWords] using
      OutwardFiniteHeight.canonicalSource_pos hfirst0
  have hstartPos : 0 < start := by
    dsimp [start]
    exact hrOnePos.trans_le (hrMono hN'pos)
  refine ⟨start, fun n ↦ ⟨hstartPos, coherentPrefix f n,
    coherentPrefix_length f n, coherentPrefix_wordsIn hf n, ?_⟩⟩
  rcases le_total n N' with hn | hn
  · have hfull : ExecutesBlocks (coherentPrefix f N') start := by
      apply (executesBlocks_iff (coherentPrefix f N') start).mpr
      refine ⟨(canonicalExecution (flattenWords (coherentPrefix f N'))).2, ?_⟩
      simpa [start, r, scheduleResidue] using
        (canonicalExecution_spec (flattenWords (coherentPrefix f N'))).2.2
    exact executesBlocks_prefix (coherentPrefix_prefix f hn) hfull
  · apply (executesBlocks_iff (coherentPrefix f n) start).mpr
    refine ⟨(canonicalExecution (flattenWords (coherentPrefix f n))).2, ?_⟩
    have hrs := hrStable n hn
    have hcanon :=
      (canonicalExecution_spec (flattenWords (coherentPrefix f n))).2.2
    change Executes (flattenWords (coherentPrefix f n)) (r n)
      (canonicalExecution (flattenWords (coherentPrefix f n))).2 at hcanon
    rw [hrs] at hcanon
    simpa [start] using hcanon

/-- QM173b.  A finite first-passage subcode supports one positive ordinary
infinite execution exactly when schedules of every finite depth admit one
uniform bound on their total unweighted extension carry. -/
theorem infiniteExecution_iff_uniformCarryBudget
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ start, InfiniteExecution (↑F : Set (List Bool)) start) ↔
      ∃ K, ∀ n, ∃ u : List (List Bool),
        u.length = n ∧ WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K := by
  constructor
  · rintro ⟨start, hstart⟩
    refine ⟨start, fun n ↦ ?_⟩
    obtain ⟨_, u, hlen, hwords, hexec⟩ := hstart n
    exact ⟨u, hlen, hwords, carrySum_le_of_executesBlocks hexec⟩
  · rintro ⟨K, hK⟩
    obtain ⟨f, hf⟩ := exists_coherent_boundedSchedules hK
    exact coherent_boundedSchedules_give_infiniteExecution hfirst hf

/-- A uniform finite-subcode carry budget supplies an explicit ordinary
Syracuse counterexample seed. -/
theorem exists_not_syracuseReachesOne_of_uniformCarryBudget
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w)
    {K : ℕ}
    (hK : ∀ n, ∃ u : List (List Bool),
      u.length = n ∧ WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K) :
    ∃ start, ¬ CleanLean.Collatz.SyracuseReachesOne start := by
  obtain ⟨start, hinfinite⟩ :=
    (infiniteExecution_iff_uniformCarryBudget F hfirst).2 ⟨K, hK⟩
  refine ⟨start, OutwardCodeCounterexample.not_syracuseReachesOne_of_infiniteExecution
    (C := (↑F : Set (List Bool))) ?_ hinfinite⟩
  intro w hw
  exact (hfirst w hw).1

/-- The existing literal outward-code consumer turns the conditional bounded
carry criterion into a refutation of the standard unaccelerated Collatz
conjecture. -/
theorem not_conjecture_of_uniformCarryBudget
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w)
    {K : ℕ}
    (hK : ∀ n, ∃ u : List (List Bool),
      u.length = n ∧ WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    (infiniteExecution_iff_uniformCarryBudget F hfirst).2 ⟨K, hK⟩
  exact OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (C := (↑F : Set (List Bool)))
    (fun w hw ↦ (hfirst w hw).1) hinfinite

/-! ## Exact finite-horizon dynamic program -/

/-- Bellman value for `r` further finite-subcode edges after `pre`. -/
noncomputable def finiteHorizonCost
    (F : Finset (List Bool)) (hF : F.Nonempty) :
    ℕ → List (List Bool) → ℕ
  | 0, _ => 0
  | r + 1, pre =>
      let costs := F.image fun w ↦
        extensionCarry pre w + finiteHorizonCost F hF r (pre ++ [w])
      costs.min' (hF.image _)

@[simp] theorem finiteHorizonCost_zero
    (F : Finset (List Bool)) (hF : F.Nonempty) (pre : List (List Bool)) :
    finiteHorizonCost F hF 0 pre = 0 := rfl

/-- QM173c, the exact Bellman recursion. -/
theorem finiteHorizonCost_succ
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (r : ℕ) (pre : List (List Bool)) :
    finiteHorizonCost F hF (r + 1) pre =
      (F.image fun w ↦ extensionCarry pre w +
        finiteHorizonCost F hF r (pre ++ [w])).min' (hF.image _) := rfl

theorem finiteHorizonCost_le_choice
    (F : Finset (List Bool)) (hF : F.Nonempty)
    {r : ℕ} {pre : List (List Bool)} {w : List Bool} (hw : w ∈ F) :
    finiteHorizonCost F hF (r + 1) pre ≤
      extensionCarry pre w + finiteHorizonCost F hF r (pre ++ [w]) := by
  rw [finiteHorizonCost_succ]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem exists_choice_finiteHorizonCost_eq
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (r : ℕ) (pre : List (List Bool)) :
    ∃ w ∈ F, finiteHorizonCost F hF (r + 1) pre =
      extensionCarry pre w + finiteHorizonCost F hF r (pre ++ [w]) := by
  rw [finiteHorizonCost_succ]
  have hmem := Finset.min'_mem
    (F.image fun w ↦ extensionCarry pre w +
      finiteHorizonCost F hF r (pre ++ [w])) (hF.image _)
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hmem
  exact ⟨w, hw, heq.symm⟩

/-- The Bellman value is below the carry cost of every admissible suffix. -/
theorem finiteHorizonCost_le_carrySumFrom
    (F : Finset (List Bool)) (hF : F.Nonempty)
    {r : ℕ} {pre suffix : List (List Bool)}
    (hlen : suffix.length = r)
    (hwords : WordsIn (↑F : Set (List Bool)) suffix) :
    finiteHorizonCost F hF r pre ≤ carrySumFrom pre suffix := by
  induction suffix generalizing r pre with
  | nil =>
      subst r
      simp [carrySumFrom]
  | cons w suffix ih =>
      have hw : w ∈ F := hwords w (by simp)
      have htail : WordsIn (↑F : Set (List Bool)) suffix := by
        intro v hv
        exact hwords v (by simp [hv])
      cases r with
      | zero => simp at hlen
      | succ r =>
          have hlen' : suffix.length = r := by simpa using hlen
          calc
            finiteHorizonCost F hF (r + 1) pre ≤
                extensionCarry pre w +
                  finiteHorizonCost F hF r (pre ++ [w]) :=
              finiteHorizonCost_le_choice F hF hw
            _ ≤ extensionCarry pre w +
                carrySumFrom (pre ++ [w]) suffix :=
              Nat.add_le_add_left (ih hlen' htail) _
            _ = carrySumFrom pre (w :: suffix) := rfl

/-- The Bellman minimum is attained by an actual finite schedule. -/
theorem finiteHorizonCost_realized
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (r : ℕ) (pre : List (List Bool)) :
    ∃ suffix : List (List Bool), suffix.length = r ∧
      WordsIn (↑F : Set (List Bool)) suffix ∧
      carrySumFrom pre suffix = finiteHorizonCost F hF r pre := by
  induction r generalizing pre with
  | zero => exact ⟨[], rfl, by simp [WordsIn], by simp [carrySumFrom]⟩
  | succ r ih =>
      obtain ⟨w, hw, hcost⟩ := exists_choice_finiteHorizonCost_eq F hF r pre
      obtain ⟨suffix, hlen, hwords, htailCost⟩ := ih (pre ++ [w])
      refine ⟨w :: suffix, by simp [hlen], ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hw
        · exact hwords v hv
      · simp only [carrySumFrom]
        rw [htailCost, hcost]

/-- Exact finite-horizon decision form used by a bounded-carry searcher. -/
theorem finiteHorizonCost_le_iff_exists_schedule
    (F : Finset (List Bool)) (hF : F.Nonempty) (r K : ℕ) :
    finiteHorizonCost F hF r [] ≤ K ↔
      ∃ u : List (List Bool), u.length = r ∧
        WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K := by
  constructor
  · intro hcost
    obtain ⟨u, hlen, hwords, heq⟩ := finiteHorizonCost_realized F hF r []
    exact ⟨u, hlen, hwords, by simpa [carrySum] using heq.le.trans hcost⟩
  · rintro ⟨u, hlen, hwords, hcarry⟩
    exact (finiteHorizonCost_le_carrySumFrom F hF hlen hwords).trans <| by
      simpa [carrySum] using hcarry

/-- The optimal carry required to reach depth `r` is nondecreasing in the
horizon.  A deeper minimizing path restricts to a shallower admissible path. -/
theorem finiteHorizonCost_root_mono
    (F : Finset (List Bool)) (hF : F.Nonempty) :
    Monotone (fun r ↦ finiteHorizonCost F hF r []) := by
  apply monotone_nat_of_le_succ
  intro r
  obtain ⟨u, hlen, hwords, hcost⟩ := finiteHorizonCost_realized F hF (r + 1) []
  let pre := u.take r
  have hpreLen : pre.length = r := by
    simp [pre, hlen]
  have hpreWords : WordsIn (↑F : Set (List Bool)) pre := by
    intro w hw
    exact hwords w (List.mem_of_mem_take hw)
  calc
    finiteHorizonCost F hF r [] ≤ carrySumFrom [] pre :=
      finiteHorizonCost_le_carrySumFrom F hF hpreLen hpreWords
    _ ≤ carrySumFrom [] u := by
      exact carrySum_mono_prefix (List.take_prefix r u)
    _ = finiteHorizonCost F hF (r + 1) [] := hcost

/-- Scalar Bellman form of QM173b: a finite subcode has one ordinary
infinite execution exactly when its optimal finite-horizon carry costs are
uniformly bounded. -/
theorem infiniteExecution_iff_bounded_finiteHorizonCost
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ start, InfiniteExecution (↑F : Set (List Bool)) start) ↔
      BoundedRange (fun r ↦ finiteHorizonCost F hF r []) := by
  rw [infiniteExecution_iff_uniformCarryBudget F hfirst]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun r ↦ ?_⟩
    exact (finiteHorizonCost_le_iff_exists_schedule F hF r K).2 (hK r)
  · rintro ⟨K, hK⟩
    refine ⟨K, fun r ↦ ?_⟩
    exact (finiteHorizonCost_le_iff_exists_schedule F hF r K).1 (hK r)

/-- Since the Bellman values form a monotone natural sequence, boundedness
is equivalently eventual constancy. -/
theorem infiniteExecution_iff_eventuallyConstant_finiteHorizonCost
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ start, InfiniteExecution (↑F : Set (List Bool)) start) ↔
      EventuallyConstant (fun r ↦ finiteHorizonCost F hF r []) := by
  rw [eventuallyConstant_iff_boundedRange_of_monotone
    (finiteHorizonCost_root_mono F hF)]
  exact infiniteExecution_iff_bounded_finiteHorizonCost F hF hfirst

/-- Conditional Collatz endpoint stated only in terms of the scalar Bellman
sequence. -/
theorem not_conjecture_of_bounded_finiteHorizonCost
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (hfirst : ∀ w ∈ F, FirstPassage w)
    (hbounded : BoundedRange (fun r ↦ finiteHorizonCost F hF r [])) :
    ¬ CleanLean.Collatz.Conjecture := by
  obtain ⟨start, hinfinite⟩ :=
    (infiniteExecution_iff_bounded_finiteHorizonCost F hF hfirst).2 hbounded
  exact OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (C := (↑F : Set (List Bool)))
    (fun w hw ↦ (hfirst w hw).1) hinfinite

/-! ## Finite reachability to a zero-carry ray -/

/-- A uniformly bounded carry branch eventually enters a prefix from which
arbitrarily long suffixes cost exactly zero.  This is the search-theoretic
normal form of the integer fact that a bounded sum has only finitely many
positive summands. -/
theorem uniformCarryBudget_iff_exists_zeroCarryTail
    (F : Finset (List Bool)) :
    (∃ K, ∀ n, ∃ u : List (List Bool),
      u.length = n ∧ WordsIn (↑F : Set (List Bool)) u ∧ carrySum u ≤ K) ↔
      ∃ pre : List (List Bool), WordsIn (↑F : Set (List Bool)) pre ∧
        ∀ r, ∃ suffix : List (List Bool), suffix.length = r ∧
          WordsIn (↑F : Set (List Bool)) suffix ∧
          carrySumFrom pre suffix = 0 := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨f, hf⟩ := exists_coherent_boundedSchedules hK
    let c : ℕ → ℕ := fun n ↦ carrySum (coherentPrefix f n)
    have hcMono : Monotone c := by
      apply monotone_nat_of_le_succ
      intro n
      dsimp [c]
      rw [coherentPrefix_succ]
      exact carrySum_mono_prefix (List.prefix_append _ _)
    have hcBound : BoundedRange c :=
      ⟨K, fun n ↦ coherentPrefix_carry_le hf n⟩
    obtain ⟨N, hN⟩ :=
      (eventuallyConstant_iff_boundedRange_of_monotone hcMono).2 hcBound
    refine ⟨coherentPrefix f N, coherentPrefix_wordsIn hf N, fun r ↦ ?_⟩
    let full := coherentPrefix f (N + r)
    let suffix := full.drop N
    have hNle : N ≤ N + r := Nat.le_add_right _ _
    have htake : full.take N = coherentPrefix f N := by
      exact coherentPrefix_take f hNle
    have happ : coherentPrefix f N ++ suffix = full := by
      dsimp [suffix]
      rw [← htake]
      exact List.take_append_drop N full
    have hsuffixLen : suffix.length = r := by
      simp [suffix, full, coherentPrefix_length]
    have hfullWords : WordsIn (↑F : Set (List Bool)) full :=
      coherentPrefix_wordsIn hf (N + r)
    have hsuffixWords : WordsIn (↑F : Set (List Bool)) suffix := by
      intro w hw
      exact hfullWords w (List.mem_of_mem_drop hw)
    refine ⟨suffix, hsuffixLen, hsuffixWords, ?_⟩
    have hcEq : carrySum full = carrySum (coherentPrefix f N) := by
      exact (hN (N + r) hNle).trans (hN N rfl.le).symm
    rw [← happ, carrySum_append] at hcEq
    omega
  · rintro ⟨pre, hpreWords, htail⟩
    refine ⟨carrySum pre, fun n ↦ ?_⟩
    rcases le_total n pre.length with hn | hn
    · let u := pre.take n
      refine ⟨u, by simp [u, hn], ?_, ?_⟩
      · intro w hw
        exact hpreWords w (List.mem_of_mem_take hw)
      · exact carrySum_mono_prefix (List.take_prefix n pre)
    · obtain ⟨suffix, hlen, hwords, hzero⟩ := htail (n - pre.length)
      let u := pre ++ suffix
      refine ⟨u, ?_, ?_, ?_⟩
      · simp [u, hlen, Nat.add_sub_of_le hn]
      · intro w hw
        simp only [u, List.mem_append] at hw
        exact hw.elim (hpreWords w) (hwords w)
      · change carrySum (pre ++ suffix) ≤ carrySum pre
        rw [carrySum_append, hzero, Nat.add_zero]

/-- First-passage specialization: a finite subcode supports an ordinary
infinite execution exactly when some finite schedule reaches an
arbitrarily-deep zero-carry tail tree. -/
theorem infiniteExecution_iff_exists_zeroCarryTail
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ start, InfiniteExecution (↑F : Set (List Bool)) start) ↔
      ∃ pre : List (List Bool), WordsIn (↑F : Set (List Bool)) pre ∧
        ∀ r, ∃ suffix : List (List Bool), suffix.length = r ∧
          WordsIn (↑F : Set (List Bool)) suffix ∧
          carrySumFrom pre suffix = 0 := by
  exact (infiniteExecution_iff_uniformCarryBudget F hfirst).trans
    (uniformCarryBudget_iff_exists_zeroCarryTail F)

end

end OutwardFiniteSubcodeCarry
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFiniteSubcodeCarry

/-!
# Literal semantics of zero carry

An extension carry is zero exactly when the canonical endpoint of the
existing schedule literally executes the appended parity word.  Consequently
a zero-carry first-passage tree has at most one child at every node: it is a
single deterministic ordinary orbit, not a source of symbolic branching.
-/

namespace KontoroC
namespace OutwardZeroCarrySemantics

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardCylinderRenewal OutwardFirstPassage OutwardFiniteHeight
  OutwardFiniteSubcodeCarry

noncomputable section

/-- Canonical target residue of a flattened block schedule. -/
def scheduleTarget (u : List (List Bool)) : ℕ :=
  (canonicalExecution (flattenWords u)).2

/-- A natural starts an execution of `w` exactly when it belongs to the
canonical dyadic source residue class of `w`. -/
theorem exists_executes_iff_source_mod (w : List Bool) (source : ℕ) :
    (∃ target, Executes w source target) ↔
      source % 2 ^ w.length = (canonicalExecution w).1 := by
  constructor
  · rintro ⟨target, hexec⟩
    have hmod := executes_source_modEq w hexec
      (canonicalExecution_spec w).2.2
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt (canonicalExecution_spec w).1]
  · intro hsourceMod
    let k := source / 2 ^ w.length
    have hsource : source = (canonicalExecution w).1 + 2 ^ w.length * k := by
      calc
        source = source % 2 ^ w.length + 2 ^ w.length * (source / 2 ^ w.length) :=
          (Nat.mod_add_div source (2 ^ w.length)).symm
        _ = (canonicalExecution w).1 + 2 ^ w.length * k := by
          rw [hsourceMod]
    refine ⟨(canonicalExecution w).2 + 3 ^ w.count true * k, ?_⟩
    rw [hsource]
    exact executes_shift w (canonicalExecution_spec w).2.2 k

/-- If the current canonical endpoint executes the appended word, the longer
canonical cylinder has exactly the same source residue. -/
theorem scheduleResidue_append_eq_of_target_executes
    (u : List (List Bool)) (w : List Bool) {target : ℕ}
    (hword : Executes w (scheduleTarget u) target) :
    scheduleResidue (u ++ [w]) = scheduleResidue u := by
  have hpre : Executes (flattenWords u)
      (scheduleResidue u) (scheduleTarget u) := by
    simpa [scheduleResidue, scheduleTarget] using
      (canonicalExecution_spec (flattenWords u)).2.2
  have hcat : Executes (flattenWords (u ++ [w]))
      (scheduleResidue u) target := by
    simpa [flattenWords_append, flattenWords] using
      (executes_append (flattenWords u) w).mpr
        ⟨scheduleTarget u, hpre, hword⟩
  have hmod := executes_source_modEq (flattenWords (u ++ [w])) hcat
    (canonicalExecution_spec (flattenWords (u ++ [w]))).2.2
  have hprefixLt : scheduleResidue u < 2 ^ scheduleLength (u ++ [w]) := by
    have hu := (canonicalExecution_spec (flattenWords u)).1
    have hpow : 2 ^ scheduleLength u ≤ 2 ^ scheduleLength (u ++ [w]) := by
      apply Nat.pow_le_pow_right (by omega)
      rw [scheduleLength_append_singleton]
      omega
    have hu' : scheduleResidue u < 2 ^ scheduleLength u := by
      simpa [scheduleResidue, scheduleLength] using hu
    exact hu'.trans_le hpow
  have hfullLt : scheduleResidue (u ++ [w]) <
      2 ^ scheduleLength (u ++ [w]) := by
    simpa [scheduleResidue, scheduleLength] using
      (canonicalExecution_spec (flattenWords (u ++ [w]))).1
  exact (hmod.eq_of_lt_of_lt hprefixLt hfullLt).symm

/-- Zero carry is equivalent to mere executability of the next word from the
current canonical endpoint. -/
theorem extensionCarry_eq_zero_iff_exists_executes
    (u : List (List Bool)) (w : List Bool) :
    extensionCarry u w = 0 ↔
      ∃ target, Executes w (scheduleTarget u) target := by
  constructor
  · intro hcarry
    have hsource := scheduleResidue_append_singleton u w
    rw [hcarry, Nat.mul_zero, Nat.add_zero] at hsource
    have hfull : Executes (flattenWords u ++ w)
        (scheduleResidue u) (scheduleTarget (u ++ [w])) := by
      have hcanonical :=
        (canonicalExecution_spec (flattenWords (u ++ [w]))).2.2
      change Executes (flattenWords (u ++ [w]))
        (scheduleResidue (u ++ [w])) (scheduleTarget (u ++ [w])) at hcanonical
      rw [hsource] at hcanonical
      simpa [flattenWords_append, flattenWords] using hcanonical
    obtain ⟨middle, hpre, hword⟩ :=
      (executes_append (flattenWords u) w).mp hfull
    have hmiddle : middle = scheduleTarget u := by
      exact executes_target_unique (flattenWords u) hpre <| by
        simpa [scheduleResidue, scheduleTarget] using
          (canonicalExecution_spec (flattenWords u)).2.2
    exact ⟨scheduleTarget (u ++ [w]), by simpa [hmiddle] using hword⟩
  · rintro ⟨target, hword⟩
    have hsource := scheduleResidue_append_eq_of_target_executes u w hword
    rw [extensionCarry, hsource]
    exact Nat.div_eq_of_lt <| by
      simpa [scheduleResidue, scheduleLength] using
        (canonicalExecution_spec (flattenWords u)).1

/-- The exact endpoint form of zero carry. -/
theorem extensionCarry_eq_zero_iff_executes
    (u : List (List Bool)) (w : List Bool) :
    extensionCarry u w = 0 ↔
      Executes w (scheduleTarget u) (scheduleTarget (u ++ [w])) := by
  constructor
  · intro hcarry
    obtain ⟨target, hword⟩ :=
      (extensionCarry_eq_zero_iff_exists_executes u w).mp hcarry
    have hsource := scheduleResidue_append_eq_of_target_executes u w hword
    have hpre : Executes (flattenWords u)
        (scheduleResidue u) (scheduleTarget u) := by
      simpa [scheduleResidue, scheduleTarget] using
        (canonicalExecution_spec (flattenWords u)).2.2
    have hcat : Executes (flattenWords (u ++ [w]))
        (scheduleResidue (u ++ [w])) target := by
      simpa [flattenWords_append, flattenWords, hsource] using
        (executes_append (flattenWords u) w).mpr
          ⟨scheduleTarget u, hpre, hword⟩
    have htarget : target = scheduleTarget (u ++ [w]) := by
      exact executes_target_unique (flattenWords (u ++ [w])) hcat <| by
        simpa [scheduleResidue, scheduleTarget] using
          (canonicalExecution_spec (flattenWords (u ++ [w]))).2.2
    simpa [htarget] using hword
  · intro hword
    exact (extensionCarry_eq_zero_iff_exists_executes u w).mpr
      ⟨scheduleTarget (u ++ [w]), hword⟩

/-- Congruence-only form: zero carry means the current canonical endpoint
lies in the appended word's exact dyadic parity cylinder. -/
theorem extensionCarry_eq_zero_iff_target_mod
    (u : List (List Bool)) (w : List Bool) :
    extensionCarry u w = 0 ↔
      scheduleTarget u % 2 ^ w.length = (canonicalExecution w).1 := by
  exact (extensionCarry_eq_zero_iff_exists_executes u w).trans
    (exists_executes_iff_source_mod w (scheduleTarget u))

/-- A first-passage zero-carry node has at most one child. -/
theorem zeroCarry_word_unique
    {u : List (List Bool)} {w v : List Bool}
    (hwFirst : FirstPassage w) (hvFirst : FirstPassage v)
    (hwZero : extensionCarry u w = 0)
    (hvZero : extensionCarry u v = 0) :
    w = v := by
  exact firstPassage_eq_of_common_source hwFirst hvFirst
    ((extensionCarry_eq_zero_iff_executes u w).mp hwZero)
    ((extensionCarry_eq_zero_iff_executes u v).mp hvZero)

/-- The apparent zero-carry child set of a finite first-passage alphabet. -/
noncomputable def zeroCarryChildren
    (F : Finset (List Bool)) (u : List (List Bool)) : Finset (List Bool) :=
  F.filter fun w ↦ extensionCarry u w = 0

/-- The zero-carry child set has cardinality at most one. -/
theorem zeroCarryChildren_card_le_one
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w)
    (u : List (List Bool)) :
    (zeroCarryChildren F u).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro w hw v hv
  rw [zeroCarryChildren, Finset.mem_filter] at hw hv
  exact zeroCarry_word_unique (hfirst w hw.1) (hfirst v hv.1) hw.2 hv.2

/-- Zero total suffix carry is exactly literal block execution from the
canonical endpoint of the prefix. -/
theorem carrySumFrom_eq_zero_iff_executesBlocks
    (pre suffix : List (List Bool)) :
    carrySumFrom pre suffix = 0 ↔
      ExecutesBlocks suffix (scheduleTarget pre) := by
  induction suffix generalizing pre with
  | nil => simp [carrySumFrom, ExecutesBlocks]
  | cons w suffix ih =>
      simp only [carrySumFrom, Nat.add_eq_zero_iff, ExecutesBlocks]
      constructor
      · rintro ⟨hzero, htailZero⟩
        refine ⟨scheduleTarget (pre ++ [w]),
          (extensionCarry_eq_zero_iff_executes pre w).mp hzero, ?_⟩
        exact (ih (pre ++ [w])).mp htailZero
      · rintro ⟨middle, hword, htail⟩
        have hzero : extensionCarry pre w = 0 :=
          (extensionCarry_eq_zero_iff_exists_executes pre w).mpr
            ⟨middle, hword⟩
        have hmiddle : middle = scheduleTarget (pre ++ [w]) :=
          executes_target_unique w hword
            ((extensionCarry_eq_zero_iff_executes pre w).mp hzero)
        refine ⟨hzero, (ih (pre ++ [w])).mpr ?_⟩
        simpa [hmiddle] using htail

/-- A first-passage word cannot execute from zero. -/
theorem source_pos_of_executes_firstPassage
    {w : List Bool} {source target : ℕ}
    (hfirst : FirstPassage w) (hexec : Executes w source target) :
    0 < source := by
  by_contra hnot
  have hzero : source = 0 := by omega
  have hcount := executes_zero_count_true_eq_zero (hzero ▸ hexec)
  have hout := hfirst.1
  simp only [WordOutward, hcount, pow_zero] at hout
  have hpow : 0 < 2 ^ w.length := by positivity
  omega

/-- Literal first-passage block schedules of one fixed length are uniquely
determined by their ordinary source. -/
theorem executesBlocks_eq_of_firstPassage_same_length
    {left right : List (List Bool)} {source : ℕ}
    (hleftWords : ∀ w ∈ left, FirstPassage w)
    (hrightWords : ∀ w ∈ right, FirstPassage w)
    (hleftExec : ExecutesBlocks left source)
    (hrightExec : ExecutesBlocks right source)
    (hlen : left.length = right.length) :
    left = right := by
  induction left generalizing right source with
  | nil => simpa using hlen.symm
  | cons w ws ih =>
      cases right with
      | nil => simp at hlen
      | cons v vs =>
          obtain ⟨middleW, hw, hws⟩ := hleftExec
          obtain ⟨middleV, hv, hvs⟩ := hrightExec
          have hwFirst : FirstPassage w := hleftWords w (by simp)
          have hvFirst : FirstPassage v := hrightWords v (by simp)
          have hwv : w = v :=
            firstPassage_eq_of_common_source hwFirst hvFirst hw hv
          subst v
          have hmiddle : middleW = middleV :=
            executes_target_unique w hw hv
          subst middleV
          have hwsWords : ∀ z ∈ ws, FirstPassage z := by
            intro z hz
            exact hleftWords z (by simp [hz])
          have hvsWords : ∀ z ∈ vs, FirstPassage z := by
            intro z hz
            exact hrightWords z (by simp [hz])
          have htailLen : ws.length = vs.length := by simpa using hlen
          rw [ih hwsWords hvsWords hws hvs htailLen]

/-- Hence two zero-carry first-passage suffixes of the same depth from one
prefix are equal. -/
theorem zeroCarry_suffix_unique
    {F : Finset (List Bool)}
    (hfirst : ∀ w ∈ F, FirstPassage w)
    {pre left right : List (List Bool)}
    (hleftWords : WordsIn (↑F : Set (List Bool)) left)
    (hrightWords : WordsIn (↑F : Set (List Bool)) right)
    (hleftZero : carrySumFrom pre left = 0)
    (hrightZero : carrySumFrom pre right = 0)
    (hlen : left.length = right.length) :
    left = right := by
  apply executesBlocks_eq_of_firstPassage_same_length
    (fun w hw ↦ hfirst w (hleftWords w hw))
    (fun w hw ↦ hfirst w (hrightWords w hw))
    ((carrySumFrom_eq_zero_iff_executesBlocks pre left).mp hleftZero)
    ((carrySumFrom_eq_zero_iff_executesBlocks pre right).mp hrightZero)
    hlen

/-- Zero-carry suffix witnesses at different depths are automatically nested;
Kőnig compactness is unnecessary once zero carry has been reached. -/
theorem zeroCarry_suffix_prefix
    {F : Finset (List Bool)}
    (hfirst : ∀ w ∈ F, FirstPassage w)
    {pre left right : List (List Bool)}
    (hleftWords : WordsIn (↑F : Set (List Bool)) left)
    (hrightWords : WordsIn (↑F : Set (List Bool)) right)
    (hleftZero : carrySumFrom pre left = 0)
    (hrightZero : carrySumFrom pre right = 0)
    (hlen : left.length ≤ right.length) :
    left <+: right := by
  have htakeWords : WordsIn (↑F : Set (List Bool))
      (right.take left.length) := by
    intro w hw
    exact hrightWords w (List.mem_of_mem_take hw)
  have hrightExec :=
    (carrySumFrom_eq_zero_iff_executesBlocks pre right).mp hrightZero
  have htakeExec : ExecutesBlocks (right.take left.length) (scheduleTarget pre) :=
    executesBlocks_prefix (List.take_prefix left.length right) hrightExec
  have htakeZero : carrySumFrom pre (right.take left.length) = 0 :=
    (carrySumFrom_eq_zero_iff_executesBlocks pre _).mpr htakeExec
  have htakeLen : (right.take left.length).length = left.length := by
    simp [List.length_take, hlen]
  have heq : left = right.take left.length :=
    zeroCarry_suffix_unique hfirst hleftWords htakeWords hleftZero htakeZero
      htakeLen.symm
  rw [List.prefix_iff_eq_take]
  exact heq

/-- The all-depth zero-carry condition at a prefix is exactly an ordinary
infinite execution from that prefix's canonical endpoint. -/
theorem zeroCarryTail_iff_infiniteExecution
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w)
    (pre : List (List Bool)) :
    (∀ r, ∃ suffix : List (List Bool), suffix.length = r ∧
      WordsIn (↑F : Set (List Bool)) suffix ∧
      carrySumFrom pre suffix = 0) ↔
      InfiniteExecution (↑F : Set (List Bool)) (scheduleTarget pre) := by
  constructor
  · intro htail
    obtain ⟨one, honeLen, honeWords, honeZero⟩ := htail 1
    have honeExec :=
      (carrySumFrom_eq_zero_iff_executesBlocks pre one).mp honeZero
    have hsourcePos : 0 < scheduleTarget pre := by
      cases one with
      | nil => simp at honeLen
      | cons w ws =>
          obtain ⟨middle, hw, _⟩ := honeExec
          exact source_pos_of_executes_firstPassage
            (hfirst w (honeWords w (by simp))) hw
    intro r
    obtain ⟨suffix, hlen, hwords, hzero⟩ := htail r
    exact ⟨hsourcePos, suffix, hlen, hwords,
      (carrySumFrom_eq_zero_iff_executesBlocks pre suffix).mp hzero⟩
  · intro hinfinite r
    obtain ⟨_, suffix, hlen, hwords, hexec⟩ := hinfinite r
    exact ⟨suffix, hlen, hwords,
      (carrySumFrom_eq_zero_iff_executesBlocks pre suffix).mpr hexec⟩

/-- Existential normal form: the zero-carry-tail target is already an
ordinary all-depth seed.  The finite prefix only names that seed. -/
theorem exists_zeroCarryTail_iff_exists_canonicalTarget_infiniteExecution
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ pre : List (List Bool), WordsIn (↑F : Set (List Bool)) pre ∧
      ∀ r, ∃ suffix : List (List Bool), suffix.length = r ∧
        WordsIn (↑F : Set (List Bool)) suffix ∧
        carrySumFrom pre suffix = 0) ↔
      ∃ pre : List (List Bool), WordsIn (↑F : Set (List Bool)) pre ∧
        InfiniteExecution (↑F : Set (List Bool)) (scheduleTarget pre) := by
  constructor <;> rintro ⟨pre, hpreWords, htail⟩
  · exact ⟨pre, hpreWords, (zeroCarryTail_iff_infiniteExecution F hfirst pre).mp htail⟩
  · exact ⟨pre, hpreWords, (zeroCarryTail_iff_infiniteExecution F hfirst pre).mpr htail⟩

/-- Combining carry compactness with its literal semantics: the finite
subcode has some ordinary infinite execution iff one canonical endpoint of a
finite subcode prefix already has such an execution. -/
theorem infiniteExecution_iff_exists_canonicalTarget_infiniteExecution
    (F : Finset (List Bool))
    (hfirst : ∀ w ∈ F, FirstPassage w) :
    (∃ start, InfiniteExecution (↑F : Set (List Bool)) start) ↔
      ∃ pre : List (List Bool), WordsIn (↑F : Set (List Bool)) pre ∧
        InfiniteExecution (↑F : Set (List Bool)) (scheduleTarget pre) := by
  exact (infiniteExecution_iff_exists_zeroCarryTail F hfirst).trans
    (exists_zeroCarryTail_iff_exists_canonicalTarget_infiniteExecution F hfirst)

end

end OutwardZeroCarrySemantics
end KontoroC

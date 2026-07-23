/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCylinderRenewal

/-!
# The odd-source / residue-two target slice

This file proves the exact scalar bijection behind QM158d.  It separates that
cheap arithmetic fact from the harder combinatorial claim that deleting an
initial even bit cannot lower first-passage depth.
-/

namespace KontoroC
namespace OutwardOddSlice

open ShortcutParityPeriodicNoGo OutwardFirstPassage
  OutwardCodeCompactness OutwardBoundaryRenewal

def FirstPassageCode : Set (List Bool) := {w | FirstPassage w}

def RealizesFirstPassageDepth (n x : ℕ) : Prop :=
  RealizesDepth FirstPassageCode n x

/-! ## Multiplicative record chunks -/

def SlopeLT (u v : List Bool) : Prop :=
  3 ^ u.count true * 2 ^ v.length < 3 ^ v.count true * 2 ^ u.length

def RecordOutward (w : List Bool) : Prop :=
  WordOutward w ∧ ∀ u, ProperPrefix u w → SlopeLT u w

theorem slopeLT_append_left_iff (p u v : List Bool) :
    SlopeLT (p ++ u) (p ++ v) ↔ SlopeLT u v := by
  let c := 3 ^ p.count true * 2 ^ p.length
  have hc : 0 < c := by positivity
  rw [SlopeLT, SlopeLT]
  simp only [List.count_append, List.length_append, pow_add]
  convert (Nat.mul_lt_mul_left hc) using 1 <;> dsimp [c] <;> ring

theorem slopeLT_nil_iff_wordOutward (w : List Bool) :
    SlopeLT [] w ↔ WordOutward w := by
  simp [SlopeLT, WordOutward]

theorem firstPassage_recordOutward {w : List Bool} (hw : FirstPassage w) :
    RecordOutward w := by
  refine ⟨hw.1, fun u hu => ?_⟩
  have hnon : 3 ^ u.count true ≤ 2 ^ u.length :=
    Nat.le_of_not_gt (hw.2 u hu)
  have hleft := Nat.mul_le_mul_right (2 ^ w.length) hnon
  have hright := (Nat.mul_lt_mul_right
    (by positivity : 0 < 2 ^ u.length)).2 hw.1
  rw [SlopeLT]
  exact (by
    calc
      3 ^ u.count true * 2 ^ w.length ≤
          2 ^ u.length * 2 ^ w.length := hleft
      _ = 2 ^ w.length * 2 ^ u.length := by ring
      _ < 3 ^ w.count true * 2 ^ u.length := hright)

/-- A nonempty suffix after any prefix cut of a record-outward word remains
record-outward. -/
theorem RecordOutward.suffix {u r : List Bool}
    (hrec : RecordOutward (u ++ r)) (hr : r ≠ []) : RecordOutward r := by
  have hup : ProperPrefix u (u ++ r) := by
    exact ⟨List.prefix_append _ _, by
      intro heq
      have hlen := congrArg List.length heq
      simp at hlen
      exact hr hlen⟩
  have hout : WordOutward r := by
    rw [← slopeLT_nil_iff_wordOutward,
      ← slopeLT_append_left_iff u [] r]
    simpa using hrec.2 u hup
  refine ⟨hout, fun q hq => ?_⟩
  have huq : ProperPrefix (u ++ q) (u ++ r) := by
    obtain ⟨tail, htail⟩ := hq.1
    constructor
    · rw [← htail, ← List.append_assoc]
      exact List.prefix_append (u ++ q) tail
    · intro heq
      exact hq.2 (List.append_cancel_left heq)
  exact (slopeLT_append_left_iff u q r).mp (hrec.2 (u ++ q) huq)

theorem recordChunks_word {chunks : List (List Bool)}
    (hchunks : ∀ w ∈ chunks, RecordOutward w) :
    ∃ words : List (List Bool),
      WordsIn FirstPassageCode words ∧
      chunks.length ≤ words.length ∧
      flattenWords chunks = flattenWords words := by
  cases chunks with
  | nil => exact ⟨[], by simp [WordsIn], by simp, by simp [flattenWords]⟩
  | cons w ws =>
      have hwrec : RecordOutward w := hchunks w (by simp)
      obtain ⟨u, hup, hufirst⟩ := exists_firstPassage_prefix w hwrec.1
      obtain ⟨r, hwr⟩ := hup
      subst w
      have hune : u ≠ [] := firstPassage_ne_nil hufirst
      by_cases hr : r = []
      · subst r
        have htail : ∀ v ∈ ws, RecordOutward v := by
          intro v hv
          exact hchunks v (by simp [hv])
        obtain ⟨words, hwords, hlen, hflat⟩ := recordChunks_word htail
        refine ⟨u :: words, ?_, ?_, ?_⟩
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hufirst
          · exact hwords v hv
        · simp only [List.length_cons]
          omega
        · simp [flattenWords, hflat]
      · have hrrec : RecordOutward r :=
          RecordOutward.suffix hwrec hr
        have hnext : ∀ v ∈ r :: ws, RecordOutward v := by
          intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hrrec
          · exact hchunks v (by simp [hv])
        obtain ⟨words, hwords, hlen, hflat⟩ := recordChunks_word hnext
        refine ⟨u :: words, ?_, ?_, ?_⟩
        · intro v hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hufirst
          · exact hwords v hv
        · simp only [List.length_cons] at hlen ⊢
          omega
        · simp only [flattenWords, List.append_assoc]
          rw [← hflat]
          simp [flattenWords]
termination_by (flattenWords chunks).length
decreasing_by
  · have huPos : 0 < u.length := List.length_pos_iff.mpr hune
    simp_all [flattenWords]
  · have huPos : 0 < u.length := List.length_pos_iff.mpr hune
    have hlen := congrArg List.length hwr
    simp only [List.length_append] at hlen
    simp_all [flattenWords]
    omega

/-! ## Execution adapters for resegmentation -/

theorem executesBlocks_iff_flatten {words : List (List Bool)} {start : ℕ} :
    ExecutesBlocks words start ↔
      ∃ finish, Executes (flattenWords words) start finish := by
  induction words generalizing start with
  | nil =>
      constructor
      · intro _
        exact ⟨start, by simp [flattenWords, Executes]⟩
      · intro _
        trivial
  | cons w words ih =>
      constructor
      · rintro ⟨middle, hw, hrest⟩
        obtain ⟨finish, hflat⟩ := ih.mp hrest
        exact ⟨finish, (executes_append w (flattenWords words)).2
          ⟨middle, hw, hflat⟩⟩
      · rintro ⟨finish, hflat⟩
        obtain ⟨middle, hw, hrest⟩ :=
          (executes_append w (flattenWords words)).1 hflat
        exact ⟨middle, hw, ih.mpr ⟨finish, hrest⟩⟩

theorem executesBlocks_take {words : List (List Bool)} {start n : ℕ}
    (h : ExecutesBlocks words start) :
    ExecutesBlocks (words.take n) start := by
  induction n generalizing words start with
  | zero => simp [ExecutesBlocks]
  | succ n ih =>
      cases words with
      | nil => simp [ExecutesBlocks]
      | cons w words =>
          obtain ⟨middle, hw, hrest⟩ := h
          exact ⟨middle, hw, ih hrest⟩

theorem wordsIn_take {C : Set (List Bool)} {words : List (List Bool)} {n : ℕ}
    (h : WordsIn C words) : WordsIn C (words.take n) := by
  intro w hw
  exact h w (List.mem_of_mem_take hw)

/-- At an even source, literal parity forces the first first-passage word to
start with `false`; deleting that instruction starts the same remaining
execution at the half-source. -/
theorem firstPassage_execution_of_double_source
    {w : List Bool} {source target : ℕ}
    (hfirst : FirstPassage w)
    (hw : Executes w (2 * source) target) :
    ∃ tail : List Bool,
      w = false :: tail ∧ tail ≠ [] ∧ Executes tail source target := by
  cases w with
  | nil => exact (firstPassage_ne_nil hfirst rfl).elim
  | cons bit tail =>
      obtain ⟨middle, hstep, hrest⟩ := hw
      cases bit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          have hmiddle : middle = source := by omega
          subst middle
          have htail : tail ≠ [] := by
            intro hnil
            subst tail
            norm_num [FirstPassage, WordOutward] at hfirst
          exact ⟨tail, rfl, htail, hrest⟩
      | true =>
          simp only [↓reduceIte] at hstep
          omega

/-- The missing odd-part monotonicity lemma in QM158d.  Halving a positive
even source cannot reduce its first-passage depth; the remaining parity word
is resegmented through record-outward chunks. -/
theorem half_realizesFirstPassageDepth {n source : ℕ}
    (hdepth : RealizesFirstPassageDepth n (2 * source)) :
    RealizesFirstPassageDepth n source := by
  have hsource : 0 < source := by
    have := hdepth.1
    omega
  rcases hdepth with ⟨_, words, hlen, hwords, hexec⟩
  cases words with
  | nil =>
      have hn : n = 0 := by simpa using hlen.symm
      subst n
      exact ⟨hsource, [], rfl, by simp [WordsIn], by simp [ExecutesBlocks]⟩
  | cons w words =>
      obtain ⟨middle, hw, hrest⟩ := hexec
      have hfirst : FirstPassage w := hwords w (by simp)
      obtain ⟨tail, hwEq, htail, htailExec⟩ :=
        firstPassage_execution_of_double_source hfirst hw
      have htailRec : RecordOutward tail := by
        have hwRec : RecordOutward (false :: tail) := by
          simpa [hwEq] using firstPassage_recordOutward hfirst
        have hshape : (false :: tail) = [false] ++ tail := by rfl
        rw [hshape] at hwRec
        exact RecordOutward.suffix hwRec htail
      have hrecordChunks : ∀ v ∈ tail :: words, RecordOutward v := by
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact htailRec
        · exact firstPassage_recordOutward (hwords v (by simp [hv]))
      obtain ⟨newWords, hnewWords, hnewLen, hflat⟩ :=
        recordChunks_word hrecordChunks
      have hchunkExec : ExecutesBlocks (tail :: words) source :=
        ⟨middle, htailExec, hrest⟩
      obtain ⟨finish, hflatExec⟩ := executesBlocks_iff_flatten.mp hchunkExec
      have hnewExec : ExecutesBlocks newWords source := by
        apply executesBlocks_iff_flatten.mpr
        exact ⟨finish, by rwa [hflat] at hflatExec⟩
      have hnle : n ≤ newWords.length := by
        have hchunksLen : (tail :: words).length = n := by
          simpa [hwEq] using hlen
        omega
      refine ⟨hsource, newWords.take n, List.length_take_of_le hnle,
        wordsIn_take hnewWords, executesBlocks_take hnewExec⟩

/-- Therefore every least positive depth realizer is odd. -/
theorem least_realizer_odd {n h : ℕ}
    (hh : RealizesFirstPassageDepth n h)
    (hhLeast : ∀ x, RealizesFirstPassageDepth n x → h ≤ x) : Odd h := by
  by_contra hnotOdd
  have heven : Even h := Nat.not_odd_iff_even.mp hnotOdd
  obtain ⟨source, hsourceEq⟩ := heven
  have hhalf : RealizesFirstPassageDepth n source := by
    apply half_realizesFirstPassageDepth
    rw [two_mul, ← hsourceEq]
    exact hh
  have hsourcePos : 0 < source := hhalf.1
  have hle : h ≤ source := hhLeast source hhalf
  rw [hsourceEq] at hle
  omega

/-- Literal odd parity plus first-passage minimality forces the first word to
be `[true]`. -/
theorem firstPassage_execution_of_odd_source_eq_true
    {w : List Bool} {source target : ℕ}
    (hodd : Odd source) (hfirst : FirstPassage w)
    (hw : Executes w source target) :
    w = [true] ∧ 2 * target = 3 * source + 1 := by
  cases w with
  | nil => exact (firstPassage_ne_nil hfirst rfl).elim
  | cons bit tail =>
      obtain ⟨middle, hstep, htail⟩ := hw
      cases bit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          have heven : 2 ∣ source := ⟨middle, hstep.symm⟩
          exact (hodd.not_two_dvd_nat heven).elim
      | true =>
          have ht : tail = [] := firstPassage_cons_true_eq_singleton hfirst
          subst tail
          simp only [Executes] at htail
          subst target
          exact ⟨rfl, by simpa using hstep⟩

/-- Forward half of QM158d: an odd source completing `n+1` blocks begins
with the forced word `[true]` and lands in the residue-two slice at depth
`n`. -/
theorem odd_successor_to_residueTwo {n source : ℕ}
    (hodd : Odd source) (hdepth : RealizesFirstPassageDepth (n + 1) source) :
    ∃ target,
      RealizesFirstPassageDepth n target ∧ target % 3 = 2 ∧
        2 * target = 3 * source + 1 := by
  rcases hdepth with ⟨hsource, ws, hlen, hwords, hexec⟩
  cases ws with
  | nil => simp at hlen
  | cons w ws =>
      obtain ⟨middle, hw, hrest⟩ := hexec
      have hfirst : FirstPassage w := hwords w (by simp)
      obtain ⟨hwEq, hstep⟩ :=
        firstPassage_execution_of_odd_source_eq_true hodd hfirst hw
      have hmiddle : 0 < middle := by omega
      have htailWords : WordsIn FirstPassageCode ws := by
        intro v hv
        exact hwords v (by simp [hv])
      have htailDepth : RealizesFirstPassageDepth n middle := by
        refine ⟨hmiddle, ws, ?_, htailWords, hrest⟩
        simpa [hwEq] using hlen
      have hmod : middle % 3 = 2 := by
        have hc := congrArg (fun z : ℕ => z % 3) hstep
        simp [Nat.add_mod, Nat.mul_mod] at hc
        have hlt := Nat.mod_lt middle (by omega : 0 < 3)
        omega
      exact ⟨middle, htailDepth, hmod, hstep⟩

/-- Reverse half of QM158d: every positive depth-`n` target in class two
modulo three has the positive odd predecessor `(2y-1)/3`, which gains the
forced first-passage word `[true]`. -/
theorem residueTwo_to_odd_successor {n target : ℕ}
    (hdepth : RealizesFirstPassageDepth n target)
    (hmod : target % 3 = 2) :
    let source := (2 * target - 1) / 3
    0 < source ∧ Odd source ∧
      RealizesFirstPassageDepth (n + 1) source ∧
      2 * target = 3 * source + 1 := by
  let source := (2 * target - 1) / 3
  have htarget : 0 < target := hdepth.1
  have hnumDiv : 3 ∣ 2 * target - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hsourceEq : 3 * source = 2 * target - 1 := by
    dsimp [source]
    exact Nat.mul_div_cancel' hnumDiv
  have hsource : 0 < source := by omega
  have hodd : Odd source := by
    rw [Nat.odd_iff]
    have hlt := Nat.mod_lt source (by omega : 0 < 2)
    omega
  have hstep : 2 * target = 3 * source + 1 := by omega
  have honeFirst : FirstPassage [true] := by
    constructor
    · norm_num [WordOutward]
    · intro u hu
      have hlen := properPrefix_length_lt hu
      have hueq : u = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst u
      norm_num [WordOutward]
  have hexecOne : Executes [true] source target := by
    simp only [Executes]
    exact ⟨target, by simpa using hstep, rfl⟩
  rcases hdepth with ⟨_, ws, hlen, hwords, hexec⟩
  have hnewDepth : RealizesFirstPassageDepth (n + 1) source := by
    refine ⟨hsource, [true] :: ws, by simp [hlen], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact honeFirst
      · exact hwords w hw
    · exact ⟨target, hexecOne, hexec⟩
  exact ⟨hsource, hodd, hnewDepth, hstep⟩

/-- Conditional scalar minimum theorem.  Once oddness of the least
depth-`n+1` source is supplied, the residue-two slice formula is forced. -/
theorem least_successor_eq_residueTwo_slice
    {n h m : ℕ}
    (hh : RealizesFirstPassageDepth (n + 1) h)
    (hhOdd : Odd h)
    (hhLeast : ∀ x, RealizesFirstPassageDepth (n + 1) x → h ≤ x)
    (hm : RealizesFirstPassageDepth n m)
    (hmMod : m % 3 = 2)
    (hmLeast : ∀ y, RealizesFirstPassageDepth n y → y % 3 = 2 → m ≤ y) :
    h = (2 * m - 1) / 3 := by
  obtain ⟨y, hyDepth, hyMod, hyEq⟩ := odd_successor_to_residueTwo hhOdd hh
  have hmy : m ≤ y := hmLeast y hyDepth hyMod
  have hs := residueTwo_to_odd_successor hm hmMod
  dsimp only at hs
  rcases hs with ⟨_, _, hsDepth, hsEq⟩
  let s := (2 * m - 1) / 3
  have hhs : h ≤ s := hhLeast s hsDepth
  have hsh : s ≤ h := by
    have hsourceEq : 3 * s = 2 * m - 1 := by omega
    omega
  exact le_antisymm hhs hsh

/-- Full QM158d: oddness is now discharged by the resegmentation theorem. -/
theorem least_successor_eq_residueTwo_slice_unconditional
    {n h m : ℕ}
    (hh : RealizesFirstPassageDepth (n + 1) h)
    (hhLeast : ∀ x, RealizesFirstPassageDepth (n + 1) x → h ≤ x)
    (hm : RealizesFirstPassageDepth n m)
    (hmMod : m % 3 = 2)
    (hmLeast : ∀ y, RealizesFirstPassageDepth n y → y % 3 = 2 → m ≤ y) :
    h = (2 * m - 1) / 3 :=
  least_successor_eq_residueTwo_slice hh (least_realizer_odd hh hhLeast)
    hhLeast hm hmMod hmLeast

end OutwardOddSlice
end KontoroC

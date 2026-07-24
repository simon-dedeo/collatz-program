/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardLiteralMacroOrbit
import KontoroC.OutwardRechargeChain

/-!
# Completeness of the canonical odd-charge recharge map

The invariant bridge proves that an infinite orbit of the canonical recharge
map gives an infinite literal first-passage execution.  This file proves the
converse at a positive odd boundary charge.

The main semantic ingredient is a continuation theorem for the prefix-free
first-passage code: if an infinite literal execution has already executed a
finite certified block prefix, then its exact endpoint again has an infinite
execution.  Applying this to one nontrivial recharge and its complete forced
one-letter drain makes `canonicalRechargeMap` a complete deterministic model,
not merely a sound source of candidate edges.
-/

namespace KontoroC
namespace OutwardCanonicalRechargeCompleteness

open ShortcutParityPeriodicNoGo OutwardCodeCompactness OutwardFiniteHeight
  OutwardFirstPassage OutwardOddSlice OutwardInvariantBridge
  OutwardSemanticAliasNoGo OutwardLiteralMacroOrbit OutwardCylinderRenewal

/-- Removing a certified finite prefix from an infinite execution of the
prefix-free first-passage code leaves an infinite execution at the literal
endpoint of that prefix. -/
theorem infiniteExecution_after_prefix
    {headWords : List (List Bool)} {start middle : ℕ}
    (hinfinite : InfiniteExecution FirstPassageCode start)
    (hprefixWords : WordsIn FirstPassageCode headWords)
    (hprefixExec : ExecutesBlocksTo headWords start middle) :
    InfiniteExecution FirstPassageCode middle := by
  have hstart : 0 < start := (hinfinite 0).1
  have hmiddle : 0 < middle :=
    executes_pos hstart (executesBlocksTo_iff_flatten.mp hprefixExec)
  intro n
  cases n with
  | zero =>
      exact ⟨hmiddle, [], rfl, by simp [WordsIn], by simp [ExecutesBlocks]⟩
  | succ n =>
      obtain ⟨_, full, hfullLength, hfullWords, hfullExec⟩ :=
        hinfinite (headWords.length + (n + 1))
      obtain ⟨finish, hfullTo⟩ :=
        executesBlocks_iff_exists_endpoint.mp hfullExec
      have hprefixFlat := executesBlocksTo_iff_flatten.mp hprefixExec
      have hfullFlat := executesBlocksTo_iff_flatten.mp hfullTo
      have hblockPrefix : headWords <+: full := by
        rcases executes_common_source_comparable hprefixFlat hfullFlat with
            hp | hp
        · exact wordsIn_prefix_of_flatten_prefix
            hprefixWords hfullWords hp
        · have hreverse : full <+: headWords :=
            wordsIn_prefix_of_flatten_prefix hfullWords hprefixWords hp
          have hle := hreverse.length_le
          omega
      obtain ⟨suffix, hsuffix⟩ := hblockPrefix
      have hsuffixLength : suffix.length = n + 1 := by
        rw [← hsuffix] at hfullLength
        simp only [List.length_append] at hfullLength
        omega
      have hsuffixWords : WordsIn FirstPassageCode suffix := by
        intro word hword
        apply hfullWords word
        rw [← hsuffix]
        exact List.mem_append_right headWords hword
      have hconcatTo :
          ExecutesBlocksTo (headWords ++ suffix) start finish := by
        simpa [hsuffix] using hfullTo
      obtain ⟨joining, hprefixTo, hsuffixTo⟩ :=
        (executesBlocksTo_append headWords suffix).mp hconcatTo
      have hjoining : joining = middle :=
        executes_target_unique (flattenWords headWords)
          (executesBlocksTo_iff_flatten.mp hprefixTo)
          (executesBlocksTo_iff_flatten.mp hprefixExec)
      subst joining
      exact ⟨hmiddle, suffix, hsuffixLength, hsuffixWords,
        hsuffixTo.executesBlocks⟩

/-- A first-passage word executed from a positive boundary ends at another
positive boundary. -/
theorem firstPassage_execution_from_boundary_has_boundary_target
    {w : List Bool} {H finish : ℕ}
    (hH : 0 < H) (hfirst : FirstPassage w)
    (hexec : Executes w (3 * H - 1) finish) :
    ∃ K, 0 < K ∧ finish = 3 * K - 1 := by
  let hne := firstPassage_ne_nil hfirst
  let u := w.dropLast
  have hlast := firstPassage_last_eq_true hfirst
  have hdecomp : u ++ [true] = w := by
    calc
      u ++ [true] = u ++ [w.getLast hne] := by rw [hlast]
      _ = w := List.dropLast_append_getLast hne
  rw [← hdecomp] at hexec
  obtain ⟨beforeLast, _, hlastExec⟩ :=
    (executes_append u [true]).mp hexec
  simp only [Executes] at hlastExec
  obtain ⟨target, hstep, hend⟩ := hlastExec
  subst target
  have hfinish : 0 < finish := executes_pos (by omega) hexec
  have hmod : finish % 3 = 2 := by
    have hcongr := congrArg (fun z : ℕ => z % 3) hstep
    simp [Nat.add_mod, Nat.mul_mod] at hcongr
    have hlt := Nat.mod_lt finish (by omega : 0 < 3)
    omega
  have hdiv : 3 ∣ finish + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  let K := (finish + 1) / 3
  have hKmul : 3 * K = finish + 1 := by
    dsimp [K]
    exact Nat.mul_div_cancel' hdiv
  have hK : 0 < K := by omega
  exact ⟨K, hK, by omega⟩

/-- At an odd charge the first executable first-passage word cannot be the
one-letter drain word. -/
theorem first_word_ne_true_of_odd_charge
    {w : List Bool} {H finish : ℕ}
    (hodd : Odd H) (hexec : Executes w (3 * H - 1) finish) :
    w ≠ [true] := by
  intro hword
  subst w
  simp only [Executes] at hexec
  obtain ⟨target, hstep, _⟩ := hexec
  have hstep' : 2 * target = 3 * (3 * H - 1) + 1 := by
    simpa using hstep
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at hstep'
  omega

/-- One infinite execution at a positive odd boundary supplies the next
canonical recharge value, and infinity survives at that exact value. -/
theorem infiniteExecution_has_canonical_step
    {H : ℕ} (hH : 0 < H) (hodd : Odd H)
    (hinfinite : InfiniteExecution FirstPassageCode (3 * H - 1)) :
    ∃ R,
      canonicalRechargeMap H = some R ∧
      InfiniteExecution FirstPassageCode (3 * R - 1) := by
  obtain ⟨_, words, hlength, hwords, hexecBlocks⟩ := hinfinite 1
  cases words with
  | nil => simp at hlength
  | cons w tail =>
      have htail : tail = [] := by
        have : tail.length = 0 := by simpa using hlength
        exact List.eq_nil_of_length_eq_zero this
      subst tail
      obtain ⟨finish, hw, _⟩ := hexecBlocks
      have hfirst : FirstPassage w := hwords w (by simp)
      have hwne : w ≠ [true] := first_word_ne_true_of_odd_charge hodd hw
      obtain ⟨K, hK, hfinish⟩ :=
        firstPassage_execution_from_boundary_has_boundary_target hH hfirst hw
      rw [hfinish] at hw
      let a := padicValNat 2 K
      let u := K.divMaxPow 2
      let R := 3 ^ a * u
      have hrecharge : RechargeThenDrain H R := by
        exact ⟨hH, w, K, hK, hfirst, hwne, hw, rfl⟩
      obtain ⟨macroWords, hmacro⟩ := hrecharge.exists_macro
      refine ⟨R, canonicalRechargeMap_eq_some_iff.mpr hrecharge, ?_⟩
      exact infiniteExecution_after_prefix hinfinite
        hmacro.wordsIn hmacro.executesTo

/-- A canonical odd-charge orbit is an ordinary sequence, not a 2-adic or
symbolic inverse-limit object. -/
def HasInfiniteCanonicalOrbit (H : ℕ) : Prop :=
  ∃ charge : ℕ → ℕ,
    charge 0 = H ∧
    ∀ n, canonicalRechargeMap (charge n) = some (charge (n + 1))

/-- Completeness direction: an infinite literal execution from a positive
odd charge determines an infinite orbit of the canonical partial map. -/
theorem infiniteExecution_gives_canonicalOrbit
    {H : ℕ} (hH : 0 < H) (hodd : Odd H)
    (hinfinite : InfiniteExecution FirstPassageCode (3 * H - 1)) :
    HasInfiniteCanonicalOrbit H := by
  let I : ℕ → Prop := fun K =>
    0 < K ∧ Odd K ∧ InfiniteExecution FirstPassageCode (3 * K - 1)
  have hserial : ∀ s : {K // I K}, ∃ t : {K // I K},
      canonicalRechargeMap s.1 = some t.1 := by
    intro s
    obtain ⟨R, hmap, hRInfinite⟩ :=
      infiniteExecution_has_canonical_step s.2.1 s.2.2.1 s.2.2.2
    have hsemantic := canonicalRechargeMap_eq_some_iff.mp hmap
    have hRodd : Odd R :=
      hsemantic.target_odd_and_three_dvd.1
    have hRpos : 0 < R := by
      obtain ⟨k, hk⟩ := hRodd
      omega
    exact ⟨⟨R, hRpos, hRodd, hRInfinite⟩, hmap⟩
  let next : {K // I K} → {K // I K} := fun s => Classical.choose (hserial s)
  let charge : ℕ → ℕ := fun n => ((next^[n]) ⟨H, hH, hodd, hinfinite⟩).1
  refine ⟨charge, rfl, ?_⟩
  intro n
  have hnext :=
    Classical.choose_spec (hserial ((next^[n]) ⟨H, hH, hodd, hinfinite⟩))
  simpa only [charge, next, Function.iterate_succ_apply'] using hnext

/-- Soundness direction: every canonical-map orbit supplies literal recharge
macros and hence an infinite execution. -/
theorem canonicalOrbit_gives_infiniteExecution
    {H : ℕ} (horbit : HasInfiniteCanonicalOrbit H) :
    InfiniteExecution FirstPassageCode (3 * H - 1) := by
  obtain ⟨charge, hzero, hstep⟩ := horbit
  let words : ℕ → List (List Bool) := fun n =>
    Classical.choose
      (canonicalRechargeMap_eq_some_iff.mp (hstep n)).exists_macro
  have hmacro : ∀ n,
      RechargeMacro (charge n) (charge (n + 1)) (words n) := by
    intro n
    exact Classical.choose_spec
      (canonicalRechargeMap_eq_some_iff.mp (hstep n)).exists_macro
  have hinfinite := orbit_gives_infiniteExecution charge words hmacro
  simpa [hzero] using hinfinite

/-- Exact reduction of the outward counterexample problem at a positive odd
charge to one deterministic partial-map orbit. -/
theorem infiniteExecution_iff_canonicalOrbit
    {H : ℕ} (hH : 0 < H) (hodd : Odd H) :
    InfiniteExecution FirstPassageCode (3 * H - 1) ↔
      HasInfiniteCanonicalOrbit H := by
  exact ⟨infiniteExecution_gives_canonicalOrbit hH hodd,
    canonicalOrbit_gives_infiniteExecution⟩

/-! ## Finite partial-iterate interface -/

/-- The ordinary partial iterates of the canonical recharge map.  A `none`
value records a literal finite obstruction, rather than a failed symbolic
search heuristic. -/
noncomputable def canonicalRechargeIterate : ℕ → ℕ → Option ℕ
  | 0, H => some H
  | n + 1, H =>
      (canonicalRechargeIterate n H).bind canonicalRechargeMap

/-- An infinite canonical orbit makes every finite partial iterate defined,
at exactly the corresponding ordinary charge. -/
theorem canonicalOrbit_gives_iterate_eq_some
    {H : ℕ} {charge : ℕ → ℕ}
    (hzero : charge 0 = H)
    (hstep : ∀ n,
      canonicalRechargeMap (charge n) = some (charge (n + 1))) :
    ∀ n, canonicalRechargeIterate n H = some (charge n) := by
  intro n
  induction n with
  | zero => simp [canonicalRechargeIterate, hzero]
  | succ n ih =>
      simp only [canonicalRechargeIterate, ih, Option.bind_some]
      exact hstep n

/-- Conversely, definedness at every finite depth coheres automatically,
because the canonical relation is a partial function. -/
theorem canonicalOrbit_iff_all_iterates_defined {H : ℕ} :
    HasInfiniteCanonicalOrbit H ↔
      ∀ n, ∃ K, canonicalRechargeIterate n H = some K := by
  constructor
  · rintro ⟨charge, hzero, hstep⟩ n
    exact ⟨charge n,
      canonicalOrbit_gives_iterate_eq_some hzero hstep n⟩
  · intro hdefined
    let charge : ℕ → ℕ := fun n => Classical.choose (hdefined n)
    have hspec : ∀ n,
        canonicalRechargeIterate n H = some (charge n) := fun n =>
      Classical.choose_spec (hdefined n)
    refine ⟨charge, ?_, ?_⟩
    · have hzero := hspec 0
      simp only [canonicalRechargeIterate, Option.some.injEq] at hzero
      exact hzero.symm
    · intro n
      have hnext := hspec (n + 1)
      simp only [canonicalRechargeIterate, hspec n,
        Option.bind_some] at hnext
      exact hnext

/-- Exact finite-definedness formulation of the outward counterexample
problem at a positive odd boundary. -/
theorem infiniteExecution_iff_all_canonicalIterates_defined
    {H : ℕ} (hH : 0 < H) (hodd : Odd H) :
    InfiniteExecution FirstPassageCode (3 * H - 1) ↔
      ∀ n, ∃ K, canonicalRechargeIterate n H = some K := by
  exact (infiniteExecution_iff_canonicalOrbit hH hodd).trans
    canonicalOrbit_iff_all_iterates_defined

/-- One kernel-certified undefined finite iterate rules out infinite outward
first-passage execution from that odd boundary charge. -/
theorem iterate_eq_none_rules_out_infiniteExecution
    {H n : ℕ} (hH : 0 < H) (hodd : Odd H)
    (hnone : canonicalRechargeIterate n H = none) :
    ¬ InfiniteExecution FirstPassageCode (3 * H - 1) := by
  intro hinfinite
  obtain ⟨K, hsome⟩ :=
    (infiniteExecution_iff_all_canonicalIterates_defined hH hodd).mp
      hinfinite n
  rw [hnone] at hsome
  simp at hsome

/-- A canonical orbit reaches the existing Syracuse counterexample endpoint. -/
theorem canonicalOrbit_gives_not_syracuseReachesOne
    {H : ℕ} (horbit : HasInfiniteCanonicalOrbit H) :
    ¬ CleanLean.Collatz.SyracuseReachesOne (3 * H - 1) := by
  exact OutwardCodeCounterexample.not_syracuseReachesOne_of_infiniteExecution
    (fun _ hw => hw.1) (canonicalOrbit_gives_infiniteExecution horbit)

/-- A canonical orbit also refutes the standard unaccelerated Collatz
conjecture through the already audited Syracuse bridge. -/
theorem canonicalOrbit_gives_not_collatz
    {H : ℕ} (horbit : HasInfiniteCanonicalOrbit H) :
    ¬ CleanLean.Collatz.Conjecture := by
  exact OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (fun _ hw => hw.1) (canonicalOrbit_gives_infiniteExecution horbit)

end OutwardCanonicalRechargeCompleteness
end KontoroC

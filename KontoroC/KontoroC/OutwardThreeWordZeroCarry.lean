/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardZeroCarrySemantics
import KontoroC.OutwardWriterDecoderLiteral

/-!
# The exact three-word zero-carry charge map

This module packages the literal arithmetic behind the finite first-passage
alphabet `1`, `011`, `010111`.  It is a reduction, not an existence result:
an infinite orbit of the partial charge map would already be an ordinary
infinite shortcut execution.
-/

namespace KontoroC
namespace OutwardThreeWordZeroCarry

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardFirstPassage OutwardBoundaryRenewal OutwardWriterDecoderLiteral
  OutwardFiniteSubcodeCarry OutwardZeroCarrySemantics

/-- The three branches of the smallest finite alphabet used by the exact
carry worker. -/
inductive Branch
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- Literal first-passage word emitted by a branch. -/
def Branch.word : Branch → List Bool
  | .A => [true]
  | .B => [false, true, true]
  | .C => [false, true, false, true, true, true]

/-- Endpoint-sensitive arithmetic relation on positive boundary charges. -/
def Branch.Step : Branch → ℕ → ℕ → Prop
  | .A, H, H' => 2 * H' = 3 * H
  | .B, H, H' => 8 * H' = 9 * H + 3
  | .C, H, H' => 64 * H' = 81 * H + 63

theorem branch_word_firstPassage (b : Branch) : FirstPassage b.word := by
  cases b with
  | A =>
      constructor
      · norm_num [Branch.word, WordOutward]
      · intro u hu
        have hlen := properPrefix_length_lt hu
        have huNil : u = [] := by
          have : u.length = 0 := by simpa [Branch.word] using hlen
          exact List.eq_nil_of_length_eq_zero this
        subst u
        norm_num [WordOutward]
  | B =>
      constructor
      · norm_num [Branch.word, WordOutward]
      · intro u hu
        have hlen : u.length < 3 := by
          simpa [Branch.word] using properPrefix_length_lt hu
        have hp := hu.1
        rw [List.prefix_iff_eq_take] at hp
        rw [hp]
        have hle : u.length ≤ 2 := by omega
        interval_cases h : u.length <;>
          norm_num [Branch.word, WordOutward] at hlen ⊢
  | C => simpa [Branch.word, writerWord] using writerWord_firstPassage

theorem branchA_base_executes : Executes Branch.A.word 1 2 := by
  norm_num [Branch.word, Executes]

theorem branchB_base_executes : Executes Branch.B.word 6 8 := by
  simp only [Branch.word, Executes]
  exact ⟨3, by norm_num,
    ⟨5, by norm_num,
    ⟨8, by norm_num, rfl⟩⟩⟩

theorem branchC_base_executes : Executes Branch.C.word 18 26 := by
  simpa [Branch.word, writerWord] using writer_base_executes

/-- The branch balance is exactly literal shortcut execution between the
corresponding completed boundary coordinates. -/
theorem branch_step_iff_executes (b : Branch) {H H' : ℕ}
    (hH : 0 < H) (hH' : 0 < H') :
    b.Step H H' ↔ Executes b.word (3 * H - 1) (3 * H' - 1) := by
  cases b with
  | A =>
      constructor
      · intro hbalance
        have hmod : H % 2 = 0 := by
          simp only [Branch.Step] at hbalance
          omega
        let k := H / 2
        have hHform : H = 2 * k := by dsimp [k]; omega
        have hH'form : H' = 3 * k := by
          simp only [Branch.Step] at hbalance
          omega
        have hk : 0 < k := by omega
        simpa [Branch.word, hHform, hH'form] using
          even_boundary_executes_true k hk
      · intro hexec
        have hexact := program_exact Branch.A.word hexec
        norm_num [Branch.word, programData, accumulate, initialData,
          ParityData.step] at hexact
        simp only [Branch.Step]
        omega
  | B =>
      constructor
      · intro hbalance
        let k := H / 8
        have hmod : H % 8 = 5 := by
          simp only [Branch.Step] at hbalance
          omega
        have hHform : H = 8 * k + 5 := by
          dsimp [k]
          omega
        have hH'form : H' = 9 * k + 6 := by
          simp only [Branch.Step] at hbalance
          omega
        have hshift := executes_shift Branch.B.word
          branchB_base_executes (3 * k + 1)
        norm_num [Branch.word] at hshift
        convert hshift using 1 <;>
          simp [Branch.word, hHform, hH'form] <;> omega
      · intro hexec
        have hexact := program_exact Branch.B.word hexec
        norm_num [Branch.word, programData, accumulate, initialData,
          ParityData.step] at hexact
        simp only [Branch.Step]
        omega
  | C =>
      constructor
      · intro hbalance
        let k := H / 64
        have hmod : H % 64 = 49 := by
          simp only [Branch.Step] at hbalance
          omega
        have hHform : H = 64 * k + 49 := by
          dsimp [k]
          omega
        have hH'form : H' = 81 * k + 63 := by
          simp only [Branch.Step] at hbalance
          omega
        have hshift := executes_shift Branch.C.word
          branchC_base_executes (3 * k + 2)
        norm_num [Branch.word] at hshift
        convert hshift using 1 <;>
          simp [Branch.word, hHform, hH'form] <;> omega
      · intro hexec
        have hexact := program_exact Branch.C.word hexec
        norm_num [Branch.word, programData, accumulate, initialData,
          ParityData.step] at hexact
        simp only [Branch.Step]
        omega

/-- Every defined branch strictly increases a positive charge. -/
theorem branch_step_strict {b : Branch} {H H' : ℕ}
    (hH : 0 < H) (hstep : b.Step H H') : H < H' := by
  cases b <;> simp only [Branch.Step] at hstep <;> omega

/-- Exact dyadic domain of each branch. -/
theorem branch_defined_iff (b : Branch) (H : ℕ) :
    (∃ H', b.Step H H') ↔
      match b with
      | .A => H % 2 = 0
      | .B => H % 8 = 5
      | .C => H % 64 = 49 := by
  cases b with
  | A =>
      simp only [Branch.Step]
      constructor
      · rintro ⟨H', h⟩
        omega
      · intro h
        exact ⟨3 * (H / 2), by omega⟩
  | B =>
      simp only [Branch.Step]
      constructor
      · rintro ⟨H', h⟩
        omega
      · intro h
        exact ⟨(9 * H + 3) / 8, by omega⟩
  | C =>
      simp only [Branch.Step]
      constructor
      · rintro ⟨H', h⟩
        omega
      · intro h
        exact ⟨(81 * H + 63) / 64, by omega⟩

/-- At one charge, the three dyadic branch domains are disjoint. -/
theorem branch_unique_of_steps {left right : Branch} {H H₁ H₂ : ℕ}
    (hleft : left.Step H H₁) (hright : right.Step H H₂) :
    left = right := by
  cases left <;> cases right <;>
    simp only [Branch.Step] at hleft hright ⊢ <;> omega

/-- Once the branch is fixed its natural target is unique. -/
theorem target_unique_of_steps {b : Branch} {H H₁ H₂ : ℕ}
    (h₁ : b.Step H H₁) (h₂ : b.Step H H₂) : H₁ = H₂ := by
  cases b <;> simp only [Branch.Step] at h₁ h₂ <;> omega

/-- The relational partial map obtained by forgetting the branch label. -/
def ThreeWordStep (H H' : ℕ) : Prop :=
  ∃ b : Branch, b.Step H H'

/-- The partial map is defined on exactly 41 of the 64 residue classes,
written as its three disjoint variable-length dyadic cylinders. -/
theorem exists_threeWordStep_iff (H : ℕ) :
    (∃ H', ThreeWordStep H H') ↔
      H % 2 = 0 ∨ H % 8 = 5 ∨ H % 64 = 49 := by
  constructor
  · rintro ⟨H', b, hstep⟩
    cases b with
    | A => exact Or.inl ((branch_defined_iff Branch.A H).mp ⟨H', hstep⟩)
    | B => exact Or.inr <| Or.inl ((branch_defined_iff Branch.B H).mp ⟨H', hstep⟩)
    | C => exact Or.inr <| Or.inr ((branch_defined_iff Branch.C H).mp ⟨H', hstep⟩)
  · rintro (hA | hB | hC)
    · obtain ⟨H', hstep⟩ := (branch_defined_iff Branch.A H).mpr hA
      exact ⟨H', Branch.A, hstep⟩
    · obtain ⟨H', hstep⟩ := (branch_defined_iff Branch.B H).mpr hB
      exact ⟨H', Branch.B, hstep⟩
    · obtain ⟨H', hstep⟩ := (branch_defined_iff Branch.C H).mpr hC
      exact ⟨H', Branch.C, hstep⟩

/-- The three-word relation is a partial function. -/
theorem threeWordStep_right_unique {H H₁ H₂ : ℕ}
    (h₁ : ThreeWordStep H H₁) (h₂ : ThreeWordStep H H₂) :
    H₁ = H₂ := by
  obtain ⟨b₁, hb₁⟩ := h₁
  obtain ⟨b₂, hb₂⟩ := h₂
  have heq : b₁ = b₂ := branch_unique_of_steps hb₁ hb₂
  subst b₂
  exact target_unique_of_steps hb₁ hb₂

/-- Every defined transition strictly increases a positive charge. -/
theorem threeWordStep_strict {H H' : ℕ}
    (hH : 0 < H) (hstep : ThreeWordStep H H') : H < H' := by
  obtain ⟨b, hb⟩ := hstep
  exact branch_step_strict hH hb

/-- Literal zero carry at completed boundary endpoints is exactly one step
of the displayed charge relation. -/
theorem extensionCarry_eq_zero_iff_branchStep
    (pre : List (List Bool)) (b : Branch) {H H' : ℕ}
    (hH : 0 < H) (hH' : 0 < H')
    (hsource : scheduleTarget pre = 3 * H - 1)
    (htarget : scheduleTarget (pre ++ [b.word]) = 3 * H' - 1) :
    extensionCarry pre b.word = 0 ↔ b.Step H H' := by
  rw [extensionCarry_eq_zero_iff_executes, hsource, htarget]
  exact (branch_step_iff_executes b hH hH').symm

/-- An infinite orbit grows at least linearly. -/
theorem orbit_charge_add_le
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hpos : 0 < charge 0)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1)))
    (n : ℕ) :
    charge 0 + n ≤ charge n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hbaseLe : charge 0 ≤ charge n := by omega
      have hchargePos : 0 < charge n := hpos.trans_le hbaseLe
      have hlt := branch_step_strict hchargePos (hstep n)
      omega

/-- An infinite positive orbit cannot eventually use only the drain branch
`A`; the genuine recharge branches `B` or `C` occur infinitely often. -/
theorem nonA_branch_times_infinite
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hpos : ∀ n, 0 < charge n)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1))) :
    {n | branch n ≠ Branch.A}.Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  have htailA : ∀ t, branch (M + 1 + t) = Branch.A := by
    intro t
    by_contra hne
    have hmem : M + 1 + t ∈ {n | branch n ≠ Branch.A} := hne
    have := hM _ hmem
    omega
  apply no_positive_repeated_outward_word Branch.A.word
    (by simp [Branch.word]) (branch_word_firstPassage Branch.A).1
  refine ⟨fun t ↦ 3 * charge (M + 1 + t) - 1, ?_, ?_⟩
  · intro t
    have hthree : 3 ≤ 3 * charge (M + 1 + t) :=
      Nat.mul_le_mul_left 3 (hpos _)
    exact Nat.sub_pos_of_lt (by omega)
  · intro t
    have hs := hstep (M + 1 + t)
    rw [htailA t] at hs
    have hexec := (branch_step_iff_executes Branch.A
      (hpos _) (hpos _)).mp hs
    simpa [Nat.add_assoc] using hexec

/-! ## Exact infinite-orbit consumer -/

/-- Set-valued form of the three-word alphabet. -/
def ThreeWordCode : Set (List Bool) :=
  {w | ∃ b : Branch, w = b.word}

theorem threeWordCode_firstPassage {w : List Bool}
    (hw : w ∈ ThreeWordCode) : FirstPassage w := by
  obtain ⟨b, rfl⟩ := hw
  exact branch_word_firstPassage b

/-- First `n` literal words emitted by a labeled charge orbit. -/
def orbitWords (branch : ℕ → Branch) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 => (branch 0).word :: orbitWords (fun t ↦ branch (t + 1)) n

@[simp] theorem orbitWords_length (branch : ℕ → Branch) (n : ℕ) :
    (orbitWords branch n).length = n := by
  induction n generalizing branch with
  | zero => rfl
  | succ n ih => simp [orbitWords, ih]

theorem orbitWords_wordsIn (branch : ℕ → Branch) (n : ℕ) :
    WordsIn ThreeWordCode (orbitWords branch n) := by
  induction n generalizing branch with
  | zero => simp [orbitWords, WordsIn]
  | succ n ih =>
      intro w hw
      simp only [orbitWords, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨branch 0, rfl⟩
      · exact ih (fun t ↦ branch (t + 1)) w hw

/-- Every finite prefix of a charge orbit is a literal block execution. -/
theorem orbitWords_executesBlocks
    (charge : ℕ → ℕ) (branch : ℕ → Branch)
    (hpos : ∀ n, 0 < charge n)
    (hstep : ∀ n, (branch n).Step (charge n) (charge (n + 1)))
    (n : ℕ) :
    ExecutesBlocks (orbitWords branch n) (3 * charge 0 - 1) := by
  induction n generalizing charge branch with
  | zero => simp [orbitWords, ExecutesBlocks]
  | succ n ih =>
      simp only [orbitWords, ExecutesBlocks]
      refine ⟨3 * charge 1 - 1,
        (branch_step_iff_executes (branch 0) (hpos 0) (hpos 1)).mp
          (hstep 0), ?_⟩
      have htail := ih (fun t ↦ charge (t + 1))
        (fun t ↦ branch (t + 1)) (fun t ↦ hpos (t + 1))
        (fun t ↦ by simpa [Nat.add_assoc] using hstep (t + 1))
      simpa using htail

/-- A positive ordinary infinite orbit of the relational charge map. -/
def HasInfiniteThreeWordOrbit (H : ℕ) : Prop :=
  ∃ charge : ℕ → ℕ, ∃ branch : ℕ → Branch,
    charge 0 = H ∧
    (∀ n, 0 < charge n) ∧
    ∀ n, (branch n).Step (charge n) (charge (n + 1))

/-- Constructing one such ordinary charge orbit is already enough to obtain
an infinite execution of the three-word first-passage code. -/
theorem threeWordOrbit_gives_infiniteExecution {H : ℕ}
    (horbit : HasInfiniteThreeWordOrbit H) :
    InfiniteExecution ThreeWordCode (3 * H - 1) := by
  obtain ⟨charge, branch, hzero, hpos, hstep⟩ := horbit
  intro n
  have hstart : 0 < 3 * H - 1 := by
    have hthree : 3 ≤ 3 * H := by
      rw [← hzero]
      exact Nat.mul_le_mul_left 3 (hpos 0)
    exact Nat.sub_pos_of_lt (by omega)
  refine ⟨hstart,
    orbitWords branch n, orbitWords_length branch n,
    orbitWords_wordsIn branch n, ?_⟩
  simpa [hzero] using orbitWords_executesBlocks charge branch hpos hstep n

/-- Conditional counterexample endpoint for the exact three-word map. -/
theorem not_conjecture_of_threeWordOrbit {H : ℕ}
    (horbit : HasInfiniteThreeWordOrbit H) :
    ¬ CleanLean.Collatz.Conjecture := by
  apply OutwardCodeCounterexample.not_conjecture_of_infiniteExecution
    (C := ThreeWordCode)
  · intro w hw
    exact (threeWordCode_firstPassage hw).1
  · exact threeWordOrbit_gives_infiniteExecution horbit

end OutwardThreeWordZeroCarry
end KontoroC

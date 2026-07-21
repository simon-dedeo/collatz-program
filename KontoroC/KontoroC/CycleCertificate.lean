/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ValuationWord

/-!
# Replayable cycle certificates

This file connects a fully accelerated valuation-word cycle to the project's
faithful unaccelerated Collatz conjecture.  The executable checker is merely a
front end: its soundness theorem returns the literal negation of
`CleanLean.Collatz.Conjecture`.
-/

namespace KontoroC

open CleanLean.Collatz

/-- Number of ordinary Collatz steps represented by a valuation word. -/
def ordinaryDuration (ks : List ℕ) : ℕ :=
  (ks.map (fun k => k + 1)).sum

@[simp] theorem ordinaryDuration_nil : ordinaryDuration [] = 0 := rfl

@[simp] theorem ordinaryDuration_cons (k : ℕ) (ks : List ℕ) :
    ordinaryDuration (k :: ks) = (k + 1) + ordinaryDuration ks := by
  simp [ordinaryDuration]

theorem step_iterate_two_pow_mul (k q : ℕ) :
    step^[k] (2 ^ k * q) = q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have hstep : step (2 ^ (k + 1) * q) = 2 ^ k * q := by
        have hfactor : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
          rw [Nat.pow_succ]
          ring
        rw [hfactor]
        simp [step]
      rw [hstep, ih]

/-- One exact fully accelerated instruction is an ordinary odd step followed
by exactly `k` halving steps. -/
theorem step_iterate_instruction {n k : ℕ}
    (h : LegalInstruction n k) :
    step^[k + 1] n = oddStep n := by
  rw [Function.iterate_succ_apply]
  have hnmod : n % 2 = 1 := h.2.1
  have hodd : n % 2 ≠ 0 := by omega
  rw [step_of_odd hodd]
  rw [← legalInstruction_step_equation h]
  exact step_iterate_two_pow_mul k (oddStep n)

/-- A legal valuation word replays exactly under the ordinary Collatz map. -/
theorem step_iterate_ordinaryDuration {x : ℕ} {ks : List ℕ}
    (h : WordLegal x ks) :
    step^[ordinaryDuration ks] x = runWord x ks := by
  induction ks generalizing x with
  | nil => simp
  | cons k ks ih =>
      rw [ordinaryDuration_cons, Nat.add_comm, Function.iterate_add_apply,
        step_iterate_instruction h.1]
      exact ih h.2

theorem ordinaryDuration_pos_of_ne_nil {ks : List ℕ} (hks : ks ≠ []) :
    0 < ordinaryDuration ks := by
  cases ks with
  | nil => exact absurd rfl hks
  | cons k ks => simp

theorem iterate_mul_period {f : ℕ → ℕ} {n p : ℕ}
    (hperiod : f^[p] n = n) (m : ℕ) :
    f^[p * m] n = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hperiod, ih]

/-- The ordinary forward orbit of `1` is the familiar three-cycle. -/
theorem step_iterate_one (j : ℕ) :
    step^[j] 1 = 1 ∨ step^[j] 1 = 4 ∨ step^[j] 1 = 2 := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inl step_one)
      · exact Or.inr (Or.inr step_four)
      · exact Or.inl step_two

/-- A positive odd periodic point that reaches `1` is `1`. -/
theorem odd_periodic_eq_one_of_reachesOne {n p : ℕ}
    (hodd : n % 2 = 1) (hp : 0 < p)
    (hperiod : step^[p] n = n) (hreach : ReachesOne n) : n = 1 := by
  obtain ⟨j, hj⟩ := hreach
  have hmultiple : step^[p * j] n = n := iterate_mul_period hperiod j
  have hjle : j ≤ p * j := Nat.le_mul_of_pos_left j hp
  have hdecomp : p * j = (p * j - j) + j := by omega
  rw [hdecomp, Function.iterate_add_apply, hj] at hmultiple
  rcases step_iterate_one (p * j - j) with h | h | h
  · rw [h] at hmultiple
    exact hmultiple.symm
  · rw [h] at hmultiple
    omega
  · rw [h] at hmultiple
    omega

/-- A nonempty legal accelerated cycle at a positive odd seed other than `1`
is a literal counterexample to the standard Collatz conjecture. -/
theorem not_conjecture_of_legal_cycle {x : ℕ} {ks : List ℕ}
    (hks : ks ≠ []) (hlegal : WordLegal x ks)
    (hclose : runWord x ks = x) (hne : x ≠ 1) :
    ¬Conjecture := by
  cases ks with
  | nil => exact (hks rfl).elim
  | cons k ks =>
      have hx : 0 < x := hlegal.1.1
      have hodd : x % 2 = 1 := hlegal.1.2.1
      have hp : 0 < ordinaryDuration (k :: ks) :=
        ordinaryDuration_pos_of_ne_nil (by simp)
      have hperiod : step^[ordinaryDuration (k :: ks)] x = x :=
        (step_iterate_ordinaryDuration hlegal).trans hclose
      intro hconj
      exact hne (odd_periodic_eq_one_of_reachesOne hodd hp hperiod (hconj x hx))

/-- Portable finite data emitted by a cycle search. -/
structure CycleCertificate where
  seed : ℕ
  word : List ℕ
deriving Repr, DecidableEq

/-- Propositional semantics of a valid nontrivial cycle certificate. -/
def CycleCertificate.Valid (c : CycleCertificate) : Prop :=
  c.word ≠ [] ∧ WordLegal c.seed c.word ∧
    runWord c.seed c.word = c.seed ∧ c.seed ≠ 1

instance CycleCertificate.instDecidableValid (c : CycleCertificate) : Decidable c.Valid := by
  unfold CycleCertificate.Valid
  infer_instance

/-- Executable cycle-certificate checker. -/
def CycleCertificate.check (c : CycleCertificate) : Bool :=
  decide c.Valid

theorem CycleCertificate.valid_of_check {c : CycleCertificate}
    (h : c.check = true) : c.Valid := by
  simpa [CycleCertificate.check] using h

/-- End-to-end soundness of the executable cycle checker. -/
theorem CycleCertificate.not_conjecture_of_check {c : CycleCertificate}
    (h : c.check = true) : ¬Conjecture := by
  obtain ⟨hne, hlegal, hclose, hone⟩ := c.valid_of_check h
  exact not_conjecture_of_legal_cycle hne hlegal hclose hone

/-! ## The portable `collatz-accelerated-cycle-v1` payload -/

/-- Orbit entries stored by the portable certificate, before each step. -/
def orbitValues : ℕ → List ℕ → List ℕ
  | _x, [] => []
  | x, _k :: ks => x :: orbitValues (oddStep x) ks

@[simp] theorem orbitValues_length (x : ℕ) (ks : List ℕ) :
    (orbitValues x ks).length = ks.length := by
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih => simp [orbitValues, ih]

/-- Lean representation of the numerical worker's
`collatz-accelerated-cycle-v1` payload.  All redundant fields are checked
against the word rather than trusted. -/
structure CycleArtifact where
  word : List ℕ
  seed : ℕ
  orbit : List ℕ
  affineConstant : ℕ
  totalHalvings : ℕ
  acceleratedSteps : ℕ
  ordinarySteps : ℕ
deriving Repr, DecidableEq

/-- Exact semantics of every mathematical field in the portable payload. -/
def CycleArtifact.Valid (c : CycleArtifact) : Prop :=
  c.word ≠ [] ∧
  WordLegal c.seed c.word ∧
  runWord c.seed c.word = c.seed ∧
  c.orbit = orbitValues c.seed c.word ∧
  c.affineConstant = affineOffset c.word ∧
  c.totalHalvings = totalValuation c.word ∧
  c.acceleratedSteps = c.word.length ∧
  c.ordinarySteps = ordinaryDuration c.word

instance CycleArtifact.instDecidableValid (c : CycleArtifact) : Decidable c.Valid := by
  unfold CycleArtifact.Valid
  infer_instance

/-- Executable checker for the portable payload after JSON parsing. -/
def CycleArtifact.check (c : CycleArtifact) : Bool :=
  decide c.Valid

/-- The separate disproof gate: validity plus a nontrivial seed. -/
def CycleArtifact.checkNontrivial (c : CycleArtifact) : Bool :=
  c.check && decide (c.seed ≠ 1)

theorem CycleArtifact.valid_of_check {c : CycleArtifact}
    (h : c.check = true) : c.Valid := by
  simpa [CycleArtifact.check] using h

theorem CycleArtifact.not_conjecture_of_checkNontrivial {c : CycleArtifact}
    (h : c.checkNontrivial = true) : ¬Conjecture := by
  have hpairs : c.check = true ∧ decide (c.seed ≠ 1) = true := by
    simpa [CycleArtifact.checkNontrivial, Bool.and_eq_true] using h
  have hvalid := c.valid_of_check hpairs.1
  have hne : c.seed ≠ 1 := of_decide_eq_true hpairs.2
  exact not_conjecture_of_legal_cycle hvalid.1 hvalid.2.1 hvalid.2.2.1 hne

end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardThreeWordZeroCarry
import KontoroC.OutwardCanonicalRechargeCompleteness

/-!
# Reduced positive-carry coordinates for the three-word subcode

This module proves the lossless `(D,c,z)` transition system behind the exact
finite-subcode carry worker.  It contains no finite search result and no
infinite-orbit witness.
-/

namespace KontoroC
namespace OutwardThreeWordReducedState

open ShortcutParityPeriodicNoGo OutwardCodeCompactness OutwardFirstPassage
  OutwardCylinderRenewal OutwardFiniteSubcodeCarry OutwardZeroCarrySemantics
  OutwardThreeWordZeroCarry OutwardCanonicalRechargeCompleteness
  OutwardInvariantBridge OutwardFiniteHeight

noncomputable section

/-- Number of odd shortcut instructions in a block schedule. -/
def scheduleOddCount (u : List (List Bool)) : ℕ :=
  (flattenWords u).count true

theorem scheduleOddCount_append_singleton
    (u : List (List Bool)) (w : List Bool) :
    scheduleOddCount (u ++ [w]) = scheduleOddCount u + w.count true := by
  simp [scheduleOddCount, flattenWords_append, flattenWords]

/-- The canonical execution of an extended schedule reaches this exact
intermediate source before beginning the newly appended word. -/
theorem appended_word_executes_from_shifted_target
    (u : List (List Bool)) (w : List Bool) :
    Executes w
      (scheduleTarget u + 3 ^ scheduleOddCount u * extensionCarry u w)
      (scheduleTarget (u ++ [w])) := by
  let q := extensionCarry u w
  have hprefix : Executes (flattenWords u)
      (scheduleResidue u) (scheduleTarget u) := by
    simpa [scheduleResidue, scheduleTarget] using
      (canonicalExecution_spec (flattenWords u)).2.2
  have hshift := executes_shift (flattenWords u) hprefix q
  have hsource := scheduleResidue_append_singleton u w
  have hshift' : Executes (flattenWords u)
      (scheduleResidue (u ++ [w]))
      (scheduleTarget u + 3 ^ scheduleOddCount u * q) := by
    simpa [q, scheduleLength, scheduleOddCount, hsource] using hshift
  have hfull : Executes (flattenWords (u ++ [w]))
      (scheduleResidue (u ++ [w])) (scheduleTarget (u ++ [w])) := by
    simpa [scheduleResidue, scheduleTarget] using
      (canonicalExecution_spec (flattenWords (u ++ [w]))).2.2
  obtain ⟨middle, hprefix', hword⟩ :=
    (executes_append (flattenWords u) w).mp <| by
      simpa [flattenWords_append, flattenWords] using hfull
  have hmiddle : middle =
      scheduleTarget u + 3 ^ scheduleOddCount u * q :=
    executes_target_unique (flattenWords u) hprefix' hshift'
  simpa [hmiddle] using hword

/-- Arithmetic data retained by the lossless reduced recurrence. -/
structure ReducedState where
  D : ℕ
  c : ℕ
  z : ℕ
  deriving DecidableEq, Repr

namespace ReducedState

/-- The canonical range scale at fixed `D`. -/
def M (s : ReducedState) : ℕ := 3 ^ (s.D - 1)

/-- Boundary charge represented by `(c,z)`. -/
def charge (s : ReducedState) : ℕ := 3 ^ s.c * s.z

/-- Intrinsic state-space conditions. -/
def Valid (s : ReducedState) : Prop :=
  0 < s.D ∧ 0 < s.z ∧ s.z ≤ s.M ∧ ¬3 ∣ s.z

/-- A schedule has exactly the displayed reduced coordinates.  The equation
`Q=D+c` avoids truncated subtraction in the formal interface. -/
def Encodes (u : List (List Bool)) (s : ReducedState) : Prop :=
  s.Valid ∧
  scheduleOddCount u = s.D + s.c ∧
  scheduleTarget u = 3 * s.charge - 1

theorem D_pos {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : 0 < s.D := h.1.1

theorem z_pos {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : 0 < s.z := h.1.2.1

theorem z_le_M {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : s.z ≤ s.M := h.1.2.2.1

theorem three_not_dvd_z {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : ¬3 ∣ s.z := h.1.2.2.2

theorem oddCount_eq {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : scheduleOddCount u = s.D + s.c := h.2.1

theorem target_eq {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : scheduleTarget u = 3 * s.charge - 1 := h.2.2

theorem charge_pos {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) : 0 < s.charge := by
  exact Nat.mul_pos (by positivity) (z_pos h)

/-- The shifted source exposed by the semantic carry lemma is again a
completed boundary, with charge `3^c (z+M*q)`. -/
theorem shiftedTarget_eq_boundary
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) (q : ℕ) :
    scheduleTarget u + 3 ^ scheduleOddCount u * q =
      3 * (3 ^ s.c * (s.z + s.M * q)) - 1 := by
  have hDpos : 0 < s.D := D_pos h
  have hpow : 3 ^ scheduleOddCount u = 3 * (3 ^ s.c * s.M) := by
    rw [oddCount_eq h, show s.D + s.c = s.c + (s.D - 1) + 1 by omega,
      pow_succ, pow_add]
    simp only [M]
    ring
  have hcharge : 0 < s.charge := charge_pos h
  have hcore :
      3 * s.charge + 3 ^ scheduleOddCount u * q =
        3 * (3 ^ s.c * (s.z + s.M * q)) := by
    rw [hpow]
    simp only [charge]
    ring
  rw [target_eq h]
  omega

/-- One appended word executes from the exact reduced-state shifted charge. -/
theorem appended_word_executes
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) (w : List Bool) :
    Executes w
      (3 * (3 ^ s.c * (s.z + s.M * extensionCarry u w)) - 1)
      (scheduleTarget (u ++ [w])) := by
  rw [← shiftedTarget_eq_boundary h (extensionCarry u w)]
  exact appended_word_executes_from_shifted_target u w

/-- The actual child boundary charge and its exact labeled branch equation. -/
theorem extension_has_branchStep
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) (b : Branch) :
    ∃ H', 0 < H' ∧
      scheduleTarget (u ++ [b.word]) = 3 * H' - 1 ∧
      b.Step (3 ^ s.c * (s.z + s.M * extensionCarry u b.word)) H' := by
  have hexec := appended_word_executes h b.word
  have hsourceCharge :
      0 < 3 ^ s.c * (s.z + s.M * extensionCarry u b.word) := by
    apply Nat.mul_pos (by positivity)
    exact Nat.add_pos_left (z_pos h) _
  have hsource :
      0 < 3 * (3 ^ s.c * (s.z + s.M * extensionCarry u b.word)) - 1 := by
    have hthree :
        3 ≤ 3 * (3 ^ s.c * (s.z + s.M * extensionCarry u b.word)) :=
      Nat.mul_le_mul_left 3 hsourceCharge
    exact Nat.sub_pos_of_lt (by omega)
  obtain ⟨H', hH', htarget⟩ :=
    firstPassage_execution_has_boundary_target hsource
      (branch_word_firstPassage b) hexec
  refine ⟨H', hH', htarget, ?_⟩
  apply (branch_step_iff_executes b hsourceCharge hH').mpr
  rw [← htarget]
  exact hexec

/-- Reduced child of the one-letter branch. -/
def stepA (s : ReducedState) (q : ℕ) : ReducedState :=
  ⟨s.D, s.c + 1, (s.z + s.M * q) / 2⟩

/-- Reduced child of the `011` branch. -/
def stepB (s : ReducedState) (q : ℕ) : ReducedState :=
  ⟨s.D + s.c + 1, 1,
    (3 ^ (s.c + 1) * (s.z + s.M * q) + 1) / 8⟩

/-- Reduced child of the `010111` branch. -/
def stepC (s : ReducedState) (q : ℕ) : ReducedState :=
  ⟨s.D + s.c + 2, 2,
    (3 ^ (s.c + 2) * (s.z + s.M * q) + 7) / 64⟩

/-- Cancellation lemma used to prove uniqueness of the newly introduced
dyadic carry digit. -/
theorem affine_mod_unique {modulus base coeff q r residue : ℕ}
    (hcop : Nat.Coprime modulus coeff)
    (hq : (base + coeff * q) % modulus = residue)
    (hr : (base + coeff * r) % modulus = residue)
    (hqLt : q < modulus) (hrLt : r < modulus) :
    r = q := by
  have hmod : base + coeff * q ≡ base + coeff * r [MOD modulus] := by
    rw [Nat.ModEq]
    rw [hq, hr]
  have htail : coeff * q ≡ coeff * r [MOD modulus] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl base) hmod
  have hqr : q ≡ r [MOD modulus] :=
    Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one htail
  exact (hqr.eq_of_lt_of_lt hqLt hrLt).symm

/-- The one-letter extension carry is exactly the parity of `z`. -/
theorem extensionCarry_A_eq_mod_two
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    extensionCarry u Branch.A.word = s.z % 2 := by
  let q := extensionCarry u Branch.A.word
  change q = s.z % 2
  have hq : q < 2 := by
    simpa [q, Branch.word] using extensionCarry_lt_twoPow u Branch.A.word
  obtain ⟨H', _, _, hstep⟩ := extension_has_branchStep h Branch.A
  change Branch.A.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hEvenCharge : 2 ∣ 3 ^ s.c * (s.z + s.M * q) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact (branch_defined_iff Branch.A _).mp ⟨H', hstep⟩
  have hcop : Nat.Coprime 2 (3 ^ s.c) :=
    (by norm_num : Nat.Coprime 2 3).pow_right s.c
  have hEvenInner : 2 ∣ s.z + s.M * q :=
    hcop.dvd_of_dvd_mul_left hEvenCharge
  have hModd : Odd s.M := by
    exact Odd.pow (by norm_num : Odd (3 : ℕ))
  have hMmod : s.M % 2 = 1 := Nat.odd_iff.mp hModd
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hMmod] at hEvenInner
  have hzlt : s.z % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- Complete reduced transition for the one-letter branch. -/
theorem encodes_stepA
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    (stepA s (extensionCarry u Branch.A.word)).Encodes
      (u ++ [Branch.A.word]) := by
  let q := extensionCarry u Branch.A.word
  let child := stepA s q
  change child.Encodes (u ++ [Branch.A.word])
  obtain ⟨H', hH', htarget, hstep⟩ := extension_has_branchStep h Branch.A
  change Branch.A.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hq : q < 2 := by
    simpa [q, Branch.word] using extensionCarry_lt_twoPow u Branch.A.word
  have hdiv : 2 ∣ s.z + s.M * q := by
    have hEvenCharge : 2 ∣ 3 ^ s.c * (s.z + s.M * q) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact (branch_defined_iff Branch.A _).mp ⟨H', hstep⟩
    exact ((by norm_num : Nat.Coprime 2 3).pow_right s.c).dvd_of_dvd_mul_left
      hEvenCharge
  have hzEq : child.z * 2 = s.z + s.M * q := by
    dsimp [child, stepA]
    exact Nat.div_mul_cancel hdiv
  have hchargeEq : H' = child.charge := by
    simp only [Branch.Step] at hstep
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    rw [hstep, ← hzEq]
    simp [child, stepA, charge, pow_succ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨ReducedState.D_pos (s := s) h, ?_, ?_, ?_⟩
    · dsimp [child, stepA] at hH' hchargeEq ⊢
      have : 0 < child.charge := hchargeEq ▸ hH'
      simp only [charge, child, stepA] at this
      exact Nat.pos_of_mul_pos_left this
    · have hzle := z_le_M h
      have hqle : q ≤ 1 := by omega
      have hMq : s.M * q ≤ s.M := by
        simpa using Nat.mul_le_mul_left s.M hqle
      have hsum : s.z + s.M * q ≤ 2 * s.M := by omega
      change (s.z + s.M * q) / 2 ≤ s.M
      apply (Nat.div_le_iff_le_mul (by omega)).2
      omega
    · by_cases hD : 2 ≤ s.D
      · have hMdiv : 3 ∣ s.M := by
          rw [M, show s.D - 1 = (s.D - 2) + 1 by omega, pow_succ]
          exact dvd_mul_left 3 _
        intro hthree
        have hthreeSum : 3 ∣ s.z + s.M * q := by
          rw [← hzEq]
          exact dvd_mul_of_dvd_left hthree 2
        have hthreeMq : 3 ∣ s.M * q := dvd_mul_of_dvd_left hMdiv q
        exact (three_not_dvd_z h) ((Nat.dvd_add_iff_left hthreeMq).mpr hthreeSum)
      · have hDpos := D_pos h
        have hDone : s.D = 1 := by omega
        have hzOne : s.z = 1 := by
          have hzle := z_le_M h
          have hzpos := z_pos h
          simp [M, hDone] at hzle
          omega
        have hqOne : q = 1 := by
          have hqRaw := extensionCarry_A_eq_mod_two h
          change q = s.z % 2 at hqRaw
          simpa [hzOne] using hqRaw
        change ¬3 ∣ child.z
        simp [child, stepA, M, hDone, hzOne, hqOne]
  · rw [scheduleOddCount_append_singleton, oddCount_eq h]
    change s.D + s.c + 1 = child.D + child.c
    simp [child, stepA]
    omega
  · calc
      scheduleTarget (u ++ [Branch.A.word]) = 3 * H' - 1 := htarget
      _ = 3 * child.charge - 1 := by rw [hchargeEq]

/-- The `011` carry is the unique digit below eight placing the shifted
charge in the branch cylinder `5 mod 8`. -/
theorem extensionCarry_B_spec
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    let q := extensionCarry u Branch.B.word
    q < 8 ∧
      (3 ^ s.c * (s.z + s.M * q)) % 8 = 5 ∧
      ∀ r < 8, (3 ^ s.c * (s.z + s.M * r)) % 8 = 5 → r = q := by
  let q := extensionCarry u Branch.B.word
  have hq : q < 8 := by
    simpa [q, Branch.word] using extensionCarry_lt_twoPow u Branch.B.word
  obtain ⟨H', _, _, hstep⟩ := extension_has_branchStep h Branch.B
  change Branch.B.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hdomain : (3 ^ s.c * (s.z + s.M * q)) % 8 = 5 :=
    (branch_defined_iff Branch.B _).mp ⟨H', hstep⟩
  refine ⟨hq, hdomain, ?_⟩
  intro r hr hrdomain
  have hc : Nat.Coprime 8 (3 ^ s.c) :=
    (by norm_num : Nat.Coprime 8 3).pow_right s.c
  have hM : Nat.Coprime 8 s.M := by
    exact (by norm_num : Nat.Coprime 8 3).pow_right (s.D - 1)
  have hcoeff : Nat.Coprime 8 (3 ^ s.c * s.M) := hc.mul_right hM
  apply affine_mod_unique hcoeff (residue := 5) (hqLt := hq) (hrLt := hr)
  · simpa [mul_add, mul_assoc] using hdomain
  · simpa [mul_add, mul_assoc] using hrdomain

/-- Complete reduced transition for `011`. -/
theorem encodes_stepB
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    (stepB s (extensionCarry u Branch.B.word)).Encodes
      (u ++ [Branch.B.word]) := by
  let q := extensionCarry u Branch.B.word
  let child := stepB s q
  change child.Encodes (u ++ [Branch.B.word])
  obtain ⟨H', hH', htarget, hstep⟩ := extension_has_branchStep h Branch.B
  change Branch.B.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hq : q < 8 := (extensionCarry_B_spec h).1
  let N := 3 ^ (s.c + 1) * (s.z + s.M * q) + 1
  have hNform : N = 3 * (3 ^ s.c * (s.z + s.M * q)) + 1 := by
    dsimp [N]
    rw [pow_succ]
    ring
  have hdiv : 8 ∣ N := by
    have hthreeN : 8 ∣ 3 * N := by
      simp only [Branch.Step] at hstep
      refine ⟨H', ?_⟩
      rw [hNform]
      omega
    exact (by norm_num : Nat.Coprime 8 3).dvd_of_dvd_mul_left hthreeN
  have hzEq : child.z * 8 = N := by
    dsimp [child, stepB]
    exact Nat.div_mul_cancel hdiv
  have hchargeEq : H' = child.charge := by
    simp only [Branch.Step] at hstep
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8)
    rw [hstep]
    calc
      9 * (3 ^ s.c * (s.z + s.M * q)) + 3 = 3 * N := by
        rw [hNform]
        ring
      _ = 3 * (child.z * 8) := by rw [hzEq]
      _ = 8 * child.charge := by
        simp [child, stepB, charge]
        ring
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by dsimp [child, stepB]; omega, ?_, ?_, ?_⟩
    · have hchildCharge : 0 < child.charge := hchargeEq ▸ hH'
      dsimp [child, stepB, charge] at hchildCharge ⊢
      exact Nat.pos_of_mul_pos_left hchildCharge
    · have hzle := z_le_M h
      have hqle : q ≤ 7 := by omega
      have hMq : s.M * q ≤ 7 * s.M := by
        have := Nat.mul_le_mul_left s.M hqle
        nlinarith
      have hsum : s.z + s.M * q ≤ 8 * s.M := by omega
      have hDpos := D_pos h
      have hpowM : 3 ^ (s.c + 1) * s.M = child.M := by
        dsimp [child, stepB, M]
        rw [← pow_add]
        congr 1
        omega
      have hNle : N ≤ 8 * child.M + 1 := by
        calc
          N = 3 ^ (s.c + 1) * (s.z + s.M * q) + 1 := rfl
          _ ≤ 3 ^ (s.c + 1) * (8 * s.M) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) 1
          _ = 8 * child.M + 1 := by rw [← hpowM]; ring
      change N / 8 ≤ child.M
      exact (Nat.div_le_iff_le_mul (by omega)).2 (by omega)
    · intro hthree
      obtain ⟨k, hk⟩ := hthree
      rw [hk] at hzEq
      omega
  · rw [scheduleOddCount_append_singleton, oddCount_eq h]
    change s.D + s.c + 2 = child.D + child.c
    simp [child, stepB]
  · calc
      scheduleTarget (u ++ [Branch.B.word]) = 3 * H' - 1 := htarget
      _ = 3 * child.charge - 1 := by rw [hchargeEq]

/-- The `010111` carry is the unique digit below 64 placing the shifted
charge in the branch cylinder `49 mod 64`. -/
theorem extensionCarry_C_spec
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    let q := extensionCarry u Branch.C.word
    q < 64 ∧
      (3 ^ s.c * (s.z + s.M * q)) % 64 = 49 ∧
      ∀ r < 64, (3 ^ s.c * (s.z + s.M * r)) % 64 = 49 → r = q := by
  let q := extensionCarry u Branch.C.word
  have hq : q < 64 := by
    simpa [q, Branch.word] using extensionCarry_lt_twoPow u Branch.C.word
  obtain ⟨H', _, _, hstep⟩ := extension_has_branchStep h Branch.C
  change Branch.C.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hdomain : (3 ^ s.c * (s.z + s.M * q)) % 64 = 49 :=
    (branch_defined_iff Branch.C _).mp ⟨H', hstep⟩
  refine ⟨hq, hdomain, ?_⟩
  intro r hr hrdomain
  have hc : Nat.Coprime 64 (3 ^ s.c) :=
    (by norm_num : Nat.Coprime 64 3).pow_right s.c
  have hM : Nat.Coprime 64 s.M := by
    exact (by norm_num : Nat.Coprime 64 3).pow_right (s.D - 1)
  have hcoeff : Nat.Coprime 64 (3 ^ s.c * s.M) := hc.mul_right hM
  apply affine_mod_unique hcoeff (residue := 49) (hqLt := hq) (hrLt := hr)
  · simpa [mul_add, mul_assoc] using hdomain
  · simpa [mul_add, mul_assoc] using hrdomain

/-- Complete reduced transition for `010111`. -/
theorem encodes_stepC
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) :
    (stepC s (extensionCarry u Branch.C.word)).Encodes
      (u ++ [Branch.C.word]) := by
  let q := extensionCarry u Branch.C.word
  let child := stepC s q
  change child.Encodes (u ++ [Branch.C.word])
  obtain ⟨H', hH', htarget, hstep⟩ := extension_has_branchStep h Branch.C
  change Branch.C.Step (3 ^ s.c * (s.z + s.M * q)) H' at hstep
  have hq : q < 64 := (extensionCarry_C_spec h).1
  let N := 3 ^ (s.c + 2) * (s.z + s.M * q) + 7
  have hNform : N = 9 * (3 ^ s.c * (s.z + s.M * q)) + 7 := by
    dsimp [N]
    rw [show s.c + 2 = s.c + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have hdiv : 64 ∣ N := by
    have hnineN : 64 ∣ 9 * N := by
      simp only [Branch.Step] at hstep
      refine ⟨H', ?_⟩
      rw [hNform]
      omega
    exact (by norm_num : Nat.Coprime 64 9).dvd_of_dvd_mul_left hnineN
  have hzEq : child.z * 64 = N := by
    dsimp [child, stepC]
    exact Nat.div_mul_cancel hdiv
  have hchargeEq : H' = child.charge := by
    simp only [Branch.Step] at hstep
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 64)
    rw [hstep]
    calc
      81 * (3 ^ s.c * (s.z + s.M * q)) + 63 = 9 * N := by
        rw [hNform]
        ring
      _ = 9 * (child.z * 64) := by rw [hzEq]
      _ = 64 * child.charge := by
        simp [child, stepC, charge]
        ring
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by dsimp [child, stepC]; omega, ?_, ?_, ?_⟩
    · have hchildCharge : 0 < child.charge := hchargeEq ▸ hH'
      dsimp [child, stepC, charge] at hchildCharge ⊢
      exact Nat.pos_of_mul_pos_left hchildCharge
    · have hzle := z_le_M h
      have hqle : q ≤ 63 := by omega
      have hMq : s.M * q ≤ 63 * s.M := by
        have := Nat.mul_le_mul_left s.M hqle
        nlinarith
      have hsum : s.z + s.M * q ≤ 64 * s.M := by omega
      have hDpos := D_pos h
      have hpowM : 3 ^ (s.c + 2) * s.M = child.M := by
        dsimp [child, stepC, M]
        rw [← pow_add]
        congr 1
        omega
      have hNle : N ≤ 64 * child.M + 7 := by
        calc
          N = 3 ^ (s.c + 2) * (s.z + s.M * q) + 7 := rfl
          _ ≤ 3 ^ (s.c + 2) * (64 * s.M) + 7 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) 7
          _ = 64 * child.M + 7 := by rw [← hpowM]; ring
      change N / 64 ≤ child.M
      exact (Nat.div_le_iff_le_mul (by omega)).2 (by omega)
    · intro hthree
      obtain ⟨k, hk⟩ := hthree
      rw [hk] at hzEq
      omega
  · rw [scheduleOddCount_append_singleton, oddCount_eq h]
    change s.D + s.c + 4 = child.D + child.c
    simp [child, stepC]
  · calc
      scheduleTarget (u ++ [Branch.C.word]) = 3 * H' - 1 := htarget
      _ = 3 * child.charge - 1 := by rw [hchargeEq]

/-- Uniform transition function, still parameterized by the exact carry. -/
def step : Branch → ReducedState → ℕ → ReducedState
  | .A => stepA
  | .B => stepB
  | .C => stepC

/-- QM174a in one statement. -/
theorem encodes_step
    {u : List (List Bool)} {s : ReducedState}
    (h : s.Encodes u) (b : Branch) :
    (step b s (extensionCarry u b.word)).Encodes (u ++ [b.word]) := by
  cases b with
  | A => exact encodes_stepA h
  | B => exact encodes_stepB h
  | C => exact encodes_stepC h

/-- Exact root coordinates advertised by the reduced worker. -/
def rootState : Branch → ReducedState
  | .A => ⟨1, 0, 1⟩
  | .B => ⟨1, 1, 1⟩
  | .C => ⟨2, 2, 1⟩

theorem canonicalExecution_branch (b : Branch) :
    canonicalExecution b.word =
      match b with
      | .A => (1, 2)
      | .B => (6, 8)
      | .C => (18, 26) := by
  cases b with
  | A =>
      exact (canonicalExecution_unique Branch.A.word (1, 2)
        ⟨by norm_num [Branch.word], by norm_num [Branch.word],
          branchA_base_executes⟩).symm
  | B =>
      exact (canonicalExecution_unique Branch.B.word (6, 8)
        ⟨by norm_num [Branch.word], by norm_num [Branch.word],
          branchB_base_executes⟩).symm
  | C =>
      exact (canonicalExecution_unique Branch.C.word (18, 26)
        ⟨by norm_num [Branch.word], by norm_num [Branch.word],
          branchC_base_executes⟩).symm

theorem rootState_encodes (b : Branch) :
    (rootState b).Encodes [b.word] := by
  cases b with
  | A =>
      have hcanon : canonicalExecution [true] = (1, 2) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.A
      simp [Encodes, Valid, rootState, M, charge, scheduleOddCount,
        scheduleTarget, flattenWords, Branch.word, hcanon]
  | B =>
      have hcanon : canonicalExecution [false, true, true] = (6, 8) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.B
      simp [Encodes, Valid, rootState, M, charge, scheduleOddCount,
        scheduleTarget, flattenWords, Branch.word, hcanon]
  | C =>
      have hcanon :
          canonicalExecution [false, true, false, true, true, true] =
            (18, 26) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.C
      simp [Encodes, Valid, rootState, M, charge, scheduleOddCount,
        scheduleTarget, flattenWords, Branch.word, hcanon]

/-- Exact first carries are `1`, `6`, and `18`; bounded algebraic triples
not obtained this way are not claimed reachable. -/
theorem root_extensionCarry (b : Branch) :
    extensionCarry [] b.word =
      match b with
      | .A => 1
      | .B => 6
      | .C => 18 := by
  cases b with
  | A =>
      have hcanon : canonicalExecution [true] = (1, 2) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.A
      simp [extensionCarry, scheduleResidue, scheduleLength, flattenWords,
        Branch.word, hcanon]
  | B =>
      have hcanon : canonicalExecution [false, true, true] = (6, 8) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.B
      simp [extensionCarry, scheduleResidue, scheduleLength, flattenWords,
        Branch.word, hcanon]
  | C =>
      have hcanon :
          canonicalExecution [false, true, false, true, true, true] =
            (18, 26) := by
        simpa [Branch.word] using canonicalExecution_branch Branch.C
      simp [extensionCarry, scheduleResidue, scheduleLength, flattenWords,
        Branch.word, hcanon]

/-! ## Exact infinite-orbit equivalence for the concrete subcode -/

/-- Removing one known first-passage block from an infinite execution leaves
an infinite execution in the same subcode at its literal endpoint. -/
theorem infiniteExecution_after_first
    {C : Set (List Bool)}
    (hfirst : ∀ w ∈ C, FirstPassage w)
    {w : List Bool} {start middle : ℕ}
    (hwC : w ∈ C) (hw : Executes w start middle)
    (hinfinite : InfiniteExecution C start) :
    InfiniteExecution C middle := by
  have hstart : 0 < start := (hinfinite 0).1
  have hmiddle : 0 < middle := executes_pos hstart hw
  intro n
  obtain ⟨_, full, hlen, hwords, hexec⟩ := hinfinite (n + 1)
  cases full with
  | nil => simp at hlen
  | cons v vs =>
      obtain ⟨next, hv, hvs⟩ := hexec
      have hvC : v ∈ C := hwords v (by simp)
      have hvEq : v = w :=
        firstPassage_eq_of_common_source (hfirst v hvC) (hfirst w hwC) hv hw
      subst v
      have hnext : next = middle := executes_target_unique w hv hw
      subst next
      have hvsWords : WordsIn C vs := by
        intro z hz
        exact hwords z (by simp [hz])
      exact ⟨hmiddle, vs, by simpa using hlen, hvsWords, hvs⟩

/-- One infinite execution at a positive completed boundary supplies the next
labeled charge step, and infinity survives at its endpoint. -/
theorem infiniteExecution_has_threeWordStep
    {H : ℕ} (hH : 0 < H)
    (hinfinite : InfiniteExecution ThreeWordCode (3 * H - 1)) :
    ∃ (b : Branch) (H' : ℕ), b.Step H H' ∧
      InfiniteExecution ThreeWordCode (3 * H' - 1) := by
  obtain ⟨_, words, hlen, hwords, hexec⟩ := hinfinite 1
  cases words with
  | nil => simp at hlen
  | cons w tail =>
      have htail : tail = [] := by
        have : tail.length = 0 := by simpa using hlen
        exact List.eq_nil_of_length_eq_zero this
      subst tail
      obtain ⟨middle, hw, _⟩ := hexec
      obtain ⟨b, hword⟩ := hwords w (by simp)
      subst w
      obtain ⟨H', hH', htarget⟩ :=
        firstPassage_execution_from_boundary_has_boundary_target hH
          (branch_word_firstPassage b) hw
      rw [htarget] at hw
      refine ⟨b, H',
        (branch_step_iff_executes b hH hH').mpr hw, ?_⟩
      exact infiniteExecution_after_first
        (fun z hz ↦ threeWordCode_firstPassage hz)
        ⟨b, rfl⟩ hw hinfinite

/-- Completeness direction for the charge map: literal infinity determines
an ordinary `Nat` charge orbit and a labeled branch stream. -/
theorem infiniteExecution_gives_threeWordOrbit
    {H : ℕ} (hH : 0 < H)
    (hinfinite : InfiniteExecution ThreeWordCode (3 * H - 1)) :
    HasInfiniteThreeWordOrbit H := by
  let I : ℕ → Prop := fun K ↦
    0 < K ∧ InfiniteExecution ThreeWordCode (3 * K - 1)
  have hserial : ∀ s : {K // I K},
      ∃ t : {K // I K}, ∃ b : Branch, b.Step s.1 t.1 := by
    intro s
    obtain ⟨b, H', hstep, htail⟩ :=
      infiniteExecution_has_threeWordStep s.2.1 s.2.2
    have hH' : 0 < H' := by
      have := (htail 0).1
      omega
    exact ⟨⟨H', hH', htail⟩, b, hstep⟩
  let next : {K // I K} → {K // I K} := fun s ↦ Classical.choose (hserial s)
  let label : {K // I K} → Branch := fun s ↦
    Classical.choose (Classical.choose_spec (hserial s))
  let initial : {K // I K} := ⟨H, hH, hinfinite⟩
  let charge : ℕ → ℕ := fun n ↦ ((next^[n]) initial).1
  let branch : ℕ → Branch := fun n ↦ label ((next^[n]) initial)
  refine ⟨charge, branch, rfl, ?_, ?_⟩
  · intro n
    exact ((next^[n]) initial).2.1
  · intro n
    have hspec := Classical.choose_spec
      (Classical.choose_spec (hserial ((next^[n]) initial)))
    simpa only [charge, branch, label, next, Function.iterate_succ_apply'] using hspec

/-- At a positive boundary, the three-word charge map is exactly equivalent
to literal infinite execution. -/
theorem infiniteExecution_iff_threeWordOrbit
    {H : ℕ} (hH : 0 < H) :
    InfiniteExecution ThreeWordCode (3 * H - 1) ↔
      HasInfiniteThreeWordOrbit H := by
  exact ⟨infiniteExecution_gives_threeWordOrbit hH,
    threeWordOrbit_gives_infiniteExecution⟩

/-- Concrete finite alphabet used in QM174. -/
def threeWordFinset : Finset (List Bool) :=
  {Branch.A.word, Branch.B.word, Branch.C.word}

theorem threeWordFinset_coe :
    (↑threeWordFinset : Set (List Bool)) = ThreeWordCode := by
  ext w
  constructor
  · intro hw
    have hw' : w = Branch.A.word ∨ w = Branch.B.word ∨
        w = Branch.C.word := by
      simpa [threeWordFinset] using hw
    rcases hw' with hA | hB | hC
    · exact ⟨Branch.A, hA⟩
    · exact ⟨Branch.B, hB⟩
    · exact ⟨Branch.C, hC⟩
  · rintro ⟨b, rfl⟩
    cases b <;> simp [threeWordFinset]

theorem threeWordFinset_firstPassage
    (w : List Bool) (hw : w ∈ threeWordFinset) : FirstPassage w := by
  apply threeWordCode_firstPassage
  rw [← threeWordFinset_coe]
  exact hw

theorem scheduleTarget_nil : scheduleTarget [] = 0 := by
  have hcanon : canonicalExecution [] = (0, 0) :=
    (canonicalExecution_unique [] (0, 0)
      ⟨by norm_num, by norm_num, by simp [Executes]⟩).symm
  simp [scheduleTarget, flattenWords, hcanon]

/-- A nonempty first-passage prefix has a positive completed-boundary target. -/
theorem scheduleTarget_eq_boundary_of_nonempty
    {pre : List (List Bool)} (hne : pre ≠ [])
    (hwords : WordsIn ThreeWordCode pre) :
    ∃ H, 0 < H ∧ scheduleTarget pre = 3 * H - 1 := by
  rcases List.eq_nil_or_concat pre with hnil | ⟨head, w, rfl⟩
  · exact (hne hnil).elim
  · have hfull : Executes (flattenWords (head.concat w))
        (scheduleResidue (head.concat w)) (scheduleTarget (head.concat w)) := by
      simpa [scheduleResidue, scheduleTarget] using
        (canonicalExecution_spec (flattenWords (head.concat w))).2.2
    obtain ⟨middle, _, hw⟩ :=
      (executes_append (flattenWords head) w).mp <| by
        simpa [List.concat_eq_append, flattenWords_append, flattenWords] using hfull
    have hwC : w ∈ ThreeWordCode := hwords w (by simp)
    have hw' : Executes w middle (scheduleTarget (head.concat w)) := by
      simpa [List.concat_eq_append] using hw
    have hsource : 0 < middle :=
      source_pos_of_executes_firstPassage (threeWordCode_firstPassage hwC) hw'
    exact firstPassage_execution_has_boundary_target hsource
      (threeWordCode_firstPassage hwC) hw'

/-- QM174c.  Any infinite execution in the finite subcode is equivalent to
finite canonical reachability of one positive ordinary orbit of QM174b. -/
theorem exists_infiniteExecution_iff_reaches_threeWordOrbit :
    (∃ start, InfiniteExecution (↑threeWordFinset : Set (List Bool)) start) ↔
      ∃ pre H,
        WordsIn (↑threeWordFinset : Set (List Bool)) pre ∧
        0 < H ∧ scheduleTarget pre = 3 * H - 1 ∧
        HasInfiniteThreeWordOrbit H := by
  constructor
  · intro hinfinite
    obtain ⟨pre, hpreWords, htail⟩ :=
      (infiniteExecution_iff_exists_canonicalTarget_infiniteExecution
        threeWordFinset threeWordFinset_firstPassage).mp hinfinite
    have htargetPos : 0 < scheduleTarget pre := (htail 0).1
    have hpreNe : pre ≠ [] := by
      intro hnil
      subst pre
      rw [scheduleTarget_nil] at htargetPos
      omega
    have hpreWordsCode : WordsIn ThreeWordCode pre := by
      rw [← threeWordFinset_coe]
      exact hpreWords
    obtain ⟨H, hH, htarget⟩ :=
      scheduleTarget_eq_boundary_of_nonempty hpreNe hpreWordsCode
    have htailCode : InfiniteExecution ThreeWordCode (3 * H - 1) := by
      rw [← htarget, ← threeWordFinset_coe]
      exact htail
    exact ⟨pre, H, hpreWords, hH, htarget,
      infiniteExecution_gives_threeWordOrbit hH htailCode⟩
  · rintro ⟨pre, H, hpreWords, hH, htarget, horbit⟩
    refine ⟨3 * H - 1, ?_⟩
    rw [threeWordFinset_coe]
    exact threeWordOrbit_gives_infiniteExecution horbit

end ReducedState

end

end OutwardThreeWordReducedState
end KontoroC

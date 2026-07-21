/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.OscillationIdentity

/-!
# Concrete coordinates for the finite KL residue system

A level-`k` state `m = 2 (mod 3)` is written uniquely as `m = 2 + 3s`, with
`s : ZMod (3^(k-1))`.  In this coordinate the transport `m -> 4m` is the
affine permutation `s -> 4s + 2`, and the three branch classes are simply the
value of `s` modulo three.

The definitions below deliberately expose all uses of representatives in the
digit-losing refinement maps.  The next lemmas in this module will prove that
the resulting branch targets and fibers agree with the original residue
formulas.
-/

namespace CleanLean.KL

namespace ResidueSystem

/-- State coordinates at precision `3^k`. -/
abbrev State (k : ℕ) := ZMod (3 ^ (k - 1))

/-- Coarse coordinates after one 3-adic digit has been lost. -/
abbrev Coarse (k : ℕ) := ZMod (3 ^ (k - 2))

@[simp] theorem card_state (k : ℕ) : Fintype.card (State k) = 3 ^ (k - 1) :=
  ZMod.card _

@[simp] theorem card_coarse (k : ℕ) : Fintype.card (Coarse k) = 3 ^ (k - 2) :=
  ZMod.card _

theorem four_coprime_three_pow (n : ℕ) : Nat.Coprime 4 (3 ^ n) := by
  exact (by norm_num : Nat.Coprime 4 3).pow_right n

/-- The affine transport `s -> 4s + 2` is a permutation because four is a
unit modulo every power of three. -/
def transport (k : ℕ) : State k ≃ State k := by
  let u : (ZMod (3 ^ (k - 1)))ˣ :=
    ZMod.unitOfCoprime 4 (four_coprime_three_pow (k - 1))
  exact
    { toFun := fun s => (u : ZMod (3 ^ (k - 1))) * s + 2
      invFun := fun s => (↑(u⁻¹) : ZMod (3 ^ (k - 1))) * (s - 2)
      left_inv := by
        intro s
        simp
      right_inv := by
        intro s
        simp [mul_sub] }

@[simp] theorem transport_apply (k : ℕ) (s : State k) :
    transport k s = 4 * s + 2 := by
  simp [transport, ZMod.coe_unitOfCoprime]

/-- In the original residue representative `m = 2+3s`, the affine coordinate
transport is exactly multiplication by four modulo `3^k`. -/
theorem transport_residue_modEq (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    2 + 3 * (transport k s).val ≡ 4 * (2 + 3 * s.val) [MOD 3 ^ k] := by
  let n := 3 ^ (k - 1)
  have heqz :
      ((transport k s).val : ZMod n) = ((4 * s.val + 2 : ℕ) : ZMod n) := by
    calc
      ((transport k s).val : ZMod n) = transport k s := ZMod.natCast_zmod_val _
      _ = 4 * s + 2 := transport_apply k s
      _ = ((4 * s.val + 2 : ℕ) : ZMod n) := by
        rw [← ZMod.natCast_zmod_val s]
        norm_num
  have hcoord :
      (transport k s).val ≡ 4 * s.val + 2 [MOD n] :=
    (ZMod.natCast_eq_natCast_iff _ _ n).1 heqz
  have hscaled := hcoord.mul_left' 3
  have hadd := hscaled.add_left 2
  have hpow : 3 * n = 3 ^ k := by
    have hsub : k = (k - 1) + 1 := by omega
    calc
      3 * n = 3 * 3 ^ (k - 1) := rfl
      _ = 3 ^ ((k - 1) + 1) := by rw [pow_succ']
      _ = 3 ^ k := by rw [← hsub]
  rw [hpow] at hadd
  convert hadd using 1
  all_goals ring

/-- Branch type in the coordinate `m = 2 + 3s`: digits `0,1,2` correspond
to residues `2,5,8 (mod 9)`. -/
def branch (k : ℕ) (s : State k) : Branch :=
  match s.val % 3 with
  | 0 => .retarded
  | 1 => .neutral
  | _ => .advanced

@[simp] theorem branch_zero (k : ℕ) : branch k 0 = .retarded := by
  simp [branch]

theorem branch_eq_retarded_iff (k : ℕ) (s : State k) :
    branch k s = .retarded ↔ s.val % 3 = 0 := by
  generalize hq : s.val % 3 = q
  have hlt : q < 3 := by
    rw [← hq]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases q <;> simp [branch, hq]

theorem branch_eq_neutral_iff (k : ℕ) (s : State k) :
    branch k s = .neutral ↔ s.val % 3 = 1 := by
  generalize hq : s.val % 3 = q
  have hlt : q < 3 := by
    rw [← hq]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases q <;> simp [branch, hq]

theorem branch_eq_advanced_iff (k : ℕ) (s : State k) :
    branch k s = .advanced ↔ s.val % 3 = 2 := by
  generalize hq : s.val % 3 = q
  have hlt : q < 3 := by
    rw [← hq]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases q <;> simp [branch, hq]

/-- The coordinate branch digit agrees with the original residue `m = 2+3s`
modulo nine. -/
theorem branch_eq_retarded_iff_residue (k : ℕ) (s : State k) :
    branch k s = .retarded ↔ (2 + 3 * s.val) % 9 = 2 := by
  rw [branch_eq_retarded_iff]
  have hdiv3 := Nat.mod_add_div s.val 3
  have hdiv9 := Nat.mod_add_div (2 + 3 * s.val) 9
  constructor <;> omega

theorem branch_eq_neutral_iff_residue (k : ℕ) (s : State k) :
    branch k s = .neutral ↔ (2 + 3 * s.val) % 9 = 5 := by
  rw [branch_eq_neutral_iff]
  have hdiv3 := Nat.mod_add_div s.val 3
  have hdiv9 := Nat.mod_add_div (2 + 3 * s.val) 9
  constructor <;> omega

theorem branch_eq_advanced_iff_residue (k : ℕ) (s : State k) :
    branch k s = .advanced ↔ (2 + 3 * s.val) % 9 = 8 := by
  rw [branch_eq_advanced_iff]
  have hdiv3 := Nat.mod_add_div s.val 3
  have hdiv9 := Nat.mod_add_div (2 + 3 * s.val) 9
  constructor <;> omega

/-- A chosen representative for the coarse retarded target.  On the retarded
branch, `s.val` is divisible by three and this is the coordinate of
`(4m-2)/3`.  Values off that branch are immaterial to the operator. -/
def retardedTarget (k : ℕ) (s : State k) : Coarse k :=
  (4 * (s.val / 3) : ℕ)

/-- A chosen representative for the coarse advanced target.  On the advanced
branch, write `s.val = 3q+2`; then this is `1+2q`, the coordinate of
`(2m-1)/3`.  Values off that branch are immaterial to the operator. -/
def advancedTarget (k : ℕ) (s : State k) : Coarse k :=
  (1 + 2 * (s.val / 3) : ℕ)

/-- Before reduction modulo the coarse power of three, the retarded target
coordinate is exactly the quotient of `(4m-2)/3` when `m=2+3s`. -/
theorem retarded_target_numerator (k : ℕ) (s : State k)
    (hs : branch k s = .retarded) :
    4 * (2 + 3 * s.val) - 2 =
      3 * (2 + 3 * (4 * (s.val / 3))) := by
  have hmod : s.val % 3 = 0 := (branch_eq_retarded_iff k s).1 hs
  have hdiv := Nat.mod_add_div s.val 3
  omega

/-- Before reduction modulo the coarse power of three, the advanced target
coordinate is exactly the quotient of `(2m-1)/3` when `m=2+3s`. -/
theorem advanced_target_numerator (k : ℕ) (s : State k)
    (hs : branch k s = .advanced) :
    2 * (2 + 3 * s.val) - 1 =
      3 * (2 + 3 * (1 + 2 * (s.val / 3))) := by
  have hmod : s.val % 3 = 2 := (branch_eq_advanced_iff k s).1 hs
  have hdiv := Nat.mod_add_div s.val 3
  omega

/-- The branch-dependent coarse refinement target. -/
def refinementTarget (k : ℕ) (s : State k) : Coarse k :=
  match branch k s with
  | .retarded => retardedTarget k s
  | .neutral => 0
  | .advanced => advancedTarget k s

/-- The three level-`k` lifts of a level-`k-1` coarse coordinate. -/
def fiber (k : ℕ) (r : Coarse k) (j : Fin 3) : State k :=
  (r.val + j.val * 3 ^ (k - 2) : ℕ)

theorem three_pow_level (k : ℕ) (hk : 2 ≤ k) :
    3 ^ (k - 1) = 3 * 3 ^ (k - 2) := by
  have hsub : k - 1 = (k - 2) + 1 := by omega
  rw [hsub, pow_succ]
  ring

/-- The chosen three lifts have the displayed canonical representatives. -/
theorem fiber_val (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) (j : Fin 3) :
    (fiber k r j).val = r.val + j.val * 3 ^ (k - 2) := by
  have hr : r.val < 3 ^ (k - 2) := ZMod.val_lt r
  have hp : 0 < 3 ^ (k - 2) := pow_pos (by norm_num) _
  have hlevel := three_pow_level k hk
  fin_cases j <;>
    apply ZMod.val_natCast_of_lt <;>
    nlinarith

/-- The lift coordinate is genuinely a three-element fiber. -/
theorem fiber_injective (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    Function.Injective (fiber k r) := by
  intro i j hij
  have hv := congrArg ZMod.val hij
  rw [fiber_val k hk r i, fiber_val k hk r j] at hv
  have hp : 0 < 3 ^ (k - 2) := pow_pos (by norm_num) _
  apply Fin.ext
  nlinarith

/-- Taken together, the coarse coordinate and the lift digit identify a fine
state uniquely.  This is stronger than injectivity within one fiber and is
the fact needed by the oscillation identity. -/
theorem fiberPair_injective (k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (fun p : Coarse k × Fin 3 => fiber k p.1 p.2) := by
  rintro ⟨r, i⟩ ⟨s, j⟩ hij
  have hv := congrArg ZMod.val hij
  rw [fiber_val k hk r i, fiber_val k hk s j] at hv
  have hr : r.val < 3 ^ (k - 2) := ZMod.val_lt r
  have hs : s.val < 3 ^ (k - 2) := ZMod.val_lt s
  have hp : 0 < 3 ^ (k - 2) := pow_pos (by norm_num) _
  have hrsVal : r.val = s.val := by
    calc
      r.val = (r.val + i.val * 3 ^ (k - 2)) % 3 ^ (k - 2) := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      _ = (s.val + j.val * 3 ^ (k - 2)) % 3 ^ (k - 2) := by rw [hv]
      _ = s.val := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hmul : i.val * 3 ^ (k - 2) = j.val * 3 ^ (k - 2) := by
    omega
  have hijVal : i.val = j.val := Nat.mul_right_cancel hp hmul
  have hrs : r = s := ZMod.val_injective _ hrsVal
  have hij' : i = j := Fin.ext hijVal
  simp [hrs, hij']

theorem card_coarse_prod_three (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Coarse k × Fin 3) = Fintype.card (State k) := by
  rw [Fintype.card_prod, card_coarse, Fintype.card_fin, card_state]
  rw [three_pow_level k hk]
  ring

/-- The top-digit fiber decomposition as an actual finite equivalence. -/
noncomputable def fiberEquiv (k : ℕ) (hk : 2 ≤ k) : Coarse k × Fin 3 ≃ State k :=
  Equiv.ofBijective (fun p => fiber k p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fiberPair_injective k hk, card_coarse_prod_three k hk⟩)

/-- The alternative decomposition by the *low* base-three digit.  It is used
to count the retarded/neutral/advanced branch classes. -/
def lowDigit (k : ℕ) (r : Coarse k) (j : Fin 3) : State k :=
  (3 * r.val + j.val : ℕ)

theorem lowDigit_val (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) (j : Fin 3) :
    (lowDigit k r j).val = 3 * r.val + j.val := by
  have hr : r.val < 3 ^ (k - 2) := ZMod.val_lt r
  have hp : 0 < 3 ^ (k - 2) := pow_pos (by norm_num) _
  have hlevel := three_pow_level k hk
  apply ZMod.val_natCast_of_lt
  rw [hlevel]
  have hj : j.val < 3 := j.isLt
  omega

theorem lowDigitPair_injective (k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (fun p : Coarse k × Fin 3 => lowDigit k p.1 p.2) := by
  rintro ⟨r, i⟩ ⟨s, j⟩ hij
  have hv := congrArg ZMod.val hij
  rw [lowDigit_val k hk r i, lowDigit_val k hk s j] at hv
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hrsVal : r.val = s.val := by omega
  have hijVal : i.val = j.val := by omega
  have hrs : r = s := ZMod.val_injective _ hrsVal
  have hij' : i = j := Fin.ext hijVal
  simp [hrs, hij']

/-- Branch classes really are the three low-digit slices. -/
theorem branch_lowDigit (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) (j : Fin 3) :
    branch k (lowDigit k r j) =
      match j.val with
      | 0 => .retarded
      | 1 => .neutral
      | _ => .advanced := by
  rw [branch]
  rw [lowDigit_val k hk]
  fin_cases j <;> simp

@[simp] theorem branch_lowDigit_zero (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    branch k (lowDigit k r 0) = .retarded := by
  simpa using branch_lowDigit k hk r 0

@[simp] theorem branch_lowDigit_one (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    branch k (lowDigit k r 1) = .neutral := by
  simpa using branch_lowDigit k hk r 1

@[simp] theorem branch_lowDigit_two (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    branch k (lowDigit k r 2) = .advanced := by
  simpa using branch_lowDigit k hk r 2

noncomputable def lowDigitEquiv (k : ℕ) (hk : 2 ≤ k) :
    Coarse k × Fin 3 ≃ State k :=
  Equiv.ofBijective (fun p => lowDigit k p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨lowDigitPair_injective k hk, card_coarse_prod_three k hk⟩)

/-- Multiplication by four on the coarse quotient. -/
def coarseMulFour (k : ℕ) : Coarse k ≃ Coarse k := by
  let u : (ZMod (3 ^ (k - 2)))ˣ :=
    ZMod.unitOfCoprime 4 (four_coprime_three_pow (k - 2))
  exact
    { toFun := fun r => (u : ZMod (3 ^ (k - 2))) * r
      invFun := fun r => (↑(u⁻¹) : ZMod (3 ^ (k - 2))) * r
      left_inv := by intro r; simp
      right_inv := by intro r; simp }

@[simp] theorem coarseMulFour_apply (k : ℕ) (r : Coarse k) :
    coarseMulFour k r = 4 * r := by
  simp [coarseMulFour, ZMod.coe_unitOfCoprime]

theorem two_coprime_three_pow (n : ℕ) : Nat.Coprime 2 (3 ^ n) := by
  exact (by norm_num : Nat.Coprime 2 3).pow_right n

/-- The advanced target map `r ↦ 1+2r` is also a coarse permutation. -/
def coarseAffineTwo (k : ℕ) : Coarse k ≃ Coarse k := by
  let u : (ZMod (3 ^ (k - 2)))ˣ :=
    ZMod.unitOfCoprime 2 (two_coprime_three_pow (k - 2))
  exact
    { toFun := fun r => 1 + (u : ZMod (3 ^ (k - 2))) * r
      invFun := fun r => (↑(u⁻¹) : ZMod (3 ^ (k - 2))) * (r - 1)
      left_inv := by intro r; simp
      right_inv := by intro r; simp }

@[simp] theorem coarseAffineTwo_apply (k : ℕ) (r : Coarse k) :
    coarseAffineTwo k r = 1 + 2 * r := by
  simp [coarseAffineTwo, ZMod.coe_unitOfCoprime]

theorem refinementTarget_lowDigit_zero (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    refinementTarget k (lowDigit k r 0) = coarseMulFour k r := by
  simp only [refinementTarget, branch_lowDigit k hk r 0, retardedTarget,
    lowDigit_val k hk r 0, Fin.val_zero, add_zero]
  rw [coarseMulFour_apply]
  rw [← ZMod.natCast_zmod_val r]
  norm_num

theorem refinementTarget_lowDigit_two (k : ℕ) (hk : 2 ≤ k) (r : Coarse k) :
    refinementTarget k (lowDigit k r 2) = coarseAffineTwo k r := by
  have hdiv : (3 * r.val + 2) / 3 = r.val := by
    rw [Nat.mul_add_div (by norm_num : 0 < 3)]
    norm_num
  simp only [refinementTarget, branch_lowDigit k hk r 2, advancedTarget,
    lowDigit_val k hk r 2, Fin.val_two, hdiv]
  rw [coarseAffineTwo_apply]
  rw [← ZMod.natCast_zmod_val r]
  norm_num

/-- Concrete finite-system data in `m = 2+3s` coordinates.  For `k < 2` the
types are harmless degenerate quotients; all KL theorems will assume `2 <= k`. -/
def system (k : ℕ) : FiniteSystem where
  State := State k
  Coarse := Coarse k
  transport := transport k
  branch := branch k
  refinementTarget := refinementTarget k
  fiber := fiber k

/-- The three refinement fibers partition the concrete fine state space.
This discharges the first combinatorial hypothesis of the exact oscillation
identity. -/
theorem fiber_partition (k : ℕ) (hk : 2 ≤ k) (c : State k → ℝ) :
    ∑ r, (system k).fiberSum c r = (system k).totalMass c := by
  letI : Fintype (State k) := (system k).stateFintype
  letI : Fintype (Coarse k) := (system k).coarseFintype
  have h : (∑ r : Coarse k, (c (fiber k r 0) + c (fiber k r 1) +
      c (fiber k r 2))) = ∑ s : State k, c s := by
    calc
      (∑ r : Coarse k, (c (fiber k r 0) + c (fiber k r 1) + c (fiber k r 2))) =
          ∑ r : Coarse k, ∑ j : Fin 3, c (fiber k r j) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Fin.sum_univ_three]
      _ = ∑ p : Coarse k × Fin 3, c (fiber k p.1 p.2) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ s, c s := (fiberEquiv k hk).sum_comp c
  simpa only [FiniteSystem.fiberSum, FiniteSystem.totalMass, system] using h

/-- The retarded and advanced low-digit slices each map bijectively onto the
coarse targets.  Consequently their summed minimum contributions are one
copy apiece of the total minimum mass.  This discharges the second concrete
combinatorial hypothesis of the exact oscillation identity. -/
theorem branch_balance (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (c : State k → ℝ) :
    ∑ m, (system k).branchTerm w c m =
      (w.retarded + w.advanced) * (system k).minimumMass c := by
  letI : Fintype (State k) := (system k).stateFintype
  letI : Fintype (Coarse k) := (system k).coarseFintype
  let f : Coarse k → ℝ := fun r => (system k).fiberMin c r
  calc
    (∑ m, (system k).branchTerm w c m) =
        ∑ p : Coarse k × Fin 3,
          (system k).branchTerm w c (lowDigit k p.1 p.2) :=
      ((lowDigitEquiv k hk).sum_comp
        (fun m => (system k).branchTerm w c m)).symm
    _ = ∑ r : Coarse k,
        ((system k).branchTerm w c (lowDigit k r 0) +
          (system k).branchTerm w c (lowDigit k r 1) +
          (system k).branchTerm w c (lowDigit k r 2)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.sum_univ_three]
    _ = ∑ r : Coarse k,
        (w.retarded * f (coarseMulFour k r) +
          w.advanced * f (coarseAffineTwo k r)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [FiniteSystem.branchTerm, system, branch_lowDigit_zero k hk r,
        branch_lowDigit_one k hk r, branch_lowDigit_two k hk r,
        refinementTarget_lowDigit_zero k hk r,
        refinementTarget_lowDigit_two k hk r]
      simp [f, system]
    _ = w.retarded * (∑ r : Coarse k, f (coarseMulFour k r)) +
        w.advanced * (∑ r : Coarse k, f (coarseAffineTwo k r)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = w.retarded * (∑ r : Coarse k, f r) +
        w.advanced * (∑ r : Coarse k, f r) := by
      rw [(coarseMulFour k).sum_comp f, (coarseAffineTwo k).sum_comp f]
    _ = (w.retarded + w.advanced) * (∑ r : Coarse k, f r) := by ring
    _ = (w.retarded + w.advanced) * (system k).minimumMass c := by
      rfl

/-- Fully concrete finite oscillation identity for the residue system. -/
theorem concrete_oscillation_identity (k : ℕ) (hk : 2 ≤ k)
    (w : Weights ℝ) (c : State k → ℝ)
    (hEigen : ∀ m, c m = (system k).operator w c m)
    (hmass : (system k).totalMass c ≠ 0) :
    FiniteSystem.annealedValue w - 1 =
      (w.retarded + w.advanced) * (system k).normalizedDefect c := by
  exact (system k).annealedValue_sub_one_eq_branchWeight_mul_normalizedDefect
    w c hEigen (fiber_partition k hk c) (branch_balance k hk w c) hmass

end ResidueSystem

end CleanLean.KL

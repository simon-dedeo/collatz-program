/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.FiniteSystem

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

/-- Concrete finite-system data in `m = 2+3s` coordinates.  For `k < 2` the
types are harmless degenerate quotients; all KL theorems will assume `2 <= k`. -/
def system (k : ℕ) : FiniteSystem where
  State := State k
  Coarse := Coarse k
  transport := transport k
  branch := branch k
  refinementTarget := refinementTarget k
  fiber := fiber k

end ResidueSystem

end CleanLean.KL

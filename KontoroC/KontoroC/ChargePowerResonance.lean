/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePowerQuine

/-!
# The recharge-23 perfect-power resonance

At recharge length `h = 23`, the coefficients in the charge-bouncer
perfect-power identity are themselves complete 23rd powers.  This file
formalizes the resulting equation and an exact four-prime local sieve.

The result is deliberately scoped to the single rail `u = F * r^23`.
A correction rail changes the reproduction identity and is not excluded here.
-/

namespace KontoroC

namespace ChargePowerResonance

open ChargePowerQuine

/-- `5 * Φ₂₃(A,B)`, written without importing cyclotomic-polynomial theory. -/
def G23 : ℤ :=
  5 * ∑ i ∈ Finset.range 23, A ^ (22 - i) * B ^ i

theorem G23_mod_277 : (G23 : ZMod 277) = 216 := by
  norm_num [G23, A, B, Finset.sum_range_succ]
  decide

theorem G23_mod_599 : (G23 : ZMod 599) = 283 := by
  norm_num [G23, A, B, Finset.sum_range_succ]
  decide

theorem G23_mod_829 : (G23 : ZMod 829) = 28 := by
  norm_num [G23, A, B, Finset.sum_range_succ]
  decide

theorem G23_mod_1151 : (G23 : ZMod 1151) = 1030 := by
  norm_num [G23, A, B, Finset.sum_range_succ]
  decide

/-- The bivariate geometric-factor identity defining `G23`. -/
theorem A_pow_twentyThree_sub_B_pow_twentyThree :
    A ^ 23 - B ^ 23 = F * G23 := by
  rw [G23]
  have hfactor : A ^ 23 - B ^ 23 =
      (A - B) * ∑ i ∈ Finset.range 23, A ^ (22 - i) * B ^ i := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hfactor, A_sub_B]
  ring

/-- The recharge-23 equation after all complete 23rd powers are absorbed. -/
abbrev ResonanceEquation (e : Fin 23) (R : Type*) [CommRing R]
    (g x y : R) : Prop :=
  (3 : R) ^ e.val * x ^ 23 = g + y ^ 23

/-- The standard representatives `0, ..., p-1` of `ZMod p`. -/
def allResidues (p : ℕ) [NeZero p] : List (ZMod p) :=
  List.map (fun n : ℕ ↦ (n : ZMod p)) (List.range p)

theorem mem_allResidues (p : ℕ) [NeZero p] (x : ZMod p) :
    x ∈ allResidues p := by
  have hx : x ∈ List.map (fun n : ℕ ↦ (n : ZMod p)) (List.range p) :=
    (@List.mem_map ℕ (ZMod p) x (fun n ↦ (n : ZMod p))
      (List.range p)).mpr
        ⟨x.val, List.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  rw [allResidues]
  exact hx

/-- Deduplicated list of 23rd-power residues.  Enumerating this list rather
than all pairs in the field makes the four kernel computations small. -/
def powerResidues (p : ℕ) [NeZero p] : List (ZMod p) :=
  (List.map (fun z : ZMod p ↦ z ^ 23) (allResidues p)).eraseDups

theorem pow_mem_powerResidues (p : ℕ) [NeZero p] (x : ZMod p) :
    x ^ 23 ∈ powerResidues p := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map_of_mem (f := fun z ↦ z ^ 23) (mem_allResidues p x)

/-- Boolean local-solubility test on the complete 23rd-power residue sets. -/
def locallySoluble (p : ℕ) [NeZero p] (e : Fin 23) (g : ZMod p) : Bool :=
  (powerResidues p).any fun u ↦
    (powerResidues p).any fun v ↦ decide ((3 : ZMod p) ^ e.val * u = g + v)

theorem locallySoluble_of_solution (p : ℕ) [NeZero p]
    (e : Fin 23) (g x y : ZMod p)
    (h : ResonanceEquation e (ZMod p) g x y) :
    locallySoluble p e g = true := by
  simp only [locallySoluble, List.any_eq_true]
  refine ⟨x ^ 23, pow_mem_powerResidues p x, ?_⟩
  refine ⟨y ^ 23, pow_mem_powerResidues p y, ?_⟩
  exact decide_eq_true h

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
-- Kernel reduction enumerates all deduplicated 23rd-power residues.
/-- At `p=277`, nine of the 23 exponent classes remain. -/
theorem sieve277 (e : Fin 23)
    (h : locallySoluble 277 e (216 : ZMod 277) = true) :
    e.val = 0 ∨ e.val = 2 ∨ e.val = 4 ∨ e.val = 5 ∨ e.val = 6 ∨
      e.val = 14 ∨ e.val = 15 ∨ e.val = 18 ∨ e.val = 21 := by
  revert e
  decide

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
-- Kernel reduction enumerates all deduplicated 23rd-power residues.
/-- At `p=599`, five exponent classes remain. -/
theorem sieve599 (e : Fin 23)
    (hprev : e.val = 0 ∨ e.val = 2 ∨ e.val = 4 ∨ e.val = 5 ∨ e.val = 6 ∨
      e.val = 14 ∨ e.val = 15 ∨ e.val = 18 ∨ e.val = 21)
    (h : locallySoluble 599 e (283 : ZMod 599) = true) :
    e.val = 0 ∨ e.val = 4 ∨ e.val = 5 ∨ e.val = 14 ∨ e.val = 15 := by
  revert e
  decide

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
-- Kernel reduction enumerates all deduplicated 23rd-power residues.
/-- At `p=829`, only the classes 5 and 15 remain. -/
theorem sieve829 (e : Fin 23)
    (hprev : e.val = 0 ∨ e.val = 4 ∨ e.val = 5 ∨ e.val = 14 ∨ e.val = 15)
    (h : locallySoluble 829 e (28 : ZMod 829) = true) :
    e.val = 5 ∨ e.val = 15 := by
  revert e
  decide

set_option maxRecDepth 500000 in
set_option maxHeartbeats 20000000 in
-- Kernel reduction enumerates all deduplicated 23rd-power residues.
/-- At `p=1151`, the final local exponent class is `e=15`. -/
theorem sieve1151 (e : Fin 23)
    (hprev : e.val = 5 ∨ e.val = 15)
    (h : locallySoluble 1151 e (1030 : ZMod 1151) = true) :
    e.val = 15 := by
  revert e
  decide

/-- The four exact residue calculations leave only exponent class `15`. -/
theorem reduced_exponent_eq_fifteen (e : Fin 23) (x y : ℤ)
    (h : ResonanceEquation e ℤ G23 x y) : e.val = 15 := by
  have h277eq : ResonanceEquation e (ZMod 277) 216
      (x : ZMod 277) (y : ZMod 277) := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod 277)) h
    norm_num [G23_mod_277] at hc
    exact hc
  have h277 := sieve277 e
    (locallySoluble_of_solution 277 e 216 _ _ h277eq)
  have h599eq : ResonanceEquation e (ZMod 599) 283
      (x : ZMod 599) (y : ZMod 599) := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod 599)) h
    norm_num [G23_mod_599] at hc
    exact hc
  have h599 := sieve599 e h277
    (locallySoluble_of_solution 599 e 283 _ _ h599eq)
  have h829eq : ResonanceEquation e (ZMod 829) 28
      (x : ZMod 829) (y : ZMod 829) := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod 829)) h
    norm_num [G23_mod_829] at hc
    exact hc
  have h829 := sieve829 e h599
    (locallySoluble_of_solution 829 e 28 _ _ h829eq)
  have h1151eq : ResonanceEquation e (ZMod 1151) 1030
      (x : ZMod 1151) (y : ZMod 1151) := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod 1151)) h
    norm_num [G23_mod_1151] at hc
    exact hc
  exact sieve1151 e h829
    (locallySoluble_of_solution 1151 e 1030 _ _ h1151eq)

/-- At recharge length 23, cancellation of the fixed divisor gives `G23`. -/
theorem recharge_twentyThree_equation
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B ^ 23 * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A ^ 23 * q) :
    A ^ 23 * C ^ m * r ^ 23 - B ^ 23 * D ^ m' * r' ^ 23 = G23 := by
  have h := power_quine_identity (h := 23) hin hout
  rw [A_pow_twentyThree_sub_B_pow_twentyThree] at h
  exact mul_left_cancel₀ (by norm_num [F, chargeFixedDivisor]) h

/-- Absorb all complete powers in the recharge-23 equation. -/
theorem recharge_twentyThree_reduces
    {m m' : ℕ} {r r' : ℤ}
    (h : (3 : ℤ) ^ (114 * 23 + 17 * m) * r ^ 23 =
      G23 + 2 ^ (154 * 23 + 23 * m') * r' ^ 23) :
    let k := 114 * 23 + 17 * m
    let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
    ResonanceEquation e ℤ G23
      (3 ^ (k / 23) * r) (2 ^ (154 + m') * r') := by
  dsimp only
  have hk : (114 * 23 + 17 * m) % 23 +
      23 * ((114 * 23 + 17 * m) / 23) = 114 * 23 + 17 * m :=
    Nat.mod_add_div _ _
  have htwo : 23 * (154 + m') = 154 * 23 + 23 * m' := by omega
  rw [← hk, ← htwo] at h
  rw [absorb_complete_power] at h
  have hright : (2 : ℤ) ^ (23 * (154 + m')) * r' ^ 23 =
      (2 ^ (154 + m') * r') ^ 23 := by
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  rw [hright] at h
  exact h

/-- Any recharge-23 transition on the single perfect-power rail must use
opcode class `m = 9 (mod 23)`. -/
theorem recharge_twentyThree_opcode_mod_twentyThree
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B ^ 23 * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A ^ 23 * q) :
    m % 23 = 9 := by
  have hbase := recharge_twentyThree_equation hin hout
  have hfamily : (3 : ℤ) ^ (114 * 23 + 17 * m) * r ^ 23 =
      G23 + 2 ^ (154 * 23 + 23 * m') * r' ^ 23 := by
    rw [A, B, C, D] at hbase
    rw [← pow_mul (3 : ℤ) 114 23, ← pow_mul (3 : ℤ) 17 m,
      ← pow_mul (2 : ℤ) 154 23, ← pow_mul (2 : ℤ) 23 m',
      ← pow_add, ← pow_add] at hbase
    linarith
  let k := 114 * 23 + 17 * m
  let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
  have hred : ResonanceEquation e ℤ G23
      (3 ^ (k / 23) * r) (2 ^ (154 + m') * r') := by
    exact recharge_twentyThree_reduces hfamily
  have he : e.val = 15 := reduced_exponent_eq_fifteen e _ _ hred
  dsimp [e, k] at he
  omega

/-- The sole generalized Fermat/Thue equation left by the four-prime sieve. -/
def R23Solution : Prop :=
  ∃ x y : ℤ, ResonanceEquation ⟨15, by omega⟩ ℤ G23 x y

/-- Every recharge-23 transition preserving the single perfect-power family
supplies an integer solution to `R23Solution`.  No converse is claimed. -/
theorem recharge_twentyThree_supplies_R23
    {m m' : ℕ} {r r' q : ℤ}
    (hin : C ^ m * (F * r ^ 23) = 1 + B ^ 23 * q)
    (hout : D ^ m' * (F * r' ^ 23) = 1 + A ^ 23 * q) :
    R23Solution := by
  have hbase := recharge_twentyThree_equation hin hout
  have hfamily : (3 : ℤ) ^ (114 * 23 + 17 * m) * r ^ 23 =
      G23 + 2 ^ (154 * 23 + 23 * m') * r' ^ 23 := by
    rw [A, B, C, D] at hbase
    rw [← pow_mul (3 : ℤ) 114 23, ← pow_mul (3 : ℤ) 17 m,
      ← pow_mul (2 : ℤ) 154 23, ← pow_mul (2 : ℤ) 23 m',
      ← pow_add, ← pow_add] at hbase
    linarith
  let k := 114 * 23 + 17 * m
  let e : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by omega)⟩
  let x : ℤ := 3 ^ (k / 23) * r
  let y : ℤ := 2 ^ (154 + m') * r'
  have hred : ResonanceEquation e ℤ G23 x y := by
    exact recharge_twentyThree_reduces hfamily
  have he : e = ⟨15, by omega⟩ :=
    Fin.ext (reduced_exponent_eq_fifteen e x y hred)
  exact ⟨x, y, by simpa [he] using hred⟩

/-- Thus a no-solution theorem for `R23Solution` kills the uncorrected
single perfect-power rail at recharge length 23. -/
theorem no_recharge_twentyThree_power_quine (hR23 : ¬ R23Solution) :
    ¬ ∃ (m m' : ℕ) (r r' q : ℤ),
      C ^ m * (F * r ^ 23) = 1 + B ^ 23 * q ∧
      D ^ m' * (F * r' ^ 23) = 1 + A ^ 23 * q := by
  rintro ⟨m, m', r, r', q, hin, hout⟩
  exact hR23 (recharge_twentyThree_supplies_R23 hin hout)

end ChargePowerResonance

end KontoroC

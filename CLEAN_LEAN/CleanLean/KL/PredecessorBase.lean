/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.KLPredecessorFunctions
import CleanLean.KL.KLWeights
import CleanLean.KL.ConcreteElimination

/-!
# The concrete KL base difference inequalities

This file lifts the targetwise reverse-tree decomposition to the literal
residue-class infimum functions.  It contains no numerical certificate and
does not use the false printed equality (2.1).
-/

namespace CleanLean.KL

open CleanLean.Collatz

/-- Coordinate of an actual integer target in the concrete class-2 state
space.  The accompanying lemmas use this only when `a=2 (mod 3)`. -/
def klStateOf (k a : ℕ) : ResidueSystem.State k :=
  ((a - 2) / 3 : ℕ)

theorem two_add_three_mul_stateCoord {a : ℕ}
    (ha3 : a % 3 = 2) :
    2 + 3 * ((a - 2) / 3) = a := by
  have hdecomp := Nat.mod_add_div a 3
  omega

theorem klStateOf_val_modEq (k a : ℕ) :
    (klStateOf k a).val ≡ (a - 2) / 3 [MOD 3 ^ (k - 1)] := by
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (ZMod.natCast_zmod_val (klStateOf k a))

theorem klStateOf_target_modEq
    {k a : ℕ} (hk : 1 ≤ k) (ha3 : a % 3 = 2) :
    a ≡ 2 + 3 * (klStateOf k a).val [MOD 3 ^ k] := by
  have h := (klStateOf_val_modEq k a).symm.mul_left' 3
  have hadd := h.add_left 2
  have hpow : 3 * 3 ^ (k - 1) = 3 ^ k := by
    calc
      3 * 3 ^ (k - 1) = 3 ^ ((k - 1) + 1) := by rw [pow_succ']
      _ = 3 ^ k := by congr 1 <;> omega
  rw [hpow] at hadd
  calc
    a = 2 + 3 * ((a - 2) / 3) :=
      (two_add_three_mul_stateCoord ha3).symm
    _ ≡ 2 + 3 * (klStateOf k a).val [MOD 3 ^ k] := hadd

/-- Any fine state whose coordinate reduces to `r` lies in the displayed
three-element top-digit fiber over `r`. -/
theorem exists_fiber_eq_of_val_modEq
    {k : ℕ} (hk : 2 ≤ k) (s : ResidueSystem.State k)
    (r : ResidueSystem.Coarse k)
    (hsr : s.val ≡ r.val [MOD 3 ^ (k - 2)]) :
    ∃ j : Fin 3, ResidueSystem.fiber k r j = s := by
  let modulus : ℕ := 3 ^ (k - 2)
  have hmodulus : 0 < modulus := by positivity
  have hlevel := ResidueSystem.three_pow_level k hk
  have hslt : s.val < 3 * modulus := by
    rw [← hlevel]
    exact ZMod.val_lt s
  have hquot : s.val / modulus < 3 :=
    (Nat.div_lt_iff_lt_mul hmodulus).2 (by simpa [mul_comm] using hslt)
  let j : Fin 3 := ⟨s.val / modulus, hquot⟩
  refine ⟨j, ZMod.val_injective _ ?_⟩
  rw [ResidueSystem.fiber_val k hk]
  have hrlt : r.val < modulus := ZMod.val_lt r
  have hrem : s.val % modulus = r.val :=
    Nat.mod_eq_of_modEq hsr hrlt
  have hdecomp := Nat.mod_add_div s.val modulus
  dsimp [j, modulus] at hdecomp hrem ⊢
  calc
    r.val + s.val / 3 ^ (k - 2) * 3 ^ (k - 2) =
        s.val % 3 ^ (k - 2) +
          3 ^ (k - 2) * (s.val / 3 ^ (k - 2)) := by
            rw [hrem]
            congr 1
            exact Nat.mul_comm _ _
    _ = s.val := hdecomp

/-- Convert congruence of class-2 integer representatives at coarse precision
to membership of their state coordinates in the same top-digit fiber. -/
theorem exists_fiber_eq_klStateOf_of_modEq
    {k a : ℕ} (hk : 2 ≤ k) (ha3 : a % 3 = 2)
    (r : ResidueSystem.Coarse k)
    (ha : a ≡ 2 + 3 * r.val [MOD 3 ^ (k - 1)]) :
    ∃ j : Fin 3, ResidueSystem.fiber k r j = klStateOf k a := by
  apply exists_fiber_eq_of_val_modEq hk
  have hcoord : (a - 2) / 3 ≡ r.val [MOD 3 ^ (k - 2)] := by
    have haeq : a = 2 + 3 * ((a - 2) / 3) :=
      (two_add_three_mul_stateCoord ha3).symm
    rw [haeq] at ha
    have hcancel :
        3 * ((a - 2) / 3) ≡ 3 * r.val [MOD 3 ^ (k - 1)] := by
      exact (Nat.ModEq.refl 2).add_left_cancel ha
    rw [ResidueSystem.three_pow_level k hk] at hcancel
    exact Nat.ModEq.mul_left_cancel' (by norm_num) hcancel
  have hstate := klStateOf_val_modEq k a
  have hpowDvd : 3 ^ (k - 2) ∣ 3 ^ (k - 1) :=
    pow_dvd_pow 3 (by omega)
  exact (hstate.of_dvd hpowDvd).trans hcoord

theorem klTarget_mod_three
    {k : ℕ} (hk : 1 ≤ k) {state : ResidueSystem.State k}
    (a : KLTarget k state) : a.val % 3 = 2 := by
  have hpow : 3 ∣ 3 ^ k := by
    rw [show k = (k - 1) + 1 by omega, pow_succ']
    exact dvd_mul_right 3 (3 ^ (k - 1))
  have hmod := a.property.2.1.of_dvd hpow
  change a.val % 3 = (2 + 3 * state.val) % 3 at hmod
  simpa using hmod

theorem klTarget_mod_nine
    {k : ℕ} (hk : 2 ≤ k) {state : ResidueSystem.State k}
    (a : KLTarget k state) :
    a.val % 9 = (2 + 3 * state.val) % 9 := by
  have hpow : 9 ∣ 3 ^ k := by
    have hdiv : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk
    norm_num at hdiv ⊢
    exact hdiv
  have hmod := a.property.2.1.of_dvd hpow
  exact hmod

/-- The `4a` child lies in the transported fine residue state. -/
def klTransportTarget
    {k : ℕ} (hk : 1 ≤ k) (state : ResidueSystem.State k)
    (a : KLTarget k state) :
    KLTarget k (ResidueSystem.transport k state) := by
  refine ⟨4 * a.val, Nat.mul_pos (by norm_num) a.property.1, ?_, ?_⟩
  · have hmul := a.property.2.1.mul (Nat.ModEq.refl 4)
    have hmul' :
        4 * a.val ≡ 4 * (2 + 3 * state.val) [MOD 3 ^ k] := by
      simpa [mul_comm] using hmul
    exact hmul'.trans (ResidueSystem.transport_residue_modEq k hk state).symm
  · have hnon := nonperiodic_two_pow_mul a.property.2.2 2
    simpa using hnon

theorem zmod_val_modEq_natCast (n q : ℕ) (hn : 0 < n) :
    ((q : ZMod n)).val ≡ q [MOD n] := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (ZMod.natCast_zmod_val (q : ZMod n))

theorem three_pow_succ (k : ℕ) (hk : 1 ≤ k) :
    3 ^ k = 3 * 3 ^ (k - 1) := by
  calc
    3 ^ k = 3 ^ ((k - 1) + 1) := by congr 1 <;> omega
    _ = 3 * 3 ^ (k - 1) := by rw [pow_succ']

/-- Original-residue statement for the D3 odd child. -/
theorem oddPredecessor_modEq_refinementTarget
    {k : ℕ} (hk : 2 ≤ k) (state : ResidueSystem.State k)
    (hbranch : ResidueSystem.branch k state = .advanced)
    (a : KLTarget k state) :
    (2 * a.val - 1) / 3 ≡
      2 + 3 * (ResidueSystem.refinementTarget k state).val
        [MOD 3 ^ (k - 1)] := by
  let m := 2 + 3 * state.val
  let c := (2 * a.val - 1) / 3
  let u := 1 + 2 * (state.val / 3)
  have ha3 : a.val % 3 = 2 := klTarget_mod_three (by omega) a
  have hthreeA : 3 * c = 2 * a.val - 1 := by
    exact three_mul_oddPredecessor a.property.1 ha3
  have hnumState : 2 * m - 1 = 3 * (2 + 3 * u) := by
    exact ResidueSystem.advanced_target_numerator k state hbranch
  have hmul := a.property.2.1.mul (Nat.ModEq.refl 2)
  have hmul' : 2 * a.val ≡ 2 * m [MOD 3 ^ k] := by
    simpa [m, mul_comm] using hmul
  have hsub : 2 * a.val - 1 ≡ 2 * m - 1 [MOD 3 ^ k] :=
    hmul'.sub (by omega) (by dsimp [m]; omega) (Nat.ModEq.refl 1)
  have hsub' : 3 * c ≡ 3 * (2 + 3 * u) [MOD 3 ^ k] := by
    calc
      3 * c = 2 * a.val - 1 := hthreeA
      _ ≡ 2 * m - 1 [MOD 3 ^ k] := hsub
      _ = 3 * (2 + 3 * u) := hnumState
  have hscaled : 3 * c ≡ 3 * (2 + 3 * u) [MOD 3 * 3 ^ (k - 1)] := by
    rw [← three_pow_succ k (by omega)]
    exact hsub'
  have hcU : c ≡ 2 + 3 * u [MOD 3 ^ (k - 1)] :=
    Nat.ModEq.mul_left_cancel' (by norm_num) hscaled
  have huVal :
      u ≡ (ResidueSystem.advancedTarget k state).val [MOD 3 ^ (k - 2)] := by
    exact (zmod_val_modEq_natCast (3 ^ (k - 2)) u (by positivity)).symm
  have hrep := huVal.mul_left' 3 |>.add_left 2
  have hrep' :
      2 + 3 * u ≡ 2 + 3 * (ResidueSystem.advancedTarget k state).val
        [MOD 3 ^ (k - 1)] := by
    rw [ResidueSystem.three_pow_level k hk]
    exact hrep
  have href : ResidueSystem.refinementTarget k state =
      ResidueSystem.advancedTarget k state := by
    simp [ResidueSystem.refinementTarget, hbranch]
  rw [href]
  exact hcU.trans hrep'

/-- Original-residue statement for the D1 doubled odd child. -/
theorem doubleOddPredecessor_modEq_refinementTarget
    {k : ℕ} (hk : 2 ≤ k) (state : ResidueSystem.State k)
    (hbranch : ResidueSystem.branch k state = .retarded)
    (a : KLTarget k state) :
    2 * ((2 * a.val - 1) / 3) ≡
      2 + 3 * (ResidueSystem.refinementTarget k state).val
        [MOD 3 ^ (k - 1)] := by
  let m := 2 + 3 * state.val
  let c := (2 * a.val - 1) / 3
  let d := 2 * c
  let u := 4 * (state.val / 3)
  have ha3 : a.val % 3 = 2 := klTarget_mod_three (by omega) a
  have hthreeC : 3 * c = 2 * a.val - 1 :=
    three_mul_oddPredecessor a.property.1 ha3
  have hthreeD : 3 * d = 4 * a.val - 2 := by
    dsimp [d]
    omega
  have hnumState : 4 * m - 2 = 3 * (2 + 3 * u) := by
    exact ResidueSystem.retarded_target_numerator k state hbranch
  have hmul := a.property.2.1.mul (Nat.ModEq.refl 4)
  have hmul' : 4 * a.val ≡ 4 * m [MOD 3 ^ k] := by
    simpa [m, mul_comm] using hmul
  have hsub : 4 * a.val - 2 ≡ 4 * m - 2 [MOD 3 ^ k] :=
    hmul'.sub (by omega) (by dsimp [m]; omega) (Nat.ModEq.refl 2)
  have hsub' : 3 * d ≡ 3 * (2 + 3 * u) [MOD 3 ^ k] := by
    calc
      3 * d = 4 * a.val - 2 := hthreeD
      _ ≡ 4 * m - 2 [MOD 3 ^ k] := hsub
      _ = 3 * (2 + 3 * u) := hnumState
  have hscaled : 3 * d ≡ 3 * (2 + 3 * u) [MOD 3 * 3 ^ (k - 1)] := by
    rw [← three_pow_succ k (by omega)]
    exact hsub'
  have hdU : d ≡ 2 + 3 * u [MOD 3 ^ (k - 1)] :=
    Nat.ModEq.mul_left_cancel' (by norm_num) hscaled
  have huVal :
      u ≡ (ResidueSystem.retardedTarget k state).val [MOD 3 ^ (k - 2)] := by
    exact (zmod_val_modEq_natCast (3 ^ (k - 2)) u (by positivity)).symm
  have hrep := huVal.mul_left' 3 |>.add_left 2
  have hrep' :
      2 + 3 * u ≡ 2 + 3 * (ResidueSystem.retardedTarget k state).val
        [MOD 3 ^ (k - 1)] := by
    rw [ResidueSystem.three_pow_level k hk]
    exact hrep
  have href : ResidueSystem.refinementTarget k state =
      ResidueSystem.retardedTarget k state := by
    simp [ResidueSystem.refinementTarget, hbranch]
  rw [href]
  exact hdU.trans hrep'

theorem klPhi_le_target
    {k : ℕ} {state : ResidueSystem.State k}
    (a : KLTarget k state) (y : ℝ) :
    klPhi k state y ≤ (klTargetCount a.val y : ℝ) := by
  change (klPhiNat k state y : ℝ) ≤ (klTargetCount a.val y : ℝ)
  exact_mod_cast klPhiNat_le_target y a

/-- A target in one of the three refinement fibers bounds their minimum. -/
theorem branchPhiMin_le_target
    {k : ℕ} (state : ResidueSystem.State k) (j : Fin 3)
    (a : KLTarget k
      (ResidueSystem.fiber k
        (ResidueSystem.refinementTarget k state) j))
    (y : ℝ) :
    min
        (klPhi k (ResidueSystem.fiber k
          (ResidueSystem.refinementTarget k state) 0) y)
        (min
          (klPhi k (ResidueSystem.fiber k
            (ResidueSystem.refinementTarget k state) 1) y)
          (klPhi k (ResidueSystem.fiber k
            (ResidueSystem.refinementTarget k state) 2) y)) ≤
      (klTargetCount a.val y : ℝ) := by
  fin_cases j
  · exact (min_le_left _ _).trans (klPhi_le_target a y)
  · exact (min_le_right _ _).trans
      ((min_le_left _ _).trans (klPhi_le_target a y))
  · exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (klPhi_le_target a y))

theorem exists_retardedChildTarget
    {k : ℕ} (hk : 2 ≤ k) (state : ResidueSystem.State k)
    (hbranch : ResidueSystem.branch k state = .retarded)
    (a : KLTarget k state) :
    ∃ j : Fin 3, ∃ child : KLTarget k (ResidueSystem.fiber k
        (ResidueSystem.refinementTarget k state) j),
      child.val = 2 * ((2 * a.val - 1) / 3) := by
  have ha9 : a.val % 9 = 2 := by
    rw [klTarget_mod_nine hk a]
    exact (ResidueSystem.branch_eq_retarded_iff_residue k state).mp hbranch
  have ha3 : a.val % 3 = 2 := klTarget_mod_three (by omega) a
  let c := (2 * a.val - 1) / 3
  let d := 2 * c
  have hcpos : 0 < c := by
    have hthree := three_mul_oddPredecessor a.property.1 ha3
    dsimp [c]
    omega
  have hcstep : syracuseStep c = a.val :=
    syracuseStep_oddPredecessor a.property.1 ha3
  have hcnon : ¬ IsSyracusePeriodic c :=
    nonperiodic_of_target_reaches a.property.2.2 ⟨1, by simpa using hcstep⟩
  have hdnon : ¬ IsSyracusePeriodic d := by
    dsimp [d]
    exact nonperiodic_two_pow_mul hcnon 1
  have hd3 : d % 3 = 2 := by
    have hthree := three_mul_oddPredecessor a.property.1 ha3
    have hcdecomp := Nat.mod_add_div c 3
    have hadecomp := Nat.mod_add_div a.val 9
    dsimp [c, d] at hthree hcdecomp ⊢
    omega
  have hdmod := doubleOddPredecessor_modEq_refinementTarget hk state hbranch a
  obtain ⟨j, hj⟩ := exists_fiber_eq_klStateOf_of_modEq hk hd3
    (ResidueSystem.refinementTarget k state) hdmod
  refine ⟨j, ?_⟩
  rw [hj]
  exact ⟨⟨d, by dsimp [d]; positivity,
    klStateOf_target_modEq (by omega) hd3, hdnon⟩, rfl⟩

theorem exists_advancedChildTarget
    {k : ℕ} (hk : 2 ≤ k) (state : ResidueSystem.State k)
    (hbranch : ResidueSystem.branch k state = .advanced)
    (a : KLTarget k state) :
    ∃ j : Fin 3, ∃ child : KLTarget k (ResidueSystem.fiber k
        (ResidueSystem.refinementTarget k state) j),
      child.val = (2 * a.val - 1) / 3 := by
  have ha9 : a.val % 9 = 8 := by
    rw [klTarget_mod_nine hk a]
    exact (ResidueSystem.branch_eq_advanced_iff_residue k state).mp hbranch
  have ha3 : a.val % 3 = 2 := klTarget_mod_three (by omega) a
  let c := (2 * a.val - 1) / 3
  have hcpos : 0 < c := by
    have hthree := three_mul_oddPredecessor a.property.1 ha3
    dsimp [c]
    omega
  have hc3 : c % 3 = 2 := by
    have hthree := three_mul_oddPredecessor a.property.1 ha3
    have hcdecomp := Nat.mod_add_div c 3
    have hadecomp := Nat.mod_add_div a.val 9
    dsimp [c] at hthree hcdecomp ⊢
    omega
  have hcstep : syracuseStep c = a.val :=
    syracuseStep_oddPredecessor a.property.1 ha3
  have hcnon : ¬ IsSyracusePeriodic c :=
    nonperiodic_of_target_reaches a.property.2.2 ⟨1, by simpa using hcstep⟩
  have hcmod := oddPredecessor_modEq_refinementTarget hk state hbranch a
  obtain ⟨j, hj⟩ := exists_fiber_eq_klStateOf_of_modEq hk hc3
    (ResidueSystem.refinementTarget k state) hcmod
  refine ⟨j, ?_⟩
  rw [hj]
  exact ⟨⟨c, hcpos, klStateOf_target_modEq (by omega) hc3, hcnon⟩, rfl⟩

theorem two_rpow_sub_two_mul_four (a : ℕ) (y : ℝ) :
    (2 : ℝ) ^ (y - 2) * (4 * a : ℕ) =
      (2 : ℝ) ^ y * a := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_sub h2]
  norm_num only [Real.rpow_natCast]
  push_cast
  field_simp


theorem klCutoff_four (a : ℕ) (y : ℝ) :
    klCutoff (4 * a) (y - 2) = klCutoff a y := by
  unfold klCutoff
  congr 1
  exact two_rpow_sub_two_mul_four a y

/-- At scale `y>=2`, the two halving steps from `4a` fit under the target
cutoff. -/
theorem four_mul_le_klCutoff {a : ℕ} {y : ℝ} (hy : 2 ≤ y) :
    4 * a ≤ klCutoff a y := by
  rw [← klCutoff_four a y]
  exact klCutoff_self_le (by linarith)

/-- Transport contribution to every targetwise base row. -/
theorem klTargetCount_four_le
    {a : ℕ} (ha : 0 < a) {y : ℝ} (hy : 2 ≤ y) :
    klTargetCount (4 * a) (y - 2) ≤ klTargetCount a y := by
  rw [klTargetCount, klTargetCount, klCutoff_four]
  exact boundedPredecessorCount_four_le ha (four_mul_le_klCutoff hy)

/-- Common real cutoff on the odd inverse branch. -/
noncomputable def klOddScale (a : ℕ) (y : ℝ) : ℕ :=
  ⌊(2 : ℝ) ^ (y - 1) * (2 * a - 1 : ℕ)⌋₊

theorem two_rpow_advanced_mul_oddPredecessor
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) (y : ℝ) :
    (2 : ℝ) ^ (y + alpha - 1) * ((2 * a - 1) / 3 : ℕ) =
      (2 : ℝ) ^ (y - 1) * (2 * a - 1 : ℕ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hthree := three_mul_oddPredecessor ha ha3
  rw [show y + alpha - 1 = (y - 1) + alpha by ring,
    Real.rpow_add h2, two_rpow_alpha]
  push_cast
  norm_num
  have hthreeR : (3 : ℝ) * (((2 * a - 1) / 3 : ℕ) : ℝ) =
      ((2 * a - 1 : ℕ) : ℝ) := by exact_mod_cast hthree
  calc
    (2 : ℝ) ^ (y - 1) * 3 * (((2 * a - 1) / 3 : ℕ) : ℝ) =
        (2 : ℝ) ^ (y - 1) *
          ((3 : ℝ) * (((2 * a - 1) / 3 : ℕ) : ℝ)) := by ring
    _ = (2 : ℝ) ^ (y - 1) * ((2 * a - 1 : ℕ) : ℝ) := by rw [hthreeR]

theorem two_rpow_retarded_mul_doubleOddPredecessor
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) (y : ℝ) :
    (2 : ℝ) ^ (y + alpha - 2) *
        (2 * ((2 * a - 1) / 3) : ℕ) =
      (2 : ℝ) ^ (y - 1) * (2 * a - 1 : ℕ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hthree := three_mul_oddPredecessor ha ha3
  rw [show y + alpha - 2 = (y - 2) + alpha by ring,
    Real.rpow_add h2, two_rpow_alpha]
  push_cast
  have hthreeR : (3 : ℝ) * (((2 * a - 1) / 3 : ℕ) : ℝ) =
      ((2 * a - 1 : ℕ) : ℝ) := by exact_mod_cast hthree
  have hshift : (2 : ℝ) ^ (y - 1) = 2 * (2 : ℝ) ^ (y - 2) := by
    calc
      (2 : ℝ) ^ (y - 1) = (2 : ℝ) ^ ((y - 2) + 1) := by congr 1 <;> ring
      _ = (2 : ℝ) ^ (y - 2) * (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add h2 _ _
      _ = 2 * (2 : ℝ) ^ (y - 2) := by
        rw [Real.rpow_one]
        ring
  calc
    (2 : ℝ) ^ (y - 2) * 3 *
        (2 * (((2 * a - 1) / 3 : ℕ) : ℝ)) =
      2 * (2 : ℝ) ^ (y - 2) *
        ((3 : ℝ) * (((2 * a - 1) / 3 : ℕ) : ℝ)) := by ring
    _ = 2 * (2 : ℝ) ^ (y - 2) * ((2 * a - 1 : ℕ) : ℝ) := by rw [hthreeR]
    _ = (2 : ℝ) ^ (y - 1) * ((2 * a - 1 : ℕ) : ℝ) := by rw [hshift]

theorem klCutoff_oddPredecessor_advanced
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) (y : ℝ) :
    klCutoff ((2 * a - 1) / 3) (y + alpha - 1) =
      klOddScale a y := by
  unfold klCutoff klOddScale
  congr 1
  exact two_rpow_advanced_mul_oddPredecessor ha ha3 y

theorem klCutoff_doubleOddPredecessor_retarded
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2) (y : ℝ) :
    klCutoff (2 * ((2 * a - 1) / 3)) (y + alpha - 2) =
      klOddScale a y := by
  unfold klCutoff klOddScale
  congr 1
  exact two_rpow_retarded_mul_doubleOddPredecessor ha ha3 y

theorem klOddScale_le_klCutoff
    {a : ℕ} (ha : 0 < a) (y : ℝ) :
    klOddScale a y ≤ klCutoff a y := by
  unfold klOddScale klCutoff
  apply Nat.floor_mono
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpow : (2 : ℝ) ^ y = (2 : ℝ) ^ (y - 1) * 2 := by
    calc
      (2 : ℝ) ^ y = (2 : ℝ) ^ ((y - 1) + 1) := by congr 1 <;> ring
      _ = (2 : ℝ) ^ (y - 1) * (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add h2 _ _
      _ = (2 : ℝ) ^ (y - 1) * 2 := by rw [Real.rpow_one]
  rw [hpow]
  have hpowNonneg : 0 ≤ (2 : ℝ) ^ (y - 1) :=
    (Real.rpow_pos_of_pos h2 _).le
  push_cast
  have hsubCast : ((2 * a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsubCast]
  nlinarith

/-- Targetwise D3 before residue-class infimization. -/
theorem klTargetCount_four_add_oddPredecessor_le
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 = 2)
    (hanon : ¬ IsSyracusePeriodic a) {y : ℝ} (hy : 2 ≤ y) :
    klTargetCount (4 * a) (y - 2) +
        klTargetCount ((2 * a - 1) / 3) (y + alpha - 1) ≤
      klTargetCount a y := by
  rw [klTargetCount, klTargetCount, klTargetCount,
    klCutoff_four,
    klCutoff_oddPredecessor_advanced ha ha3]
  exact boundedPredecessorCount_four_add_oddPredecessor_le
    ha ha3 hanon (klOddScale_le_klCutoff ha y)
      (four_mul_le_klCutoff hy)

/-- Targetwise D1 before residue-class infimization.  The corrected
targetwise doubling identity replaces the false equality after infimizing. -/
theorem klTargetCount_four_add_doubleOddPredecessor_le
    {a : ℕ} (ha : 0 < a) (ha9 : a % 9 = 2)
    (hanon : ¬ IsSyracusePeriodic a) {y : ℝ} (hy : 2 ≤ y) :
    klTargetCount (4 * a) (y - 2) +
        klTargetCount (2 * ((2 * a - 1) / 3)) (y + alpha - 2) ≤
      klTargetCount a y := by
  have ha3 : a % 3 = 2 := by
    have hdecomp := Nat.mod_add_div a 9
    omega
  let c := (2 * a - 1) / 3
  have hcpos : 0 < c := by
    have hthree := three_mul_oddPredecessor ha ha3
    dsimp [c]
    omega
  have hc3 : c % 3 = 1 := by
    have hthree := three_mul_oddPredecessor ha ha3
    have hcdecomp := Nat.mod_add_div c 3
    have hadecomp := Nat.mod_add_div a 9
    dsimp [c] at hthree ⊢
    omega
  have hcstep : syracuseStep c = a := syracuseStep_oddPredecessor ha ha3
  have hcnon : ¬ IsSyracusePeriodic c :=
    nonperiodic_of_target_reaches hanon ⟨1, by simpa using hcstep⟩
  have hshift : 0 ≤ y + alpha - 2 := by linarith [one_lt_alpha]
  have hdoubleCutoff : 2 * c ≤ klOddScale a y := by
    rw [← klCutoff_doubleOddPredecessor_retarded ha ha3]
    exact klCutoff_self_le hshift
  have hcountEq :
      boundedPredecessorCount c (klOddScale a y) =
        boundedPredecessorCount (2 * c) (klOddScale a y) + 1 :=
    boundedPredecessorCount_eq_succ_double hcpos hc3 hcnon hdoubleCutoff
  rw [klTargetCount, klTargetCount, klTargetCount,
    klCutoff_four,
    klCutoff_doubleOddPredecessor_retarded ha ha3]
  have hcore := boundedPredecessorCount_four_add_oddPredecessor_le
    ha ha3 hanon (klOddScale_le_klCutoff ha y)
      (four_mul_le_klCutoff hy)
  dsimp [c] at hcountEq
  omega

/-- The literal residue-infimum predecessor functions satisfy all three
Krasikov--Lagarias base difference rows. -/
theorem predecessorPhi_satisfiesBaseSystem
    {k : ℕ} (hk : 2 ≤ k) :
    ConcreteElimination.SatisfiesBaseSystem k (klPhi k) := by
  intro state y hy
  obtain ⟨a, haInf⟩ :=
    klPhiNat_attained (y := y) ((klTargetsNonempty k) state)
  have hparent :
      (klTargetCount a.val y : ℝ) = klPhi k state y := by
    change (klTargetCount a.val y : ℝ) = (klPhiNat k state y : ℝ)
    exact_mod_cast haInf
  have htransport :
      klPhi k (ResidueSystem.transport k state) (y - 2) ≤
        (klTargetCount (4 * a.val) (y - 2) : ℝ) := by
    simpa [klTransportTarget] using
      klPhi_le_target (klTransportTarget (by omega) state a) (y - 2)
  generalize hbranch : ResidueSystem.branch k state = branch
  cases branch with
  | retarded =>
      have ha9 : a.val % 9 = 2 := by
        rw [klTarget_mod_nine hk a]
        exact (ResidueSystem.branch_eq_retarded_iff_residue k state).mp hbranch
      obtain ⟨j, child, hchildVal⟩ :=
        exists_retardedChildTarget hk state hbranch a
      have hchild := branchPhiMin_le_target state j child
        (y + alpha - 2)
      rw [hchildVal] at hchild
      have htargetNat := klTargetCount_four_add_doubleOddPredecessor_le
        a.property.1 ha9 a.property.2.2 hy
      have htarget :
          (klTargetCount (4 * a.val) (y - 2) : ℝ) +
              (klTargetCount (2 * ((2 * a.val - 1) / 3))
                (y + alpha - 2) : ℝ) ≤
            (klTargetCount a.val y : ℝ) := by
        exact_mod_cast htargetNat
      simp only [ConcreteElimination.baseBody,
        ConcreteElimination.splitBody, ResidueSystem.system, hbranch,
        ConcreteElimination.transportLeaf,
        ConcreteElimination.branchMinimum,
        ConcreteElimination.inf3,
        ConcreteElimination.branchLeaf,
        ConcreteElimination.branchLabel,
        EliminationTree.eval, PrincipalLabel.value,
        zero_add,
        show y + (0 - 2) = y - 2 by ring,
        show y + (alpha - 2) = y + alpha - 2 by ring]
      exact (add_le_add htransport hchild).trans htarget |>.trans_eq hparent
  | neutral =>
      have htargetNat := klTargetCount_four_le a.property.1 hy
      have htarget :
          (klTargetCount (4 * a.val) (y - 2) : ℝ) ≤
            (klTargetCount a.val y : ℝ) := by
        exact_mod_cast htargetNat
      simp only [ConcreteElimination.baseBody,
        ConcreteElimination.splitBody, ResidueSystem.system, hbranch,
        ConcreteElimination.transportLeaf,
        EliminationTree.eval, PrincipalLabel.value,
        zero_add,
        show y + (0 - 2) = y - 2 by ring]
      exact htransport.trans htarget |>.trans_eq hparent
  | advanced =>
      have ha3 : a.val % 3 = 2 := klTarget_mod_three (by omega) a
      obtain ⟨j, child, hchildVal⟩ :=
        exists_advancedChildTarget hk state hbranch a
      have hchild := branchPhiMin_le_target state j child
        (y + alpha - 1)
      rw [hchildVal] at hchild
      have htargetNat := klTargetCount_four_add_oddPredecessor_le
        a.property.1 ha3 a.property.2.2 hy
      have htarget :
          (klTargetCount (4 * a.val) (y - 2) : ℝ) +
              (klTargetCount ((2 * a.val - 1) / 3)
                (y + alpha - 1) : ℝ) ≤
            (klTargetCount a.val y : ℝ) := by
        exact_mod_cast htargetNat
      simp only [ConcreteElimination.baseBody,
        ConcreteElimination.splitBody, ResidueSystem.system, hbranch,
        ConcreteElimination.transportLeaf,
        ConcreteElimination.branchMinimum,
        ConcreteElimination.inf3,
        ConcreteElimination.branchLeaf,
        ConcreteElimination.branchLabel,
        EliminationTree.eval, PrincipalLabel.value,
        zero_add,
        show y + (0 - 2) = y - 2 by ring,
        show y + (alpha - 1) = y + alpha - 1 by ring]
      exact (add_le_add htransport hchild).trans htarget |>.trans_eq hparent

end CleanLean.KL

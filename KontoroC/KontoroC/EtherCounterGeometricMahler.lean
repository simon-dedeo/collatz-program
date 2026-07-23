/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterLinearTheta

/-!
# Geometric ether schedules and a Mahler-value obstruction

For a one-based geometric branch schedule `n_t = n₀ * d^t`, the forced
ternary core of the autonomous ether register obeys

`2^(8*n_(t+1)+15) u_(t+1) = 3^(6*n_t+11) u_t + 17`.

This file proves the exact finite backward expansion and identifies its
`Q_2` limit with the lacunary Mahler series

`G(x) = sum_j (2^15/3^11)^j * x^(1+d+...+d^(j-1))`.

It also proves the functional equation `G(x)=1+a*x*G(x^d)`.  An elementary
ordered-rational argument ultimately excludes every such positive ray
unconditionally; the p-adic irrationality endpoint is retained as an
independent arithmetic interpretation.  No transcendence theorem is
postulated.
-/

namespace KontoroC
namespace EtherCounterGeometricMahler

open Filter Topology MersennePacketRenewal

def branch (n₀ d t : ℕ) : ℕ := n₀ * d ^ t

def binaryExponent (n₀ d t : ℕ) : ℕ :=
  8 * branch n₀ d (t + 1) + 15

def ternaryExponent (n₀ d t : ℕ) : ℕ :=
  6 * branch n₀ d t + 11

/-- `1+d+⋯+d^(j-1)`, defined without natural-number division. -/
def geometricExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + d * geometricExponent d j

@[simp] theorem geometricExponent_zero (d : ℕ) :
    geometricExponent d 0 = 0 := rfl

@[simp] theorem geometricExponent_succ (d j : ℕ) :
    geometricExponent d (j + 1) = 1 + d * geometricExponent d j := rfl

theorem geometricExponent_add_power (d j : ℕ) :
    geometricExponent d j + d ^ j = geometricExponent d (j + 1) := by
  induction j with
  | zero => simp [geometricExponent]
  | succ j ih =>
      calc
        geometricExponent d (j + 1) + d ^ (j + 1) =
            (1 + d * geometricExponent d j) + d * d ^ j := by
          rw [geometricExponent_succ, pow_succ]
          ring
        _ = 1 + d * (geometricExponent d j + d ^ j) := by ring
        _ = 1 + d * geometricExponent d (j + 1) := by rw [ih]
        _ = geometricExponent d (j + 2) := by
          simp [geometricExponent]

theorem geometricExponent_eq_sum (d j : ℕ) :
    geometricExponent d j = ∑ k ∈ Finset.range j, d ^ k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact (geometricExponent_add_power d j).symm

/-- One-based form of the uniform EC17 defect contraction. -/
theorem fifteen_mul_two_pow_lt_three_pow (n : ℕ) (hn : 0 < n) :
    15 * 2 ^ (8 * n + 15) < 3 ^ (6 * n + 11) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hbase : 15 * 2 ^ 23 < 3 ^ 17 := by norm_num
  have hscale : (2 ^ 8) ^ k ≤ (3 ^ 6) ^ k :=
    Nat.pow_le_pow_left (by norm_num) k
  have hscale_pos : 0 < (2 ^ 8) ^ k := by positivity
  calc
    15 * 2 ^ (8 * (k + 1) + 15) =
        (15 * 2 ^ 23) * (2 ^ 8) ^ k := by
      rw [show 8 * (k + 1) + 15 = 23 + 8 * k by omega,
        pow_add, pow_mul]
      ring
    _ < 3 ^ 17 * (2 ^ 8) ^ k :=
      (Nat.mul_lt_mul_right hscale_pos).2 hbase
    _ ≤ 3 ^ 17 * (3 ^ 6) ^ k := Nat.mul_le_mul_left _ hscale
    _ = 3 ^ (6 * (k + 1) + 11) := by
      rw [show 6 * (k + 1) + 11 = 17 + 6 * k by omega,
        pow_add, pow_mul]

/-- A coarse expansion separator used by the elementary geometric no-go. -/
theorem two_mul_three_pow_lt_two_pow_double (n : ℕ) (hn : 0 < n) :
    2 * 3 ^ (6 * n + 11) < 2 ^ (16 * n + 15) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hbase : 2 * 3 ^ 17 < 2 ^ 31 := by norm_num
  have hscale : (3 ^ 6) ^ k ≤ (2 ^ 16) ^ k :=
    Nat.pow_le_pow_left (by norm_num) k
  have hscale_pos : 0 < (3 ^ 6) ^ k := by positivity
  calc
    2 * 3 ^ (6 * (k + 1) + 11) =
        (2 * 3 ^ 17) * (3 ^ 6) ^ k := by
      rw [show 6 * (k + 1) + 11 = 17 + 6 * k by omega,
        pow_add, pow_mul]
      ring
    _ < 2 ^ 31 * (3 ^ 6) ^ k :=
      (Nat.mul_lt_mul_right hscale_pos).2 hbase
    _ ≤ 2 ^ 31 * (2 ^ 16) ^ k := Nat.mul_le_mul_left _ hscale
    _ = 2 ^ (16 * (k + 1) + 15) := by
      rw [show 16 * (k + 1) + 15 = 31 + 16 * k by omega,
        pow_add, pow_mul]

/-- A necessary arithmetic projection of an infinite EC17 core orbit on a
positive geometric branch schedule. -/
structure Ray where
  initialBranch : ℕ
  multiplier : ℕ
  initialBranch_pos : 0 < initialBranch
  multiplier_ge_two : 2 ≤ multiplier
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  balance : ∀ t,
    2 ^ binaryExponent initialBranch multiplier t * core (t + 1) =
      3 ^ ternaryExponent initialBranch multiplier t * core t + 17

namespace Ray

def backwardCoeff (g : Ray) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
    (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t

def backwardDefect (g : Ray) (t : ℕ) : ℚ :=
  17 / (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t

theorem step_backward (g : Ray) (t : ℕ) :
    (g.core t : ℚ) =
      g.backwardCoeff t * g.core (t + 1) - g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t *
          g.core (t + 1) =
        (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t *
          g.core t + 17 := by
    exact_mod_cast g.balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree :
      (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier t ≠ 0 := by
    positivity
  field_simp
  nlinarith

theorem finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ) =
      backwardPrefixProduct g.backwardCoeff N * g.core N -
        backwardPrefixDefect g.backwardCoeff g.backwardDefect N :=
  backward_affine_unroll (fun t => g.step_backward t) N

theorem backwardPrefixDefect_eq_sum (g : Ray) (N : ℕ) :
    backwardPrefixDefect g.backwardCoeff g.backwardDefect N =
      ∑ t ∈ Finset.range N,
        backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect, Finset.sum_range_succ, ih]

/-- Closed product exponent underlying QM78. -/
theorem backwardPrefixProduct_eq_closed (g : Ray) (N : ℕ) :
    backwardPrefixProduct g.backwardCoeff N =
      (2 : ℚ) ^
          (8 * g.initialBranch * g.multiplier *
            geometricExponent g.multiplier N + 15 * N) /
        (3 : ℚ) ^
          (6 * g.initialBranch * geometricExponent g.multiplier N + 11 * N) := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, ih]
      simp only [backwardCoeff, binaryExponent, ternaryExponent, branch]
      rw [div_mul_div_comm, ← pow_add, ← pow_add]
      congr 2
      · rw [pow_succ]
        calc
          8 * g.initialBranch * g.multiplier *
                  geometricExponent g.multiplier N + 15 * N +
                (8 * (g.initialBranch *
                    (g.multiplier ^ N * g.multiplier)) + 15) =
              8 * g.initialBranch * g.multiplier *
                  (geometricExponent g.multiplier N + g.multiplier ^ N) +
                15 * (N + 1) := by ring
          _ = 8 * g.initialBranch * g.multiplier *
                  geometricExponent g.multiplier (N + 1) + 15 * (N + 1) := by
            rw [geometricExponent_add_power]
      · calc
          6 * g.initialBranch * geometricExponent g.multiplier N + 11 * N +
                (6 * (g.initialBranch * g.multiplier ^ N) + 11) =
              6 * g.initialBranch *
                  (geometricExponent g.multiplier N + g.multiplier ^ N) +
                11 * (N + 1) := by ring
          _ = 6 * g.initialBranch * geometricExponent g.multiplier (N + 1) +
                11 * (N + 1) := by
            rw [geometricExponent_add_power]

def coefficient (_g : Ray) : ℚ := (2 : ℚ) ^ 15 / (3 : ℚ) ^ 11

def argument (g : Ray) : ℚ :=
  (2 : ℚ) ^ (8 * g.initialBranch * g.multiplier) /
    (3 : ℚ) ^ (6 * g.initialBranch * g.multiplier)

def mahlerTerm (g : Ray) (j : ℕ) : ℚ :=
  g.coefficient ^ j * g.argument ^ geometricExponent g.multiplier j

def candidateScale (g : Ray) : ℚ :=
  17 / (3 : ℚ) ^ (6 * g.initialBranch + 11)

/-- QM78 in coefficient form: the `j`th accumulated defect is exactly the
scaled `j`th term of the lacunary Mahler series. -/
theorem weightedDefect_eq_scaled_mahlerTerm (g : Ray) (j : ℕ) :
    backwardPrefixProduct g.backwardCoeff j * g.backwardDefect j =
      g.candidateScale * g.mahlerTerm j := by
  rw [g.backwardPrefixProduct_eq_closed j]
  have he := geometricExponent_add_power g.multiplier j
  simp only [backwardDefect, ternaryExponent, branch, candidateScale,
    mahlerTerm, coefficient, argument]
  simp only [div_pow, pow_add, pow_mul]
  field_simp
  simp only [← pow_mul, ← pow_add]
  congr 1
  calc
    6 * g.initialBranch +
          6 * g.initialBranch * g.multiplier *
            geometricExponent g.multiplier j =
        6 * g.initialBranch *
          (1 + g.multiplier * geometricExponent g.multiplier j) := by ring
    _ = 6 * g.initialBranch * geometricExponent g.multiplier (j + 1) := by
      rw [geometricExponent_succ]
    _ = 6 * g.initialBranch *
          (geometricExponent g.multiplier j + g.multiplier ^ j) := by rw [he]
    _ = 6 * g.initialBranch * geometricExponent g.multiplier j +
          6 * g.initialBranch * g.multiplier ^ j := by ring

/-! ## Elementary real obstruction -/

/-- The positive defect term at time `t`, before passing to `Q_2`. -/
def weightedDefect (g : Ray) (t : ℕ) : ℚ :=
  backwardPrefixProduct g.backwardCoeff t * g.backwardDefect t

theorem branch_pos (g : Ray) (t : ℕ) :
    0 < branch g.initialBranch g.multiplier t := by
  exact Nat.mul_pos g.initialBranch_pos
    (pow_pos (lt_of_lt_of_le (by norm_num) g.multiplier_ge_two) t)

theorem two_mul_branch_le_next (g : Ray) (t : ℕ) :
    2 * branch g.initialBranch g.multiplier t ≤
      branch g.initialBranch g.multiplier (t + 1) := by
  simp only [branch, pow_succ]
  nlinarith [g.multiplier_ge_two,
    Nat.zero_le (g.initialBranch * g.multiplier ^ t)]

/-- A geometric schedule makes every backward coefficient larger than two.
This is deliberately coarser than the closed product formula. -/
theorem two_lt_backwardCoeff (g : Ray) (t : ℕ) :
    (2 : ℚ) < g.backwardCoeff t := by
  let n := branch g.initialBranch g.multiplier t
  have hn : 0 < n := g.branch_pos t
  have hdouble : 2 * n ≤ branch g.initialBranch g.multiplier (t + 1) :=
    g.two_mul_branch_le_next t
  have hexp : 16 * n + 15 ≤
      binaryExponent g.initialBranch g.multiplier t := by
    simp only [binaryExponent]
    omega
  have hpow : 2 ^ (16 * n + 15) ≤
      2 ^ binaryExponent g.initialBranch g.multiplier t :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hnat :
      2 * 3 ^ ternaryExponent g.initialBranch g.multiplier t <
        2 ^ binaryExponent g.initialBranch g.multiplier t := by
    apply (two_mul_three_pow_lt_two_pow_double n hn).trans_le
    simpa only [ternaryExponent] using hpow
  rw [backwardCoeff]
  apply (lt_div_iff₀ (by positivity :
    (0 : ℚ) < 3 ^ ternaryExponent g.initialBranch g.multiplier t)).2
  exact_mod_cast hnat

theorem backwardPrefixProduct_pos (g : Ray) (t : ℕ) :
    0 < backwardPrefixProduct g.backwardCoeff t := by
  induction t with
  | zero => simp [backwardPrefixProduct]
  | succ t ih =>
      rw [backwardPrefixProduct]
      exact mul_pos ih (by simp [backwardCoeff])

theorem weightedDefect_pos (g : Ray) (t : ℕ) :
    0 < g.weightedDefect t :=
  mul_pos (g.backwardPrefixProduct_pos t) (by simp [backwardDefect])

/-- Exact cancellation behind QM84. -/
theorem weightedDefect_succ (g : Ray) (t : ℕ) :
    g.weightedDefect (t + 1) =
      g.weightedDefect t *
        ((2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
          (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1)) := by
  simp only [weightedDefect, backwardPrefixProduct, backwardCoeff,
    backwardDefect]
  ring

/-- QM84 without division: consecutive positive defect terms contract by a
factor strictly smaller than `1/15`. -/
theorem fifteen_mul_weightedDefect_succ_lt (g : Ray) (t : ℕ) :
    15 * g.weightedDefect (t + 1) < g.weightedDefect t := by
  have hn : 0 < branch g.initialBranch g.multiplier (t + 1) :=
    g.branch_pos (t + 1)
  have hnat := fifteen_mul_two_pow_lt_three_pow
    (branch g.initialBranch g.multiplier (t + 1)) hn
  have hnatQ :
      (15 : ℚ) * (2 : ℚ) ^
          (8 * branch g.initialBranch g.multiplier (t + 1) + 15) <
        (3 : ℚ) ^
          (6 * branch g.initialBranch g.multiplier (t + 1) + 11) := by
    exact_mod_cast hnat
  have hratio :
      15 * ((2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
        (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1)) < 1 := by
    calc
      15 * ((2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
          (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1)) =
          (15 * (2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t) /
            (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1) :=
        by ring
      _ < 1 := by
        apply (div_lt_iff₀ (by positivity :
          (0 : ℚ) < 3 ^ ternaryExponent g.initialBranch g.multiplier (t + 1))).2
        simpa only [binaryExponent, ternaryExponent, one_mul] using hnatQ
  rw [g.weightedDefect_succ]
  have hw := g.weightedDefect_pos t
  calc
    15 * (g.weightedDefect t *
        ((2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
          (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1))) =
        g.weightedDefect t *
          (15 * ((2 : ℚ) ^ binaryExponent g.initialBranch g.multiplier t /
            (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier (t + 1))) := by
      ring
    _ < g.weightedDefect t * 1 := mul_lt_mul_of_pos_left hratio hw
    _ = g.weightedDefect t := mul_one _

/-- The finite defect partial sum plus twice its next term never exceeds
twice the initial term.  This is a convenient coarse geometric-tail bound. -/
theorem defectPartial_add_two_weightedDefect_le (g : Ray) (N : ℕ) :
    backwardPrefixDefect g.backwardCoeff g.backwardDefect N +
        2 * g.weightedDefect N ≤
      2 * g.weightedDefect 0 := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect]
      change
        backwardPrefixDefect g.backwardCoeff g.backwardDefect N +
              g.weightedDefect N + 2 * g.weightedDefect (N + 1) ≤
          2 * g.weightedDefect 0
      have hcontract := g.fifteen_mul_weightedDefect_succ_lt N
      have hpos := g.weightedDefect_pos (N + 1)
      have htwo : 2 * g.weightedDefect (N + 1) ≤
          g.weightedDefect N := by linarith
      exact le_trans (by linarith) ih

theorem backwardPrefixDefect_nonneg (g : Ray) (N : ℕ) :
    0 ≤ backwardPrefixDefect g.backwardCoeff g.backwardDefect N := by
  rw [g.backwardPrefixDefect_eq_sum]
  exact Finset.sum_nonneg fun t _ => (g.weightedDefect_pos t).le

theorem two_mul_weightedDefect_zero_lt_one (g : Ray) :
    2 * g.weightedDefect 0 < 1 := by
  have hn : 17 ≤ ternaryExponent g.initialBranch g.multiplier 0 := by
    simp only [ternaryExponent, branch, pow_zero, mul_one]
    have := g.initialBranch_pos
    omega
  have hpow : 3 ^ 17 ≤
      3 ^ ternaryExponent g.initialBranch g.multiplier 0 :=
    Nat.pow_le_pow_right (by norm_num) hn
  have hden : 34 < 3 ^ ternaryExponent g.initialBranch g.multiplier 0 :=
    (by norm_num : 34 < 3 ^ 17).trans_le hpow
  have hdenQ : (34 : ℚ) <
      (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier 0 := by
    exact_mod_cast hden
  simp only [weightedDefect, backwardPrefixProduct, backwardDefect,
    one_mul]
  calc
    2 * (17 / (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier 0) =
        34 / (3 : ℚ) ^ ternaryExponent g.initialBranch g.multiplier 0 := by
      ring
    _ < 1 := by
      apply (div_lt_iff₀ (by positivity :
        (0 : ℚ) < 3 ^ ternaryExponent g.initialBranch g.multiplier 0)).2
      simpa using hdenQ

/-- QM85 in the only form needed downstream. -/
theorem backwardPrefixDefect_lt_one (g : Ray) (N : ℕ) :
    backwardPrefixDefect g.backwardCoeff g.backwardDefect N < 1 := by
  have htail := g.defectPartial_add_two_weightedDefect_le N
  have hpos := g.weightedDefect_pos N
  exact lt_of_le_of_lt (by linarith) g.two_mul_weightedDefect_zero_lt_one

/-- QM86: every cumulative scale lies in a fixed unit-width interval. -/
theorem cumulativeScale_trap (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ) ≤
        backwardPrefixProduct g.backwardCoeff N * g.core N ∧
      backwardPrefixProduct g.backwardCoeff N * g.core N <
        (g.core 0 : ℚ) + 1 := by
  have hseries := g.finite_series N
  have hnonneg := g.backwardPrefixDefect_nonneg N
  have hlt := g.backwardPrefixDefect_lt_one N
  constructor <;> linarith

/-- Prefix products grow faster than `2^(N+1)`. -/
theorem two_pow_succ_lt_backwardPrefixProduct (g : Ray) (N : ℕ) :
    (2 : ℚ) ^ (N + 1) <
      backwardPrefixProduct g.backwardCoeff (N + 1) := by
  induction N with
  | zero =>
      simp only [backwardPrefixProduct, pow_one, one_mul]
      exact g.two_lt_backwardCoeff 0
  | succ N ih =>
      rw [backwardPrefixProduct]
      have hp : 0 < backwardPrefixProduct g.backwardCoeff (N + 1) := by
        exact g.backwardPrefixProduct_pos (N + 1)
      calc
        (2 : ℚ) ^ (N + 1 + 1) = 2 ^ (N + 1) * 2 := by
          rw [pow_succ]
        _ < backwardPrefixProduct g.backwardCoeff (N + 1) * 2 :=
          mul_lt_mul_of_pos_right ih (by norm_num)
        _ < backwardPrefixProduct g.backwardCoeff (N + 1) *
            g.backwardCoeff (N + 1) :=
          mul_lt_mul_of_pos_left (g.two_lt_backwardCoeff (N + 1)) hp

/-- QM87: geometric one-based EC17 rays are unconditionally impossible.
The proof is finite and ordered; no p-adic transcendence input is used. -/
theorem impossible (g : Ray) : False := by
  let N := g.core 0 + 1
  have htrap := g.cumulativeScale_trap N
  have hprod := g.two_pow_succ_lt_backwardPrefixProduct (g.core 0)
  have hcore : (1 : ℚ) ≤ g.core N := by
    exact_mod_cast g.core_pos N
  have hscale : (2 : ℚ) ^ N <
      backwardPrefixProduct g.backwardCoeff N * g.core N := by
    have hN : N = g.core 0 + 1 := rfl
    rw [hN]
    calc
      (2 : ℚ) ^ (g.core 0 + 1) <
          backwardPrefixProduct g.backwardCoeff (g.core 0 + 1) := hprod
      _ = backwardPrefixProduct g.backwardCoeff (g.core 0 + 1) * 1 := by ring
      _ ≤ backwardPrefixProduct g.backwardCoeff (g.core 0 + 1) *
          g.core (g.core 0 + 1) :=
        mul_le_mul_of_nonneg_left hcore
          (le_of_lt (g.backwardPrefixProduct_pos (g.core 0 + 1)))
  have hnat : (g.core 0 : ℚ) + 1 < (2 : ℚ) ^ N := by
    exact_mod_cast (show g.core 0 + 1 < 2 ^ (g.core 0 + 1) from
      Nat.lt_two_pow_self)
  linarith

end Ray

/-! ## The p-adic Mahler function -/

noncomputable def padicCoefficient : ℚ_[2] :=
  (2 : ℚ_[2]) ^ 15 / (3 : ℚ_[2]) ^ 11

noncomputable def padicMahlerTerm (d : ℕ) (x : ℚ_[2]) (j : ℕ) : ℚ_[2] :=
  padicCoefficient ^ j * x ^ geometricExponent d j

theorem padicMahlerTerm_zero (d : ℕ) (x : ℚ_[2]) :
    padicMahlerTerm d x 0 = 1 := by simp [padicMahlerTerm]

/-- The coefficient-level identity behind `G(x)=1+a*x*G(x^d)`. -/
theorem padicMahlerTerm_succ (d : ℕ) (x : ℚ_[2]) (j : ℕ) :
    padicMahlerTerm d x (j + 1) =
      padicCoefficient * x * padicMahlerTerm d (x ^ d) j := by
  simp only [padicMahlerTerm, geometricExponent_succ, pow_succ, pow_add,
    pow_mul]
  ring

theorem norm_padicCoefficient :
    ‖padicCoefficient‖ = ((2 : ℝ)⁻¹) ^ 15 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [padicCoefficient, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_padicMahlerTerm_le (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1)
    (j : ℕ) :
    ‖padicMahlerTerm d x j‖ ≤ (((2 : ℝ)⁻¹) ^ 15) ^ j := by
  rw [padicMahlerTerm, norm_mul, norm_pow, norm_pow, norm_padicCoefficient]
  have hxpow : ‖x‖ ^ geometricExponent d j ≤ 1 :=
    pow_le_one₀ (norm_nonneg x) hx
  simpa using mul_le_mul_of_nonneg_left hxpow (by positivity :
    0 ≤ (((2 : ℝ)⁻¹) ^ 15) ^ j)

theorem padicMahlerTerm_tendsto_zero (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    Tendsto (padicMahlerTerm d x) atTop (nhds 0) := by
  apply squeeze_zero_norm (norm_padicMahlerTerm_le d hx)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicMahlerTerm_summable (d : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    Summable (padicMahlerTerm d x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using padicMahlerTerm_tendsto_zero d hx

noncomputable def padicMahler (d : ℕ) (x : ℚ_[2]) : ℚ_[2] :=
  ∑' j, padicMahlerTerm d x j

/-- QM80: the literal p-adic Mahler functional equation on the closed unit
ball. -/
theorem padicMahler_functionalEquation (d : ℕ) (x : ℚ_[2])
    (hx : ‖x‖ ≤ 1) :
    padicMahler d x = 1 + padicCoefficient * x * padicMahler d (x ^ d) := by
  have hxd : ‖x ^ d‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg x) hx
  unfold padicMahler
  rw [(padicMahlerTerm_summable d hx).tsum_eq_zero_add,
    padicMahlerTerm_zero]
  congr 1
  rw [← (padicMahlerTerm_summable d hxd).tsum_mul_left
    (padicCoefficient * x)]
  apply tsum_congr
  intro j
  exact padicMahlerTerm_succ d x j

/-! ## The exact EC17 endpoint -/

namespace Ray

noncomputable def padicArgument (g : Ray) : ℚ_[2] := (g.argument : ℚ_[2])

theorem norm_padicArgument (g : Ray) :
    ‖g.padicArgument‖ =
      ((2 : ℝ)⁻¹) ^ (8 * g.initialBranch * g.multiplier) := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [padicArgument, argument, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_padicArgument_le_one (g : Ray) : ‖g.padicArgument‖ ≤ 1 := by
  rw [g.norm_padicArgument]
  exact pow_le_one₀ (by positivity) (by norm_num)

noncomputable def padicMahlerValue (g : Ray) : ℚ_[2] :=
  padicMahler g.multiplier g.padicArgument

theorem padicMahlerValue_functionalEquation (g : Ray) :
    g.padicMahlerValue =
      1 + padicCoefficient * g.padicArgument *
        padicMahler g.multiplier (g.padicArgument ^ g.multiplier) :=
  padicMahler_functionalEquation g.multiplier g.padicArgument
    g.norm_padicArgument_le_one

noncomputable def padicDefectTerm (g : Ray) (j : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff j * g.backwardDefect j : ℚ_[2])

theorem binaryExponent_pos (g : Ray) (t : ℕ) :
    0 < binaryExponent g.initialBranch g.multiplier t := by
  simp [binaryExponent]

theorem norm_backwardCoeff (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ =
      ((2 : ℝ)⁻¹) ^ binaryExponent g.initialBranch g.multiplier t := by
  have htwo : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
  have hthree : ‖(3 : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  rw [backwardCoeff, Rat.cast_div, Rat.cast_pow, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofNat, norm_div, norm_pow, norm_pow,
    htwo, hthree, one_pow, div_one]

theorem norm_backwardCoeff_le_half (g : Ray) (t : ℕ) :
    ‖(g.backwardCoeff t : ℚ_[2])‖ ≤ (2 : ℝ)⁻¹ := by
  rw [g.norm_backwardCoeff]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (g.binaryExponent_pos t).ne'
  rw [hn, pow_succ]
  have hpow : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) n]

theorem norm_backwardPrefixProduct_le (g : Ray) (N : ℕ) :
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ ≤
      ((2 : ℝ)⁻¹) ^ N := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct, Rat.cast_mul, norm_mul, pow_succ]
      exact mul_le_mul ih (g.norm_backwardCoeff_le_half N)
        (norm_nonneg _) (by positivity)

theorem norm_backwardDefect_le_one (g : Ray) (t : ℕ) :
    ‖(g.backwardDefect t : ℚ_[2])‖ ≤ 1 := by
  have hthree : ‖((3 : ℚ) : ℚ_[2])‖ = 1 := by
    norm_num only [Rat.cast_ofNat]
    exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
  have h17 : ‖(17 : ℚ_[2])‖ ≤ 1 := by
    change ‖((Int.ofNat 17 : ℤ) : ℚ_[2])‖ ≤ 1
    exact Padic.norm_int_le_one (p := 2) (Int.ofNat 17)
  rw [backwardDefect, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    norm_div, norm_pow, hthree, one_pow, div_one]
  exact h17

theorem norm_padicDefectTerm_le (g : Ray) (j : ℕ) :
    ‖g.padicDefectTerm j‖ ≤ ((2 : ℝ)⁻¹) ^ j := by
  rw [padicDefectTerm, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ *
          ‖(g.backwardDefect j : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (g.norm_backwardDefect_le_one j)
        (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff j : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ j := g.norm_backwardPrefixProduct_le j

theorem padicDefectTerm_tendsto_zero (g : Ray) :
    Tendsto g.padicDefectTerm atTop (nhds 0) := by
  apply squeeze_zero_norm g.norm_padicDefectTerm_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padicDefectTerm_summable (g : Ray) : Summable g.padicDefectTerm := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using g.padicDefectTerm_tendsto_zero

noncomputable def padicDefectSum (g : Ray) : ℚ_[2] :=
  ∑' j, g.padicDefectTerm j

theorem padicDefectTerm_eq_scaled_mahlerTerm (g : Ray) (j : ℕ) :
    g.padicDefectTerm j =
      (g.candidateScale : ℚ_[2]) *
        padicMahlerTerm g.multiplier g.padicArgument j := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.weightedDefect_eq_scaled_mahlerTerm j)
  simpa [padicDefectTerm, padicMahlerTerm, padicCoefficient,
    padicArgument, mahlerTerm, coefficient, argument, Rat.cast_mul,
    Rat.cast_pow] using h

theorem padicDefectSum_eq_scaled_mahlerValue (g : Ray) :
    g.padicDefectSum =
      (g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by
  have hs := (padicMahlerTerm_summable g.multiplier
    g.norm_padicArgument_le_one).hasSum.mul_left (g.candidateScale : ℚ_[2])
  have hfun :
      (fun j => (g.candidateScale : ℚ_[2]) *
        padicMahlerTerm g.multiplier g.padicArgument j) = g.padicDefectTerm := by
    funext j
    exact (g.padicDefectTerm_eq_scaled_mahlerTerm j).symm
  rw [hfun] at hs
  exact g.padicDefectTerm_summable.hasSum.unique hs

noncomputable def padicDefectPartial (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixDefect g.backwardCoeff g.backwardDefect N : ℚ_[2])

theorem padicDefectPartial_eq_sum (g : Ray) (N : ℕ) :
    g.padicDefectPartial N =
      ∑ j ∈ Finset.range N, g.padicDefectTerm j := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2]))
    (g.backwardPrefixDefect_eq_sum N)
  simpa [padicDefectPartial, padicDefectTerm, map_sum, Rat.cast_mul] using h

theorem padicDefectPartial_tendsto_sum (g : Ray) :
    Tendsto g.padicDefectPartial atTop (nhds g.padicDefectSum) := by
  have hsum := g.padicDefectTerm_summable.hasSum.tendsto_sum_nat
  have heq : g.padicDefectPartial = fun N =>
      ∑ j ∈ Finset.range N, g.padicDefectTerm j := by
    funext N
    exact g.padicDefectPartial_eq_sum N
  rw [heq]
  simpa only [padicDefectSum] using hsum

noncomputable def padicTerminal (g : Ray) (N : ℕ) : ℚ_[2] :=
  (backwardPrefixProduct g.backwardCoeff N : ℚ_[2]) * g.core N

theorem norm_padicTerminal_le (g : Ray) (N : ℕ) :
    ‖g.padicTerminal N‖ ≤ ((2 : ℝ)⁻¹) ^ N := by
  have hcore : ‖(g.core N : ℚ_[2])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := 2) (Int.ofNat (g.core N))
  rw [padicTerminal, norm_mul]
  calc
    ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ *
          ‖(g.core N : ℚ_[2])‖ ≤
        ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left hcore (norm_nonneg _)
    _ = ‖(backwardPrefixProduct g.backwardCoeff N : ℚ_[2])‖ := mul_one _
    _ ≤ ((2 : ℝ)⁻¹) ^ N := g.norm_backwardPrefixProduct_le N

theorem padicTerminal_tendsto_zero (g : Ray) :
    Tendsto g.padicTerminal atTop (nhds 0) := by
  apply squeeze_zero_norm g.norm_padicTerminal_le
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)

theorem padic_finite_series (g : Ray) (N : ℕ) :
    (g.core 0 : ℚ_[2]) =
      g.padicTerminal N - g.padicDefectPartial N := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[2])) (g.finite_series N)
  simpa [padicTerminal, padicDefectPartial, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast] using h

/-- QM79: every ordinary geometric EC17 ray forces its initial core to equal
the negative scaled Mahler value in `Q_2`. -/
theorem initial_eq_negative_scaled_mahlerValue (g : Ray) :
    (g.core 0 : ℚ_[2]) =
      -(g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by
  have heq : g.padicDefectPartial = fun N =>
      g.padicTerminal N - (g.core 0 : ℚ_[2]) := by
    funext N
    have h := g.padic_finite_series N
    linear_combination h
  have hlim : Tendsto g.padicDefectPartial atTop
      (nhds (-(g.core 0 : ℚ_[2]))) := by
    rw [heq]
    simpa only [zero_sub] using
      g.padicTerminal_tendsto_zero.sub tendsto_const_nhds
  have hsum : g.padicDefectSum = -(g.core 0 : ℚ_[2]) :=
    tendsto_nhds_unique g.padicDefectPartial_tendsto_sum hlim
  rw [g.padicDefectSum_eq_scaled_mahlerValue] at hsum
  calc
    (g.core 0 : ℚ_[2]) =
        -((g.candidateScale : ℚ_[2]) * g.padicMahlerValue) := by
      rw [hsum]
      simp
    _ = -(g.candidateScale : ℚ_[2]) * g.padicMahlerValue := by ring

theorem candidateScale_ne_zero (g : Ray) : g.candidateScale ≠ 0 := by
  simp [candidateScale]

theorem padic_candidateScale_ne_zero (g : Ray) :
    (g.candidateScale : ℚ_[2]) ≠ 0 := by
  exact_mod_cast g.candidateScale_ne_zero

/-- QM81, with the published transcendence input exposed as a premise. -/
theorem false_of_mahlerValue_irrational (g : Ray)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      g.padicMahlerValue) : False := by
  apply hirr (-(g.core 0 : ℚ) / g.candidateScale)
  rw [Rat.cast_div, Rat.cast_neg]
  apply (eq_div_iff g.padic_candidateScale_ne_zero).2
  have h := g.initial_eq_negative_scaled_mahlerValue
  have hcast : (((g.core 0 : ℚ) : ℚ_[2])) = (g.core 0 : ℚ_[2]) := by
    norm_num
  rw [hcast]
  rw [h]
  ring

end Ray

end EtherCounterGeometricMahler

/-! ## Connection to the executable ether normalization -/

open EtherCounterGeometricMahler
open MersennePacketRenewal

namespace EtherCounterAperiodic.TernaryCoreOrbit

/-! ## A schedule-independent cumulative-scale trap -/

def generalBackwardCoeff (o : EtherCounterAperiodic.TernaryCoreOrbit)
    (t : ℕ) : ℚ :=
  (2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
    (3 : ℚ) ^ (6 * o.level t + 17)

def generalBackwardDefect (o : EtherCounterAperiodic.TernaryCoreOrbit)
    (t : ℕ) : ℚ :=
  17 / (3 : ℚ) ^ (6 * o.level t + 17)

def generalWeightedDefect (o : EtherCounterAperiodic.TernaryCoreOrbit)
    (t : ℕ) : ℚ :=
  backwardPrefixProduct o.generalBackwardCoeff t * o.generalBackwardDefect t

/-- One-based branch level and its two prefix sums. -/
def oneBasedLevel (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) : ℕ :=
  o.level t + 1

def oneBasedLevelSum (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, o.oneBasedLevel i

def nextOneBasedLevelSum (o : EtherCounterAperiodic.TernaryCoreOrbit)
    (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, o.oneBasedLevel (i + 1)

theorem oneBasedLevelSum_succ
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    o.oneBasedLevelSum (N + 1) =
      o.oneBasedLevelSum N + o.oneBasedLevel N := by
  simp [oneBasedLevelSum, Finset.sum_range_succ]

theorem nextOneBasedLevelSum_succ
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    o.nextOneBasedLevelSum (N + 1) =
      o.nextOneBasedLevelSum N + o.oneBasedLevel (N + 1) := by
  simp [nextOneBasedLevelSum, Finset.sum_range_succ]

/-- Telescoping relation `T_N+n_0=S_N+n_N`. -/
theorem nextSum_add_initial_eq_sum_add_terminal
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    o.nextOneBasedLevelSum N + o.oneBasedLevel 0 =
      o.oneBasedLevelSum N + o.oneBasedLevel N := by
  induction N with
  | zero => simp [oneBasedLevelSum, nextOneBasedLevelSum]
  | succ N ih =>
      rw [o.nextOneBasedLevelSum_succ, o.oneBasedLevelSum_succ]
      omega

/-- Closed cumulative coefficient for an arbitrary schedule. -/
theorem generalBackwardPrefixProduct_eq_closed
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    backwardPrefixProduct o.generalBackwardCoeff N =
      (2 : ℚ) ^ (8 * o.nextOneBasedLevelSum N + 15 * N) /
        (3 : ℚ) ^ (6 * o.oneBasedLevelSum N + 11 * N) := by
  induction N with
  | zero => simp [backwardPrefixProduct, oneBasedLevelSum,
      nextOneBasedLevelSum]
  | succ N ih =>
      rw [backwardPrefixProduct, ih, o.nextOneBasedLevelSum_succ,
        o.oneBasedLevelSum_succ]
      simp only [generalBackwardCoeff, oneBasedLevel]
      rw [div_mul_div_comm, ← pow_add, ← pow_add]
      congr 2 <;> omega

theorem general_step_backward
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) :
    (o.core t : ℚ) =
      o.generalBackwardCoeff t * o.core (t + 1) -
        o.generalBackwardDefect t := by
  have h :
      (2 : ℚ) ^ (8 * o.level (t + 1) + 23) * o.core (t + 1) =
        (3 : ℚ) ^ (6 * o.level t + 17) * o.core t + 17 := by
    exact_mod_cast o.balance t
  dsimp [generalBackwardCoeff, generalBackwardDefect]
  field_simp
  nlinarith

theorem general_finite_series
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    (o.core 0 : ℚ) =
      backwardPrefixProduct o.generalBackwardCoeff N * o.core N -
        backwardPrefixDefect o.generalBackwardCoeff o.generalBackwardDefect N :=
  backward_affine_unroll (fun t => o.general_step_backward t) N

theorem generalBackwardPrefixProduct_pos
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    0 < backwardPrefixProduct o.generalBackwardCoeff N := by
  induction N with
  | zero => simp [backwardPrefixProduct]
  | succ N ih =>
      rw [backwardPrefixProduct]
      exact mul_pos ih (by simp [generalBackwardCoeff])

theorem generalWeightedDefect_pos
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) :
    0 < o.generalWeightedDefect t :=
  mul_pos (o.generalBackwardPrefixProduct_pos t)
    (by simp [generalBackwardDefect])

theorem generalWeightedDefect_succ
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) :
    o.generalWeightedDefect (t + 1) =
      o.generalWeightedDefect t *
        ((2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
          (3 : ℚ) ^ (6 * o.level (t + 1) + 17)) := by
  simp only [generalWeightedDefect, backwardPrefixProduct,
    generalBackwardCoeff, generalBackwardDefect]
  ring

theorem fifteen_mul_generalWeightedDefect_succ_lt
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) :
    15 * o.generalWeightedDefect (t + 1) <
      o.generalWeightedDefect t := by
  have hnat := EtherCounterAperiodic.fifteen_mul_edgeB_lt_edgeA
    (o.level (t + 1))
  have hnat' :
      15 * 2 ^ (8 * o.level (t + 1) + 23) <
        3 ^ (6 * o.level (t + 1) + 17) := by
    simpa [EtherCounterAperiodic.edgeA, EtherCounterAperiodic.edgeB,
      EtherCounterAperiodic.binaryExponent,
      EtherCounterAperiodic.ternaryExponent] using hnat
  have hnatQ :
      (15 : ℚ) * (2 : ℚ) ^ (8 * o.level (t + 1) + 23) <
        (3 : ℚ) ^ (6 * o.level (t + 1) + 17) := by
    exact_mod_cast hnat'
  have hratio :
      15 * ((2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
        (3 : ℚ) ^ (6 * o.level (t + 1) + 17)) < 1 := by
    calc
      15 * ((2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
          (3 : ℚ) ^ (6 * o.level (t + 1) + 17)) =
          (15 * (2 : ℚ) ^ (8 * o.level (t + 1) + 23)) /
            (3 : ℚ) ^ (6 * o.level (t + 1) + 17) := by ring
      _ < 1 := by
        apply (div_lt_iff₀ (by positivity :
          (0 : ℚ) < 3 ^ (6 * o.level (t + 1) + 17))).2
        simpa using hnatQ
  rw [o.generalWeightedDefect_succ]
  have hw := o.generalWeightedDefect_pos t
  calc
    15 * (o.generalWeightedDefect t *
        ((2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
          (3 : ℚ) ^ (6 * o.level (t + 1) + 17))) =
        o.generalWeightedDefect t *
          (15 * ((2 : ℚ) ^ (8 * o.level (t + 1) + 23) /
            (3 : ℚ) ^ (6 * o.level (t + 1) + 17))) := by ring
    _ < o.generalWeightedDefect t * 1 := mul_lt_mul_of_pos_left hratio hw
    _ = o.generalWeightedDefect t := mul_one _

theorem generalDefectPartial_add_two_weighted_le
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    backwardPrefixDefect o.generalBackwardCoeff o.generalBackwardDefect N +
        2 * o.generalWeightedDefect N ≤
      2 * o.generalWeightedDefect 0 := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect]
      change
        backwardPrefixDefect o.generalBackwardCoeff o.generalBackwardDefect N +
              o.generalWeightedDefect N +
                2 * o.generalWeightedDefect (N + 1) ≤
          2 * o.generalWeightedDefect 0
      have hcontract := o.fifteen_mul_generalWeightedDefect_succ_lt N
      have hpos := o.generalWeightedDefect_pos (N + 1)
      have htwo : 2 * o.generalWeightedDefect (N + 1) ≤
          o.generalWeightedDefect N := by linarith
      exact le_trans (by linarith) ih

theorem generalBackwardPrefixDefect_nonneg
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    0 ≤ backwardPrefixDefect o.generalBackwardCoeff o.generalBackwardDefect N := by
  induction N with
  | zero => simp [backwardPrefixDefect]
  | succ N ih =>
      rw [backwardPrefixDefect]
      exact add_nonneg ih (o.generalWeightedDefect_pos N).le

theorem two_mul_generalWeightedDefect_zero_lt_one
    (o : EtherCounterAperiodic.TernaryCoreOrbit) :
    2 * o.generalWeightedDefect 0 < 1 := by
  have hden : 34 < 3 ^ (6 * o.level 0 + 17) := by
    exact (by norm_num : 34 < 3 ^ 17).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hdenQ : (34 : ℚ) < (3 : ℚ) ^ (6 * o.level 0 + 17) := by
    exact_mod_cast hden
  simp only [generalWeightedDefect, backwardPrefixProduct,
    generalBackwardDefect, one_mul]
  calc
    2 * (17 / (3 : ℚ) ^ (6 * o.level 0 + 17)) =
        34 / (3 : ℚ) ^ (6 * o.level 0 + 17) := by ring
    _ < 1 := by
      apply (div_lt_iff₀ (by positivity :
        (0 : ℚ) < 3 ^ (6 * o.level 0 + 17))).2
      simpa using hdenQ

/-- Schedule-independent form of QM86. -/
theorem general_cumulativeScale_trap
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    (o.core 0 : ℚ) ≤
        backwardPrefixProduct o.generalBackwardCoeff N * o.core N ∧
      backwardPrefixProduct o.generalBackwardCoeff N * o.core N <
        (o.core 0 : ℚ) + 1 := by
  have hseries := o.general_finite_series N
  have hnonneg := o.generalBackwardPrefixDefect_nonneg N
  have htail := o.generalDefectPartial_add_two_weighted_le N
  have hterm := o.generalWeightedDefect_pos N
  have hinitial := o.two_mul_generalWeightedDefect_zero_lt_one
  have hdefect :
      backwardPrefixDefect o.generalBackwardCoeff o.generalBackwardDefect N < 1 :=
    lt_of_le_of_lt (by linarith) hinitial
  constructor <;> linarith

/-- Every positive execution keeps its cumulative backward coefficient below
the fixed natural threshold `core(0)+1`. -/
theorem general_backwardPrefixProduct_lt_core_succ
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) :
    backwardPrefixProduct o.generalBackwardCoeff N < (o.core 0 : ℚ) + 1 := by
  have htrap := (o.general_cumulativeScale_trap N).2
  have hcore : (1 : ℚ) ≤ o.core N := by exact_mod_cast o.core_pos N
  have hp := o.generalBackwardPrefixProduct_pos N
  nlinarith

theorem three_pow_41_lt_two_pow_65 : 3 ^ 41 < 2 ^ 65 := by norm_num

/-- QM89: a sharp integral ceiling on every one-based branch history.  It is
obtained from the universal product budget using `3^41 < 2^65`. -/
theorem terminalBranch_ceiling
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (N : ℕ) (hN : 0 < N) :
    328 * o.oneBasedLevel N <
      62 * o.oneBasedLevelSum N + 328 * o.oneBasedLevel 0 +
        100 * N + 41 * o.core 0 := by
  by_contra hbad
  push Not at hbad
  let S := o.oneBasedLevelSum N
  let T := o.nextOneBasedLevelSum N
  let n₀ := o.oneBasedLevel 0
  let nN := o.oneBasedLevel N
  let u₀ := o.core 0
  have hshift : T + n₀ = S + nN := by
    simpa [S, T, n₀, nN] using o.nextSum_add_initial_eq_sum_add_terminal N
  have hbad' : 62 * S + 328 * n₀ + 100 * N + 41 * u₀ ≤
      328 * nN := by
    simpa [S, n₀, nN, u₀] using hbad
  have hexponents :
      390 * S + 715 * N + 41 * u₀ ≤ 328 * T + 615 * N := by
    omega
  let k := 6 * S + 11 * N
  have hk : 0 < k := by simp [k]; omega
  have hdenNat : 3 ^ (246 * S + 451 * N) <
      2 ^ (390 * S + 715 * N) := by
    calc
      3 ^ (246 * S + 451 * N) = (3 ^ 41) ^ k := by
        rw [show 246 * S + 451 * N = 41 * k by simp [k]; omega,
          pow_mul]
      _ < (2 ^ 65) ^ k := Nat.pow_lt_pow_left three_pow_41_lt_two_pow_65 hk.ne'
      _ = 2 ^ (390 * S + 715 * N) := by
        rw [← pow_mul]
        congr 1
        simp [k]
        omega
  have hdenQ :
      (3 : ℚ) ^ (246 * S + 451 * N) <
        (2 : ℚ) ^ (390 * S + 715 * N) := by
    exact_mod_cast hdenNat
  have hnumPow :
      (2 : ℚ) ^ (390 * S + 715 * N + 41 * u₀) ≤
        (2 : ℚ) ^ (328 * T + 615 * N) :=
    pow_le_pow_right₀ (by norm_num) hexponents
  have hlower :
      (2 : ℚ) ^ (41 * u₀) <
        ((2 : ℚ) ^ (328 * T + 615 * N) /
          (3 : ℚ) ^ (246 * S + 451 * N)) := by
    have hfirst :
        (2 : ℚ) ^ (41 * u₀) ≤
          (2 : ℚ) ^ (328 * T + 615 * N) /
            (2 : ℚ) ^ (390 * S + 715 * N) := by
      apply (le_div_iff₀ (by positivity :
        (0 : ℚ) < 2 ^ (390 * S + 715 * N))).2
      rw [← pow_add]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnumPow
    exact lt_of_le_of_lt hfirst
      ((div_lt_div_iff_of_pos_left
        (by positivity : (0 : ℚ) < 2 ^ (328 * T + 615 * N))
        (by positivity : (0 : ℚ) < 2 ^ (390 * S + 715 * N))
        (by positivity : (0 : ℚ) < 3 ^ (246 * S + 451 * N))).2 hdenQ)
  have hproductPower :
      (2 : ℚ) ^ (41 * u₀) <
        (backwardPrefixProduct o.generalBackwardCoeff N) ^ 41 := by
    have hnumEq : (8 * T + 15 * N) * 41 = 328 * T + 615 * N := by omega
    have hdenEq : (6 * S + 11 * N) * 41 = 246 * S + 451 * N := by omega
    rw [o.generalBackwardPrefixProduct_eq_closed N, div_pow,
      ← pow_mul, ← pow_mul, hnumEq, hdenEq]
    simpa [S, T] using hlower
  have hcoreTwoNat : u₀ + 1 ≤ 2 ^ u₀ := by
    exact (Nat.add_one_le_iff).2 Nat.lt_two_pow_self
  have hcoreTwo : (u₀ : ℚ) + 1 ≤ (2 : ℚ) ^ u₀ := by
    exact_mod_cast hcoreTwoNat
  have hproductUpper := o.general_backwardPrefixProduct_lt_core_succ N
  have hpowUpper :
      (backwardPrefixProduct o.generalBackwardCoeff N) ^ 41 <
        ((u₀ : ℚ) + 1) ^ 41 :=
    pow_lt_pow_left₀ (by simpa [u₀] using hproductUpper)
      (le_of_lt (o.generalBackwardPrefixProduct_pos N)) (by norm_num)
  have hcorePow : ((u₀ : ℚ) + 1) ^ 41 ≤
      (2 : ℚ) ^ (41 * u₀) := by
    calc
      ((u₀ : ℚ) + 1) ^ 41 ≤ ((2 : ℚ) ^ u₀) ^ 41 :=
        pow_le_pow_left₀ (by positivity) hcoreTwo 41
      _ = (2 : ℚ) ^ (41 * u₀) := by
        rw [← pow_mul]
        congr 1
        omega
  exact (not_lt_of_ge hcorePow) (hproductPower.trans hpowUpper)

/-! ## Recurring local slowdown -/

/-- A step whose backward coefficient is strictly larger than two. -/
def TwoExpandingAt (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ) : Prop :=
  2 * 3 ^ (6 * o.level t + 17) < 2 ^ (8 * o.level (t + 1) + 23)

theorem two_lt_generalBackwardCoeff_of_expanding
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ)
    (h : o.TwoExpandingAt t) :
    (2 : ℚ) < o.generalBackwardCoeff t := by
  have hQ :
      (2 : ℚ) * (3 : ℚ) ^ (6 * o.level t + 17) <
        (2 : ℚ) ^ (8 * o.level (t + 1) + 23) := by
    exact_mod_cast h
  rw [generalBackwardCoeff]
  apply (lt_div_iff₀ (by positivity :
    (0 : ℚ) < 3 ^ (6 * o.level t + 17))).2
  simpa using hQ

theorem two_pow_succ_lt_generalBackwardPrefixProduct
    (o : EtherCounterAperiodic.TernaryCoreOrbit)
    (h : ∀ t, o.TwoExpandingAt t) (N : ℕ) :
    (2 : ℚ) ^ (N + 1) <
      backwardPrefixProduct o.generalBackwardCoeff (N + 1) := by
  induction N with
  | zero =>
      simp only [backwardPrefixProduct, one_mul]
      exact o.two_lt_generalBackwardCoeff_of_expanding 0 (h 0)
  | succ N ih =>
      rw [backwardPrefixProduct]
      have hp := o.generalBackwardPrefixProduct_pos (N + 1)
      calc
        (2 : ℚ) ^ (N + 1 + 1) = 2 ^ (N + 1) * 2 := by rw [pow_succ]
        _ < backwardPrefixProduct o.generalBackwardCoeff (N + 1) * 2 :=
          mul_lt_mul_of_pos_right ih (by norm_num)
        _ < backwardPrefixProduct o.generalBackwardCoeff (N + 1) *
            o.generalBackwardCoeff (N + 1) :=
          mul_lt_mul_of_pos_left
            (o.two_lt_generalBackwardCoeff_of_expanding (N + 1) (h (N + 1))) hp

theorem not_all_twoExpanding
    (o : EtherCounterAperiodic.TernaryCoreOrbit) :
    ¬ ∀ t, o.TwoExpandingAt t := by
  intro h
  let N := o.core 0 + 1
  have hprod := o.two_pow_succ_lt_generalBackwardPrefixProduct h (o.core 0)
  have hbudget := o.general_backwardPrefixProduct_lt_core_succ N
  have hnat : (o.core 0 : ℚ) + 1 < (2 : ℚ) ^ N := by
    exact_mod_cast (show o.core 0 + 1 < 2 ^ (o.core 0 + 1) from
      Nat.lt_two_pow_self)
  exact (not_lt_of_ge (le_of_lt hbudget)) (hnat.trans hprod)

/-- Discarding a finite prefix preserves the literal orbit interface. -/
def shift (o : EtherCounterAperiodic.TernaryCoreOrbit) (K : ℕ) :
    EtherCounterAperiodic.TernaryCoreOrbit where
  level t := o.level (K + t)
  core t := o.core (K + t)
  core_pos t := o.core_pos (K + t)
  balance t := by
    simpa [Nat.add_assoc] using o.balance (K + t)

/-- Every possible survivor has a non-more-than-doubling step after every
finite time.  This is the local recurrence form of the global product budget. -/
theorem exists_nonexpanding_after
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (K : ℕ) :
    ∃ t, K ≤ t ∧
      2 ^ (8 * o.level (t + 1) + 23) ≤
        2 * 3 ^ (6 * o.level t + 17) := by
  have hnot := (o.shift K).not_all_twoExpanding
  push Not at hnot
  obtain ⟨s, hs⟩ := hnot
  refine ⟨K + s, by omega, ?_⟩
  simp only [TwoExpandingAt, shift] at hs
  push Not at hs
  simpa [Nat.add_assoc] using hs

/-- The exact power inequality at a nonexpanding step implies a simple
near-linear ceiling on the next one-based branch. -/
theorem branch_ceiling_of_nonexpanding
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (t : ℕ)
    (hslow :
      2 ^ (8 * o.level (t + 1) + 23) ≤
        2 * 3 ^ (6 * o.level t + 17)) :
    328 * o.oneBasedLevel (t + 1) <
      390 * o.oneBasedLevel t + 141 := by
  let n := o.oneBasedLevel t
  let m := o.oneBasedLevel (t + 1)
  have hslow' : 2 ^ (8 * m + 15) ≤ 2 * 3 ^ (6 * n + 11) := by
    rw [show 8 * m + 15 = 8 * o.level (t + 1) + 23 by
      simp [m, oneBasedLevel]; omega]
    rw [show 6 * n + 11 = 6 * o.level t + 17 by
      simp [n, oneBasedLevel]; omega]
    exact hslow
  let k := 6 * n + 11
  have hk : 0 < k := by simp [k]
  have hden : 3 ^ (246 * n + 451) < 2 ^ (390 * n + 715) := by
    calc
      3 ^ (246 * n + 451) = (3 ^ 41) ^ k := by
        rw [show 246 * n + 451 = 41 * k by simp [k]; omega, pow_mul]
      _ < (2 ^ 65) ^ k :=
        Nat.pow_lt_pow_left three_pow_41_lt_two_pow_65 hk.ne'
      _ = 2 ^ (390 * n + 715) := by
        rw [← pow_mul]
        congr 1
        simp [k]
        omega
  have hchain : 2 ^ (328 * m + 615) < 2 ^ (390 * n + 756) := by
    calc
      2 ^ (328 * m + 615) = (2 ^ (8 * m + 15)) ^ 41 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (2 * 3 ^ (6 * n + 11)) ^ 41 := Nat.pow_le_pow_left hslow' 41
      _ = 2 ^ 41 * 3 ^ (246 * n + 451) := by
        rw [mul_pow, ← pow_mul,
          show (6 * n + 11) * 41 = 246 * n + 451 by omega]
      _ < 2 ^ 41 * 2 ^ (390 * n + 715) :=
        Nat.mul_lt_mul_of_pos_left hden (by positivity)
      _ = 2 ^ (390 * n + 756) := by
        rw [← pow_add, show 41 + (390 * n + 715) = 390 * n + 756 by omega]
  have hexp : 328 * m + 615 < 390 * n + 756 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 hchain
  simpa [n, m] using (show 328 * m < 390 * n + 141 by omega)

/-- Infinitely often, the next one-based branch is at most about `1.189`
times the current branch, in this exact integer form. -/
theorem exists_branch_ceiling_after
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (K : ℕ) :
    ∃ t, K ≤ t ∧
      328 * o.oneBasedLevel (t + 1) <
        390 * o.oneBasedLevel t + 141 := by
  obtain ⟨t, ht, hslow⟩ := o.exists_nonexpanding_after K
  exact ⟨t, ht, o.branch_ceiling_of_nonexpanding t hslow⟩

/-- A literal ternary-core orbit on a geometric one-based level schedule is
exactly the abstract EC17 ray used by the Mahler reduction. -/
def toGeometricMahlerRay
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (n₀ d : ℕ)
    (hn₀ : 0 < n₀) (hd : 2 ≤ d)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterGeometricMahler.branch n₀ d t) :
    EtherCounterGeometricMahler.Ray where
  initialBranch := n₀
  multiplier := d
  initialBranch_pos := hn₀
  multiplier_ge_two := hd
  core := o.core
  core_pos := o.core_pos
  balance t := by
    have h := o.balance t
    have hB :
        EtherCounterGeometricMahler.binaryExponent n₀ d t =
          8 * o.level (t + 1) + 23 := by
      simp only [EtherCounterGeometricMahler.binaryExponent]
      rw [← hschedule (t + 1)]
      omega
    have hA :
        EtherCounterGeometricMahler.ternaryExponent n₀ d t =
          6 * o.level t + 17 := by
      simp only [EtherCounterGeometricMahler.ternaryExponent]
      rw [← hschedule t]
      omega
    rw [hB, hA]
    exact h

/-- Conditional closure at the concrete ternary-core level.  The sole open
premise is irrationality of the explicit p-adic Mahler value. -/
theorem no_geometric_schedule_of_irrational
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (n₀ d : ℕ)
    (hn₀ : 0 < n₀) (hd : 2 ≤ d)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterGeometricMahler.branch n₀ d t)
    (hirr : NormalizedStandardPayloadStream.IsPadicIrrational
      (o.toGeometricMahlerRay n₀ d hn₀ hd hschedule).padicMahlerValue) : False :=
  (o.toGeometricMahlerRay n₀ d hn₀ hd hschedule).false_of_mahlerValue_irrational hirr

/-- Concrete unconditional form of QM87. -/
theorem no_geometric_schedule
    (o : EtherCounterAperiodic.TernaryCoreOrbit) (n₀ d : ℕ)
    (hn₀ : 0 < n₀) (hd : 2 ≤ d)
    (hschedule : ∀ t, o.level t + 1 =
      EtherCounterGeometricMahler.branch n₀ d t) : False :=
  (o.toGeometricMahlerRay n₀ d hn₀ hd hschedule).impossible

end EtherCounterAperiodic.TernaryCoreOrbit
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DoublingQuineMahlerNormalForm

/-!
# No positive integer chain for the doubling return quine

The standard Mahler coordinate exposes a stronger elementary obstruction than
regular-value transcendence.  Suppose positive natural payloads followed the
legal opcode ray `g,2g,4g,...` and satisfied the exact four-cell return

`3^R(g) F(g) = C(g) + 2^S(g) F(2g)`.

The first two monomials of `C(g)` are the fixed particular value
`b0/A`.  The other terms imply the exact divisibility

`2^(77+P(g)) | A*F(g)-b0`.

Since the difference is positive, this forces `F(g)` to have size at least
about `2^(23g)`.  On the other hand positivity of the defect in the return
gives

`F(2g) < 2^(46+8g) F(g)`.

Along the doubling ray the resulting upper exponent grows like `8g`, while
the divisibility lower exponent grows like `23g`.  Choosing the explicit
depth `N=F(0)+4` yields a contradiction.  Thus the singular homogeneous
boundary cannot restore integrality: this particular doubling-return
architecture is a wall even for arbitrary discrete positive payloads.
-/

namespace KontoroC
namespace DoublingQuineIntegerNoGo

def P (g : ℕ) : ℕ := 23 * g + 54
def Q (g : ℕ) : ℕ := 17 * g + 40
def R (g : ℕ) : ℕ := 114 + 2 * Q g
def S (g : ℕ) : ℕ := 154 + 2 * P g
def A : ℕ := 3 ^ 114
def b0 : ℕ := 3 ^ 57 + 2 ^ 77

def defect (g : ℕ) : ℕ :=
  3 ^ (2 * Q g + 57) +
    2 ^ 77 * 3 ^ (2 * Q g) +
    2 ^ (77 + P g) * 3 ^ Q g +
    2 ^ (77 + 2 * P g)

def gAt (base n : ℕ) : ℕ := base * 2 ^ n

/-- A putative positive integer payload on one legal doubling-opcode ray. -/
structure Chain where
  base : ℕ
  base_pos : 0 < base
  payload : ℕ → ℕ
  payload_pos : ∀ n, 0 < payload n
  balance : ∀ n,
    3 ^ R (gAt base n) * payload n =
      defect (gAt base n) +
        2 ^ S (gAt base n) * payload (n + 1)

theorem R_eq (g : ℕ) : R g = 194 + 34 * g := by
  simp [R, Q]
  omega

theorem S_eq (g : ℕ) : S g = 262 + 46 * g := by
  simp [S, P]
  omega

theorem S_eq_two_keyExponent (g : ℕ) :
    S g = 2 * (77 + P g) := by
  simp [S]
  omega

theorem defect_pos (g : ℕ) : 0 < defect g := by
  simp [defect]

/-- The four forcing monomials split into a fixed particular numerator and a
single high-divisibility remainder. -/
theorem defect_split (g : ℕ) :
    defect g =
      3 ^ (2 * Q g) * b0 +
        2 ^ (77 + P g) * (3 ^ Q g + 2 ^ P g) := by
  simp only [defect, b0]
  rw [show 2 * Q g + 57 = 2 * Q g + 57 by rfl,
    pow_add, pow_add]
  ring

/-- Exact integer form of the high-order approximation to `b0/A`. -/
theorem balance_factor {g F Fnext : ℕ}
    (h : 3 ^ R g * F = defect g + 2 ^ S g * Fnext) :
    3 ^ (2 * Q g) * (A * F - b0) =
      2 ^ (77 + P g) *
        (3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext) := by
  have hpowR : 3 ^ R g = 3 ^ (2 * Q g) * A := by
    simp only [R, A]
    rw [show 114 + 2 * Q g = 2 * Q g + 114 by omega, pow_add]
  have hpowS : 2 ^ S g = 2 ^ (77 + P g) * 2 ^ (77 + P g) := by
    rw [S_eq_two_keyExponent]
    rw [show 2 * (77 + P g) = (77 + P g) + (77 + P g) by omega,
      pow_add]
  have hnorm :
      3 ^ (2 * Q g) * (A * F) =
        3 ^ (2 * Q g) * b0 +
          2 ^ (77 + P g) *
            (3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext) := by
    calc
      3 ^ (2 * Q g) * (A * F) = 3 ^ R g * F := by
        rw [hpowR]
        ring
      _ = defect g + 2 ^ S g * Fnext := h
      _ = 3 ^ (2 * Q g) * b0 +
          2 ^ (77 + P g) *
            (3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext) := by
        rw [defect_split, hpowS]
        ring
  have hle : b0 ≤ A * F := by
    have hmul : 3 ^ (2 * Q g) * b0 ≤
        3 ^ (2 * Q g) * (A * F) := by
      rw [hnorm]
      exact Nat.le_add_right _ _
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  calc
    3 ^ (2 * Q g) * (A * F - b0) =
        3 ^ (2 * Q g) * (A * F) - 3 ^ (2 * Q g) * b0 := by
          exact Nat.mul_sub_left_distrib _ _ _
    _ = 2 ^ (77 + P g) *
        (3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext) := by
          omega

/-- The forced dyadic approximation is too accurate for a small positive
integer payload. -/
theorem key_power_lt_payload_scale {g F Fnext : ℕ} (hFnext : 0 < Fnext)
    (h : 3 ^ R g * F = defect g + 2 ^ S g * Fnext) :
    2 ^ (77 + P g) < A * F := by
  have hfactor := balance_factor h
  have hdvdProduct : 2 ^ (77 + P g) ∣
      3 ^ (2 * Q g) * (A * F - b0) := by
    refine ⟨3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext, ?_⟩
    exact hfactor
  have hcop : Nat.Coprime (2 ^ (77 + P g)) (3 ^ (2 * Q g)) :=
    (by norm_num : Nat.Coprime 2 3).pow _ _
  have hdvd : 2 ^ (77 + P g) ∣ A * F - b0 :=
    hcop.dvd_of_dvd_mul_left hdvdProduct
  have hsubpos : 0 < A * F - b0 := by
    have hrhspos : 0 <
        2 ^ (77 + P g) *
          (3 ^ Q g + 2 ^ P g + 2 ^ (77 + P g) * Fnext) := by positivity
    have hlhspos : 0 < 3 ^ (2 * Q g) * (A * F - b0) := by
      rw [hfactor]
      exact hrhspos
    exact Nat.pos_of_mul_pos_left hlhspos
  have hpower_le : 2 ^ (77 + P g) ≤ A * F - b0 :=
    Nat.le_of_dvd hsubpos hdvd
  have hb0pos : 0 < b0 := by simp [b0]
  omega

theorem key_power_lt_payload_scale_at (c : Chain) (n : ℕ) :
    2 ^ (131 + 23 * gAt c.base n) < A * c.payload n := by
  have h := key_power_lt_payload_scale (c.payload_pos (n + 1)) (c.balance n)
  have hexp : 77 + P (gAt c.base n) = 131 + 23 * gAt c.base n := by
    simp only [P]
    omega
  rwa [hexp] at h

/-! ## Coarse Archimedean upper growth -/

theorem three_pow_34_lt_two_pow_54 : 3 ^ 34 < 2 ^ 54 := by norm_num
set_option exponentiation.threshold 400 in
theorem three_pow_194_lt_two_pow_308 : 3 ^ 194 < 2 ^ 308 := by norm_num
theorem A_lt_two_pow_181 : A < 2 ^ 181 := by norm_num [A]

theorem three_pow_R_lt (g : ℕ) :
    3 ^ R g < 2 ^ (308 + 54 * g) := by
  rw [R_eq, pow_add, pow_mul, pow_add, pow_mul]
  exact mul_lt_mul three_pow_194_lt_two_pow_308
    (Nat.pow_le_pow_left three_pow_34_lt_two_pow_54.le g)
    (show 0 < (3 ^ 34 : ℕ) ^ g by positivity) (Nat.zero_le _)

/-- One legal return grows much more slowly than the forced approximation
precision: an exponent cost `8g+46`, versus the lower exponent `23g`. -/
theorem payload_next_lt {g F Fnext : ℕ}
    (h : 3 ^ R g * F = defect g + 2 ^ S g * Fnext) :
    Fnext < 2 ^ (46 + 8 * g) * F := by
  have hraw : 2 ^ S g * Fnext < 3 ^ R g * F := by
    rw [h]
    have hd := defect_pos g
    omega
  have hthree := three_pow_R_lt g
  have hscaled : 2 ^ S g * Fnext < 2 ^ (308 + 54 * g) * F :=
    hraw.trans_le (Nat.mul_le_mul_right F hthree.le)
  have hexp : 308 + 54 * g = S g + (46 + 8 * g) := by
    rw [S_eq]
    omega
  rw [hexp, pow_add] at hscaled
  exact (Nat.mul_lt_mul_left (show 0 < 2 ^ S g by positivity)).mp (by
    simpa [mul_assoc] using hscaled)

def upperBudget (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => upperBudget base n + (46 + 8 * gAt base n)

theorem upperBudget_eq (base N : ℕ) :
    upperBudget base N = 46 * N + 8 * base * (2 ^ N - 1) := by
  induction N with
  | zero => simp [upperBudget]
  | succ N ih =>
      rw [upperBudget, ih]
      simp only [gAt]
      have hpow : 2 ^ (N + 1) - 1 = (2 ^ N - 1) + 2 ^ N := by
        rw [pow_succ]
        have hpos : 0 < 2 ^ N := by positivity
        omega
      rw [hpow]
      ring

theorem payload_le_initial_mul_pow (c : Chain) (N : ℕ) :
    c.payload N ≤ c.payload 0 * 2 ^ upperBudget c.base N := by
  induction N with
  | zero => simp [upperBudget]
  | succ N ih =>
      have hstep := payload_next_lt (c.balance N)
      calc
        c.payload (N + 1) ≤ 2 ^ (46 + 8 * gAt c.base N) * c.payload N :=
          hstep.le
        _ ≤ 2 ^ (46 + 8 * gAt c.base N) *
            (c.payload 0 * 2 ^ upperBudget c.base N) :=
              Nat.mul_le_mul_left _ ih
        _ = c.payload 0 * 2 ^ upperBudget c.base (N + 1) := by
              rw [upperBudget, pow_add]
              ring

/-! ## Explicit exponential contradiction -/

theorem n_lt_two_pow (n : ℕ) (hn : 0 < n) : n < 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · rw [pow_succ]
        have ih' := ih (Nat.pos_of_ne_zero hn0)
        omega

/-- At the explicit depth `payload 0 + 4`, the forced `23g` precision is
larger than the complete `8g+46` Archimedean growth budget, including the
fixed denominator `A`. -/
theorem terminal_exponent_gap (c : Chain) :
    let N := c.payload 0 + 4
    c.payload 0 + 181 + upperBudget c.base N <
      131 + 23 * gAt c.base N := by
  dsimp only
  rw [upperBudget_eq]
  simp only [gAt]
  have hbase := c.base_pos
  have hpayload := c.payload_pos 0
  have hpow : c.payload 0 < 2 ^ c.payload 0 :=
    n_lt_two_pow _ hpayload
  have hscale : 16 * 2 ^ c.payload 0 = 2 ^ (c.payload 0 + 4) := by
    rw [pow_add]
    norm_num
    ring
  rw [← hscale]
  let f := c.payload 0
  let x := 16 * 2 ^ f
  have hpow_le : f + 1 ≤ 2 ^ f := by
    dsimp only [f]
    omega
  have hx : x = 16 * 2 ^ f := rfl
  have hlinear : 47 * f + 234 < 15 * x + 8 := by
    rw [hx]
    omega
  have hbx : x ≤ c.base * x := by
    exact Nat.le_mul_of_pos_left x hbase
  have hb8 : 8 ≤ 8 * c.base := by omega
  have hscaled : 15 * x + 8 ≤ 15 * (c.base * x) + 8 * c.base :=
    Nat.add_le_add (Nat.mul_le_mul_left 15 hbx) hb8
  have hxpos : 0 < x := by simp [x]
  have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel hxpos
  have hcombine :
      15 * (c.base * x) + 8 * c.base + 8 * c.base * (x - 1) =
        23 * (c.base * x) := by
    calc
      15 * (c.base * x) + 8 * c.base + 8 * c.base * (x - 1) =
          15 * (c.base * x) + 8 * c.base * ((x - 1) + 1) := by ring
      _ = 15 * (c.base * x) + 8 * c.base * x := by rw [hxsub]
      _ = 23 * (c.base * x) := by ring
  change f + 181 + (46 * (f + 4) + 8 * c.base * (x - 1)) <
    131 + 23 * (c.base * x)
  omega

/-- No positive natural payload can satisfy the legal doubling return at all
depths.  This closes arbitrary discrete singular boundary sections, not only
rational or holomorphic ansatzes. -/
theorem no_positive_integer_doubling_chain : ¬ Nonempty Chain := by
  intro hchain
  rcases hchain with ⟨c⟩
  let N := c.payload 0 + 4
  have hlower := key_power_lt_payload_scale_at c N
  have hupper := payload_le_initial_mul_pow c N
  have hA := A_lt_two_pow_181
  have hF : c.payload 0 < 2 ^ c.payload 0 :=
    n_lt_two_pow _ (c.payload_pos 0)
  have hgap := terminal_exponent_gap c
  dsimp only [N] at hlower hupper hgap ⊢
  have hchainlt :
      2 ^ (131 + 23 * gAt c.base (c.payload 0 + 4)) <
        2 ^ (c.payload 0 + 181 + upperBudget c.base (c.payload 0 + 4)) := by
    calc
      2 ^ (131 + 23 * gAt c.base (c.payload 0 + 4)) <
          A * c.payload (c.payload 0 + 4) := hlower
      _ ≤ A * (c.payload 0 *
          2 ^ upperBudget c.base (c.payload 0 + 4)) :=
            Nat.mul_le_mul_left A hupper
      _ < 2 ^ 181 * (2 ^ c.payload 0 *
          2 ^ upperBudget c.base (c.payload 0 + 4)) :=
            mul_lt_mul hA
              (Nat.mul_le_mul_right _ hF.le)
              (mul_pos (c.payload_pos 0) (by positivity)) (Nat.zero_le _)
      _ = 2 ^ (c.payload 0 + 181 +
          upperBudget c.base (c.payload 0 + 4)) := by
            rw [← pow_add, ← pow_add]
            congr 1
            omega
  have hpowle :
      2 ^ (c.payload 0 + 181 + upperBudget c.base (c.payload 0 + 4)) ≤
        2 ^ (131 + 23 * gAt c.base (c.payload 0 + 4)) :=
    Nat.pow_le_pow_right (by norm_num) hgap.le
  omega

end DoublingQuineIntegerNoGo
end KontoroC

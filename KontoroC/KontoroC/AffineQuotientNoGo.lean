/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.DispatcherBoundary

/-!
# No infinite positive orbit for an expanding coprime affine quotient

Consider a positive natural sequence satisfying

`B * x_(t+1) + c = A * x_t`.

When `A` and `B` are coprime, `B>1`, and `A>B+c`, the deviation from the
rational fixed point obeys `B*delta_(t+1)=A*delta_t`.  Consequently every
power of `B` divides the fixed positive natural `delta_0`, which is
impossible.

This is the generic obstruction needed for a charge--discharge dispatcher
which returns forever to one fixed affine quotient level.
-/

namespace KontoroC

/-- A positive all-time orbit of one affine quotient instruction. -/
structure PositiveAffineQuotientOrbit (A B c : ℕ) where
  value : ℕ → ℕ
  value_pos : ∀ t, 0 < value t
  balance : ∀ t, B * value (t + 1) + c = A * value t

namespace PositiveAffineQuotientOrbit

variable {A B c : ℕ}

/-- Natural deviation from the rational fixed point `c/(A-B)`. -/
def defect (o : PositiveAffineQuotientOrbit A B c) (t : ℕ) : ℕ :=
  (A - B) * o.value t - c

theorem coefficient_gap (hgap : B + c < A) : c < A - B := by omega

theorem defect_pos (o : PositiveAffineQuotientOrbit A B c)
    (hgap : B + c < A) (t : ℕ) : 0 < o.defect t := by
  have hcoeff : c < A - B := coefficient_gap hgap
  have hvalue := o.value_pos t
  have hle : A - B ≤ (A - B) * o.value t :=
    Nat.le_mul_of_pos_right (A - B) hvalue
  dsimp [defect]
  omega

theorem defect_spec (o : PositiveAffineQuotientOrbit A B c)
    (hgap : B + c < A) (t : ℕ) :
    c + o.defect t = (A - B) * o.value t := by
  dsimp [defect]
  have hcoeff : c < A - B := coefficient_gap hgap
  have hle : A - B ≤ (A - B) * o.value t :=
    Nat.le_mul_of_pos_right (A - B) (o.value_pos t)
  exact Nat.add_sub_of_le (by omega)

/-- The affine update becomes a homogeneous coprime scaling law for the
fixed-point defect. -/
theorem defect_balance (o : PositiveAffineQuotientOrbit A B c)
    (hgap : B + c < A) (t : ℕ) :
    B * o.defect (t + 1) = A * o.defect t := by
  let D := A - B
  have hA : A = B + D := by
    dsimp [D]
    omega
  have hs := o.balance t
  have hscaled :
      B * (c + o.defect (t + 1)) + D * c =
        A * (c + o.defect t) := by
    rw [o.defect_spec hgap (t + 1), o.defect_spec hgap t]
    calc
      B * (D * o.value (t + 1)) + D * c =
          D * (B * o.value (t + 1) + c) := by ring
      _ = D * (A * o.value t) := by rw [hs]
      _ = A * (D * o.value t) := by ring
  have hnormalized :
      A * c + B * o.defect (t + 1) =
        A * c + A * o.defect t := by
    have hAc : A * c = B * c + D * c := by rw [hA]; ring
    calc
      A * c + B * o.defect (t + 1) =
          (B * c + D * c) + B * o.defect (t + 1) := by rw [hAc]
      _ = B * (c + o.defect (t + 1)) + D * c := by ring
      _ = A * (c + o.defect t) := hscaled
      _ = A * c + A * o.defect t := by ring
  exact Nat.add_left_cancel hnormalized

/-- Exact `n`-step scaling of the fixed-point defect. -/
theorem defect_iterate (o : PositiveAffineQuotientOrbit A B c)
    (hgap : B + c < A) (n : ℕ) :
    B ^ n * o.defect n = A ^ n * o.defect 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        B ^ (n + 1) * o.defect (n + 1) =
            B ^ n * (B * o.defect (n + 1)) := by
              rw [pow_succ]
              ring
        _ = B ^ n * (A * o.defect n) := by rw [o.defect_balance hgap n]
        _ = A * (B ^ n * o.defect n) := by ring
        _ = A * (A ^ n * o.defect 0) := by rw [ih]
        _ = A ^ (n + 1) * o.defect 0 := by rw [pow_succ]; ring

/-- Coprimality forces every power of the denominator to divide the initial
defect. -/
theorem pow_dvd_initial_defect (o : PositiveAffineQuotientOrbit A B c)
    (hcop : A.Coprime B) (hgap : B + c < A) (n : ℕ) :
    B ^ n ∣ o.defect 0 := by
  have hprod : B ^ n ∣ A ^ n * o.defect 0 := by
    refine ⟨o.defect n, ?_⟩
    exact (o.defect_iterate hgap n).symm
  have hcop_pow : (B ^ n).Coprime (A ^ n) := hcop.symm.pow n n
  exact hcop_pow.dvd_of_dvd_mul_left hprod

/-- Main no-go: no positive natural orbit can execute the same expanding
coprime affine quotient instruction forever. -/
theorem impossible (o : PositiveAffineQuotientOrbit A B c)
    (hcop : A.Coprime B) (hB : 1 < B) (hgap : B + c < A) : False := by
  let d := o.defect 0
  have hd : 0 < d := o.defect_pos hgap 0
  have hdvd : B ^ d ∣ d := o.pow_dvd_initial_defect hcop hgap d
  have hle : B ^ d ≤ d := Nat.le_of_dvd hd hdvd
  have htwo : 2 ^ d ≤ B ^ d := Nat.pow_le_pow_left (by omega) d
  have hlt : d < 2 ^ d := d.lt_two_pow_self
  omega

theorem no_orbit (hcop : A.Coprime B) (hB : 1 < B)
    (hgap : B + c < A) :
    ¬ Nonempty (PositiveAffineQuotientOrbit A B c) := by
  rintro ⟨o⟩
  exact o.impossible hcop hB hgap

/-- Power-of-three over power-of-two specialization used by Collatz affine
quotient instructions. -/
theorem no_threePow_twoPow_orbit {P Q c : ℕ} (hP : 0 < P)
    (hgap : 2 ^ P + c < 3 ^ Q) :
    ¬ Nonempty (PositiveAffineQuotientOrbit (3 ^ Q) (2 ^ P) c) := by
  apply no_orbit
  · exact (by norm_num : Nat.Coprime 3 2).pow Q P
  · exact Nat.one_lt_pow (Nat.ne_of_gt hP) (by omega)
  · exact hgap

/-- The fixed-level charge--discharge coefficients have a uniform positive
Archimedean gap. -/
theorem fixedChargeLevel_gap (N : ℕ) :
    2 ^ (23 * N + 131) + 5 < 3 ^ (17 * N + 97) := by
  have hdouble : ∀ n : ℕ,
      2 ^ (23 * n + 132) < 3 ^ (17 * n + 97) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        calc
          2 ^ (23 * (n + 1) + 132) =
              2 ^ (23 * n + 132) * 2 ^ 23 := by
                rw [← pow_add]
                congr 1
          _ <
              3 ^ (17 * n + 97) * 2 ^ 23 :=
            (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).2 ih
          _ < 3 ^ (17 * n + 97) * 3 ^ 17 := by
            apply (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2
            norm_num
          _ = 3 ^ (17 * (n + 1) + 97) := by
            rw [← pow_add]
            congr 1
  have hfive : 5 < 2 ^ (23 * N + 131) := by
    have hp : 2 ^ 131 ≤ 2 ^ (23 * N + 131) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_lt_of_le (by norm_num) hp
  calc
    2 ^ (23 * N + 131) + 5 <
        2 ^ (23 * N + 131) + 2 ^ (23 * N + 131) :=
      Nat.add_lt_add_left hfive _
    _ = 2 ^ (23 * N + 132) := by
      rw [show 23 * N + 132 = (23 * N + 131) + 1 by omega, pow_succ]
      ring
    _ < 3 ^ (17 * N + 97) := hdouble N

/-- Conditional closure of the fixed finite charge level: no positive stream
can satisfy its same-level quotient recurrence forever. -/
theorem no_fixedChargeLevel_orbit (N : ℕ) :
    ¬ Nonempty (PositiveAffineQuotientOrbit
      (3 ^ (17 * N + 97)) (2 ^ (23 * N + 131)) 5) := by
  exact no_threePow_twoPow_orbit (by omega) (fixedChargeLevel_gap N)

end PositiveAffineQuotientOrbit

/-- Positive orbit of an affine quotient with a nonnegative gain on the
right-hand side. -/
structure PositiveAffineGainOrbit (A B C : ℕ) where
  value : ℕ → ℕ
  value_pos : ∀ t, 0 < value t
  balance : ∀ t, B * value (t + 1) = A * value t + C

namespace PositiveAffineGainOrbit

variable {A B C : ℕ}

def defect (o : PositiveAffineGainOrbit A B C) (t : ℕ) : ℕ :=
  (A - B) * o.value t + C

theorem defect_pos (o : PositiveAffineGainOrbit A B C)
    (hAB : B < A) (t : ℕ) : 0 < o.defect t := by
  have hD : 0 < A - B := Nat.sub_pos_of_lt hAB
  have hmul : 0 < (A - B) * o.value t := Nat.mul_pos hD (o.value_pos t)
  dsimp [defect]
  omega

/-- The gain-side affine law has the same homogeneous fixed-point-defect
scaling as the loss-side law. -/
theorem defect_balance (o : PositiveAffineGainOrbit A B C)
    (hAB : B < A) (t : ℕ) :
    B * o.defect (t + 1) = A * o.defect t := by
  let D := A - B
  have hA : A = B + D := by dsimp [D]; omega
  have hs := o.balance t
  dsimp [defect]
  calc
    B * (D * o.value (t + 1) + C) =
        D * (B * o.value (t + 1)) + B * C := by ring
    _ = D * (A * o.value t + C) + B * C := by rw [hs]
    _ = A * (D * o.value t + C) := by
      have hconst : D * C + B * C = A * C := by
        calc
          D * C + B * C = (B + D) * C := by ring
          _ = A * C := by rw [← hA]
      calc
        D * (A * o.value t + C) + B * C =
            A * (D * o.value t) + (D * C + B * C) := by ring
        _ = A * (D * o.value t) + A * C := by rw [hconst]
        _ = A * (D * o.value t + C) := by ring

theorem defect_iterate (o : PositiveAffineGainOrbit A B C)
    (hAB : B < A) (n : ℕ) :
    B ^ n * o.defect n = A ^ n * o.defect 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        B ^ (n + 1) * o.defect (n + 1) =
            B ^ n * (B * o.defect (n + 1)) := by rw [pow_succ]; ring
        _ = B ^ n * (A * o.defect n) := by rw [o.defect_balance hAB n]
        _ = A * (B ^ n * o.defect n) := by ring
        _ = A * (A ^ n * o.defect 0) := by rw [ih]
        _ = A ^ (n + 1) * o.defect 0 := by rw [pow_succ]; ring

theorem pow_dvd_initial_defect (o : PositiveAffineGainOrbit A B C)
    (hcop : A.Coprime B) (hAB : B < A) (n : ℕ) :
    B ^ n ∣ o.defect 0 := by
  have hprod : B ^ n ∣ A ^ n * o.defect 0 := by
    refine ⟨o.defect n, (o.defect_iterate hAB n).symm⟩
  exact (hcop.symm.pow n n).dvd_of_dvd_mul_left hprod

/-- No expanding coprime affine instruction with a fixed nonnegative gain can
support an infinite positive natural orbit. -/
theorem impossible (o : PositiveAffineGainOrbit A B C)
    (hcop : A.Coprime B) (hB : 1 < B) (hAB : B < A) : False := by
  let d := o.defect 0
  have hd : 0 < d := o.defect_pos hAB 0
  have hdvd : B ^ d ∣ d := o.pow_dvd_initial_defect hcop hAB d
  have hle : B ^ d ≤ d := Nat.le_of_dvd hd hdvd
  have htwo : 2 ^ d ≤ B ^ d := Nat.pow_le_pow_left (by omega) d
  exact (not_lt_of_ge (htwo.trans hle)) d.lt_two_pow_self

theorem no_orbit (hcop : A.Coprime B) (hB : 1 < B) (hAB : B < A) :
    ¬ Nonempty (PositiveAffineGainOrbit A B C) := by
  rintro ⟨o⟩
  exact o.impossible hcop hB hAB

/-- Exact constant gain in the fixed-form charge law. -/
def fixedFormGain (m : ℕ) : ℕ :=
  2 ^ 26 * 3 ^ 114 * (3 ^ (17 * m) - 2 ^ (23 * m))

theorem fixedForm_exponent_gap (m : ℕ) :
    2 ^ (154 + 23 * m) < 3 ^ (114 + 17 * m) := by
  have h := PositiveAffineQuotientOrbit.fixedChargeLevel_gap (m + 1)
  have hbare :
      2 ^ (23 * (m + 1) + 131) < 3 ^ (17 * (m + 1) + 97) := by omega
  rw [show 23 * (m + 1) + 131 = 154 + 23 * m by omega,
    show 17 * (m + 1) + 97 = 114 + 17 * m by omega] at hbare
  exact hbare

/-- The fixed-form charge bouncer cannot remain at one `m` forever, even
with its exact nonnegative gain term.  Any surviving architecture must change
level or leave this affine law. -/
theorem no_fixedFormCharge_orbit (m : ℕ) :
    ¬ Nonempty (PositiveAffineGainOrbit
      (3 ^ (114 + 17 * m)) (2 ^ (154 + 23 * m)) (fixedFormGain m)) := by
  apply no_orbit
  · exact (by norm_num : Nat.Coprime 3 2).pow _ _
  · exact Nat.one_lt_pow (by omega) (by omega)
  · exact fixedForm_exponent_gap m

end PositiveAffineGainOrbit

end KontoroC

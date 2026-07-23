/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterPeriodicTheta
import Mathlib.Data.ZMod.Units

/-!
# Finite EC17 residue certificates

For a prescribed finite list of one-based branches, backward EC17
substitution modulo `2^P` determines the initial core once the accumulated
binary exponent is at least `P`.  This file proves that bridge symbolically.
Large residue rows remain data: a checker only has to establish that the
least representative does not realize the prescribed natural prefix.
-/

namespace KontoroC
namespace EtherCounterResidueBound

variable {branch : ℕ → ℕ} {length : ℕ}

def binaryExponent (branch : ℕ → ℕ) (t : ℕ) : ℕ :=
  8 * branch (t + 1) + 15

def ternaryExponent (branch : ℕ → ℕ) (t : ℕ) : ℕ :=
  6 * branch t + 11

def binaryMass (branch : ℕ → ℕ) (start length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, binaryExponent branch (start + i)

theorem binaryMass_zero (branch : ℕ → ℕ) (start : ℕ) :
    binaryMass branch start 0 = 0 := by simp [binaryMass]

theorem binaryMass_succ (branch : ℕ → ℕ) (start length : ℕ) :
    binaryMass branch start (length + 1) =
      binaryExponent branch start + binaryMass branch (start + 1) length := by
  rw [binaryMass, Finset.sum_range_succ']
  simp only [binaryMass]
  have hsum :
      (∑ i ∈ Finset.range length,
        binaryExponent branch (start + (i + 1))) =
      ∑ i ∈ Finset.range length,
        binaryExponent branch (start + 1 + i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hsum]
  ac_rfl

/-- One exact backward EC17 step modulo `2^P`.  The inverse exists because
every power of three is a unit modulo every power of two. -/
def backStep (branch : ℕ → ℕ) (P t : ℕ) (x : ZMod (2 ^ P)) :
    ZMod (2 ^ P) :=
  ((2 : ZMod (2 ^ P)) ^ binaryExponent branch t * x - 17) *
    ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹

/-- Apply `length` backward steps beginning at time `start`. -/
def backwardEval (branch : ℕ → ℕ) (P : ℕ) :
    ℕ → ℕ → ZMod (2 ^ P) → ZMod (2 ^ P)
  | 0, _, x => x
  | length + 1, start, x =>
      backStep branch P start (backwardEval branch P length (start + 1) x)

/-- The certified residue obtained by putting zero at the terminal end. -/
def initialResidue (branch : ℕ → ℕ) (P length : ℕ) : ZMod (2 ^ P) :=
  backwardEval branch P length 0 0

theorem ternary_isUnit (branch : ℕ → ℕ) (P t : ℕ) :
    IsUnit ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) := by
  have hthree : IsUnit (3 : ZMod (2 ^ P)) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ P)).2
      ((by norm_num : Nat.Coprime 3 2).pow_right P)
  exact hthree.pow _

/-- A literal natural EC17 prefix on a prescribed branch schedule. -/
structure NaturalPrefix (branch : ℕ → ℕ) (length : ℕ) where
  branch_pos : ∀ t ≤ length, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t ≤ length, 0 < core t
  balance : ∀ t < length,
    2 ^ binaryExponent branch t * core (t + 1) =
      3 ^ ternaryExponent branch t * core t + 17

theorem backStep_core (g : NaturalPrefix branch length) (P t : ℕ)
    (ht : t < length) :
    backStep branch P t (g.core (t + 1) : ZMod (2 ^ P)) =
      (g.core t : ZMod (2 ^ P)) := by
  have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ P))) (g.balance t ht)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [backStep]
  have hu := ternary_isUnit branch P t
  calc
    ((2 : ZMod (2 ^ P)) ^ binaryExponent branch t * g.core (t + 1) - 17) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹ =
        ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t * g.core t) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹ := by
      rw [h]
      ring
    _ = g.core t *
        (((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) *
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t)⁻¹) := by ring
    _ = g.core t := by
      rw [ZMod.mul_inv_of_unit
        ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch t) hu, mul_one]

/-- Backward evaluation with the actual terminal core exactly recovers the
actual core at the beginning of the interval. -/
theorem backwardEval_core (g : NaturalPrefix branch length) (P start n : ℕ)
    (hbound : start + n ≤ length) :
    backwardEval branch P n start (g.core (start + n) : ZMod (2 ^ P)) =
      (g.core start : ZMod (2 ^ P)) := by
  induction n generalizing start with
  | zero => simp [backwardEval]
  | succ n ih =>
      rw [backwardEval]
      have htail := ih (start := start + 1) (by omega)
      rw [show start + (n + 1) = (start + 1) + n by omega, htail]
      exact backStep_core g P start (by omega)

/-- Exact dependence on the terminal residue: the difference has a factor
`2^binaryMass`.  The remaining factor is deliberately left existential,
because only its integrality matters for the residue certificate. -/
theorem backwardEval_sub_factor (branch : ℕ → ℕ) (P start length : ℕ)
    (x y : ZMod (2 ^ P)) :
    ∃ u : ZMod (2 ^ P),
      backwardEval branch P length start x -
          backwardEval branch P length start y =
        (2 : ZMod (2 ^ P)) ^ binaryMass branch start length * u * (x - y) := by
  induction length generalizing start with
  | zero =>
      refine ⟨1, ?_⟩
      simp [backwardEval, binaryMass]
  | succ length ih =>
      obtain ⟨u, hu⟩ := ih (start := start + 1)
      refine ⟨u * ((3 : ZMod (2 ^ P)) ^
        ternaryExponent branch start)⁻¹, ?_⟩
      rw [backwardEval, backwardEval, binaryMass_succ, pow_add]
      simp only [backStep]
      calc
        (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) x - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ -
            (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) y - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ =
            2 ^ binaryExponent branch start *
              (backwardEval branch P length (start + 1) x -
                backwardEval branch P length (start + 1) y) *
              (3 ^ ternaryExponent branch start)⁻¹ := by ring
        _ = 2 ^ binaryExponent branch start *
              2 ^ binaryMass branch (start + 1) length *
              (u * (3 ^ ternaryExponent branch start)⁻¹) * (x - y) := by
          rw [hu]
          ring

theorem two_pow_binaryMass_eq_zero (branch : ℕ → ℕ) (P start length : ℕ)
    (hprecision : P ≤ binaryMass branch start length) :
    (2 : ZMod (2 ^ P)) ^ binaryMass branch start length = 0 := by
  have hcast :
      ((2 ^ binaryMass branch start length : ℕ) : ZMod (2 ^ P)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.pow_dvd_pow 2 hprecision)
  simpa using hcast

/-- Once the accumulated binary exponent reaches the requested precision,
the backward result is independent of the arbitrary terminal residue. -/
theorem backwardEval_eq_zero_terminal (branch : ℕ → ℕ)
    (P start length : ℕ) (x : ZMod (2 ^ P))
    (hprecision : P ≤ binaryMass branch start length) :
    backwardEval branch P length start x =
      backwardEval branch P length start 0 := by
  obtain ⟨u, hu⟩ := backwardEval_sub_factor branch P start length x 0
  apply sub_eq_zero.mp
  rw [hu, two_pow_binaryMass_eq_zero branch P start length hprecision]
  simp

/-- QM58: every natural EC17 prefix on the schedule has the unique initial
residue computed by the zero-terminal backward recurrence. -/
theorem initial_core_cast_eq_residue (g : NaturalPrefix branch length) (P : ℕ)
    (hprecision : P ≤ binaryMass branch 0 length) :
    (g.core 0 : ZMod (2 ^ P)) = initialResidue branch P length := by
  rw [initialResidue]
  calc
    (g.core 0 : ZMod (2 ^ P)) =
        backwardEval branch P length 0 (g.core length : ZMod (2 ^ P)) := by
      symm
      simpa using backwardEval_core g P 0 length (by omega)
    _ = backwardEval branch P length 0 0 :=
      backwardEval_eq_zero_terminal branch P 0 length _ hprecision

/-- QM62: below the modulus, equality in `ZMod (2^P)` is equality of the
least natural representatives.  This is the value-level form used by exact
certificate checkers. -/
theorem initialResidue_val_eq_initial_core
    (g : NaturalPrefix branch length) (P : ℕ)
    (hprecision : P ≤ binaryMass branch 0 length)
    (hsmall : g.core 0 < 2 ^ P) :
    (initialResidue branch P length).val = g.core 0 := by
  have hcast := initial_core_cast_eq_residue g P hprecision
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hsmall] at hval
  exact hval.symm

/-- Abstract finite-certificate consumer (QM59).  If exact execution proves
that the least representative is not the initial core of any natural prefix,
then every natural prefix begins at least at the modulus. -/
theorem initial_core_ge_modulus_of_least_residue_fails
    (P : ℕ) (hprecision : P ≤ binaryMass branch 0 length)
    (hfail : ∀ g : NaturalPrefix branch length,
      g.core 0 ≠ (initialResidue branch P length).val)
    (g : NaturalPrefix branch length) :
    2 ^ P ≤ g.core 0 := by
  by_contra hlt
  push Not at hlt
  apply hfail g
  have hcast := initial_core_cast_eq_residue g P hprecision
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hlt] at hval
  exact hval

/-! ## Exact finite replay-failure certificates -/

/-- Although `NaturalPrefix` does not redundantly store an oddness field,
every core that has an outgoing EC17 balance is necessarily odd. -/
theorem NaturalPrefix.core_mod_two_eq_one
    {branch : ℕ → ℕ} {length : ℕ}
    (g : NaturalPrefix branch length) (t : ℕ) (ht : t < length) :
    g.core t % 2 = 1 := by
  have hpow : 2 ∣ 2 ^ binaryExponent branch t := by
    apply dvd_pow_self
    simp [binaryExponent]
  have hdvd : 2 ∣
      3 ^ ternaryExponent branch t * g.core t + 17 := by
    rw [← g.balance t ht]
    exact dvd_mul_of_dvd_left hpow _
  have hthree : 3 ^ ternaryExponent branch t % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero] at hdvd
  simp [Nat.add_mod, Nat.mul_mod, hthree] at hdvd
  omega

/-- A literal exact replay from a proposed initial core through `steps`
transitions.  No claim about the next transition is included. -/
structure ExactReplayTo (branch : ℕ → ℕ) (candidate steps : ℕ) where
  core : ℕ → ℕ
  initial : core 0 = candidate
  balance : ∀ t < steps,
    2 ^ binaryExponent branch t * core (t + 1) =
      3 ^ ternaryExponent branch t * core t + 17

/-- The exact necessary predicate used by CRT consumers: some positive EC17
prefix on the prescribed branch schedule starts from `candidate`. -/
def AdmitsNaturalPrefix (branch : ℕ → ℕ) (length candidate : ℕ) : Prop :=
  ∃ g : NaturalPrefix branch length, g.core 0 = candidate

/-- Determinism of the positive binary multiplier: a natural prefix with the
same initial core agrees with every supplied exact replayed core. -/
theorem ExactReplayTo.core_eq
    {branch : ℕ → ℕ} {candidate steps length : ℕ}
    (c : ExactReplayTo branch candidate steps)
    (g : NaturalPrefix branch length)
    (hsteps : steps ≤ length)
    (hinitial : g.core 0 = candidate) :
    ∀ t ≤ steps, g.core t = c.core t := by
  intro t ht
  induction t with
  | zero => exact hinitial.trans c.initial.symm
  | succ t ih =>
      have htlt : t < steps := by omega
      have hprefix := g.balance t (lt_of_lt_of_le htlt hsteps)
      have hcert := c.balance t htlt
      have hprevious : g.core t = c.core t := ih (by omega)
      have hmul :
          2 ^ binaryExponent branch t * g.core (t + 1) =
            2 ^ binaryExponent branch t * c.core (t + 1) := by
        calc
          2 ^ binaryExponent branch t * g.core (t + 1) =
              3 ^ ternaryExponent branch t * g.core t + 17 := hprefix
          _ = 3 ^ ternaryExponent branch t * c.core t + 17 := by
            rw [hprevious]
          _ = 2 ^ binaryExponent branch t * c.core (t + 1) := hcert.symm
      exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-! ### Compact composed-affine replay certificates -/

/-- Accumulated ternary exponent on a finite EC17 interval. -/
def replayTernaryMass (branch : ℕ → ℕ) (start length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, ternaryExponent branch (start + i)

theorem replayTernaryMass_zero (branch : ℕ → ℕ) (start : ℕ) :
    replayTernaryMass branch start 0 = 0 := by
  simp [replayTernaryMass]

theorem replayTernaryMass_succ (branch : ℕ → ℕ) (start length : ℕ) :
    replayTernaryMass branch start (length + 1) =
      ternaryExponent branch start +
        replayTernaryMass branch (start + 1) length := by
  rw [replayTernaryMass, Finset.sum_range_succ']
  simp only [replayTernaryMass]
  have hsum :
      (∑ i ∈ Finset.range length,
        ternaryExponent branch (start + (i + 1))) =
      ∑ i ∈ Finset.range length,
        ternaryExponent branch (start + 1 + i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hsum]
  ac_rfl

/-- Exact affine dependence of a finite backward EC17 evaluation on its
terminal value.  The earlier divisibility lemma deliberately hid the odd
factor; this identity exposes it as the inverse of the accumulated power of
three.  Thus terminal information is shifted upward by exactly
`binaryMass` binary digits, but is not destroyed at higher precision. -/
theorem backwardEval_sub_exact (branch : ℕ → ℕ) (P start length : ℕ)
    (x y : ZMod (2 ^ P)) :
    backwardEval branch P length start x -
        backwardEval branch P length start y =
      (2 : ZMod (2 ^ P)) ^ binaryMass branch start length *
        ((3 : ZMod (2 ^ P)) ^ replayTernaryMass branch start length)⁻¹ *
        (x - y) := by
  induction length generalizing start with
  | zero => simp [backwardEval, binaryMass, replayTernaryMass]
  | succ length ih =>
      rw [backwardEval, backwardEval, binaryMass_succ,
        replayTernaryMass_succ, pow_add, pow_add]
      simp only [backStep]
      have hthree : IsUnit (3 : ZMod (2 ^ P)) :=
        (ZMod.isUnit_iff_coprime 3 (2 ^ P)).2
          ((by norm_num : Nat.Coprime 3 2).pow_right P)
      have hfirst : IsUnit
          ((3 : ZMod (2 ^ P)) ^ ternaryExponent branch start) :=
        hthree.pow _
      have htail : IsUnit
          ((3 : ZMod (2 ^ P)) ^
            replayTernaryMass branch (start + 1) length) :=
        hthree.pow _
      have inv_mul_of_units (a b : ZMod (2 ^ P))
          (ha : IsUnit a) (hb : IsUnit b) :
          (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
        apply ZMod.inv_eq_of_mul_eq_one
        calc
          (a * b) * (b⁻¹ * a⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
          _ = 1 := by
            rw [ZMod.mul_inv_of_unit _ ha,
              ZMod.mul_inv_of_unit _ hb]
            simp
      calc
        (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) x - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ -
            (2 ^ binaryExponent branch start *
              backwardEval branch P length (start + 1) y - 17) *
                (3 ^ ternaryExponent branch start)⁻¹ =
            2 ^ binaryExponent branch start *
              (backwardEval branch P length (start + 1) x -
                backwardEval branch P length (start + 1) y) *
              (3 ^ ternaryExponent branch start)⁻¹ := by ring
        _ = 2 ^ binaryExponent branch start *
              (2 ^ binaryMass branch (start + 1) length *
                (3 ^ replayTernaryMass branch (start + 1) length)⁻¹ *
                (x - y)) *
              (3 ^ ternaryExponent branch start)⁻¹ := by
          rw [ih (start := start + 1)]
        _ = 2 ^ binaryExponent branch start *
              2 ^ binaryMass branch (start + 1) length *
              (3 ^ ternaryExponent branch start *
                3 ^ replayTernaryMass branch (start + 1) length)⁻¹ *
              (x - y) := by
          rw [inv_mul_of_units _ _ hfirst htail]
          ring

/-- Additive term in the EC17 interval composition, recursively split at the
first transition so the compact factorization can be decoded inductively. -/
def replayOffset (branch : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, length + 1 =>
      17 * 3 ^ replayTernaryMass branch (start + 1) length +
        2 ^ binaryExponent branch start *
          replayOffset branch (start + 1) length

theorem replayTernaryMass_shift (branch : ℕ → ℕ)
    (shift start length : ℕ) :
    replayTernaryMass (fun t => branch (shift + t)) start length =
      replayTernaryMass branch (shift + start) length := by
  simp only [replayTernaryMass]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ternaryExponent]
  rw [show shift + (start + i) = shift + start + i by omega]

theorem binaryMass_shift (branch : ℕ → ℕ) (shift start length : ℕ) :
    binaryMass (fun t => branch (shift + t)) start length =
      binaryMass branch (shift + start) length := by
  simp only [binaryMass]
  apply Finset.sum_congr rfl
  intro i _
  simp only [binaryExponent]
  rw [show shift + (start + i + 1) = shift + start + i + 1 by omega]

theorem replayOffset_shift (branch : ℕ → ℕ) (shift start length : ℕ) :
    replayOffset (fun t => branch (shift + t)) start length =
      replayOffset branch (shift + start) length := by
  induction length generalizing start with
  | zero => simp [replayOffset]
  | succ length ih =>
      simp only [replayOffset]
      rw [replayTernaryMass_shift, ih]
      have hstart : shift + (start + 1) = shift + start + 1 := by omega
      have hbinary :
          binaryExponent (fun t => branch (shift + t)) start =
            binaryExponent branch (shift + start) := by
        simp only [binaryExponent]
        rw [show shift + (start + 1) = shift + start + 1 by omega]
      rw [hstart, hbinary]

/-- One compact natural-number identity encoding an entire finite EC17
replay from `initial` to `terminal`. -/
def ComposedReplayFactor (branch : ℕ → ℕ) (start length initial terminal : ℕ) :
    Prop :=
  3 ^ replayTernaryMass branch start length * initial +
      replayOffset branch start length =
    2 ^ binaryMass branch start length * terminal

/-- Splitting a compact factorization exposes the first exact transition and
a compact factorization for the tail.  Oddness of the ternary multiplier is
what prevents a power of two from being hidden in the tail coefficient. -/
theorem composedReplayFactor_succ_iff
    (branch : ℕ → ℕ) (start length initial terminal : ℕ) :
    ComposedReplayFactor branch start (length + 1) initial terminal ↔
      ∃ next,
        2 ^ binaryExponent branch start * next =
          3 ^ ternaryExponent branch start * initial + 17 ∧
        ComposedReplayFactor branch (start + 1) length next terminal := by
  let b := binaryExponent branch start
  let a := ternaryExponent branch start
  let S := binaryMass branch (start + 1) length
  let T := replayTernaryMass branch (start + 1) length
  let C := replayOffset branch (start + 1) length
  let N := 3 ^ a * initial + 17
  have hbinary : binaryMass branch start (length + 1) = b + S := by
    simpa [b, S] using binaryMass_succ branch start length
  have hternary : replayTernaryMass branch start (length + 1) = a + T := by
    simpa [a, T] using replayTernaryMass_succ branch start length
  constructor
  · intro hfactor
    have hexpanded :
        3 ^ T * N + 2 ^ b * C = 2 ^ b * (2 ^ S * terminal) := by
      change 3 ^ replayTernaryMass branch start (length + 1) * initial +
          replayOffset branch start (length + 1) =
        2 ^ binaryMass branch start (length + 1) * terminal at hfactor
      rw [hbinary, hternary, pow_add, pow_add] at hfactor
      dsimp only [replayOffset] at hfactor
      dsimp only [a, b, S, T, C, N]
      nlinarith [hfactor]
    have hsumDvd : 2 ^ b ∣ 3 ^ T * N + 2 ^ b * C := by
      rw [hexpanded]
      exact dvd_mul_right _ _
    have hrightDvd : 2 ^ b ∣ 2 ^ b * C := dvd_mul_right _ _
    have hmulDvd : 2 ^ b ∣ 3 ^ T * N :=
      (Nat.dvd_add_left hrightDvd).mp hsumDvd
    have hcoprime : (2 ^ b).Coprime (3 ^ T) :=
      (by norm_num : Nat.Coprime 2 3).pow _ _
    have hNdiv : 2 ^ b ∣ N := hcoprime.dvd_of_dvd_mul_left hmulDvd
    let next := N / 2 ^ b
    have hstep : 2 ^ b * next = N := Nat.mul_div_cancel' hNdiv
    have htail : ComposedReplayFactor branch (start + 1) length next terminal := by
      change 3 ^ T * next + C = 2 ^ S * terminal
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ b)
      calc
        2 ^ b * (3 ^ T * next + C) =
            3 ^ T * (2 ^ b * next) + 2 ^ b * C := by ring
        _ = 3 ^ T * N + 2 ^ b * C := by rw [hstep]
        _ = 2 ^ b * (2 ^ S * terminal) := hexpanded
    refine ⟨next, ?_, htail⟩
    simpa [a, b, N] using hstep
  · rintro ⟨next, hstep, htail⟩
    change 3 ^ replayTernaryMass branch start (length + 1) * initial +
        replayOffset branch start (length + 1) =
      2 ^ binaryMass branch start (length + 1) * terminal
    change 3 ^ T * next + C = 2 ^ S * terminal at htail
    rw [hbinary, hternary, pow_add, pow_add]
    dsimp only [replayOffset]
    change
      (3 ^ a * 3 ^ T) * initial +
          (17 * 3 ^ T + 2 ^ b * C) =
        (2 ^ b * 2 ^ S) * terminal
    calc
      (3 ^ a * 3 ^ T) * initial +
            (17 * 3 ^ T + 2 ^ b * C) =
          3 ^ T * (3 ^ a * initial + 17) + 2 ^ b * C := by ring
      _ = 3 ^ T * (2 ^ b * next) + 2 ^ b * C := by
        rw [← hstep]
      _ = 2 ^ b * (3 ^ T * next + C) := by ring
      _ = 2 ^ b * (2 ^ S * terminal) := by rw [htail]
      _ = (2 ^ b * 2 ^ S) * terminal := by ring

/-- Decode a compact factorization into every exact intermediate EC17
balance.  Only the terminal core is stored in addition to the initial core. -/
theorem exactReplayTo_of_composedReplayFactor
    (branch : ℕ → ℕ) (initial terminal steps : ℕ)
    (hfactor : ComposedReplayFactor branch 0 steps initial terminal) :
    ∃ replay : ExactReplayTo branch initial steps,
      replay.core steps = terminal := by
  induction steps generalizing branch initial with
  | zero =>
      let replay : ExactReplayTo branch initial 0 := {
        core := fun _ => initial
        initial := rfl
        balance := by intro t ht; omega
      }
      refine ⟨replay, ?_⟩
      change initial = terminal
      simpa [ComposedReplayFactor, replayTernaryMass, replayOffset,
        binaryMass] using hfactor
  | succ steps ih =>
      obtain ⟨next, hstep, htail⟩ :=
        (composedReplayFactor_succ_iff branch 0 steps initial terminal).mp
          (by simpa using hfactor)
      let tailBranch : ℕ → ℕ := fun t => branch (1 + t)
      have htailShift :
          ComposedReplayFactor tailBranch 0 steps next terminal := by
        simpa [tailBranch, ComposedReplayFactor, replayTernaryMass_shift,
          replayOffset_shift, binaryMass_shift] using htail
      obtain ⟨tail, hterminal⟩ := ih tailBranch next htailShift
      let replay : ExactReplayTo branch initial (steps + 1) := {
        core := fun
          | 0 => initial
          | t + 1 => tail.core t
        initial := rfl
        balance := by
          intro t ht
          cases t with
          | zero =>
              change 2 ^ binaryExponent branch 0 * tail.core 0 =
                3 ^ ternaryExponent branch 0 * initial + 17
              rw [tail.initial]
              exact hstep
          | succ t =>
              have htt : t < steps := by omega
              have htailBalance := tail.balance t htt
              simpa only [tailBranch, binaryExponent, ternaryExponent,
                Nat.one_add, Nat.add_assoc] using htailBalance
      }
      refine ⟨replay, ?_⟩
      change tail.core steps = terminal
      exact hterminal

/-- A checker certificate for the Python `actual < required` branch: the
candidate replays exactly up to `step`, but the required binary power does
not divide the next numerator. -/
structure NondivisibleReplayFailure (branch : ℕ → ℕ) (candidate : ℕ) where
  step : ℕ
  replay : ExactReplayTo branch candidate step
  failure : ¬ 2 ^ binaryExponent branch step ∣
    3 ^ ternaryExponent branch step * replay.core step + 17

/-- A nondivisible replay-failure certificate rules out every natural prefix
long enough to contain the failed transition. -/
theorem NondivisibleReplayFailure.excludesNaturalPrefix
    {branch : ℕ → ℕ} {candidate length : ℕ}
    (c : NondivisibleReplayFailure branch candidate)
    (g : NaturalPrefix branch length)
    (hstep : c.step < length)
    (hinitial : g.core 0 = candidate) : False := by
  have heq : g.core c.step = c.replay.core c.step :=
    c.replay.core_eq g (by omega) hinitial c.step (le_refl _)
  apply c.failure
  rw [← heq, ← g.balance c.step hstep]
  exact dvd_mul_right _ _

theorem NondivisibleReplayFailure.not_admitsNaturalPrefix
    {branch : ℕ → ℕ} {candidate : ℕ}
    (c : NondivisibleReplayFailure branch candidate)
    {length : ℕ} (hstep : c.step < length) :
    ¬ AdmitsNaturalPrefix branch length candidate := by
  rintro ⟨g, hinitial⟩
  exact c.excludesNaturalPrefix g hstep hinitial

/-- A checker certificate for the Python `actual > required` branch: the
candidate replays through the reported transition, but the resulting core is
even.  This becomes a contradiction only when the required prefix includes
one further transition. -/
structure EvenQuotientReplayFailure (branch : ℕ → ℕ) (candidate : ℕ) where
  step : ℕ
  replay : ExactReplayTo branch candidate (step + 1)
  next_even : replay.core (step + 1) % 2 = 0

/-- An even-quotient certificate rules out every natural prefix containing
the following transition.  This explicit `step+1<length` guard is the
off-by-one condition needed to soundly interpret `actual > required`. -/
theorem EvenQuotientReplayFailure.excludesNaturalPrefix
    {branch : ℕ → ℕ} {candidate length : ℕ}
    (c : EvenQuotientReplayFailure branch candidate)
    (g : NaturalPrefix branch length)
    (hnext : c.step + 1 < length)
    (hinitial : g.core 0 = candidate) : False := by
  have heq : g.core (c.step + 1) = c.replay.core (c.step + 1) :=
    c.replay.core_eq g (by omega) hinitial (c.step + 1) (le_refl _)
  have hodd := g.core_mod_two_eq_one (c.step + 1) hnext
  rw [heq, c.next_even] at hodd
  omega

theorem EvenQuotientReplayFailure.not_admitsNaturalPrefix
    {branch : ℕ → ℕ} {candidate : ℕ}
    (c : EvenQuotientReplayFailure branch candidate)
    {length : ℕ} (hnext : c.step + 1 < length) :
    ¬ AdmitsNaturalPrefix branch length candidate := by
  rintro ⟨g, hinitial⟩
  exact c.excludesNaturalPrefix g hnext hinitial

/-- Compact under-divisibility certificate: one composed identity replaces
the entire list of intermediate replay cores. -/
structure CompactNondivisibleReplayFailure
    (branch : ℕ → ℕ) (candidate : ℕ) where
  step : ℕ
  terminal : ℕ
  factor : ComposedReplayFactor branch 0 step candidate terminal
  failure : ¬ 2 ^ binaryExponent branch step ∣
    3 ^ ternaryExponent branch step * terminal + 17

theorem CompactNondivisibleReplayFailure.not_admitsNaturalPrefix
    {branch : ℕ → ℕ} {candidate : ℕ}
    (c : CompactNondivisibleReplayFailure branch candidate)
    {length : ℕ} (hstep : c.step < length) :
    ¬ AdmitsNaturalPrefix branch length candidate := by
  intro hadmits
  obtain ⟨replay, hterminal⟩ :=
    exactReplayTo_of_composedReplayFactor branch candidate c.terminal c.step
      c.factor
  let expanded : NondivisibleReplayFailure branch candidate := {
    step := c.step
    replay := replay
    failure := by simpa [hterminal] using c.failure
  }
  exact expanded.not_admitsNaturalPrefix (by simpa [expanded] using hstep)
    hadmits

/-- Compact over-divisibility certificate.  The composed identity runs
through the reported transition and stores only its even terminal quotient. -/
structure CompactEvenQuotientReplayFailure
    (branch : ℕ → ℕ) (candidate : ℕ) where
  step : ℕ
  terminal : ℕ
  factor : ComposedReplayFactor branch 0 (step + 1) candidate terminal
  terminal_even : terminal % 2 = 0

theorem CompactEvenQuotientReplayFailure.not_admitsNaturalPrefix
    {branch : ℕ → ℕ} {candidate : ℕ}
    (c : CompactEvenQuotientReplayFailure branch candidate)
    {length : ℕ} (hnext : c.step + 1 < length) :
    ¬ AdmitsNaturalPrefix branch length candidate := by
  intro hadmits
  obtain ⟨replay, hterminal⟩ :=
    exactReplayTo_of_composedReplayFactor branch candidate c.terminal
      (c.step + 1) c.factor
  let expanded : EvenQuotientReplayFailure branch candidate := {
    step := c.step
    replay := replay
    next_even := by simpa [hterminal] using c.terminal_even
  }
  exact expanded.not_admitsNaturalPrefix (by simpa [expanded] using hnext)
    hadmits

/-! ## Coprime predecessor/future residue synthesis -/

/-- Reducing one literal EC17 balance modulo its ternary numerator modulus
removes the predecessor term.  Keeping the invertible power of two on the
left avoids any dependence on an implementation of modular inversion. -/
theorem ec17_successor_mul_modEq
    (previous successor previousCore successorCore : ℕ)
    (hbalance :
      2 ^ (8 * successor + 15) * successorCore =
        3 ^ (6 * previous + 11) * previousCore + 17) :
    2 ^ (8 * successor + 15) * successorCore ≡ 17
      [MOD 3 ^ (6 * previous + 11)] := by
  rw [hbalance]
  exact (Nat.modEq_modulus_mul_add_iff.mpr (Nat.ModEq.refl 17)).symm

/-- A candidate satisfying the same multiplied residue as a genuine EC17
successor is congruent to that successor.  This is QM82 in a form that is
both cheaper to kernel-check and stronger for certificate verification than
computing a modular inverse inside Lean. -/
theorem ec17_successor_modEq_of_candidate
    (previous successor previousCore successorCore candidate : ℕ)
    (hbalance :
      2 ^ (8 * successor + 15) * successorCore =
        3 ^ (6 * previous + 11) * previousCore + 17)
    (hcandidate :
      2 ^ (8 * successor + 15) * candidate ≡ 17
        [MOD 3 ^ (6 * previous + 11)]) :
    successorCore ≡ candidate [MOD 3 ^ (6 * previous + 11)] := by
  have hmul :
      2 ^ (8 * successor + 15) * successorCore ≡
        2 ^ (8 * successor + 15) * candidate
          [MOD 3 ^ (6 * previous + 11)] :=
    (ec17_successor_mul_modEq previous successor previousCore successorCore
      hbalance).trans hcandidate.symm
  apply Nat.ModEq.cancel_left_of_coprime _ hmul
  exact Nat.Coprime.gcd_eq_one
    ((by norm_num : Nat.Coprime 3 2).pow _ _)

/-- Abstract CRT certificate consumer.  If a genuine object and a canonical
representative obey the same two coprime residue constraints, but the
representative fails a necessary predicate, then every genuine object is at
least the product modulus.  This is the theorem behind the large period-three
CRT lower bounds; it contains no numerical computation. -/
theorem coprime_residue_failure_forces_product_lower_bound
    (m n candidate x : ℕ) (Required : ℕ → Prop)
    (hcoprime : m.Coprime n)
    (hxm : x ≡ candidate [MOD m])
    (hxn : x ≡ candidate [MOD n])
    (hcandidate : candidate < m * n)
    (hx : Required x) (hfail : ¬Required candidate) :
    m * n ≤ x := by
  by_contra hsmall
  push Not at hsmall
  have hproduct : x ≡ candidate [MOD m * n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).1 ⟨hxm, hxn⟩
  have heq : x = candidate :=
    hproduct.eq_of_lt_of_lt hsmall hcandidate
  exact hfail (heq ▸ hx)

end EtherCounterResidueBound
end KontoroC

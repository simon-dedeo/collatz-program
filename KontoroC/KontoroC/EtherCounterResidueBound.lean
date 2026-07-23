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

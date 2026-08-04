/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.Collatz.Defs
import Mathlib.Data.Nat.Log

/-!
# Certified stopping-time scaling

This file gives a termination-safe interface for lower bounds on Collatz
stopping time in terms of the *actual binary length* of the starting integer.
It deliberately separates a long controlled prefix from a terminating long
run: the former only proves that `1` is avoided for a stated duration, while
the latter additionally proves eventual arrival at `1`.

The main reusable object is `RecursiveScalingCertificate`.  It asks for a
family whose binary length increases by at most `C` per level and whose
certified duration is multiplied by at least `q` per level.  The theorem
`RecursiveScalingCertificate.hasTerminatingLongRun_pow` then produces, at
level `m`, a terminating seed with at most `bitLength(seed 0) + C*m` bits and
at least `q^m` Collatz steps before its first visit to `1`.

Thus an instance with `q = 2` is exactly the sought exponential-scaling
certificate.  No such Collatz family is constructed here.
-/

namespace KontoroC
namespace StoppingTimeScaling

open CleanLean.Collatz

/-- Actual binary length.  We use this only for positive seeds; the value at
zero is harmless and keeps the definition total. -/
def bitLength (n : ℕ) : ℕ :=
  (Nat.log 2 n).succ

/-- The Collatz orbit of `n` avoids `1` for the first `L` iterates.  In
particular, `Survives n 0` is vacuous. -/
def Survives (n L : ℕ) : Prop :=
  ∀ j < L, step^[j] n ≠ 1

/-- A finite, exact lower-bound certificate for the first visit to `1`.
Unlike `TerminatingLongRun`, this does not assert that the orbit ever reaches
`1`. -/
structure LongRun (n L : ℕ) : Prop where
  seed_pos : 0 < n
  survives : Survives n L

/-- A certified long run which is also known to terminate at the `1`-cycle. -/
structure TerminatingLongRun (n L : ℕ) : Prop extends LongRun n L where
  reachesOne : ReachesOne n

/-- Exact exit data sufficient to turn a controlled prefix into a certified
terminating long run. -/
structure ExactExit (n L terminal : ℕ) : Prop where
  seed_pos : 0 < n
  survives : Survives n L
  exit_eq : step^[L] n = terminal
  terminal_reachesOne : ReachesOne terminal

/-- A certified finite detour from `n` to `terminal`.  Unlike `ExactExit`,
this contains no global termination claim; it can therefore be composed with
any separately certified terminating tail from `terminal`. -/
structure ExactPrefix (n L terminal : ℕ) : Prop where
  seed_pos : 0 < n
  survives : Survives n L
  exit_eq : step^[L] n = terminal

/-- There is a terminating seed of at most `b` actual bits which avoids `1`
for at least `L` steps.  This existential formulation avoids assigning a
value to the stopping time of a hypothetical nonterminating orbit. -/
def HasTerminatingLongRun (b L : ℕ) : Prop :=
  ∃ n, bitLength n ≤ b ∧ TerminatingLongRun n L

/-- The actual bit lengths of a seed family eventually exceed every fixed
bound.  This prevents a constant finite collection of seeds from masquerading
as an asymptotic scaling family. -/
def BitLengthsTendToInfinity (seed : ℕ → ℕ) : Prop :=
  ∀ B, ∃ M, ∀ m, M ≤ m → B ≤ bitLength (seed m)

/-- Elementary, division-free formulation of a superlinear time law:
`timeFloor(b) / b` tends to infinity through integer comparison. -/
def IsSuperlinearLaw (timeFloor : ℕ → ℕ) : Prop :=
  ∀ K, ∃ B, ∀ b, B ≤ b → K * b < timeFloor b

theorem survives_mono {n L K : ℕ} (hLK : L ≤ K) (h : Survives n K) :
    Survives n L := by
  intro j hj
  exact h j (lt_of_lt_of_le hj hLK)

theorem ExactExit.toTerminatingLongRun {n L terminal : ℕ}
    (h : ExactExit n L terminal) : TerminatingLongRun n L where
  seed_pos := h.seed_pos
  survives := h.survives
  reachesOne := by
    apply reachesOne_of_iterate (k := L)
    simpa [h.exit_eq] using h.terminal_reachesOne

/-- Prepending an exact `L`-step detour to a terminating `R`-step tail gives
a terminating run of length `L + R`.  This is the semantic core of the
detour-wrapper construction below. -/
theorem ExactPrefix.prepend {n L terminal R : ℕ}
    (pfx : ExactPrefix n L terminal)
    (tail : TerminatingLongRun terminal R) :
    TerminatingLongRun n (L + R) where
  seed_pos := pfx.seed_pos
  survives := by
    intro j hj
    by_cases hjL : j < L
    · exact pfx.survives j hjL
    · have hLj : L ≤ j := Nat.le_of_not_gt hjL
      have hjR : j - L < R := by omega
      have hsplit : (j - L) + L = j := by omega
      have horbit : step^[j] n = step^[j - L] terminal := by
        calc
          step^[j] n = step^[(j - L) + L] n := by rw [hsplit]
          _ = step^[j - L] (step^[L] n) := by
            rw [Function.iterate_add_apply]
          _ = step^[j - L] terminal := by rw [pfx.exit_eq]
      rw [horbit]
      exact tail.survives (j - L) hjR
  reachesOne := by
    apply reachesOne_of_iterate (k := L)
    simpa [pfx.exit_eq] using tail.reachesOne

theorem TerminatingLongRun.mono {n L K : ℕ} (hLK : L ≤ K)
    (h : TerminatingLongRun n K) : TerminatingLongRun n L where
  seed_pos := h.seed_pos
  survives := survives_mono hLK h.survives
  reachesOne := h.reachesOne

/-- Direct family interface.  It is convenient when the bit and duration
bounds are already available in closed form. -/
structure DirectScalingCertificate (bitCap duration : ℕ → ℕ) : Type where
  seed : ℕ → ℕ
  certified : ∀ m, TerminatingLongRun (seed m) (duration m)
  bit_bound : ∀ m, bitLength (seed m) ≤ bitCap m

theorem DirectScalingCertificate.hasTerminatingLongRun
    {bitCap duration : ℕ → ℕ}
    (cert : DirectScalingCertificate bitCap duration) (m : ℕ) :
    HasTerminatingLongRun (bitCap m) (duration m) := by
  exact ⟨cert.seed m, cert.bit_bound m, cert.certified m⟩

/-- Scaling interface indexed by the seed's *actual* bit length rather than
by an external construction parameter. -/
structure BitLawScalingCertificate (timeFloor : ℕ → ℕ) : Type where
  seed : ℕ → ℕ
  bits_tend_to_infinity : BitLengthsTendToInfinity seed
  certified : ∀ m,
    TerminatingLongRun (seed m) (timeFloor (bitLength (seed m)))

theorem BitLawScalingCertificate.hasTerminatingLongRun
    {timeFloor : ℕ → ℕ} (cert : BitLawScalingCertificate timeFloor)
    (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed m))
      (timeFloor (bitLength (cert.seed m))) := by
  exact ⟨cert.seed m, le_rfl, cert.certified m⟩

/-- A bit-law certificate for a superlinear law gives terminating Collatz
seeds whose certified lifetimes eventually beat every constant multiple of
their actual bit lengths. -/
theorem BitLawScalingCertificate.eventually_lifetime_gt_mul_bits
    {timeFloor : ℕ → ℕ} (cert : BitLawScalingCertificate timeFloor)
    (hlaw : IsSuperlinearLaw timeFloor) (K : ℕ) :
    ∃ M, ∀ m, M ≤ m →
      K * bitLength (cert.seed m) < timeFloor (bitLength (cert.seed m)) := by
  obtain ⟨B, hB⟩ := hlaw K
  obtain ⟨M, hM⟩ := cert.bits_tend_to_infinity B
  exact ⟨M, fun m hm ↦ hB _ (hM m hm)⟩

/-- Exact polynomial target.  Degree two already gives a superlinear family;
higher degrees use the same semantic interface. -/
abbrev PolynomialScalingCertificate (degree : ℕ) : Type :=
  BitLawScalingCertificate (fun b ↦ b ^ degree)

/-- Exact exponential target as a function of actual seed bits. -/
abbrev ExponentialBitScalingCertificate (base : ℕ) : Type :=
  BitLawScalingCertificate (fun b ↦ base ^ b)

/-- Quadratic lifetime is a superlinear bit law. -/
theorem quadratic_isSuperlinearLaw : IsSuperlinearLaw (fun b ↦ b ^ 2) := by
  intro K
  refine ⟨K + 1, ?_⟩
  intro b hb
  change K * b < b ^ 2
  rw [pow_two]
  have hKb : K < b := by omega
  exact (Nat.mul_lt_mul_right (by omega : 0 < b)).2 hKb

/-- Recursive renormalization interface.  A certificate with `q > 1` stores
only `C` additional bits per level but multiplies the certified lifetime by
`q`.  The exact Collatz semantics and termination are carried by `certified`;
the two recurrence fields are pure resource accounting. -/
structure RecursiveScalingCertificate (C q : ℕ) : Type where
  seed : ℕ → ℕ
  duration : ℕ → ℕ
  certified : ∀ m, TerminatingLongRun (seed m) (duration m)
  bit_step : ∀ m, bitLength (seed (m + 1)) ≤ bitLength (seed m) + C
  duration_base : 1 ≤ duration 0
  duration_step : ∀ m, q * duration m ≤ duration (m + 1)

theorem RecursiveScalingCertificate.bit_bound {C q : ℕ}
    (cert : RecursiveScalingCertificate C q) (m : ℕ) :
    bitLength (cert.seed m) ≤ bitLength (cert.seed 0) + C * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        bitLength (cert.seed (m + 1)) ≤ bitLength (cert.seed m) + C :=
          cert.bit_step m
        _ ≤ (bitLength (cert.seed 0) + C * m) + C :=
          Nat.add_le_add_right ih C
        _ = bitLength (cert.seed 0) + C * (m + 1) := by
          simp only [Nat.mul_succ, Nat.add_assoc]

theorem RecursiveScalingCertificate.duration_pow_le {C q : ℕ}
    (cert : RecursiveScalingCertificate C q) (m : ℕ) :
    q ^ m ≤ cert.duration m := by
  induction m with
  | zero => simpa using cert.duration_base
  | succ m ih =>
      calc
        q ^ (m + 1) = q * q ^ m := by rw [pow_succ, Nat.mul_comm]
        _ ≤ q * cert.duration m := Nat.mul_le_mul_left q ih
        _ ≤ cert.duration (m + 1) := cert.duration_step m

/-- Fundamental scaling theorem: bounded additive bit growth plus
multiplicative lifetime growth yields a terminating `q^m`-step Collatz seed
inside a linear bit budget. -/
theorem RecursiveScalingCertificate.hasTerminatingLongRun_pow {C q : ℕ}
    (cert : RecursiveScalingCertificate C q) (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed 0) + C * m) (q ^ m) := by
  refine ⟨cert.seed m, cert.bit_bound m, ?_⟩
  exact (cert.certified m).mono (cert.duration_pow_le m)

/-- The exact exponential target, specialized to lifetime doubling. -/
theorem RecursiveScalingCertificate.hasTerminatingLongRun_two_pow {C : ℕ}
    (cert : RecursiveScalingCertificate C 2) (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed 0) + C * m) (2 ^ m) :=
  cert.hasTerminatingLongRun_pow m

/-! ## Construction principles -/

/-- A state-dependent renormalizer.  The carrier `State` can contain rails,
phase, or other proof-relevant data; only `encode s` is charged as the actual
ordinary seed.  This is the primary local construction interface because a
Collatz time-dilation law need hold only on one invariant encoded family, not
on every natural number. -/
structure EncodedTimeDilationRenormalizer (State : Type) (C q : ℕ) : Type where
  encode : State → ℕ
  next : State → State
  bit_cost : ∀ s, bitLength (encode (next s)) ≤ bitLength (encode s) + C
  dilates : ∀ {s L}, TerminatingLongRun (encode s) L →
    TerminatingLongRun (encode (next s)) (q * L)

/-- Iterating an encoded time-dilation state transition gives an exponential
recursive scaling certificate. -/
def EncodedTimeDilationRenormalizer.toRecursiveScalingCertificate
    {State : Type} {C q L : ℕ} (ren : EncodedTimeDilationRenormalizer State C q)
    (initial : State) (hL : 1 ≤ L)
    (h : TerminatingLongRun (ren.encode initial) L) :
    RecursiveScalingCertificate C q where
  seed m := ren.encode (ren.next^[m] initial)
  duration m := q ^ m * L
  certified m := by
    induction m with
    | zero => simpa using h
    | succ m ih =>
        simpa only [Function.iterate_succ_apply', pow_succ, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm] using ren.dilates ih
  bit_step m := by
    simpa only [Function.iterate_succ_apply'] using ren.bit_cost (ren.next^[m] initial)
  duration_base := by simpa using hL
  duration_step m := by
    apply le_of_eq
    rw [pow_succ]
    ac_rfl

/-- A local time-dilation renormalizer.  It adds at most `C` actual bits and
turns *any supplied terminating `L`-step run* into a terminating run lasting
at least `q*L` steps.  A single instance with `q > 1` is a seed-construction
principle for exponential stopping-time scaling. -/
structure TimeDilationRenormalizer (C q : ℕ) : Type where
  lift : ℕ → ℕ
  bit_cost : ∀ n, bitLength (lift n) ≤ bitLength n + C
  dilates : ∀ {n L}, TerminatingLongRun n L →
    TerminatingLongRun (lift n) (q * L)

/-- Iterating a local time-dilation renormalizer constructs the recursive
exponential certificate. -/
def TimeDilationRenormalizer.toRecursiveScalingCertificate
    {C q n L : ℕ} (ren : TimeDilationRenormalizer C q)
    (hL : 1 ≤ L) (h : TerminatingLongRun n L) :
    RecursiveScalingCertificate C q := by
  let encoded : EncodedTimeDilationRenormalizer ℕ C q :=
    { encode := id
      next := ren.lift
      bit_cost := ren.bit_cost
      dilates := ren.dilates }
  exact encoded.toRecursiveScalingCertificate n hL h

/-- An additive-delay recurrence.  If `gain m` grows with the construction
level, then its partial sums can give polynomial or other superlinear
lifetimes while the seed pays only `C` new bits per level. -/
structure AccumulatingScalingCertificate (C : ℕ) (gain : ℕ → ℕ) : Type where
  seed : ℕ → ℕ
  duration : ℕ → ℕ
  certified : ∀ m, TerminatingLongRun (seed m) (duration m)
  bit_step : ∀ m, bitLength (seed (m + 1)) ≤ bitLength (seed m) + C
  duration_base : 1 ≤ duration 0
  duration_step : ∀ m, duration m + gain m ≤ duration (m + 1)

/-- A bounded-bit wrapper which sends an encoded state on an exact Collatz
detour back to the previous encoded state.  It is a particularly concrete
seed-construction principle: `wrap s` is the new seed, `delay s` is the
inserted waiting time, and eventual termination is inherited from `s`.

If the inserted delays at successive levels grow like `m`, their sum is
quadratic while bit length remains linear in `m`.  If each delay dominates
the lifetime accumulated so far, the lifetime doubles at every level. -/
structure EncodedDetourWrapper (State : Type) (C : ℕ) : Type where
  encode : State → ℕ
  wrap : State → State
  delay : State → ℕ
  bit_cost : ∀ s, bitLength (encode (wrap s)) ≤ bitLength (encode s) + C
  detour : ∀ s, ExactPrefix (encode (wrap s)) (delay s) (encode s)

/-- Iterating a detour wrapper gives an additive scaling certificate whose
gain at level `m` is the exact delay inserted around the level-`m` seed. -/
def EncodedDetourWrapper.toAccumulatingScalingCertificate
    {State : Type} {C L : ℕ} (wrapper : EncodedDetourWrapper State C)
    (initial : State) (hL : 1 ≤ L)
    (h : TerminatingLongRun (wrapper.encode initial) L) :
    AccumulatingScalingCertificate C
      (fun m ↦ wrapper.delay (wrapper.wrap^[m] initial)) where
  seed m := wrapper.encode (wrapper.wrap^[m] initial)
  duration m := L + ∑ i ∈ Finset.range m,
    wrapper.delay (wrapper.wrap^[i] initial)
  certified m := by
    induction m with
    | zero => simpa using h
    | succ m ih =>
        rw [Finset.sum_range_succ]
        simpa only [Function.iterate_succ_apply', Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using
          (wrapper.detour (wrapper.wrap^[m] initial)).prepend ih
  bit_step m := by
    simpa only [Function.iterate_succ_apply'] using
      wrapper.bit_cost (wrapper.wrap^[m] initial)
  duration_base := by simpa using hL
  duration_step m := by
    simp only [Finset.sum_range_succ, Nat.add_assoc]
    exact le_rfl

theorem AccumulatingScalingCertificate.bit_bound {C : ℕ} {gain : ℕ → ℕ}
    (cert : AccumulatingScalingCertificate C gain) (m : ℕ) :
    bitLength (cert.seed m) ≤ bitLength (cert.seed 0) + C * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        bitLength (cert.seed (m + 1)) ≤ bitLength (cert.seed m) + C :=
          cert.bit_step m
        _ ≤ (bitLength (cert.seed 0) + C * m) + C :=
          Nat.add_le_add_right ih C
        _ = bitLength (cert.seed 0) + C * (m + 1) := by
          simp only [Nat.mul_succ, Nat.add_assoc]

theorem AccumulatingScalingCertificate.sum_gain_le_duration
    {C : ℕ} {gain : ℕ → ℕ}
    (cert : AccumulatingScalingCertificate C gain) (m : ℕ) :
    1 + ∑ i ∈ Finset.range m, gain i ≤ cert.duration m := by
  induction m with
  | zero => simpa using cert.duration_base
  | succ m ih =>
      calc
        1 + ∑ i ∈ Finset.range (m + 1), gain i =
            (1 + ∑ i ∈ Finset.range m, gain i) + gain m := by
              simp only [Finset.sum_range_succ, Nat.add_assoc]
        _ ≤ cert.duration m + gain m := Nat.add_le_add_right ih (gain m)
        _ ≤ cert.duration (m + 1) := cert.duration_step m

/-- If every newly inserted delay is at least the lifetime accumulated at
that level, then the certified lifetime doubles and is therefore exponential
in the construction depth. -/
theorem AccumulatingScalingCertificate.two_pow_le_duration
    {C : ℕ} {gain : ℕ → ℕ}
    (cert : AccumulatingScalingCertificate C gain)
    (gain_dominates : ∀ m, cert.duration m ≤ gain m) (m : ℕ) :
    2 ^ m ≤ cert.duration m := by
  induction m with
  | zero => simpa using cert.duration_base
  | succ m ih =>
      calc
        2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
        _ ≤ 2 * cert.duration m := Nat.mul_le_mul_left 2 ih
        _ = cert.duration m + cert.duration m := by omega
        _ ≤ cert.duration m + gain m :=
          Nat.add_le_add_left (gain_dominates m) (cert.duration m)
        _ ≤ cert.duration (m + 1) := cert.duration_step m

/-- The first `m` positive odd numbers sum to `m²`.  This is the exact
resource identity behind the simplest quadratic detour schedule. -/
theorem sum_odd_eq_square (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 * i + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Fundamental polynomial-scaling theorem: an additive gain schedule gives
the corresponding partial-sum lifetime inside a linear bit budget. -/
theorem AccumulatingScalingCertificate.hasTerminatingLongRun_sum
    {C : ℕ} {gain : ℕ → ℕ}
    (cert : AccumulatingScalingCertificate C gain) (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed 0) + C * m)
      (1 + ∑ i ∈ Finset.range m, gain i) := by
  refine ⟨cert.seed m, cert.bit_bound m, ?_⟩
  exact (cert.certified m).mono (cert.sum_gain_le_duration m)

/-- A bounded-bit construction which inserts the level-dependent delay
`2*m+1` produces an explicit quadratic lower bound. -/
theorem AccumulatingScalingCertificate.hasTerminatingLongRun_quadratic
    {C : ℕ} (cert : AccumulatingScalingCertificate C (fun m ↦ 2 * m + 1))
    (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed 0) + C * m) (1 + m ^ 2) := by
  simpa only [sum_odd_eq_square] using cert.hasTerminatingLongRun_sum m

/-- Under delay domination, the same bounded-bit additive construction gives
an exponential lower bound. -/
theorem AccumulatingScalingCertificate.hasTerminatingLongRun_two_pow
    {C : ℕ} {gain : ℕ → ℕ}
    (cert : AccumulatingScalingCertificate C gain)
    (gain_dominates : ∀ m, cert.duration m ≤ gain m) (m : ℕ) :
    HasTerminatingLongRun (bitLength (cert.seed 0) + C * m) (2 ^ m) := by
  refine ⟨cert.seed m, cert.bit_bound m, ?_⟩
  exact (cert.certified m).mono (cert.two_pow_le_duration gain_dominates m)

/-! ## Linear calibration: powers of two -/

/-- One ordinary Collatz step removes one binary digit from a positive power
of two. -/
theorem step_two_pow_succ (m : ℕ) : step (2 ^ (m + 1)) = 2 ^ m := by
  simp [step, pow_succ]

/-- Exact iterate formula for the power-of-two tail. -/
theorem iterate_two_pow_add (m j : ℕ) :
    step^[j] (2 ^ (m + j)) = 2 ^ m := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      have hpower : 2 ^ (m + (j + 1)) = 2 ^ ((m + j) + 1) := by
        congr 1
      rw [hpower, step_two_pow_succ]
      exact ih

theorem two_pow_terminatingLongRun (m : ℕ) :
    TerminatingLongRun (2 ^ m) m where
  seed_pos := Nat.pow_pos (by omega)
  survives := by
    intro j hj
    have hjle : j ≤ m := Nat.le_of_lt hj
    have horbit : step^[j] (2 ^ m) = 2 ^ (m - j) := by
      have h := iterate_two_pow_add (m - j) j
      rw [Nat.sub_add_cancel hjle] at h
      exact h
    rw [horbit]
    exact ne_of_gt (one_lt_pow' (by omega) (by omega))
  reachesOne := by
    refine ⟨m, ?_⟩
    simpa using iterate_two_pow_add 0 m

/-- Sanity check for the interface: `2^m` has exactly `m+1` bits and takes
exactly `m` steps to reach `1`.  This is a certified linear family, not a
superlinear one. -/
def powersOfTwoLinearCertificate :
    DirectScalingCertificate (fun m ↦ m + 1) (fun m ↦ m) where
  seed m := 2 ^ m
  certified := two_pow_terminatingLongRun
  bit_bound m := by
    simp [bitLength, Nat.log_pow]

end StoppingTimeScaling
end KontoroC

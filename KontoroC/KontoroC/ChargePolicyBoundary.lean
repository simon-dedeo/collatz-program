/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeBouncerPeriodicNoGo
import KontoroC.DyadicCylinderBoundary
import KontoroC.ChargeResonantConjugacy

/-!
# Ordinary-tail boundary for dependent charge policies

An endogenous opcode policy such as `U(m)=(m,392,m+4)` is not excluded by a
finite-state or periodicity argument.  Its finite prefixes nevertheless impose
one canonical dyadic address on the *initial* public tail.  This file isolates
the exact reduction: an ordinary infinite ray realizes all prefix addresses,
so their extension lifts must eventually vanish.

No phase-up residue sequence or infinite ray is supplied here.
-/

namespace KontoroC

open ChargeBouncerPeriodicNoGo

/-- An infinite dependent affine tail policy whose step denominators are
powers of two.  The phase-up rule is obtained by substituting its decoded
phase-dependent exponents and corrections. -/
structure DependentDyadicAffineRay where
  state : ℕ → ℕ
  state_pos : ∀ t, 0 < state t
  stepBits : ℕ → ℕ
  coefficient : ℕ → ℕ
  gain : ℕ → ℕ
  balance : ∀ t,
    2 ^ stepBits t * state (t + 1) =
      coefficient t * state t + gain t

namespace DependentDyadicAffineRay

def prefixBits (g : DependentDyadicAffineRay) (n : ℕ) : ℕ :=
  prefixSum g.stepBits n

def prefixCoefficient (g : DependentDyadicAffineRay) (n : ℕ) : ℕ :=
  prefixProduct g.coefficient n

def prefixGain (g : DependentDyadicAffineRay) (n : ℕ) : ℕ :=
  ChargeBouncerPeriodicNoGo.prefixGain g.coefficient
    (fun t => 2 ^ g.stepBits t) g.gain n

theorem prefixDenominator_eq_pow (g : DependentDyadicAffineRay) (n : ℕ) :
    prefixProduct (fun t => 2 ^ g.stepBits t) n = 2 ^ g.prefixBits n := by
  induction n with
  | zero => simp [prefixProduct, prefixBits, prefixSum]
  | succ n ih =>
      change prefixProduct (fun t => 2 ^ g.stepBits t) n =
        2 ^ prefixSum g.stepBits n at ih
      simp only [prefixProduct, prefixBits, prefixSum]
      rw [ih, ← pow_add]

/-- Finite elimination of a dependent policy: the accumulated dyadic
denominator times the integer endpoint equals one affine expression in the
initial tail. -/
theorem prefix_balance (g : DependentDyadicAffineRay) (n : ℕ) :
    2 ^ g.prefixBits n * g.state n =
      g.prefixCoefficient n * g.state 0 + g.prefixGain n := by
  have hfold := ChargeBouncerPeriodicNoGo.prefix_balance g.coefficient
    (fun t => 2 ^ g.stepBits t) g.gain g.state n
    (fun i _ => g.balance i)
  rw [g.prefixDenominator_eq_pow n] at hfold
  exact hfold

theorem prefix_accepts (g : DependentDyadicAffineRay) (n : ℕ) :
    2 ^ g.prefixBits n ∣
      g.prefixCoefficient n * g.state 0 + g.prefixGain n := by
  refine ⟨g.state n, ?_⟩
  exact (g.prefix_balance n).symm

end DependentDyadicAffineRay

/-! ## The endogenous phase-up policy -/

/-- Arithmetic tail ray for the canonical public policy
`U(m)=(m,392,m+4)`, with `m=r0+4t`.  The correction `kappa` remains the
policy-specific canonical-cofactor term. -/
structure PhaseUpTailRay where
  initialPhase : ℕ
  tail : ℕ → ℕ
  tail_pos : ∀ t, 0 < tail t
  kappa : ℕ → ℕ
  balance : ∀ t,
    2 ^ ChargeResonantConjugacy.binaryExponent 392
          (initialPhase + 4 * (t + 1)) * tail (t + 1) =
      3 ^ ChargeResonantConjugacy.ternaryExponent
          (initialPhase + 4 * t) 392 * tail t + kappa t

namespace PhaseUpTailRay

def phase (g : PhaseUpTailRay) (t : ℕ) : ℕ :=
  g.initialPhase + 4 * t

def stepBits (g : PhaseUpTailRay) (t : ℕ) : ℕ :=
  ChargeResonantConjugacy.binaryExponent 392 (g.phase (t + 1))

def ternaryBits (g : PhaseUpTailRay) (t : ℕ) : ℕ :=
  ChargeResonantConjugacy.ternaryExponent (g.phase t) 392

def toDependentDyadicAffineRay (g : PhaseUpTailRay) :
    DependentDyadicAffineRay where
  state := g.tail
  state_pos := g.tail_pos
  stepBits := g.stepBits
  coefficient t := 3 ^ g.ternaryBits t
  gain := g.kappa
  balance t := by
    simpa [stepBits, ternaryBits, phase] using g.balance t

theorem stepBits_pos (g : PhaseUpTailRay) (t : ℕ) :
    0 < g.stepBits t := by
  simp [stepBits, phase, ChargeResonantConjugacy.binaryExponent]

theorem prefixBits_ge (g : PhaseUpTailRay) (n : ℕ) :
    n ≤ g.toDependentDyadicAffineRay.prefixBits n := by
  induction n with
  | zero => simp [DependentDyadicAffineRay.prefixBits, prefixSum]
  | succ n ih =>
      change n ≤ prefixSum g.stepBits n at ih
      change n + 1 ≤ prefixSum g.stepBits (n + 1)
      simp only [prefixSum]
      have hpos := g.stepBits_pos n
      omega

theorem prefixPrecision_diverges (g : PhaseUpTailRay) :
    DyadicPrecisionDiverges g.toDependentDyadicAffineRay.prefixBits := by
  intro B
  refine ⟨B, fun k hk => ?_⟩
  have hB : B < 2 ^ B := B.lt_two_pow_self
  have hBk : 2 ^ B ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hkprefix : 2 ^ k ≤
      2 ^ g.toDependentDyadicAffineRay.prefixBits k :=
    Nat.pow_le_pow_right (by omega) (g.prefixBits_ge k)
  exact hB.trans_le (hBk.trans hkprefix)

theorem prefixCoefficient_eq_threePow (g : PhaseUpTailRay) (n : ℕ) :
    g.toDependentDyadicAffineRay.prefixCoefficient n =
      3 ^ prefixSum g.ternaryBits n := by
  induction n with
  | zero => simp [DependentDyadicAffineRay.prefixCoefficient,
      prefixProduct, prefixSum]
  | succ n ih =>
      change prefixProduct (fun t => 3 ^ g.ternaryBits t) (n + 1) =
        3 ^ prefixSum g.ternaryBits (n + 1)
      simp only [prefixProduct, prefixSum]
      change prefixProduct (fun t => 3 ^ g.ternaryBits t) n =
        3 ^ prefixSum g.ternaryBits n at ih
      rw [ih, ← pow_add]

theorem prefixCoefficient_coprime (g : PhaseUpTailRay) (n : ℕ) :
    (g.toDependentDyadicAffineRay.prefixCoefficient n).Coprime
      (2 ^ g.toDependentDyadicAffineRay.prefixBits n) := by
  rw [g.prefixCoefficient_eq_threePow n]
  exact (by norm_num : Nat.Coprime 3 2).pow _ _

end PhaseUpTailRay

/-! ## Finite-prefix solvability is automatic -/

/-- Every affine congruence with invertible coefficient has one canonical
residue.  This elementary fact is why arbitrarily long successful finite
prefixes are not evidence for an ordinary infinite tail. -/
theorem exists_canonical_affine_residue (M coefficient gain : ℕ)
    (hM : 0 < M) (hcop : coefficient.Coprime M) :
    ∃ residue, residue < M ∧ M ∣ coefficient * residue + gain := by
  letI : NeZero M := ⟨hM.ne'⟩
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime coefficient hcop
  let z : ZMod M := -(↑(u⁻¹) : ZMod M) * (gain : ZMod M)
  refine ⟨z.val, z.val_lt, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff (coefficient * z.val + gain) M]
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp only [z]
  rw [← ZMod.coe_unitOfCoprime coefficient hcop]
  change (u : ZMod M) * (-(↑(u⁻¹) : ZMod M) * (gain : ZMod M)) +
    (gain : ZMod M) = 0
  calc
    (u : ZMod M) * (-(↑(u⁻¹) : ZMod M) * (gain : ZMod M)) +
        (gain : ZMod M) =
      -((u : ZMod M) * (↑(u⁻¹) : ZMod M)) * (gain : ZMod M) +
        (gain : ZMod M) := by ring
    _ = 0 := by rw [Units.mul_inv]; ring

/-- Applied to a dependent dyadic affine schedule: if the accumulated odd
coefficient is coprime to the dyadic denominator, every finite depth has a
canonical accepted starting residue, independently of whether one ordinary
natural realizes all depths. -/
theorem DependentDyadicAffineRay.exists_prefix_residue
    (g : DependentDyadicAffineRay)
    (hcop : ∀ n, (g.prefixCoefficient n).Coprime (2 ^ g.prefixBits n))
    (n : ℕ) :
    ∃ residue, residue < 2 ^ g.prefixBits n ∧
      2 ^ g.prefixBits n ∣
        g.prefixCoefficient n * residue + g.prefixGain n := by
  exact exists_canonical_affine_residue _ _ _ (by positivity) (hcop n)

/-- Proof-carrying canonical solutions of the affine congruences accumulated
by finite prefixes of a dependent tail policy. -/
structure DyadicAffinePrefixSystem where
  bits : ℕ → ℕ
  coefficient : ℕ → ℕ
  gain : ℕ → ℕ
  residue : ℕ → ℕ
  precision_diverges : DyadicPrecisionDiverges bits
  residue_canonical : ∀ k, residue k < 2 ^ bits k
  coefficient_coprime : ∀ k, (coefficient k).Coprime (2 ^ bits k)
  residue_accepts : ∀ k,
    2 ^ bits k ∣ coefficient k * residue k + gain k

namespace DependentDyadicAffineRay

/-- Package canonical prefix residues for a dependent ray.  The residue data
are the only policy-specific arithmetic left after the generic affine fold. -/
def toPrefixSystem (g : DependentDyadicAffineRay) (residue : ℕ → ℕ)
    (hprecision : DyadicPrecisionDiverges g.prefixBits)
    (hcanonical : ∀ n, residue n < 2 ^ g.prefixBits n)
    (hcoprime : ∀ n,
      (g.prefixCoefficient n).Coprime (2 ^ g.prefixBits n))
    (hresidue : ∀ n, 2 ^ g.prefixBits n ∣
      g.prefixCoefficient n * residue n + g.prefixGain n) :
    DyadicAffinePrefixSystem where
  bits := g.prefixBits
  coefficient := g.prefixCoefficient
  gain := g.prefixGain
  residue := residue
  precision_diverges := hprecision
  residue_canonical := hcanonical
  coefficient_coprime := hcoprime
  residue_accepts := hresidue

end DependentDyadicAffineRay

namespace DyadicAffinePrefixSystem

/-- One initial natural tail passes every accumulated affine integrality
condition.  In a concrete opcode ray this follows from the finite affine fold
and its endpoint integer. -/
def Accepts (S : DyadicAffinePrefixSystem) (initial : ℕ) : Prop :=
  ∀ k, 2 ^ S.bits k ∣ S.coefficient k * initial + S.gain k

/-- Coprimality makes the canonical prefix address unique: every accepted
ordinary initial tail has exactly the prescribed low bits. -/
theorem mod_eq_residue (S : DyadicAffinePrefixSystem) {initial : ℕ}
    (haccepts : S.Accepts initial) (k : ℕ) :
    initial % (2 ^ S.bits k) = S.residue k := by
  let M := 2 ^ S.bits k
  have hx0 : S.coefficient k * initial + S.gain k ≡ 0 [MOD M] :=
    Nat.modEq_zero_iff_dvd.mpr (haccepts k)
  have hr0 : S.coefficient k * S.residue k + S.gain k ≡ 0 [MOD M] :=
    Nat.modEq_zero_iff_dvd.mpr (S.residue_accepts k)
  have hsum : S.coefficient k * initial + S.gain k ≡
      S.coefficient k * S.residue k + S.gain k [MOD M] :=
    hx0.trans hr0.symm
  have hmul : S.coefficient k * initial ≡
      S.coefficient k * S.residue k [MOD M] :=
    Nat.ModEq.rfl.add_right_cancel hsum
  have hcancel : initial ≡ S.residue k [MOD M] :=
    Nat.ModEq.cancel_left_of_coprime
      (S.coefficient_coprime k).symm.gcd_eq_one hmul
  change initial % M = S.residue k % M at hcancel
  simpa [M, Nat.mod_eq_of_lt (S.residue_canonical k)] using hcancel

theorem realizesDyadicResidues (S : DyadicAffinePrefixSystem) {initial : ℕ}
    (haccepts : S.Accepts initial) :
    RealizesDyadicResidues S.bits S.residue initial :=
  fun k => S.mod_eq_residue haccepts k

/-- Necessary ordinary-tail condition: accepted prefix addresses eventually
equal the initial natural literally. -/
theorem residue_eventually_eq_initial (S : DyadicAffinePrefixSystem)
    {initial : ℕ} (haccepts : S.Accepts initial) :
    ∃ K, ∀ k, K ≤ k → S.residue k = initial :=
  realizesDyadicResidues_eventually_constant S.precision_diverges
    (S.realizesDyadicResidues haccepts)

/-- If nested canonical addresses are written by extension lifts, an ordinary
accepted tail forces those lifts eventually to be zero. -/
theorem extensionLifts_eventually_zero (S : DyadicAffinePrefixSystem)
    (lift : ℕ → ℕ)
    (hstep : ∀ k, S.residue (k + 1) =
      S.residue k + 2 ^ S.bits k * lift k)
    {initial : ℕ} (haccepts : S.Accepts initial) :
    ∃ K, ∀ k, K ≤ k → lift k = 0 := by
  obtain ⟨K, hstable⟩ := S.residue_eventually_eq_initial haccepts
  refine ⟨K, fun k hk => ?_⟩
  have heq := hstep k
  rw [hstable k hk, hstable (k + 1) (by omega)] at heq
  have hpow : 0 < 2 ^ S.bits k := Nat.pow_pos (by omega)
  have hprod : 2 ^ S.bits k * lift k = 0 := by omega
  exact (Nat.mul_eq_zero.mp hprod).resolve_left hpow.ne'

/-- Operational adversarial criterion for the phase-up policy: proving
arbitrarily late nonzero canonical extension lifts rules out every ordinary
initial tail, even though every finite prefix may be inhabited. -/
theorem no_accepts_of_frequently_nonzero_extensionLifts
    (S : DyadicAffinePrefixSystem) (lift : ℕ → ℕ)
    (hstep : ∀ k, S.residue (k + 1) =
      S.residue k + 2 ^ S.bits k * lift k)
    (hfrequent : ∀ K, ∃ k, K ≤ k ∧ lift k ≠ 0) :
    ¬ ∃ initial, S.Accepts initial := by
  rintro ⟨initial, haccepts⟩
  obtain ⟨K, hzero⟩ := S.extensionLifts_eventually_zero lift hstep haccepts
  obtain ⟨k, hk, hne⟩ := hfrequent K
  exact hne (hzero k hk)

end DyadicAffinePrefixSystem
end KontoroC

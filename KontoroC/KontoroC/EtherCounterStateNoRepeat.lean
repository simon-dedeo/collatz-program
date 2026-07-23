/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.EtherCounterResidueBound

/-!
# Positive EC17 states never repeat

Every positive EC17 transition has a positive additive defect.  Composing
transitions around a hypothetical repeated public state gives a strict
coefficient inequality in one direction, while the elementary comparison
`2^(8n+15) < 3^(6n+11)` gives the opposite inequality.  Consequently an
infinite orbit must escape every finite box in `(branch, core)` space.
-/

namespace KontoroC
namespace EtherCounterStateNoRepeat

structure Orbit where
  branch : ℕ → ℕ
  branch_pos : ∀ t, 0 < branch t
  core : ℕ → ℕ
  core_pos : ∀ t, 0 < core t
  balance : ∀ t,
    2 ^ (8 * branch (t + 1) + 15) * core (t + 1) =
      3 ^ (6 * branch t + 11) * core t + 17

namespace Orbit

/-- Restrict a literal infinite positive EC17 orbit to its first `length`
steps.  This is the exact bridge from infinite schedules to the finite
residue-certificate interface. -/
def toNaturalPrefix (g : Orbit) (length : ℕ) :
    EtherCounterResidueBound.NaturalPrefix g.branch length where
  branch_pos t _ := g.branch_pos t
  core := g.core
  core_pos t _ := g.core_pos t
  balance t _ := by
    simpa [EtherCounterResidueBound.binaryExponent,
      EtherCounterResidueBound.ternaryExponent] using g.balance t

theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ n := pow_pos (by omega) n
      omega

/-- QM63: unbounded exact residue obstructions exclude a natural infinite
orbit on the prescribed branch schedule.  The premise is deliberately
abstract: each finite row may be discharged by any exact checker.

This theorem does **not** say that every schedule has such certificates.  It
says that, for one fixed literal orbit, certificate failures at cofinally
large precisions would force its one fixed initial core above arbitrarily
large powers of two. -/
theorem false_of_unbounded_residue_obstructions
    (g : Orbit) (length precision : ℕ → ℕ)
    (hprecision : ∀ j,
      precision j ≤ EtherCounterResidueBound.binaryMass
        g.branch 0 (length j))
    (hunbounded : ∀ B, ∃ j, B < precision j)
    (hfail : ∀ j
      (pref : EtherCounterResidueBound.NaturalPrefix
        g.branch (length j)),
      pref.core 0 ≠
        (EtherCounterResidueBound.initialResidue
          g.branch (precision j) (length j)).val) :
    False := by
  obtain ⟨j, hj⟩ := hunbounded (g.core 0)
  let pref := g.toNaturalPrefix (length j)
  have hlower : 2 ^ precision j ≤ g.core 0 := by
    simpa [pref, toNaturalPrefix] using
      EtherCounterResidueBound.initial_core_ge_modulus_of_least_residue_fails
        (branch := g.branch) (length := length j)
        (P := precision j) (hprecision j) (hfail j) pref
  have hupper : g.core 0 < 2 ^ precision j :=
    lt_of_lt_of_le hj (self_le_two_pow (precision j))
  exact (Nat.not_lt_of_ge hlower) hupper

def binaryFactor (g : Orbit) (t : ℕ) : ℕ :=
  2 ^ (8 * g.branch (t + 1) + 15)

def ternaryFactor (g : Orbit) (t : ℕ) : ℕ :=
  3 ^ (6 * g.branch t + 11)

def binaryProduct (g : Orbit) (start length : ℕ) : ℕ :=
  ∏ i ∈ Finset.range length, g.binaryFactor (start + i)

def ternaryProduct (g : Orbit) (start length : ℕ) : ℕ :=
  ∏ i ∈ Finset.range length, g.ternaryFactor (start + i)

def targetTernaryProduct (g : Orbit) (start length : ℕ) : ℕ :=
  ∏ i ∈ Finset.range length,
    3 ^ (6 * g.branch (start + i + 1) + 11)

theorem factor_step_strict (g : Orbit) (t : ℕ) :
    g.ternaryFactor t * g.core t <
      g.binaryFactor t * g.core (t + 1) := by
  rw [binaryFactor, ternaryFactor, g.balance t]
  omega

/-- The elementary coefficient inequality attached to every positive
one-based branch. -/
theorem binary_lt_ternary_at_branch (n : ℕ) :
    2 ^ (8 * n + 15) < 3 ^ (6 * n + 11) := by
  rw [show 8 * n + 15 = 15 + 8 * n by omega,
    show 6 * n + 11 = 11 + 6 * n by omega, pow_add, pow_add, pow_mul, pow_mul]
  exact Nat.mul_lt_mul_of_lt_of_le (by norm_num)
    (Nat.pow_le_pow_left (by norm_num) n) (by positivity)

theorem binaryProduct_lt_targetTernaryProduct (g : Orbit)
    (start length : ℕ) (hlength : 0 < length) :
    g.binaryProduct start length < g.targetTernaryProduct start length := by
  apply Finset.prod_lt_prod_of_nonempty
  · intro i _
    simp [binaryFactor]
  · intro i _
    exact binary_lt_ternary_at_branch (g.branch (start + i + 1))
  · exact Finset.nonempty_range_iff.mpr hlength.ne'

private theorem shifted_product_mul_start (f : ℕ → ℕ)
    (start length : ℕ) :
    (∏ i ∈ Finset.range length, f (start + i + 1)) * f start =
      (∏ i ∈ Finset.range length, f (start + i)) * f (start + length) := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        (∏ x ∈ Finset.range length, f (start + x + 1)) *
              f (start + length + 1) * f start =
            ((∏ x ∈ Finset.range length, f (start + x + 1)) * f start) *
              f (start + length + 1) := by ring
        _ = ((∏ x ∈ Finset.range length, f (start + x)) *
              f (start + length)) * f (start + length + 1) := by rw [ih]
        _ = (∏ x ∈ Finset.range length, f (start + x)) * f (start + length) *
              f (start + (length + 1)) := by
          congr 1

theorem binaryProduct_succ (g : Orbit) (start length : ℕ) :
    g.binaryProduct start (length + 1) =
      g.binaryProduct start length * g.binaryFactor (start + length) := by
  rw [binaryProduct, Finset.prod_range_succ]
  rfl

theorem ternaryProduct_succ (g : Orbit) (start length : ℕ) :
    g.ternaryProduct start (length + 1) =
      g.ternaryProduct start length * g.ternaryFactor (start + length) := by
  rw [ternaryProduct, Finset.prod_range_succ]
  rfl

theorem targetTernaryProduct_eq_ternaryProduct_of_endpoint
    (g : Orbit) (start length : ℕ)
    (hend : g.branch (start + length) = g.branch start) :
    g.targetTernaryProduct start length = g.ternaryProduct start length := by
  let f : ℕ → ℕ := fun t => 3 ^ (6 * g.branch t + 11)
  have hshift := shifted_product_mul_start f start length
  have hfend : f (start + length) = f start := by simp [f, hend]
  rw [hfend] at hshift
  apply Nat.mul_right_cancel (by positivity : 0 < f start)
  simpa [targetTernaryProduct, ternaryProduct, ternaryFactor, f,
    Nat.add_assoc] using hshift

/-- Multiplying the strict transition inequalities gives the strict
composed balance without having to expand the positive defect polynomial. -/
theorem composed_strict (g : Orbit) (start length : ℕ) (hlength : 0 < length) :
    g.ternaryProduct start length * g.core start <
      g.binaryProduct start length * g.core (start + length) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hlength.ne'
  induction n with
  | zero =>
      simpa [binaryProduct, ternaryProduct] using g.factor_step_strict start
  | succ n ih =>
      have ih' := ih (by omega)
      have hstep := g.factor_step_strict (start + (n + 1))
      have hleft := Nat.mul_lt_mul_of_pos_left ih'
        (by simp [ternaryFactor] : 0 < g.ternaryFactor (start + (n + 1)))
      have hright := Nat.mul_lt_mul_of_pos_left hstep
        (by simp [binaryProduct, binaryFactor] : 0 < g.binaryProduct start (n + 1))
      rw [g.binaryProduct_succ start (n + 1),
        g.ternaryProduct_succ start (n + 1)]
      calc
        (g.ternaryProduct start (n + 1) *
              g.ternaryFactor (start + (n + 1))) * g.core start =
            g.ternaryFactor (start + (n + 1)) *
              (g.ternaryProduct start (n + 1) * g.core start) := by ring
        _ < g.ternaryFactor (start + (n + 1)) *
              (g.binaryProduct start (n + 1) *
                g.core (start + (n + 1))) := hleft
        _ = g.binaryProduct start (n + 1) *
              (g.ternaryFactor (start + (n + 1)) *
                g.core (start + (n + 1))) := by ring
        _ < g.binaryProduct start (n + 1) *
              (g.binaryFactor (start + (n + 1)) *
                g.core (start + (n + 1) + 1)) := hright
        _ = (g.binaryProduct start (n + 1) *
              g.binaryFactor (start + (n + 1))) *
                g.core (start + (n + 1 + 1)) := by
          rw [show start + (n + 1) + 1 = start + (n + 1 + 1) by omega]
          ring

/-- QM60: a positive EC17 orbit never revisits one public `(branch, core)`
state after a nonempty number of steps. -/
theorem state_ne_after (g : Orbit) (start length : ℕ) (hlength : 0 < length) :
    (g.branch (start + length), g.core (start + length)) ≠
      (g.branch start, g.core start) := by
  intro hstate
  have hbranch : g.branch (start + length) = g.branch start :=
    congrArg Prod.fst hstate
  have hcore : g.core (start + length) = g.core start :=
    congrArg Prod.snd hstate
  have hcoeff := g.binaryProduct_lt_targetTernaryProduct start length hlength
  rw [g.targetTernaryProduct_eq_ternaryProduct_of_endpoint
    start length hbranch] at hcoeff
  have hforward := g.composed_strict start length hlength
  rw [hcore] at hforward
  have hreverse := Nat.mul_lt_mul_of_pos_right hcoeff (g.core_pos start)
  exact lt_asymm hforward hreverse

theorem state_injective (g : Orbit) :
    Function.Injective (fun t => (g.branch t, g.core t)) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have h := g.state_ne_after i (j - i) (Nat.sub_pos_of_lt hijlt)
    rw [Nat.add_sub_of_le hijlt.le] at h
    exact h hij.symm
  · have h := g.state_ne_after j (i - j) (Nat.sub_pos_of_lt hjilt)
    rw [Nat.add_sub_of_le hjilt.le] at h
    exact h hij

/-- QM61: every finite public state box is eventually escaped.  The theorem
does not decide which register supplies the unbounded resource. -/
theorem unbounded_public_resource (g : Orbit) (B : ℕ) :
    ∃ t, B < g.branch t ∨ B < g.core t := by
  by_contra hbounded
  have hbranch : ∀ t, g.branch t ≤ B := by
    intro t
    exact le_of_not_gt (fun h => hbounded ⟨t, Or.inl h⟩)
  have hcore : ∀ t, g.core t ≤ B := by
    intro t
    exact le_of_not_gt (fun h => hbounded ⟨t, Or.inr h⟩)
  let f : ℕ → Fin (B + 1) × Fin (B + 1) := fun t =>
    (⟨g.branch t, Nat.lt_succ_of_le (hbranch t)⟩,
      ⟨g.core t, Nat.lt_succ_of_le (hcore t)⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply g.state_injective
    apply Prod.ext
    · exact congrArg (fun z => z.1.val) hij
    · exact congrArg (fun z => z.2.val) hij
  have hinfinite : Infinite (Fin (B + 1) × Fin (B + 1)) :=
    Infinite.of_injective f hf
  exact Infinite.false hinfinite

end Orbit
end EtherCounterStateNoRepeat
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.AnnealedTrace
import CleanLean.KL.NonlinearPerron
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Transport irreducibility and uniqueness at the annealed endpoint

The affine transport `s ↦ 4s+2` is conjugate, in the paper residue
`m=2+3s`, to multiplication by four modulo `3^k`.  Mathlib's exact order
theorem for `1+3` therefore makes every transport orbit a single cycle.

The positive transport coefficient then gives an elementary Perron
uniqueness argument: a tight projective domination propagates along the
entire transport cycle.  No finite-matrix encoding is introduced.
-/

namespace CleanLean.KL

namespace ResidueSystem

open scoped BigOperators

noncomputable section

/-- The paper residue `m=2+3s`, now regarded modulo `3^k`. -/
def paperResidue (k : ℕ) (s : State k) : ZMod (3 ^ k) :=
  (2 + 3 * s.val : ℕ)

private theorem paperResidue_nat_lt (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    2 + 3 * s.val < 3 ^ k := by
  have hs := ZMod.val_lt s
  have hpow := three_pow_level (k + 1) (by omega)
  have hleft : k + 1 - 1 = k := by omega
  have hright : k + 1 - 2 = k - 1 := by omega
  rw [hleft, hright] at hpow
  omega

/-- The paper coordinate is injective on the state space. -/
theorem paperResidue_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (paperResidue k) := by
  intro s t hst
  have hval := congrArg ZMod.val hst
  simp only [paperResidue] at hval
  rw [ZMod.val_natCast_of_lt (paperResidue_nat_lt k hk s),
    ZMod.val_natCast_of_lt (paperResidue_nat_lt k hk t)] at hval
  apply ZMod.val_injective
  omega

/-- The paper residue is a unit modulo `3^k`, since it is two modulo three. -/
theorem paperResidue_isUnit (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    IsUnit (paperResidue k s) := by
  rw [paperResidue,
    ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_three hk]
  intro hdiv
  have hmod := Nat.dvd_iff_mod_eq_zero.mp hdiv
  omega

/-- Transport in affine coordinates is multiplication by four in the paper
coordinate. -/
theorem paperResidue_transport (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    paperResidue k (transport k s) = 4 * paperResidue k s := by
  calc
    paperResidue k (transport k s) =
        ((2 + 3 * (transport k s).val : ℕ) : ZMod (3 ^ k)) := rfl
    _ = ((4 * (2 + 3 * s.val) : ℕ) : ZMod (3 ^ k)) :=
      (ZMod.natCast_eq_natCast_iff _ _ (3 ^ k)).2
        (transport_residue_modEq k hk s)
    _ = 4 * paperResidue k s := by simp [paperResidue]

/-- The paper coordinate of an iterated transport. -/
theorem paperResidue_transport_iterate (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (s : State k) :
    paperResidue k ((transport k)^[n] s) =
      (4 : ZMod (3 ^ k)) ^ n * paperResidue k s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', paperResidue_transport k hk, ih,
        pow_succ']
      ring

/-- Exact multiplicative order of four in the paper modulus. -/
theorem orderOf_four_paper (k : ℕ) (hk : 1 ≤ k) :
    orderOf (4 : ZMod (3 ^ k)) = 3 ^ (k - 1) := by
  have h :=
    ZMod.orderOf_one_add_prime Nat.prime_three (by norm_num : 3 ≠ 2) (k - 1)
  rw [Nat.sub_add_cancel hk] at h
  norm_num at h
  exact h

/-- The orbit map from a chosen state, indexed by the full state-space
cardinality. -/
def transportOrbitFrom (k : ℕ) (s : State k) :
    Fin (3 ^ (k - 1)) → State k :=
  fun n => (transport k)^[n.val] s

/-- Distinct times below the state-space cardinality give distinct transport
states. -/
theorem transportOrbitFrom_injective (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    Function.Injective (transportOrbitFrom k s) := by
  intro i j hij
  have hpaper := congrArg (paperResidue k) hij
  simp only [transportOrbitFrom] at hpaper
  rw [paperResidue_transport_iterate k hk,
    paperResidue_transport_iterate k hk] at hpaper
  have hpows :
      (4 : ZMod (3 ^ k)) ^ i.val = (4 : ZMod (3 ^ k)) ^ j.val :=
    (paperResidue_isUnit k hk s).mul_right_cancel hpaper
  have horder := orderOf_four_paper k hk
  have hfinite : IsOfFinOrder (4 : ZMod (3 ^ k)) := by
    rw [← orderOf_pos_iff, horder]
    positivity
  have hmod := hfinite.pow_eq_pow_iff_modEq.mp hpows
  rw [horder] at hmod
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt

/-- Every transport orbit is the full state space. -/
def transportOrbitEquiv (k : ℕ) (hk : 1 ≤ k) (s : State k) :
    Fin (3 ^ (k - 1)) ≃ State k :=
  Equiv.ofBijective (transportOrbitFrom k s)
    ((Fintype.bijective_iff_injective_and_card (transportOrbitFrom k s)).2
      ⟨transportOrbitFrom_injective k hk s, by simp⟩)

/-- Every state is reached from every other state by fewer than
`3^(k-1)` transport steps. -/
theorem exists_transport_iterate_eq (k : ℕ) (hk : 1 ≤ k)
    (s t : State k) :
    ∃ n : Fin (3 ^ (k - 1)), (transport k)^[n.val] s = t := by
  exact (transportOrbitEquiv k hk s).surjective t

end

end ResidueSystem

namespace FiniteSystem

noncomputable section

variable (S : FiniteSystem)

/-- A nonnegative vector has nonnegative arithmetic mean on every fiber. -/
theorem fiberAverage_nonneg (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q)
    (r : S.Coarse) :
    0 ≤ S.fiberAverage c r := by
  simp only [fiberAverage]
  apply div_nonneg
  · exact add_nonneg (add_nonneg (hc _) (hc _)) (hc _)
  · norm_num

/-- The annealed operator preserves the nonnegative cone when all weights are
nonnegative. -/
theorem annealedOperator_nonneg (w : Weights ℝ)
    (hwt : 0 ≤ w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced) (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) :
    ∀ q, 0 ≤ S.annealedOperator w c q := by
  intro q
  have ht : 0 ≤ w.transport * c (S.transport q) :=
    mul_nonneg hwt (hc _)
  have hf : 0 ≤ S.fiberAverage c (S.refinementTarget q) :=
    S.fiberAverage_nonneg c hc _
  cases hb : S.branch q with
  | retarded =>
      simpa [annealedOperator, hb] using add_nonneg ht (mul_nonneg hwr hf)
  | neutral => simpa [annealedOperator, hb] using ht
  | advanced =>
      simpa [annealedOperator, hb] using add_nonneg ht (mul_nonneg hwa hf)

/-- The positive transport summand is bounded by the full annealed image when
the branch weights and vector are nonnegative. -/
theorem transport_term_le_annealedOperator (w : Weights ℝ)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) (q : S.State) :
    w.transport * c (S.transport q) ≤ S.annealedOperator w c q := by
  have hf : 0 ≤ S.fiberAverage c (S.refinementTarget q) :=
    S.fiberAverage_nonneg c hc _
  cases hb : S.branch q with
  | retarded =>
      simp only [annealedOperator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hwr hf)
  | neutral => simp [annealedOperator, hb]
  | advanced =>
      simp only [annealedOperator, hb]
      exact le_add_of_nonneg_right (mul_nonneg hwa hf)

/-- If a nonnegative annealed image vanishes at one coordinate, then the
source at its positive-weight transport predecessor vanishes. -/
theorem transport_eq_zero_of_annealedOperator_eq_zero
    (w : Weights ℝ) (hwt : 0 < w.transport)
    (hwr : 0 ≤ w.retarded) (hwa : 0 ≤ w.advanced)
    (c : S.State → ℝ) (hc : ∀ q, 0 ≤ c q) (q : S.State)
    (hzero : S.annealedOperator w c q = 0) :
    c (S.transport q) = 0 := by
  have ht : 0 ≤ w.transport * c (S.transport q) :=
    mul_nonneg hwt.le (hc _)
  have hf : 0 ≤ S.fiberAverage c (S.refinementTarget q) :=
    S.fiberAverage_nonneg c hc _
  have htzero : w.transport * c (S.transport q) = 0 := by
    cases hb : S.branch q with
    | retarded =>
        have hbranch :
            0 ≤ w.retarded * S.fiberAverage c (S.refinementTarget q) :=
          mul_nonneg hwr hf
        rw [annealedOperator, hb] at hzero
        linarith
    | neutral => simpa [annealedOperator, hb] using hzero
    | advanced =>
        have hbranch :
            0 ≤ w.advanced * S.fiberAverage c (S.refinementTarget q) :=
          mul_nonneg hwa hf
        rw [annealedOperator, hb] at hzero
        linarith
  exact (mul_eq_zero.mp htzero).resolve_left hwt.ne'

end


end FiniteSystem

namespace ResidueSystem

open scoped BigOperators

noncomputable section

/-- The concrete residue operator with its state type exposed, avoiding
dependent-projection opacity in downstream linear calculations. -/
def residueAnnealedOperator (k : ℕ) (w : Weights ℝ)
    (c : State k → ℝ) : State k → ℝ :=
  (system k).annealedOperator w c

/-- Concrete-state wrapper around linear additivity of the annealed operator. -/
theorem annealedOperator_add_residue (k : ℕ) (w : Weights ℝ)
    (c d : State k → ℝ) :
    residueAnnealedOperator k w (c + d) =
      residueAnnealedOperator k w c + residueAnnealedOperator k w d :=
  (system k).annealedOperator_add w c d

/-- Concrete-state wrapper around real homogeneity of the annealed operator. -/
theorem annealedOperator_smul_residue (k : ℕ) (w : Weights ℝ)
    (a : ℝ) (c : State k → ℝ) :
    residueAnnealedOperator k w (a • c) =
      a • residueAnnealedOperator k w c :=
  (system k).annealedOperator_smul w a c

/-- Every nonzero nonnegative annealed fixed vector is strictly positive.
Positivity propagates backward through the positive transport summand, and
the transport permutation is one full cycle. -/
theorem annealed_fixedVector_pos_of_nonnegative_nonzero
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced)
    {c : State k → ℝ} (hc : ∀ q, 0 ≤ c q) (hcne : c ≠ 0)
    (hfixed : (system k).annealedOperator w c = c) :
    ∀ q, 0 < c q := by
  have hexists : ∃ s, 0 < c s := by
    by_contra hnot
    push Not at hnot
    apply hcne
    funext s
    exact le_antisymm (hnot s) (hc s)
  obtain ⟨s, hs⟩ := hexists
  have hback (q : State k) (hq : 0 < c (transport k q)) : 0 < c q := by
    have htransport : 0 < w.transport * c (transport k q) :=
      mul_pos hwt hq
    have hle := (system k).transport_term_le_annealedOperator
      w hwr hwa c hc q
    rw [congrFun hfixed q] at hle
    exact htransport.trans_le hle
  intro q
  obtain ⟨n, hn⟩ := exists_transport_iterate_eq k hk q s
  have hiterate : ∀ m : ℕ,
      0 < c ((transport k)^[m] q) → 0 < c q := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        apply ih
        apply hback
        simpa [Function.iterate_succ_apply'] using hm
  apply hiterate n.val
  simpa [hn] using hs

/-- A strictly positive normalized annealed fixed vector is unique.  The proof
uses only positivity of the transport coefficient, nonnegativity of the two
branch coefficients, and the full transport cycle. -/
theorem annealed_fixedVector_unique
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced)
    {x y : State k → ℝ}
    (hxpos : ∀ q, 0 < x q) (hypos : ∀ q, 0 < y q)
    (hxfixed : (system k).annealedOperator w x = x)
    (hyfixed : (system k).annealedOperator w y = y)
    (hxmass : (system k).totalMass x = 1)
    (hymass : (system k).totalMass y = 1) :
    x = y := by
  obtain ⟨a, ha0, i, hdom, htight⟩ :=
    exists_tight_domination x y hxpos (fun q => (hypos q).le)
  have hapos : 0 < a := by
    have hyi := hypos i
    rw [htight] at hyi
    exact pos_of_mul_pos_left hyi (hxpos i).le
  let d : State k → ℝ := a • x + (-1 : ℝ) • y
  have hdnonneg : ∀ q, 0 ≤ d q := by
    intro q
    simp only [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hdom q]
  have hd_at_i : d i = 0 := by
    simp only [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [htight]
    ring
  have hxfixed' : residueAnnealedOperator k w x = x := hxfixed
  have hyfixed' : residueAnnealedOperator k w y = y := hyfixed
  have hdfixed : residueAnnealedOperator k w d = d := by
    calc
      residueAnnealedOperator k w d =
          residueAnnealedOperator k w (a • x + (-1 : ℝ) • y) := rfl
      _ = residueAnnealedOperator k w (a • x) +
          residueAnnealedOperator k w ((-1 : ℝ) • y) :=
        annealedOperator_add_residue k w (a • x) ((-1 : ℝ) • y)
      _ = a • residueAnnealedOperator k w x +
          (-1 : ℝ) • residueAnnealedOperator k w y := by
        exact congrArg₂ (· + ·)
          (annealedOperator_smul_residue k w a x)
          (annealedOperator_smul_residue k w (-1) y)
      _ = a • x + (-1 : ℝ) • y := by
        exact congrArg₂ (fun u v : State k → ℝ => u + v)
          (congrArg (fun z : State k → ℝ => a • z) hxfixed')
          (congrArg (fun z : State k → ℝ => (-1 : ℝ) • z) hyfixed')
      _ = d := by rfl
  have hpropagate (q : State k) (hq : d q = 0) :
      d (transport k q) = 0 := by
    apply (system k).transport_eq_zero_of_annealedOperator_eq_zero
      w hwt hwr hwa d hdnonneg q
    change residueAnnealedOperator k w d q = 0
    rw [congrFun hdfixed q, hq]
  have hiterate : ∀ n : ℕ, d ((transport k)^[n] i) = 0 := by
    intro n
    induction n with
    | zero => simpa using hd_at_i
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hpropagate _ ih
  have hdall : ∀ q, d q = 0 := by
    intro q
    obtain ⟨n, hn⟩ := exists_transport_iterate_eq k hk i q
    rw [← hn]
    exact hiterate n.val
  have hscale : y = a • x := by
    funext q
    have hq := hdall q
    simp only [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hq
    change y q = a * x q
    linarith
  have haone : a = 1 := by
    rw [hscale] at hymass
    change (∑ q : State k, a * x q) = 1 at hymass
    rw [← Finset.mul_sum] at hymass
    change (∑ q : State k, x q) = 1 at hxmass
    rw [hxmass] at hymass
    simpa using hymass
  rw [hscale, haone, one_smul]

/-- The preferred Perron interface: normalized nonnegative annealed fixed
vectors are unique.  Normalization makes them nonzero, and the full transport
cycle first upgrades them to strict positivity. -/
theorem annealed_fixedVector_unique_nonnegative
    (k : ℕ) (hk : 1 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced)
    {x y : State k → ℝ}
    (hx : ∀ q, 0 ≤ x q) (hy : ∀ q, 0 ≤ y q)
    (hxfixed : (system k).annealedOperator w x = x)
    (hyfixed : (system k).annealedOperator w y = y)
    (hxmass : (system k).totalMass x = 1)
    (hymass : (system k).totalMass y = 1) :
    x = y := by
  have hxne : x ≠ 0 := by
    intro hxzero
    change (∑ q : State k, x q) = 1 at hxmass
    rw [hxzero] at hxmass
    simp at hxmass
  have hyne : y ≠ 0 := by
    intro hyzero
    change (∑ q : State k, y q) = 1 at hymass
    rw [hyzero] at hymass
    simp at hymass
  apply annealed_fixedVector_unique k hk w hwt hwr hwa
  · exact annealed_fixedVector_pos_of_nonnegative_nonzero
      k hk w hwt hwr hwa hx hxne hxfixed
  · exact annealed_fixedVector_pos_of_nonnegative_nonzero
      k hk w hwt hwr hwa hy hyne hyfixed
  · exact hxfixed
  · exact hyfixed
  · exact hxmass
  · exact hymass

/-- Trace compatibility plus transport irreducibility identifies the trace of
a positive normalized fine fixed vector with the positive normalized coarse
fixed vector. -/
theorem oneStepTrace_fixedVector_eq
    (k : ℕ) (hk : 2 ≤ k) (w : Weights ℝ)
    (hwt : 0 < w.transport) (hwr : 0 ≤ w.retarded)
    (hwa : 0 ≤ w.advanced)
    {fine : State (k + 1) → ℝ} {coarse : State k → ℝ}
    (hfinePos : ∀ q, 0 < fine q) (hcoarsePos : ∀ q, 0 < coarse q)
    (hfineFixed : (system (k + 1)).annealedOperator w fine = fine)
    (hcoarseFixed : (system k).annealedOperator w coarse = coarse)
    (hfineMass : (system (k + 1)).totalMass fine = 1)
    (hcoarseMass : (system k).totalMass coarse = 1) :
    oneStepTrace k fine = coarse := by
  apply annealed_fixedVector_unique k (by omega) w hwt hwr hwa
  · intro q
    simp only [oneStepTrace, Fin.sum_univ_three]
    have h0 := hfinePos (fiber (k + 1) q 0)
    have h1 := hfinePos (fiber (k + 1) q 1)
    have h2 := hfinePos (fiber (k + 1) q 2)
    positivity
  · exact hcoarsePos
  · rw [← oneStepTrace_annealedOperator k hk w fine, hfineFixed]
  · exact hcoarseFixed
  · rw [totalMass_oneStepTrace k hk fine, hfineMass]
  · exact hcoarseMass

end

end ResidueSystem

end CleanLean.KL

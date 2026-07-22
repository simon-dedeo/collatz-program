/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePublicCofactor

/-!
# The public-cofactor chart has a one-sided interface tax

This file rewrites the exact public recurrence in source and target charts.
It then proves a generic finite-word identity: every internal chart change
contributes a strictly negative rational term.  Consequently no word of two
or more bare public steps is a zero-tax adapter.  This is an obstruction to
one proposed closure architecture, not a no-orbit theorem.
-/

namespace KontoroC
namespace ChargeTypedInterface

open ChargePublicCofactor

/-- Source-chart origin. -/
def tau (m : ℕ) : ℚ := 1 / (publicC : ℚ) ^ m

/-- Target-chart origin. -/
def beta (m : ℕ) : ℚ := 1 / (publicD : ℚ) ^ m

/-- Change of origin paid at an internal boundary. -/
def delta (m : ℕ) : ℚ := tau m - beta m

/-- Linear coefficient of one public step in typed coordinates. -/
def coefficient (m h m' : ℕ) : ℚ :=
  (publicB : ℚ) ^ h * (publicD : ℚ) ^ m' /
    ((publicA : ℚ) ^ h * (publicC : ℚ) ^ m)

theorem coefficient_pos (m h m' : ℕ) : 0 < coefficient m h m' := by
  simp only [coefficient]
  norm_num [publicA, publicB, publicC, publicD]
  positivity

/-- TI1: PC4 is exactly a map from the source `tau` chart to the target
`beta` chart. -/
theorem Step.typed_interface (s : ChargePublicCofactor.Step) :
    (s.source.cofactor : ℚ) - tau s.source.opcode =
      coefficient s.source.opcode s.recharge s.target.opcode *
        ((s.target.cofactor : ℚ) - beta s.target.opcode) := by
  have hABbase : publicB ≤ publicA := by
    norm_num [publicA, publicB]
  have hAB : publicB ^ s.recharge ≤ publicA ^ s.recharge :=
    Nat.pow_le_pow_left hABbase s.recharge
  have hcastGap :
      ((publicA ^ s.recharge - publicB ^ s.recharge : ℕ) : ℚ) =
        (publicA : ℚ) ^ s.recharge - (publicB : ℚ) ^ s.recharge := by
    rw [Nat.cast_sub hAB]
    norm_num
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) s.cofactor_balance
  have h :
      (publicB : ℚ) ^ s.recharge *
            ((publicD : ℚ) ^ s.target.opcode * s.target.cofactor) +
          ((publicA : ℚ) ^ s.recharge -
            (publicB : ℚ) ^ s.recharge) =
        (publicA : ℚ) ^ s.recharge *
          ((publicC : ℚ) ^ s.source.opcode * s.source.cofactor) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hcastGap] using hcast
  simp only [tau, beta, coefficient]
  have hA : (publicA : ℚ) ^ s.recharge ≠ 0 := by
    norm_num [publicA]
  have hC : (publicC : ℚ) ^ s.source.opcode ≠ 0 := by
    norm_num [publicC]
  have hD : (publicD : ℚ) ^ s.target.opcode ≠ 0 := by
    norm_num [publicD]
  field_simp
  nlinarith [h]

/-- Product of the first `n` typed coefficients. -/
def prefixCoefficient (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.range n, a i

/-- Sum of chart-change taxes at the internal boundaries of a length-`n`
word.  The endpoints `0` and `n` are deliberately absent. -/
def internalTax (a d : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ico 1 n, prefixCoefficient a j * d j

theorem prefixCoefficient_succ (a : ℕ → ℚ) (n : ℕ) :
    prefixCoefficient a (n + 1) = prefixCoefficient a n * a n := by
  simp [prefixCoefficient, Finset.prod_range_succ]

/-- TI2, as pure finite algebra.  It is stated with a bounded local-step
hypothesis, so it applies to a genuinely finite word rather than silently
assuming an infinite continuation. -/
theorem finite_typed_unroll (w tau' beta' a d : ℕ → ℚ) (N : ℕ)
    (hN : 0 < N) (hdelta : ∀ i, d i = tau' i - beta' i)
    (hstep : ∀ i, i < N →
      w i - tau' i = a i * (w (i + 1) - beta' (i + 1))) :
    w 0 - tau' 0 = internalTax a d N +
      prefixCoefficient a N * (w N - beta' N) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  induction n with
  | zero =>
      simpa [internalTax, prefixCoefficient] using hstep 0 (by omega)
  | succ n ih =>
      have hprev : ∀ i, i < n + 1 →
          w i - tau' i = a i * (w (i + 1) - beta' (i + 1)) := by
        intro i hi
        exact hstep i (by omega)
      have hi := ih (by omega) hprev
      have hlast := hstep (n + 1) (by omega)
      have hprefix : prefixCoefficient a (n + 2) =
          prefixCoefficient a (n + 1) * a (n + 1) := by
        simpa using prefixCoefficient_succ a (n + 1)
      simp only [Nat.succ_eq_add_one] at hi hlast ⊢
      rw [internalTax, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
        ← internalTax, hprefix]
      rw [hdelta (n + 1)]
      linear_combination hi +
        prefixCoefficient a (n + 1) * hlast

theorem prefixCoefficient_pos (a : ℕ → ℚ) (ha : ∀ i, 0 < a i)
    (n : ℕ) : 0 < prefixCoefficient a n := by
  exact Finset.prod_pos fun i _ => ha i

/-- A word with at least one internal boundary pays a strict negative tax. -/
theorem internalTax_neg (a d : ℕ → ℚ) (n : ℕ) (hn : 2 ≤ n)
    (ha : ∀ i, 0 < a i) (hd : ∀ i, d i < 0) :
    internalTax a d n < 0 := by
  apply Finset.sum_neg
  · intro i hi
    exact mul_neg_of_pos_of_neg (prefixCoefficient_pos a ha i) (hd i)
  · exact Finset.nonempty_Ico.mpr (by omega)

theorem publicD_lt_publicC : publicD < publicC := by
  norm_num [publicC, publicD]

theorem delta_neg {m : ℕ} (hm : 0 < m) : delta m < 0 := by
  have hp : publicD ^ m < publicC ^ m :=
    Nat.pow_lt_pow_left publicD_lt_publicC hm.ne'
  have hpq : (publicD : ℚ) ^ m < (publicC : ℚ) ^ m := by
    exact_mod_cast hp
  have hrecip := one_div_lt_one_div_of_lt
    (show 0 < (publicD : ℚ) ^ m by
      norm_num [publicD]) hpq
  simpa [delta, tau, beta] using sub_neg.mpr hrecip

/-- Exact bridge to the previously formalized opcode-debris semigroup.
`opcodeDebris m` is the integral quotient
`(C^m-D^m)/(C-D)`, so the interface tax is its negative normalization. -/
theorem delta_eq_normalized_opcodeDebris (m : ℕ) :
    delta m =
      -(((ChargeNormOpcode.registerOdd * ChargeNormOpcode.opcodeDebris m : ℤ) : ℚ)) /
        ((publicC : ℚ) ^ m * (publicD : ℚ) ^ m) := by
  have hf := congrArg (fun z : ℤ => (z : ℚ))
    (ChargeNormOpcode.opcodeDebris_factor m)
  have hC : ((ChargePowerQuine.C : ℤ) : ℚ) = (publicC : ℚ) := by
    norm_num [ChargePowerQuine.C, publicC]
  have hD : ((ChargePowerQuine.D : ℤ) : ℚ) = (publicD : ℚ) := by
    norm_num [ChargePowerQuine.D, publicD]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hf
  rw [hC, hD] at hf
  simp only [delta, tau, beta, Int.cast_mul]
  have hc : (publicC : ℚ) ^ m ≠ 0 := by norm_num [publicC]
  have hd : (publicD : ℚ) ^ m ≠ 0 := by norm_num [publicD]
  field_simp
  nlinarith [hf]

/-! ## The correction-rail equation -/

/-- TI3 is not an analogy: it is exactly equivalent to transporting a
shifted source potential to a shifted target potential. -/
theorem corrected_transport_iff
    (w w' tau₀ tau₁ beta₁ a e₀ e₁ : ℚ)
    (hstep : w - tau₀ = a * (w' - beta₁)) :
    w - (tau₀ + e₀) = a * (w' - (tau₁ + e₁)) ↔
      e₀ = a * (e₁ + (tau₁ - beta₁)) := by
  constructor <;> intro h
  · linear_combination hstep - h
  · linear_combination hstep - h

/-- TI3 specialized to one exact public step. -/
theorem Step.corrected_interface_iff (s : ChargePublicCofactor.Step)
    (e₀ e₁ : ℚ) :
    (s.source.cofactor : ℚ) - (tau s.source.opcode + e₀) =
        coefficient s.source.opcode s.recharge s.target.opcode *
          ((s.target.cofactor : ℚ) - (tau s.target.opcode + e₁)) ↔
      e₀ = coefficient s.source.opcode s.recharge s.target.opcode *
        (e₁ + delta s.target.opcode) := by
  exact corrected_transport_iff _ _ _ _ _ _ _ _
    (ChargeTypedInterface.Step.typed_interface s)

/-- A nonnegative correction before a positive-coefficient step forces the
next correction to cover at least the entire negative chart tax. -/
theorem correction_next_lower_bound {a d e₀ e₁ : ℚ}
    (ha : 0 < a) (he₀ : 0 ≤ e₀) (hrec : e₀ = a * (e₁ + d)) :
    -d ≤ e₁ := by
  have hmul : 0 ≤ a * (e₁ + d) := by rw [← hrec]; exact he₀
  have hadd : 0 ≤ e₁ + d := (mul_nonneg_iff_of_pos_left ha).mp hmul
  linarith

/-- In particular a correction rail normalized to zero at its target has a
strictly negative predecessor whenever the target opcode is positive. -/
theorem correction_before_zero_neg {a d e₀ : ℚ}
    (ha : 0 < a) (hd : d < 0) (hrec : e₀ = a * (0 + d)) : e₀ < 0 := by
  rw [hrec]
  exact mul_neg_of_pos_of_neg ha (by simpa using hd)

/-- If a backward coefficient is at most one, a nonnegative correction must
grow forward by at least the magnitude of the negative interface tax. -/
theorem correction_grows_by_tax {a d e₀ e₁ : ℚ}
    (ha : 0 < a) (ha₁ : a ≤ 1) (he₀ : 0 ≤ e₀)
    (hrec : e₀ = a * (e₁ + d)) : e₀ - d ≤ e₁ := by
  have hmul : 0 ≤ a * (e₁ + d) := by rw [← hrec]; exact he₀
  have hins : 0 ≤ e₁ + d := (mul_nonneg_iff_of_pos_left ha).mp hmul
  have hle : a * (e₁ + d) ≤ 1 * (e₁ + d) :=
    mul_le_mul_of_nonneg_right ha₁ hins
  rw [← hrec] at hle
  linarith

theorem correction_strictly_grows {a d e₀ e₁ : ℚ}
    (ha : 0 < a) (ha₁ : a ≤ 1) (hd : d < 0) (he₀ : 0 ≤ e₀)
    (hrec : e₀ = a * (e₁ + d)) : e₀ < e₁ := by
  have hgrow := correction_grows_by_tax ha ha₁ he₀ hrec
  linarith

/-- Uniformly negative taxes force at least linear growth of every
nonnegative correction rail.  Thus a bounded positive affine gauge cannot
hide a persistent interface mismatch. -/
theorem correction_linear_growth (a d e : ℕ → ℚ) (delta₀ : ℚ)
    (ha : ∀ i, 0 < a i) (ha₁ : ∀ i, a i ≤ 1)
    (hd : ∀ i, d i ≤ -delta₀) (he : ∀ i, 0 ≤ e i)
    (hrec : ∀ i, e i = a i * (e (i + 1) + d i)) (n : ℕ) :
    e 0 + (n : ℚ) * delta₀ ≤ e n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hgrow := correction_grows_by_tax (ha n) (ha₁ n) (he n) (hrec n)
      have hstep : e n + delta₀ ≤ e (n + 1) := by
        linarith [hd n]
      rw [Nat.cast_succ]
      calc
        e 0 + ((n : ℚ) + 1) * delta₀ =
            (e 0 + (n : ℚ) * delta₀) + delta₀ := by ring
        _ ≤ e n + delta₀ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right ih delta₀
        _ ≤ e (n + 1) := hstep

/-- The accumulated interface tax of any positive-opcode public word with
at least two steps is nonzero (indeed negative). -/
theorem no_zero_internal_tax (m h m' : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (hm : ∀ i, 0 < m i) :
    internalTax
      (fun i => coefficient (m i) (h i) (m' i))
      (fun i => delta (m i)) n ≠ 0 := by
  exact ne_of_lt (internalTax_neg _ _ n hn
    (fun i => coefficient_pos _ _ _) (fun i => delta_neg (hm i)))

/-! ## Linked public words -/

/-- A finite linked word of exact public-cofactor steps.  Values outside the
declared length are irrelevant; the bounded link hypotheses are what make
the object finite. -/
structure PublicWord where
  length : ℕ
  boundary : ℕ → ChargePublicCofactor.Boundary
  step : ℕ → ChargePublicCofactor.Step
  step_source : ∀ i, i < length → (step i).source = boundary i
  step_target : ∀ i, i < length → (step i).target = boundary (i + 1)

namespace PublicWord

def typedCoefficient (g : PublicWord) (i : ℕ) : ℚ :=
  coefficient (g.boundary i).opcode (g.step i).recharge
    (g.boundary (i + 1)).opcode

def typedTax (g : PublicWord) : ℚ :=
  internalTax g.typedCoefficient (fun i => delta (g.boundary i).opcode)
    g.length

theorem local_typed_interface (g : PublicWord) (i : ℕ) (hi : i < g.length) :
    ((g.boundary i).cofactor : ℚ) - tau (g.boundary i).opcode =
      g.typedCoefficient i *
        (((g.boundary (i + 1)).cofactor : ℚ) -
          beta (g.boundary (i + 1)).opcode) := by
  have h := ChargeTypedInterface.Step.typed_interface (g.step i)
  rw [g.step_source i hi, g.step_target i hi] at h
  exact h

/-- TI2 specialized all the way back to a linked word of exact public
steps. -/
theorem typed_unroll (g : PublicWord) (hN : 0 < g.length) :
    ((g.boundary 0).cofactor : ℚ) - tau (g.boundary 0).opcode =
      g.typedTax + prefixCoefficient g.typedCoefficient g.length *
        (((g.boundary g.length).cofactor : ℚ) -
          beta (g.boundary g.length).opcode) := by
  exact finite_typed_unroll
    (fun i => ((g.boundary i).cofactor : ℚ))
    (fun i => tau (g.boundary i).opcode)
    (fun i => beta (g.boundary i).opcode)
    g.typedCoefficient
    (fun i => delta (g.boundary i).opcode)
    g.length hN (fun i => rfl) (fun i hi => g.local_typed_interface i hi)

theorem typedTax_neg (g : PublicWord) (hN : 2 ≤ g.length) : g.typedTax < 0 := by
  exact internalTax_neg _ _ g.length hN
    (fun i => coefficient_pos _ _ _)
    (fun i => delta_neg (g.boundary i).opcode_pos)

theorem typedTax_ne_zero (g : PublicWord) (hN : 2 ≤ g.length) :
    g.typedTax ≠ 0 := ne_of_lt (g.typedTax_neg hN)

/-- No length-at-least-two bare public word enters exactly at its source
chart origin and exits exactly at its target chart origin.  An auxiliary
affine rail or another operation must cancel the internal tax. -/
theorem no_clean_chart_adapter (g : PublicWord) (hN : 2 ≤ g.length)
    (hsource : ((g.boundary 0).cofactor : ℚ) = tau (g.boundary 0).opcode)
    (htarget : ((g.boundary g.length).cofactor : ℚ) =
      beta (g.boundary g.length).opcode) : False := by
  have hu := g.typed_unroll (by omega)
  rw [hsource, htarget] at hu
  have hz : g.typedTax = 0 := by
    simpa using hu.symm
  exact g.typedTax_ne_zero hN hz

end PublicWord

end ChargeTypedInterface
end KontoroC

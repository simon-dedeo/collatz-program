/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeTypedInterface

/-!
# Exact algebra of the two-step phase swap

The phase-swap word restores signed chart separation by crossing the charts
at its internal boundary.  This file checks its exponent identities and the
general signed-area law.  It also records the adversarial qualification:
restoring separation does not cancel the strictly negative typed interface
tax of the internal public boundary.
-/

namespace KontoroC
namespace ChargePhaseSwap

/-- Total ternary exponent of a two-step public word with boundary opcodes
`m0,m1,m2` and recharge counts `h0,h1`. -/
def ternaryTotal (m₀ m₁ h₀ h₁ : ℕ) : ℕ :=
  114 * h₀ + 17 * m₀ + (114 * h₁ + 17 * m₁)

/-- Total binary exponent of the same word. -/
def binaryTotal (m₁ m₂ h₀ h₁ : ℕ) : ℕ :=
  154 * h₀ + 23 * m₁ + (154 * h₁ + 23 * m₂)

/-- The three boundary phases of the minimal swap word
`r -> L-r -> r+d`. -/
def boundaryPhase (L d r : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => r
  | ⟨1, _⟩ => L - r
  | ⟨2, _⟩ => r + d

/-- PS1, ternary half: the composite gain is independent of the moving
outer phase. -/
theorem ternaryTotal_phaseSwap {L r h₀ h₁ : ℕ} (hr : r ≤ L) :
    ternaryTotal r (L - r) h₀ h₁ =
      114 * (h₀ + h₁) + 17 * L := by
  simp only [ternaryTotal]
  omega

/-- PS1, binary half. -/
theorem binaryTotal_phaseSwap {L d r h₀ h₁ : ℕ} (hr : r ≤ L) :
    binaryTotal (L - r) (r + d) h₀ h₁ =
      154 * (h₀ + h₁) + 23 * (L + d) := by
  simp only [binaryTotal]
  omega

/-- Adjacent phase-swap words have signed boundary differences `(d,-d,d)`.
The statement uses integers so the internal chart crossing is visible rather
than truncated away. -/
theorem boundary_difference {L d r : ℕ} (hr : r + d ≤ L) (i : Fin 3) :
    (boundaryPhase L d (r + d) i : ℤ) -
        (boundaryPhase L d r i : ℤ) =
      if (i : ℕ) = 1 then -(d : ℤ) else (d : ℤ) := by
  fin_cases i <;> simp [boundaryPhase]
  all_goals omega

/-- PS2 in its algebraically minimal form.  Equal total `Q` and `P` give
the signed-area law after eliminating the total recharge difference. -/
theorem signed_area_law (d₀ dN internal rechargeDifference : ℤ)
    (hQ : 114 * rechargeDifference + 17 * (d₀ + internal) = 0)
    (hP : 154 * rechargeDifference + 23 * (internal + dN) = 0) :
    1311 * dN - 1309 * d₀ = -2 * internal := by
  linear_combination (57 : ℤ) * hP - (77 : ℤ) * hQ

/-- Total ternary exponent for a finite signed opcode/recharge word.  Signed
coordinates make comparison of two words direct. -/
def wordTernaryTotal (m h : ℕ → ℤ) (N : ℕ) : ℤ :=
  114 * ∑ i ∈ Finset.range N, h i +
    17 * ∑ i ∈ Finset.range N, m i

/-- Total binary exponent, using the target opcode of each step. -/
def wordBinaryTotal (m h : ℕ → ℤ) (N : ℕ) : ℤ :=
  154 * ∑ i ∈ Finset.range N, h i +
    23 * ∑ i ∈ Finset.range N, m (i + 1)

/-- PS2 stated for two actual finite opcode/recharge words with equal total
exponents, rather than merely for pre-simplified scalar equations. -/
theorem signed_area_law_of_equal_word_totals
    (m m' h h' : ℕ → ℤ) (N : ℕ) (hN : 0 < N)
    (hQ : wordTernaryTotal m h N = wordTernaryTotal m' h' N)
    (hP : wordBinaryTotal m h N = wordBinaryTotal m' h' N) :
    1311 * (m' N - m N) - 1309 * (m' 0 - m 0) =
      -2 * ∑ i ∈ Finset.Ico 1 N, (m' i - m i) := by
  let d : ℕ → ℤ := fun i => m' i - m i
  let e : ℕ → ℤ := fun i => h' i - h i
  let S : ℤ := ∑ i ∈ Finset.Ico 1 N, d i
  let E : ℤ := ∑ i ∈ Finset.range N, e i
  have hsource : (∑ i ∈ Finset.range N, d i) = d 0 + S := by
    have hs := Finset.sum_Ico_eq_sub d (show 1 ≤ N by omega)
    simp only [Finset.sum_range_one] at hs
    dsimp only [S]
    linarith
  have htarget : (∑ i ∈ Finset.range N, d (i + 1)) = S + d N := by
    have hs := Finset.sum_Ico_eq_sum_range d 1 (N + 1)
    have hsplit := Finset.sum_Ico_succ_top (show 1 ≤ N by omega) d
    rw [hs] at hsplit
    simp only [Nat.add_sub_cancel] at hsplit
    dsimp only [S]
    simpa [Nat.add_comm] using hsplit
  have hQzero : 114 * E + 17 * (d 0 + S) = 0 := by
    simp only [wordTernaryTotal] at hQ
    dsimp only [E, e, d]
    rw [← hsource]
    rw [show (∑ i ∈ Finset.range N, d i) =
        (∑ i ∈ Finset.range N, m' i) -
          (∑ i ∈ Finset.range N, m i) by
      simp [d, Finset.sum_sub_distrib]]
    simp only [Finset.sum_sub_distrib]
    linear_combination -hQ
  have hPzero : 154 * E + 23 * (S + d N) = 0 := by
    simp only [wordBinaryTotal] at hP
    dsimp only [E, e, d]
    rw [← htarget]
    rw [show (∑ i ∈ Finset.range N, d (i + 1)) =
        (∑ i ∈ Finset.range N, m' (i + 1)) -
          (∑ i ∈ Finset.range N, m (i + 1)) by
      simp [d, Finset.sum_sub_distrib]]
    simp only [Finset.sum_sub_distrib]
    linear_combination -hP
  have harea := signed_area_law (d 0) (d N) S E hQzero hPzero
  simpa [d, S] using harea

/-- Equal positive endpoint separation forces the sum of signed internal
separations to be negative.  A booster must therefore cross chart order. -/
theorem internal_eq_neg_endpoint_of_restored_separation
    (d internal rechargeDifference : ℤ)
    (hQ : 114 * rechargeDifference + 17 * (d + internal) = 0)
    (hP : 154 * rechargeDifference + 23 * (internal + d) = 0) :
    internal = -d := by
  have h := signed_area_law d d internal rechargeDifference hQ hP
  linarith

/-- The advertised smallest phase-swap delay line. -/
theorem smallest_boundary_shapes :
    (boundaryPhase 4 1 1 0, boundaryPhase 4 1 1 1, boundaryPhase 4 1 1 2) =
        (1, 3, 2) ∧
      (boundaryPhase 4 1 2 0, boundaryPhase 4 1 2 1, boundaryPhase 4 1 2 2) =
        (2, 2, 3) ∧
      (boundaryPhase 4 1 3 0, boundaryPhase 4 1 3 1, boundaryPhase 4 1 3 2) =
        (3, 1, 4) := by
  norm_num [boundaryPhase]

theorem smallest_composite_exponents :
    ternaryTotal 1 3 1 1 = 296 ∧
      binaryTotal 3 2 1 1 = 423 ∧
      ternaryTotal 2 2 1 1 = 296 ∧
      binaryTotal 2 3 1 1 = 423 := by
  norm_num [ternaryTotal, binaryTotal]

/-- Backward coefficient of every macro in the smallest equal-gain family. -/
def smallestBackwardCoefficient : ℚ := (2 : ℚ) ^ 423 / (3 : ℚ) ^ 296

theorem smallestBackwardCoefficient_pos : 0 < smallestBackwardCoefficient := by
  simp only [smallestBackwardCoefficient]
  positivity

set_option exponentiation.threshold 512 in
theorem two_pow_423_lt_three_pow_296 : 2 ^ 423 < 3 ^ 296 := by
  norm_num

theorem smallestBackwardCoefficient_lt_one : smallestBackwardCoefficient < 1 := by
  rw [smallestBackwardCoefficient, div_lt_one]
  · exact_mod_cast two_pow_423_lt_three_pow_296
  · positivity

/-! ## Adversarial qualification -/

open ChargeTypedInterface

theorem internalTax_two (a d : ℕ → ℚ) :
    internalTax a d 2 = a 0 * d 1 := by
  norm_num [internalTax, prefixCoefficient]

/-- A two-step phase swap can restore its signed chart separation, but if it
consists of exact public steps then its sole internal boundary still pays a
strictly negative typed tax. -/
theorem two_step_public_tax_neg (g : PublicWord) (hg : g.length = 2) :
    g.typedTax < 0 := by
  exact g.typedTax_neg (by omega)

/-- A nonnegative TI3 correction across one smallest phase-swap macro must
strictly increase.  Resetting phase fuel without also paying this correction
debt cannot produce a bounded positive gauge rail. -/
theorem smallest_macro_correction_strictly_grows {tax e₀ e₁ : ℚ}
    (htax : tax < 0) (he₀ : 0 ≤ e₀)
    (hrec : e₀ = smallestBackwardCoefficient * (e₁ + tax)) :
    e₀ < e₁ := by
  exact correction_strictly_grows smallestBackwardCoefficient_pos
    (le_of_lt smallestBackwardCoefficient_lt_one) htax he₀ hrec

/-! ## A conjugacy square is not an orbit link -/

/-- Canonical source cylinder of a compressed public word. -/
def sourceTail (rho binary u : ℕ) : ℕ := rho + binary * u

/-- Canonical target ray of a compressed public word. -/
def targetTail (sigma ternary u : ℕ) : ℕ := sigma + ternary * u

/-- The next word's embedded source parameter. -/
def embeddedParameter (base slope u : ℕ) : ℕ := base + slope * u

/-- A simple but decisive discriminator.  If the embedded next-source base
already lies above the current target base and its cylinder grows faster,
then no nonnegative tail can make the current output equal the next input.
A commutative conjugacy square does not supply this missing equality. -/
theorem no_orbit_link_of_embedding_outruns
    (sigma rho binary ternary base slope u : ℕ)
    (hbase : sigma < sourceTail rho binary base)
    (hgain : ternary < binary * slope) :
    targetTail sigma ternary u ≠
      sourceTail rho binary (embeddedParameter base slope u) := by
  intro heq
  have hmul : ternary * u ≤ (binary * slope) * u :=
    Nat.mul_le_mul_right u (le_of_lt hgain)
  have hlt : targetTail sigma ternary u <
      sourceTail rho binary (embeddedParameter base slope u) := by
    simp only [targetTail, sourceTail, embeddedParameter]
    calc
      sigma + ternary * u <
          (rho + binary * base) + (binary * slope) * u :=
        Nat.add_lt_add_of_lt_of_le hbase hmul
      _ = rho + binary * (base + slope * u) := by ring
  exact (Nat.ne_of_lt hlt) heq

/-! ### The two records in the smallest phase-swap artifact

These decimal constants are the exact `sigma`, next `rho`, surviving-tail
base, and slope reconstructed by the public Python verifier for the two
records `W₁→W₂` and `W₂→W₃`.  The theorems below certify the
previously unchecked literal-link equation, independently of Python. -/

-- Exact decimal certificates are intentionally kept on one line so that a
-- transcription cannot be mistaken for arithmetic punctuation.
set_option linter.style.longLine false
namespace SmallestArtifact

def sigma₁ : ℕ :=
  744889819427608873222807483681117455594052018866244857967949396769305451478102698367897709783952585474535778390409626016409376728636144996298
def rho₂ : ℕ :=
  10526197576664414351938806566698775855376515653921917826387692972996978795523047394705044713890254039636501094498171482166808014
def base₁₂ : ℕ :=
  135810878612026184695893306845777897602952180309142391529519057770026977166139251351900562747016175743599769019723537633530640145800202345155
def slope₁₂ : ℕ :=
  308129952608255164862168604192124895328380318723351135677484809422674985131340617509475856086685331327483854135738719645380635527119215095024

def sigma₂ : ℕ :=
  821248801204092541588488035795282765857224461605483619349354723138906546883963667429604951991040225812953422346505744878149511478985739521899
def rho₃ : ℕ :=
  17452685594760724370529994722988563831732583772509201389816420874812056190360163159789046891239571433002120995799685212954601271
def base₂₃ : ℕ :=
  806597868944315244916444340292750082808663916228707976104000275863669964569194845811098799267868634055229126058346153791700706846556942871536
def slope₂₃ : ℕ :=
  1659868635400486787449025759040723777508506656927541241039271721493471225341450546894411477744558095923777024007231475498850740032340438409536

theorem first_embedded_base_above :
    sigma₁ < sourceTail rho₂ (2 ^ 423) base₁₂ := by
  have hs : sigma₁ < 8 * base₁₂ := by
    norm_num [sigma₁, base₁₂]
  have hpow : 8 ≤ 2 ^ 423 := by
    exact_mod_cast (show 8 ≤ 2 ^ 423 by omega)
  simp only [sourceTail]
  calc
    sigma₁ < 8 * base₁₂ := hs
    _ ≤ 2 ^ 423 * base₁₂ := Nat.mul_le_mul_right base₁₂ hpow
    _ ≤ rho₂ + 2 ^ 423 * base₁₂ := Nat.le_add_left _ _

set_option exponentiation.threshold 512 in
theorem first_embedding_outruns :
    3 ^ 296 < 2 ^ 423 * slope₁₂ := by
  have hs : 2 ^ 169 < slope₁₂ := by
    norm_num [slope₁₂]
  calc
    3 ^ 296 < 4 ^ 296 :=
      Nat.pow_lt_pow_left (by norm_num : 3 < 4) (by norm_num : 296 ≠ 0)
    _ = 2 ^ 423 * 2 ^ 169 := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    _ < 2 ^ 423 * slope₁₂ :=
      (Nat.mul_lt_mul_left (by positivity)).2 hs

/-- The first advertised parallel square has no literal ordinary orbit link
from the output of `W₁` to the embedded source of `W₂`. -/
theorem no_first_orbit_link (u : ℕ) :
    targetTail sigma₁ (3 ^ 296) u ≠
      sourceTail rho₂ (2 ^ 423) (embeddedParameter base₁₂ slope₁₂ u) :=
  no_orbit_link_of_embedding_outruns _ _ _ _ _ _ _
    first_embedded_base_above first_embedding_outruns

theorem second_embedded_base_above :
    sigma₂ < sourceTail rho₃ (2 ^ 423) base₂₃ := by
  have hs : sigma₂ < 2 * base₂₃ := by
    norm_num [sigma₂, base₂₃]
  have hpow : 2 ≤ 2 ^ 423 := by omega
  simp only [sourceTail]
  calc
    sigma₂ < 2 * base₂₃ := hs
    _ ≤ 2 ^ 423 * base₂₃ := Nat.mul_le_mul_right base₂₃ hpow
    _ ≤ rho₃ + 2 ^ 423 * base₂₃ := Nat.le_add_left _ _

set_option exponentiation.threshold 512 in
theorem second_embedding_outruns :
    3 ^ 296 < 2 ^ 423 * slope₂₃ := by
  have hs : 2 ^ 169 < slope₂₃ := by
    norm_num [slope₂₃]
  calc
    3 ^ 296 < 4 ^ 296 :=
      Nat.pow_lt_pow_left (by norm_num : 3 < 4) (by norm_num : 296 ≠ 0)
    _ = 2 ^ 423 * 2 ^ 169 := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    _ < 2 ^ 423 * slope₂₃ :=
      (Nat.mul_lt_mul_left (by positivity)).2 hs

/-- Nor does the second square link `W₂` to `W₃`. -/
theorem no_second_orbit_link (u : ℕ) :
    targetTail sigma₂ (3 ^ 296) u ≠
      sourceTail rho₃ (2 ^ 423) (embeddedParameter base₂₃ slope₂₃ u) :=
  no_orbit_link_of_embedding_outruns _ _ _ _ _ _ _
    second_embedded_base_above second_embedding_outruns

end SmallestArtifact
set_option linter.style.longLine true

end ChargePhaseSwap
end KontoroC

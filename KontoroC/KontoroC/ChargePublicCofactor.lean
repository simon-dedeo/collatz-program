/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeNormOpcode

/-!
# Canonical public-cofactor coordinates for the charge bouncer

An accepted boundary exposes its exact two-adic opcode directly:

`y + 1 = (2^23)^m * w`, with `m > 0` and `w` odd.

This file packages those coordinates without auxiliary norm witnesses.  Its
main theorem proves that the public balance equation is not merely necessary:
with positive odd endpoints and the public register condition at the input,
it reconstructs a literal `ChargeBouncerStep`.  The endpoint congruences are
kept in the public structures even though only the input register condition is
needed by the lower-level step structure.
-/

namespace KontoroC

namespace ChargePublicCofactor

def publicA : ℕ := 3 ^ 114
def publicB : ℕ := 2 ^ 154
def publicC : ℕ := 3 ^ 17
def publicD : ℕ := 2 ^ 23

/-- The ordinary integer represented by public cofactor coordinates. -/
def publicValue (m w : ℕ) : ℕ := publicD ^ m * w - 1

/-- Canonical public data at one accepted-boundary candidate. -/
structure Boundary where
  opcode : ℕ
  cofactor : ℕ
  opcode_pos : 0 < opcode
  cofactor_pos : 0 < cofactor
  cofactor_odd : Odd cofactor
  register : chargeRegisterModulus ∣ publicValue opcode cofactor
  fixed : chargeFixedDivisor ∣ publicD ^ opcode * cofactor

namespace Boundary

def value (b : Boundary) : ℕ := publicValue b.opcode b.cofactor

theorem two_le_scale (b : Boundary) : 2 ≤ publicD ^ b.opcode := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero b.opcode_pos.ne'
  rw [hn]
  simp only [pow_succ]
  have hbase : 2 ≤ publicD := by norm_num [publicD]
  have hpow : 0 < publicD ^ n := by positivity
  nlinarith

theorem value_pos (b : Boundary) : 0 < b.value := by
  have hs := b.two_le_scale
  have hw := b.cofactor_pos
  have hmul := Nat.mul_le_mul_right b.cofactor hs
  dsimp [value, publicValue]
  omega

theorem value_add_one (b : Boundary) :
    b.value + 1 = publicD ^ b.opcode * b.cofactor := by
  dsimp [value, publicValue]
  apply Nat.sub_add_cancel
  have hs := b.two_le_scale
  have hw := b.cofactor_pos
  have hmul := Nat.mul_le_mul_right b.cofactor hs
  omega

/-- PC1 is genuinely canonical: the positive exponent and odd cofactor are
uniquely recovered from the represented ordinary integer. -/
theorem coordinates_unique (b c : Boundary) (h : b.value = c.value) :
    b.opcode = c.opcode ∧ b.cofactor = c.cofactor := by
  have hfactor :
      2 ^ (23 * b.opcode) * b.cofactor =
        2 ^ (23 * c.opcode) * c.cofactor := by
    calc
      2 ^ (23 * b.opcode) * b.cofactor =
          publicD ^ b.opcode * b.cofactor := by simp [publicD, pow_mul]
      _ = b.value + 1 := b.value_add_one.symm
      _ = c.value + 1 := by rw [h]
      _ = publicD ^ c.opcode * c.cofactor := c.value_add_one
      _ = 2 ^ (23 * c.opcode) * c.cofactor := by simp [publicD, pow_mul]
  have hu := twoPow_mul_odd_unique b.cofactor_odd c.cofactor_odd hfactor
  exact ⟨by omega, hu.2⟩

end Boundary

/-- The entirely public one-step recurrence PC3, with PC2 stored at both
endpoints. -/
structure Step where
  source : Boundary
  target : Boundary
  recharge : ℕ
  recharge_pos : 0 < recharge
  balance :
    publicA ^ recharge *
        (publicC ^ source.opcode * source.cofactor - 1) =
      publicB ^ recharge * target.value

namespace Step

private theorem scale_three_dvd (s : Step) :
    3 ∣ publicC ^ s.source.opcode * s.source.cofactor := by
  have hc : 3 ∣ publicC := by norm_num [publicC]
  have hp : publicC ∣ publicC ^ s.source.opcode :=
    dvd_pow_self publicC s.source.opcode_pos.ne'
  exact dvd_mul_of_dvd_left (hc.trans hp) s.source.cofactor

private theorem collisionNumerator_pos (s : Step) :
    0 < publicC ^ s.source.opcode * s.source.cofactor - 1 := by
  have hc : 2 ≤ publicC ^ s.source.opcode := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      s.source.opcode_pos.ne'
    rw [hn]
    simp only [pow_succ]
    have hbase : 2 ≤ publicC := by norm_num [publicC]
    have hpow : 0 < publicC ^ n := by positivity
    nlinarith
  have hmul := Nat.mul_le_mul_right s.source.cofactor hc
  apply Nat.sub_pos_of_lt
  have hcofactor : 1 ≤ s.source.cofactor := s.source.cofactor_pos
  have htwo : 2 ≤ 2 * s.source.cofactor := by
    simpa using Nat.mul_le_mul_left 2 hcofactor
  exact (by omega : 1 < 2).trans_le (htwo.trans hmul)

private theorem outputNumerator_odd (s : Step) : Odd s.target.value := by
  have hevenBase : Even publicD := by
    rw [even_iff_two_dvd]
    norm_num [publicD]
  have hevenPow : Even (publicD ^ s.target.opcode) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      s.target.opcode_pos.ne'
    rw [hn, pow_succ]
    exact hevenBase.mul_left _
  have hevenProd : Even (publicD ^ s.target.opcode * s.target.cofactor) :=
    hevenPow.mul_right _
  rcases hevenProd with ⟨k, hk⟩
  have hpos : 0 < publicD ^ s.target.opcode * s.target.cofactor := by
    exact Nat.mul_pos (pow_pos (by norm_num [publicD]) _)
      s.target.cofactor_pos
  refine ⟨k - 1, ?_⟩
  dsimp [Boundary.value, publicValue]
  omega

private theorem rechargePower_dvd_collisionNumerator (s : Step) :
    publicB ^ s.recharge ∣
      publicC ^ s.source.opcode * s.source.cofactor - 1 := by
  have hcop : Nat.Coprime (publicB ^ s.recharge) (publicA ^ s.recharge) := by
    apply Nat.Coprime.pow
    norm_num [publicA, publicB]
  apply hcop.dvd_of_dvd_mul_left
  rw [s.balance]
  exact dvd_mul_right _ _

/-- PC1--PC3 reconstruct the hidden odd collision quotient and hence an
actual accepted bouncer step.  No norm representation is used as memory. -/
def toChargeBouncerStep (s : Step) : ChargeBouncerStep := by
  let numerator := publicC ^ s.source.opcode * s.source.cofactor - 1
  let q := numerator / publicB ^ s.recharge
  have hq : publicB ^ s.recharge * q = numerator := by
    exact Nat.mul_div_cancel' s.rechargePower_dvd_collisionNumerator
  have hq_out : s.target.value = publicA ^ s.recharge * q := by
    have hcancel :
        publicB ^ s.recharge * (publicA ^ s.recharge * q) =
          publicB ^ s.recharge * s.target.value := by
      calc
        publicB ^ s.recharge * (publicA ^ s.recharge * q) =
            publicA ^ s.recharge *
              (publicB ^ s.recharge * q) := by ring
        _ = publicA ^ s.recharge * numerator := by rw [hq]
        _ = publicB ^ s.recharge * s.target.value := s.balance
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num [publicB]) _)
      hcancel).symm
  have hq_pos : 0 < q := by
    have hn := s.collisionNumerator_pos
    dsimp [numerator] at hq
    rw [← hq] at hn
    exact pos_of_mul_pos_right hn (by positivity)
  have hq_odd : Odd q := by
    have houtOdd := s.outputNumerator_odd
    rw [hq_out] at houtOdd
    exact (Nat.odd_mul.mp houtOdd).2
  have hq_not_three : ¬3 ∣ q := by
    intro hthree
    have hnumThree : 3 ∣ numerator := by
      rw [← hq]
      exact dvd_mul_of_dvd_right hthree _
    have hscaleThree := s.scale_three_dvd
    have hscalePos :
        1 ≤ publicC ^ s.source.opcode * s.source.cofactor := by
      exact (Nat.mul_pos (pow_pos (by norm_num [publicC]) _)
        s.source.cofactor_pos)
    have hnumAdd : numerator + 1 =
        publicC ^ s.source.opcode * s.source.cofactor := by
      dsimp [numerator]
      exact Nat.sub_add_cancel hscalePos
    have hone : 3 ∣ 1 := by
      rw [← hnumAdd] at hscaleThree
      exact (Nat.dvd_add_iff_left hnumThree).mpr
        (by simpa [Nat.add_comm] using hscaleThree)
    norm_num at hone
  refine
    { defectOpcode := s.source.opcode
      rechargeCount := s.recharge
      input := s.source.value
      output := s.target.value
      oddPart := q
      defectOpcode_pos := s.source.opcode_pos
      rechargeCount_pos := s.recharge_pos
      input_pos := s.source.value_pos
      oddPart_pos := hq_pos
      input_three := (by
        have hthreeM : 3 ∣ chargeRegisterModulus := by
          exact dvd_mul_of_dvd_left
            (dvd_pow_self 3 (by omega : 33 ≠ 0)) chargeDifference
        exact hthreeM.trans s.source.register)
      oddPart_odd := hq_odd
      oddPart_not_three := hq_not_three
      output_eq := by
        rw [hq_out]
        simp [publicA, pow_mul]
      rearranged := ?_ }
  rw [s.source.value_add_one]
  have hcollision :
      publicC ^ s.source.opcode * s.source.cofactor =
        1 + publicB ^ s.recharge * q := by
    have hpos : 1 ≤ publicC ^ s.source.opcode * s.source.cofactor := by
      exact (Nat.mul_pos (pow_pos (by norm_num [publicC]) _)
        s.source.cofactor_pos)
    calc
      publicC ^ s.source.opcode * s.source.cofactor =
          (publicC ^ s.source.opcode * s.source.cofactor - 1) + 1 :=
        (Nat.sub_add_cancel hpos).symm
      _ = publicB ^ s.recharge * q + 1 := by
        dsimp [numerator] at hq
        rw [hq]
      _ = 1 + publicB ^ s.recharge * q := Nat.add_comm _ _
  simp only [pow_mul]
  change publicC ^ s.source.opcode *
      (publicD ^ s.source.opcode * s.source.cofactor) =
    publicD ^ s.source.opcode *
      (1 + publicB ^ s.recharge * q)
  calc
    publicC ^ s.source.opcode *
        (publicD ^ s.source.opcode * s.source.cofactor) =
      publicD ^ s.source.opcode *
        (publicC ^ s.source.opcode * s.source.cofactor) := by ring
    _ = publicD ^ s.source.opcode *
        (1 + publicB ^ s.recharge * q) := by rw [hcollision]

/-- Cheap forward half: an accepted step in public source/target coordinates
satisfies PC3. -/
theorem balance_of_chargeBouncerStep
    (s : ChargeBouncerStep) (source target : Boundary)
    (hm : source.opcode = s.defectOpcode)
    (hin : source.value = s.input)
    (hout : target.value = s.output) :
    publicA ^ s.rechargeCount *
        (publicC ^ source.opcode * source.cofactor - 1) =
      publicB ^ s.rechargeCount * target.value := by
  have hsource :
      publicC ^ source.opcode * source.cofactor =
        1 + publicB ^ s.rechargeCount * s.oddPart := by
    have hr := s.rearranged
    rw [← hin, source.value_add_one, hm] at hr
    rw [hm]
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.pow_pos (by omega : 0 < 2) : 0 < 2 ^ (23 * s.defectOpcode))
    calc
      2 ^ (23 * s.defectOpcode) *
          (publicC ^ s.defectOpcode * source.cofactor) =
        3 ^ (17 * s.defectOpcode) *
          (publicD ^ s.defectOpcode * source.cofactor) := by
            simp only [publicC, publicD, pow_mul]
            ring
      _ = 2 ^ (23 * s.defectOpcode) *
          (1 + 2 ^ (154 * s.rechargeCount) * s.oddPart) := hr
      _ = 2 ^ (23 * s.defectOpcode) *
          (1 + publicB ^ s.rechargeCount * s.oddPart) := by
            simp [publicB, pow_mul]
  have htarget : target.value = publicA ^ s.rechargeCount * s.oddPart := by
    rw [hout, s.output_eq]
    simp [publicA, pow_mul]
  rw [hsource, htarget]
  have hBpos : 0 < publicB ^ s.rechargeCount * s.oddPart := by
    exact Nat.mul_pos (pow_pos (by norm_num [publicB]) _) s.oddPart_pos
  simp only [Nat.add_sub_cancel_left]
  ring

/-- Subtraction-free form of PC4.  Keeping the positive gap on the left is
important over `Nat`; the signed constant `B^h-A^h` is negative. -/
theorem cofactor_balance (s : Step) :
    publicB ^ s.recharge *
          (publicD ^ s.target.opcode * s.target.cofactor) +
        (publicA ^ s.recharge - publicB ^ s.recharge) =
      publicA ^ s.recharge *
        (publicC ^ s.source.opcode * s.source.cofactor) := by
  have hABbase : publicB < publicA := by
    norm_num [publicA, publicB]
  have hAB : publicB ^ s.recharge < publicA ^ s.recharge :=
    Nat.pow_lt_pow_left hABbase (Nat.ne_of_gt s.recharge_pos)
  have hsourcePos :
      1 ≤ publicC ^ s.source.opcode * s.source.cofactor := by
    exact (Nat.mul_pos (pow_pos (by norm_num [publicC]) _)
      s.source.cofactor_pos)
  have htarget :
      publicD ^ s.target.opcode * s.target.cofactor =
        s.target.value + 1 := s.target.value_add_one.symm
  have hsource :
      publicC ^ s.source.opcode * s.source.cofactor =
        (publicC ^ s.source.opcode * s.source.cofactor - 1) + 1 :=
    (Nat.sub_add_cancel hsourcePos).symm
  rw [htarget, hsource, mul_add, mul_add, mul_one, mul_one]
  rw [← s.balance]
  omega

end Step

end ChargePublicCofactor

end KontoroC

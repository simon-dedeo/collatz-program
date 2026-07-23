/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib

/-!
# Linked returning-glider tail synchronization

This file packages the universal integer algebra extracted from the exact
returning-glider packet chart.  It deliberately assumes the packet and EC17
link equations as hypotheses: finite Python reconstruction is not imported
as a theorem, and no infinite linked orbit or Collatz counterexample is
asserted.

The main conclusions are:

* every linked successor has boundary numerator of exact 3-adic order two;
* its literal boundary lies at exact precision `6*n` around `-881/473`;
* at any fixed lower precision, the successor tail coordinate depends only
  on the successor branch and not on the source core or affine lift.
-/

namespace KontoroC
namespace GliderKLTailSynchronization

/-- QM144a: the packet/core chart implies the moving-target identity for
the literal boundary numerator `Z`. -/
theorem packetChart_identity {K u Z : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (hK : 83790531 * K - 874281 = 3 * 2 ^ (8 * n - 5) * u)
    (hZ : Z = 2 ^ 35 * K - 358513857) :
    473 * 3 ^ 10 * Z = 2 ^ (8 * n + 30) * u - 9591553 := by
  have hpow : (2 : ℤ) ^ 35 * 2 ^ (8 * n - 5) =
      2 ^ (8 * n + 30) := by
    rw [← pow_add]
    congr 1
    omega
  have htriple :
      3 * (473 * 3 ^ 10 * Z) =
        3 * (2 ^ (8 * n + 30) * u - 9591553) := by
    calc
      3 * (473 * 3 ^ 10 * Z) =
          2 ^ 35 * (83790531 * K - 874281) - 3 * 9591553 := by
        rw [hZ]
        norm_num
        ring
      _ = 2 ^ 35 * (3 * 2 ^ (8 * n - 5) * u) - 3 * 9591553 := by
        rw [hK]
      _ = 3 * (2 ^ (8 * n + 30) * u - 9591553) := by
        rw [← hpow]
        ring
  exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) htriple

/-- QM144b from the already normalized successor chart and the exact EC17
link equation. -/
theorem linkedRail_factorization {u u' Z' : ℤ} {n m : ℕ} (hn : 1 ≤ n)
    (hchart :
      473 * 3 ^ 10 * Z' = 2 ^ (8 * m + 30) * u' - 9591553)
    (hlink :
      2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    473 * Z' = 9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17) := by
  have hpow2 : (2 : ℤ) ^ (8 * m + 30) =
      2 ^ 15 * 2 ^ (8 * m + 15) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow3 : (3 : ℤ) ^ (6 * n + 11) =
      3 ^ 12 * 3 ^ (6 * n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hscaled :
      473 * 3 ^ 10 * Z' =
        3 ^ 10 * (9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17)) := by
    calc
      473 * 3 ^ 10 * Z' =
          2 ^ (8 * m + 30) * u' - 9591553 := hchart
      _ = 2 ^ 15 * (2 ^ (8 * m + 15) * u') - 9591553 := by
        rw [hpow2]
        ring
      _ = 2 ^ 15 * (3 ^ (6 * n + 11) * u + 17) - 9591553 := by
        rw [hlink]
      _ = 3 ^ 10 *
          (9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17)) := by
        rw [hpow3]
        norm_num
        ring
  apply mul_right_cancel₀ (pow_ne_zero 10 (by norm_num : (3 : ℤ) ≠ 0))
  calc
    473 * Z' * 3 ^ 10 = 473 * 3 ^ 10 * Z' := by ring
    _ = 3 ^ 10 *
        (9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17)) := hscaled
    _ = 9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17) * 3 ^ 10 := by
      ring

/-- Direct packet-level consumer of `packetChart_identity` and the EC17
link.  Only the successor packet chart is needed for the factorization. -/
theorem linkedRail_factorization_of_packet {K' u u' Z' : ℤ} {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hK' : 83790531 * K' - 874281 = 3 * 2 ^ (8 * m - 5) * u')
    (hZ' : Z' = 2 ^ 35 * K' - 358513857)
    (hlink : 2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    473 * Z' = 9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17) :=
  linkedRail_factorization hn (packetChart_identity hm hK' hZ') hlink

/-- QM144c: the linked numerator has exactly two factors of three, stated
without relying on a valuation API. -/
theorem linkedRail_exact_two {u Z' : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (h : 473 * Z' = 9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17)) :
    (9 : ℤ) ∣ Z' ∧ ¬(27 : ℤ) ∣ Z' := by
  let B : ℤ := 2 ^ 15 * 3 ^ (6 * n - 1) * u - 17
  have hB : 473 * Z' = 9 * B := h
  have h9mul : (9 : ℤ) ∣ 473 * Z' := ⟨B, hB⟩
  have h9 : (9 : ℤ) ∣ Z' :=
    Int.dvd_of_dvd_mul_right_of_gcd_one h9mul (by norm_num)
  refine ⟨h9, ?_⟩
  intro h27
  obtain ⟨w, hw⟩ := h27
  have hcancel : 473 * 3 * w = B := by
    apply mul_left_cancel₀ (by norm_num : (9 : ℤ) ≠ 0)
    calc
      9 * (473 * 3 * w) = 473 * (27 * w) := by ring
      _ = 473 * Z' := by rw [hw]
      _ = 9 * B := hB
  have h3B : (3 : ℤ) ∣ B :=
    ⟨473 * w, by rw [← hcancel]; ring⟩
  have h3pow : (3 : ℤ) ∣ 3 ^ (6 * n - 1) :=
    dvd_pow_self 3 (by omega)
  have h3first : (3 : ℤ) ∣ 2 ^ 15 * 3 ^ (6 * n - 1) * u :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3pow _) _
  have h317 : (3 : ℤ) ∣ 17 := by
    have hdifference := dvd_sub h3first h3B
    simpa [B] using hdifference
  norm_num at h317

/-- QM144d: conversion from the numerator chart to the rational center of
the literal Collatz boundary.  The division in `C'+1=8*Z'/3` is represented
by its exact cross-multiplied equation. -/
theorem boundary_center_identity {u Z' C' : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (hB : 473 * Z' = 9 * (2 ^ 15 * 3 ^ (6 * n - 1) * u - 17))
    (hC : 3 * (C' + 1) = 8 * Z') :
    473 * C' + 881 = 2 ^ 18 * 3 ^ (6 * n) * u := by
  let B : ℤ := 2 ^ 15 * 3 ^ (6 * n - 1) * u - 17
  have hB' : 473 * Z' = 9 * B := hB
  have htriple : 3 * (473 * (C' + 1)) = 3 * (24 * B) := by
    calc
      3 * (473 * (C' + 1)) = 473 * (3 * (C' + 1)) := by ring
      _ = 473 * (8 * Z') := by rw [hC]
      _ = 8 * (473 * Z') := by ring
      _ = 8 * (9 * B) := by rw [hB']
      _ = 3 * (24 * B) := by ring
  have hbase : 473 * (C' + 1) = 24 * B :=
    mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) htriple
  have hpow3 : (3 : ℤ) ^ (6 * n) = 3 ^ (6 * n - 1) * 3 := by
    calc
      (3 : ℤ) ^ (6 * n) = 3 ^ ((6 * n - 1) + 1) := by
        congr 1
        omega
      _ = 3 ^ (6 * n - 1) * 3 := by rw [pow_succ]
  rw [hpow3]
  dsimp [B] at hbase
  norm_num at hbase ⊢
  linear_combination hbase

/-- Exact 3-adic precision of the rational-center identity when the source
core is `1 mod 3`. -/
theorem boundary_center_exact_precision {u C' : ℤ} {n : ℕ}
    (hcenter : 473 * C' + 881 = 2 ^ 18 * 3 ^ (6 * n) * u)
    (hu : u % 3 = 1) :
    (3 : ℤ) ^ (6 * n) ∣ 473 * C' + 881 ∧
      ¬(3 : ℤ) ^ (6 * n + 1) ∣ 473 * C' + 881 := by
  constructor
  · refine ⟨2 ^ 18 * u, ?_⟩
    rw [hcenter]
    ring
  · intro hnext
    obtain ⟨w, hw⟩ := hnext
    have hcancel : 2 ^ 18 * u = 3 * w := by
      apply mul_left_cancel₀
        (pow_ne_zero (6 * n) (by norm_num : (3 : ℤ) ≠ 0))
      calc
        3 ^ (6 * n) * (2 ^ 18 * u) =
            2 ^ 18 * 3 ^ (6 * n) * u := by ring
        _ = 473 * C' + 881 := hcenter.symm
        _ = 3 ^ (6 * n + 1) * w := hw
        _ = 3 ^ (6 * n) * (3 * w) := by rw [pow_succ]; ring
    have h3mul : (3 : ℤ) ∣ 2 ^ 18 * u := ⟨w, hcancel⟩
    have h3u : (3 : ℤ) ∣ u :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h3mul (by norm_num)
    have hzero : u % 3 = 0 := Int.emod_eq_zero_of_dvd h3u
    omega

/-- First part of QM144e: enough source precision removes the source term
from the successor EC17 equation. -/
theorem linkedCore_modEq {u u' : ℤ} {n m d : ℕ} (hd : d ≤ 6 * n + 1)
    (hlink :
      2 ^ (8 * m + 15) * u' = 3 ^ (6 * n + 11) * u + 17) :
    Int.ModEq (3 ^ (d + 10)) (2 ^ (8 * m + 15) * u') 17 := by
  rw [Int.modEq_iff_dvd]
  have hpow : (3 : ℤ) ^ (d + 10) ∣ 3 ^ (6 * n + 11) :=
    pow_dvd_pow 3 (by omega)
  have hmul : (3 : ℤ) ^ (d + 10) ∣ 3 ^ (6 * n + 11) * u :=
    dvd_mul_of_dvd_left hpow u
  rw [hlink]
  simpa using hmul

/-- Multiplication by the dyadic EC17 coefficient is injective modulo every
power of three. -/
theorem linkedCore_unique {u₁ u₂ : ℤ} {m d : ℕ}
    (h₁ : Int.ModEq (3 ^ (d + 10)) (2 ^ (8 * m + 15) * u₁) 17)
    (h₂ : Int.ModEq (3 ^ (d + 10)) (2 ^ (8 * m + 15) * u₂) 17) :
    Int.ModEq (3 ^ (d + 10)) u₁ u₂ := by
  have hmul : Int.ModEq (3 ^ (d + 10))
      (2 ^ (8 * m + 15) * u₁) (2 ^ (8 * m + 15) * u₂) :=
    h₁.trans h₂.symm
  rw [Int.modEq_iff_dvd] at hmul ⊢
  have hcoprime :
      IsCoprime ((3 : ℤ) ^ (d + 10)) (2 ^ (8 * m + 15)) :=
    (by norm_num : IsCoprime (3 : ℤ) 2).pow
  apply hcoprime.dvd_of_dvd_mul_left
  simpa [mul_sub] using hmul

/-- Final fixed-depth synchronization interface of QM144e.  Once two linked
successor cores lie on the same branch chart, their tail coordinates agree
modulo `3^d`. -/
theorem tailCoordinate_unique {u₁ u₂ U q₁ q₂ : ℤ} {d : ℕ}
    (hcore : Int.ModEq (3 ^ (d + 10)) u₁ u₂)
    (hu₁ : u₁ = U + 473 * 2 ^ 20 * 3 ^ 10 * q₁)
    (hu₂ : u₂ = U + 473 * 2 ^ 20 * 3 ^ 10 * q₂) :
    Int.ModEq (3 ^ d) q₁ q₂ := by
  have hpow : (3 : ℤ) ^ (d + 10) = 3 ^ 10 * 3 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hu₁, hu₂, hpow] at hcore
  have hscaled : Int.ModEq (3 ^ 10 * 3 ^ d)
      (3 ^ 10 * (473 * 2 ^ 20 * q₁))
      (3 ^ 10 * (473 * 2 ^ 20 * q₂)) := by
    convert hcore.add_left_cancel' U using 1 <;> ring
  have hunit := hscaled.mul_left_cancel'
    (pow_ne_zero 10 (by norm_num : (3 : ℤ) ≠ 0))
  rw [Int.modEq_iff_dvd] at hunit ⊢
  have hcoprime : IsCoprime ((3 : ℤ) ^ d) (473 * 2 ^ 20) :=
    (by norm_num : IsCoprime (3 : ℤ) (473 * 2 ^ 20)).pow_left
  apply hcoprime.dvd_of_dvd_mul_left
  simpa [mul_sub] using hunit

/-- Combined fixed-depth consumer: two links into the same successor branch
have identical tail coordinates to every precision allowed by both source
lengths. -/
theorem linkedTailCoordinate_unique
    {u₁ u₂ u₁' u₂' U q₁ q₂ : ℤ} {n₁ n₂ m d : ℕ}
    (hd₁ : d ≤ 6 * n₁ + 1) (hd₂ : d ≤ 6 * n₂ + 1)
    (hlink₁ :
      2 ^ (8 * m + 15) * u₁' = 3 ^ (6 * n₁ + 11) * u₁ + 17)
    (hlink₂ :
      2 ^ (8 * m + 15) * u₂' = 3 ^ (6 * n₂ + 11) * u₂ + 17)
    (hu₁' : u₁' = U + 473 * 2 ^ 20 * 3 ^ 10 * q₁)
    (hu₂' : u₂' = U + 473 * 2 ^ 20 * 3 ^ 10 * q₂) :
    Int.ModEq (3 ^ d) q₁ q₂ := by
  apply tailCoordinate_unique
    (linkedCore_unique (linkedCore_modEq hd₁ hlink₁)
      (linkedCore_modEq hd₂ hlink₂)) hu₁' hu₂'

end GliderKLTailSynchronization
end KontoroC

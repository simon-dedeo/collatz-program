/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargePolicyBoundary

/-!
# Affine successor cylinders and their finite information budget

This file packages QM47, the generic algebra behind intersections of an
odd-affine output family with a dyadic input cylinder.  It also records the
important adversarial qualification to QM48: a zero new address digit leaves
the accumulated address unchanged, but it does not reset accumulated source
precision or manufacture a new independent tail.

For any fixed ordinary initial natural, once the accumulated bit precision
diverges, the remaining source quotient is eventually zero and all later
canonical extension digits must be zero.  Odd multiplication of the *current*
tail can route existing information, but it cannot evade this source budget.
-/

namespace KontoroC
namespace AffineSuccessorCylinder

/-- QM47 in division-free form.  The base coefficient identity automatically
extends to the entire successor cylinder. -/
theorem successor_balance (S P R D a b t : ℕ)
    (hbase : S + P * a = R + 2 ^ D * b) :
    S + P * (a + 2 ^ D * t) =
      R + 2 ^ D * (b + P * t) := by
  calc
    S + P * (a + 2 ^ D * t) =
        (S + P * a) + 2 ^ D * (P * t) := by ring
    _ = (R + 2 ^ D * b) + 2 ^ D * (P * t) := by rw [hbase]
    _ = R + 2 ^ D * (b + P * t) := by ring

/-- Prefix composition before any interpretation as a counter.  The source
tail has one new dyadic digit; the current tail keeps an odd affine payload. -/
theorem prefix_extension_balance
    (initialAddress initialBits currentOffset currentMultiplier : ℕ)
    (edgeAddress edgeBits digit residual tail : ℕ)
    (hintersection :
      currentOffset + currentMultiplier * digit =
        edgeAddress + 2 ^ edgeBits * residual) :
    currentOffset + currentMultiplier * (digit + 2 ^ edgeBits * tail) =
      edgeAddress + 2 ^ edgeBits * (residual + currentMultiplier * tail) ∧
    initialAddress + 2 ^ initialBits * (digit + 2 ^ edgeBits * tail) =
      (initialAddress + 2 ^ initialBits * digit) +
        2 ^ (initialBits + edgeBits) * tail := by
  constructor
  · calc
      currentOffset + currentMultiplier * (digit + 2 ^ edgeBits * tail) =
          (currentOffset + currentMultiplier * digit) +
            2 ^ edgeBits * (currentMultiplier * tail) := by ring
      _ = (edgeAddress + 2 ^ edgeBits * residual) +
            2 ^ edgeBits * (currentMultiplier * tail) := by rw [hintersection]
      _ = edgeAddress +
            2 ^ edgeBits * (residual + currentMultiplier * tail) := by ring
  · rw [pow_add]
    ring

/-- Honest content of a zero extension digit: the old initial address is
unchanged, while precision still increases and the current affine state still
updates.  No new free parameter is produced. -/
theorem zero_digit_extension
    (initialAddress initialBits currentOffset currentMultiplier : ℕ)
    (edgeAddress edgeBits residual tail : ℕ)
    (hintersection : currentOffset = edgeAddress + 2 ^ edgeBits * residual) :
    currentOffset + currentMultiplier * (2 ^ edgeBits * tail) =
      edgeAddress + 2 ^ edgeBits * (residual + currentMultiplier * tail) ∧
    initialAddress + 2 ^ initialBits * (2 ^ edgeBits * tail) =
      initialAddress + 2 ^ (initialBits + edgeBits) * tail := by
  constructor
  · rw [hintersection]
    ring
  · rw [pow_add]
    ring

/-- A fixed ordinary initial tail cannot retain a positive free quotient once
the accumulated source precision dominates the prefix index. -/
theorem sourceTail_eventually_zero
    (initial : ℕ) (address bits sourceTail : ℕ → ℕ)
    (hbits : ∀ n, n ≤ bits n)
    (hdecomp : ∀ n,
      initial = address n + 2 ^ bits n * sourceTail n) :
    ∃ K, ∀ n ≥ K, sourceTail n = 0 := by
  refine ⟨initial + 1, ?_⟩
  intro n hn
  by_contra hne
  have htail : 0 < sourceTail n := Nat.pos_of_ne_zero hne
  have hpow_le : 2 ^ bits n ≤ initial := by
    have hfactor : 2 ^ bits n ≤ 2 ^ bits n * sourceTail n := by
      simpa using Nat.mul_le_mul_left (2 ^ bits n) htail
    have h := hdecomp n
    omega
  have hpow_mono : 2 ^ n ≤ 2 ^ bits n :=
    pow_le_pow_right' (by omega) (hbits n)
  have hnlt : initial < n := by omega
  have hlarge : initial < 2 ^ bits n := by
    calc
      initial < n := hnlt
      _ < 2 ^ n := n.lt_two_pow_self
      _ ≤ 2 ^ bits n := hpow_mono
  omega

/-- If canonical prefix addresses are built from dyadic extension digits,
then every ordinary realization forces those digits eventually to vanish.
This is the direct compiler version of
`DyadicAffinePrefixSystem.extensionLifts_eventually_zero`. -/
theorem extensionDigit_eventually_zero
    (initial : ℕ) (address bits sourceTail digit : ℕ → ℕ)
    (hbits : ∀ n, n ≤ bits n)
    (hdecomp : ∀ n,
      initial = address n + 2 ^ bits n * sourceTail n)
    (hstep : ∀ n,
      address (n + 1) = address n + 2 ^ bits n * digit n) :
    ∃ K, ∀ n ≥ K, digit n = 0 := by
  obtain ⟨K, hzero⟩ :=
    sourceTail_eventually_zero initial address bits sourceTail hbits hdecomp
  refine ⟨K, ?_⟩
  intro n hn
  have haddr : address n = initial := by
    have h := hdecomp n
    rw [hzero n hn, mul_zero, add_zero] at h
    exact h.symm
  have haddrNext : address (n + 1) = initial := by
    have h := hdecomp (n + 1)
    rw [hzero (n + 1) (by omega), mul_zero, add_zero] at h
    exact h.symm
  have hs := hstep n
  rw [haddr, haddrNext] at hs
  have hprod : 2 ^ bits n * digit n = 0 := by omega
  exact (Nat.mul_eq_zero.mp hprod).resolve_left (by positivity)

/-- Operational no-go: arbitrarily late nonzero extension digits cannot be
funded by one ordinary natural, regardless of odd affine transformations of
the current tail. -/
theorem no_ordinary_source_of_frequently_nonzero_digits
    (address bits sourceTail digit : ℕ → ℕ)
    (hbits : ∀ n, n ≤ bits n)
    (hstep : ∀ n,
      address (n + 1) = address n + 2 ^ bits n * digit n)
    (hfrequent : ∀ K, ∃ n ≥ K, digit n ≠ 0) :
    ¬ ∃ initial, ∀ n,
      initial = address n + 2 ^ bits n * sourceTail n := by
  rintro ⟨initial, hdecomp⟩
  obtain ⟨K, hzero⟩ := extensionDigit_eventually_zero
    initial address bits sourceTail digit hbits hdecomp hstep
  obtain ⟨n, hn, hne⟩ := hfrequent K
  exact hne (hzero n hn)

end AffineSuccessorCylinder
end KontoroC

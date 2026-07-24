/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardMultiplicativeHolonomyNoGo
import KontoroC.KLMinusOneRail

/-!
# Nested literal all-odd replays can converge only to the 2-adic point -1

For every finite depth `L`, the positive natural `2^L - 1` executes exactly
`L` odd shortcut steps and ends at `3^L - 1`.  The seed residues are perfectly
compatible as `L` grows.  Nevertheless no single ordinary natural has all of
those residues: their inverse-limit address is `-1` in the 2-adics.

This supplies an exact countermodel to another tempting promotion.  Literal
finite replay, increasing arithmetic values, and compatible cylinders at
every depth do not imply one ordinary infinite seed.  The Archimedean
boundedness/eventual-constancy gate remains essential.
-/

namespace KontoroC
namespace OutwardNestedAllOddNoRoot

open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardInvariantBridge OutwardOddSlice OutwardWriterDecoderLiteral

/-- The depth-`L` representative of the nested all-odd cylinder. -/
def allOddSeed (L : ℕ) : ℕ := 2 ^ L - 1

/-- Exact execution of a finite all-odd word, with a general positive odd-rail
payload. -/
theorem executes_replicate_true {L t : ℕ} (ht : 0 < t) :
    Executes (List.replicate L true) (2 ^ L * t - 1) (3 ^ L * t - 1) := by
  induction L generalizing t with
  | zero => simp [Executes]
  | succ L ih =>
      rw [List.replicate_succ]
      simp only [Executes]
      let middle := 3 * 2 ^ L * t - 1
      refine ⟨middle, ?_, ?_⟩
      · simp only [if_true]
        let a := 2 ^ L * t
        have ha : 0 < a := Nat.mul_pos (by positivity) ht
        have hstart : 2 ^ (L + 1) * t - 1 = 2 * a - 1 := by
          dsimp only [a]
          rw [pow_succ]
          ring_nf
        have hmiddle : middle = 3 * a - 1 := by
          dsimp only [middle, a]
          ring_nf
        rw [hstart, hmiddle]
        omega
      · have htail := ih (t := 3 * t) (by positivity)
        simpa [middle, pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using htail

/-- Endpoint-sensitive block form: the exact first-passage word `[true]` is
executed `L` times. -/
theorem executesBlocksTo_allOddSeed (L : ℕ) :
    ExecutesBlocksTo (List.replicate L [true])
      (allOddSeed L) (3 ^ L - 1) := by
  apply executesBlocksTo_iff_flatten.mpr
  rw [flattenWords_replicate_singleton_true]
  simpa [allOddSeed] using
    (executes_replicate_true (L := L) (t := 1) (by omega))

/-- Every block in the finite replay is a genuine first-passage word. -/
theorem wordsIn_allOddSeed (L : ℕ) :
    WordsIn FirstPassageCode (List.replicate L [true]) := by
  intro word hword
  have hwordEq : word = [true] := by
    simpa using (List.eq_of_mem_replicate hword)
  subst word
  exact singleton_true_firstPassage

/-- Hence every positive finite depth has a literal first-passage realization
from its corresponding positive ordinary seed. -/
theorem realizesDepth_allOddSeed (L : ℕ) :
    RealizesDepth FirstPassageCode (L + 1) (allOddSeed (L + 1)) := by
  refine ⟨?_, List.replicate (L + 1) [true], by simp,
    wordsIn_allOddSeed (L + 1), ?_⟩
  · have hp : 1 < 2 ^ (L + 1) := Nat.one_lt_pow (by omega) (by omega)
    change 0 < 2 ^ (L + 1) - 1
    omega
  · exact (executesBlocksTo_allOddSeed (L + 1)).executesBlocks

/-- Consecutive depth representatives are compatible modulo the entire
earlier dyadic precision. -/
theorem allOddSeed_succ_modEq (L : ℕ) :
    allOddSeed (L + 1) ≡ allOddSeed L [MOD 2 ^ L] := by
  have heq : allOddSeed (L + 1) = 2 ^ L + allOddSeed L := by
    simp only [allOddSeed, pow_succ]
    omega
  rw [heq]
  simpa only [mul_one] using (Nat.ModEq.modulus_mul_add (m := 2 ^ L) (a := 1)
    (b := allOddSeed L))

/-- Matching the residue `-1 mod 2^L` already forces the ordinary number to
have size at least `2^L - 1`. -/
theorem allOddResidue_forces_scale {n L : ℕ}
    (hresidue : n % 2 ^ L = allOddSeed L) :
    2 ^ L ≤ n + 1 := by
  have hle := Nat.mod_le n (2 ^ L)
  rw [hresidue] at hle
  simp only [allOddSeed] at hle
  omega

/-- No ordinary natural realizes the compatible all-odd seed cylinder at
every depth. -/
theorem no_ordinary_allOdd_inverseLimit_root :
    ¬ ∃ n : ℕ, ∀ L : ℕ,
      n % 2 ^ (L + 1) = allOddSeed (L + 1) := by
  rintro ⟨n, hall⟩
  have hscale := allOddResidue_forces_scale (hall n)
  have hlarge : n + 1 < 2 ^ (n + 1) := Nat.lt_pow_self (by omega)
  omega

/-- Packaged separation theorem: exact literal realizations exist at every
finite depth and their seeds are nested, but no ordinary seed realizes the
whole tower. -/
theorem finite_literal_replay_and_compatibility_do_not_give_ordinary_root :
    (∀ L : ℕ,
      RealizesDepth FirstPassageCode (L + 1) (allOddSeed (L + 1))) ∧
    (∀ L : ℕ,
      allOddSeed (L + 1) ≡ allOddSeed L [MOD 2 ^ L]) ∧
    ¬ ∃ n : ℕ, ∀ L : ℕ,
      n % 2 ^ (L + 1) = allOddSeed (L + 1) := by
  exact ⟨realizesDepth_allOddSeed, allOddSeed_succ_modEq,
    no_ordinary_allOdd_inverseLimit_root⟩

end OutwardNestedAllOddNoRoot
end KontoroC

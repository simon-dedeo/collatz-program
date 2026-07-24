/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCanonicalRechargeCompleteness

/-!
# Canonical recharge tails after two finite histories meet

The canonical odd-charge recharge map is a partial function.  Consequently,
once two verified finite histories reach the same ordinary charge, all of
their future behavior is literally identical.  In particular, prepending a
long finite history to an already terminating tail can create a new
finite-depth record without supplying any new evidence about infinite
survival.

This module records the exact laws needed by deterministic recharge censuses:
`none` persists, first-undefined depths shift by the prefix length, and the
existence of an infinite canonical orbit is invariant under a verified finite
prefix.  These are semantic statements about the audited canonical map, not
statistical interpretations of a bounded scan.
-/

namespace KontoroC
namespace OutwardCanonicalTailMerger

open OutwardCanonicalRechargeCompleteness

/-- Failure after `m+n` steps is exactly failure in the prefix, or successful
arrival at a unique intermediate charge followed by suffix failure. -/
theorem canonicalRechargeIterate_add_eq_none_iff
    {m n H : ℕ} :
    canonicalRechargeIterate (m + n) H = none ↔
      canonicalRechargeIterate m H = none ∨
        ∃ J, canonicalRechargeIterate m H = some J ∧
          canonicalRechargeIterate n J = none := by
  rw [canonicalRechargeIterate_add]
  cases hprefix : canonicalRechargeIterate m H with
  | none => simp
  | some J => simp

/-- Once a canonical iterate is undefined, every later iterate is undefined. -/
theorem canonicalRechargeIterate_none_persists
    {m H : ℕ}
    (hnone : canonicalRechargeIterate m H = none) (n : ℕ) :
    canonicalRechargeIterate (m + n) H = none := by
  rw [canonicalRechargeIterate_add, hnone]
  rfl

/-- A verified prefix transports an undefined suffix back to the original
source. -/
theorem canonicalRechargeIterate_none_after_prefix
    {m n H J : ℕ}
    (hprefix : canonicalRechargeIterate m H = some J)
    (hsuffix : canonicalRechargeIterate n J = none) :
    canonicalRechargeIterate (m + n) H = none := by
  rw [canonicalRechargeIterate_add, hprefix]
  exact hsuffix

/-- Once two finite histories meet, all equally long future iterates agree,
including simultaneous undefinedness. -/
theorem canonicalRechargeIterate_eq_of_meeting
    {m n H K J : ℕ}
    (hleft : canonicalRechargeIterate m H = some J)
    (hright : canonicalRechargeIterate n K = some J)
    (r : ℕ) :
    canonicalRechargeIterate (m + r) H =
      canonicalRechargeIterate (n + r) K := by
  rw [canonicalRechargeIterate_add, canonicalRechargeIterate_add,
    hleft, hright]

/-- Defined survival for `r` more steps is unchanged by a verified prefix. -/
theorem exists_iterate_add_iff_after_prefix
    {m r H J : ℕ}
    (hprefix : canonicalRechargeIterate m H = some J) :
    (∃ K, canonicalRechargeIterate (m + r) H = some K) ↔
      ∃ K, canonicalRechargeIterate r J = some K := by
  rw [canonicalRechargeIterate_add, hprefix]
  simp

/-- The first depth at which a partial canonical computation is undefined. -/
def FirstUndefinedAt (depth H : ℕ) : Prop :=
  canonicalRechargeIterate depth H = none ∧
    ∀ r, r < depth → ∃ K, canonicalRechargeIterate r H = some K

/-- A successful prefix shifts the exact first-undefined depth by precisely
its length.  This is the exact record-depth accounting law for a census that
discovers a longer prehistory into a previously known terminating tail. -/
theorem firstUndefinedAt_add_iff_after_prefix
    {m r H J : ℕ}
    (hprefix : canonicalRechargeIterate m H = some J) :
    FirstUndefinedAt (m + r) H ↔ FirstUndefinedAt r J := by
  constructor
  · rintro ⟨htotalNone, htotalBefore⟩
    have hsuffixNone : canonicalRechargeIterate r J = none := by
      rw [canonicalRechargeIterate_add, hprefix] at htotalNone
      exact htotalNone
    refine ⟨hsuffixNone, ?_⟩
    intro q hqr
    obtain ⟨K, hK⟩ := htotalBefore (m + q) (by omega)
    rw [canonicalRechargeIterate_add, hprefix] at hK
    exact ⟨K, hK⟩
  · rintro ⟨hsuffixNone, hsuffixBefore⟩
    refine ⟨canonicalRechargeIterate_none_after_prefix
      hprefix hsuffixNone, ?_⟩
    intro q hq
    by_cases hqm : q < m
    · have hmdecomp : q + (m - q) = m := Nat.add_sub_of_le hqm.le
      have hprefix' :
          canonicalRechargeIterate (q + (m - q)) H = some J := by
        simpa [hmdecomp] using hprefix
      obtain ⟨K, hK, _⟩ :=
        canonicalRechargeIterate_prefix_of_add_eq_some hprefix'
      exact ⟨K, hK⟩
    · have hmq : m ≤ q := Nat.le_of_not_gt hqm
      let s := q - m
      have hslt : s < r := by
        dsimp [s]
        omega
      obtain ⟨K, hK⟩ := hsuffixBefore s hslt
      refine ⟨K, ?_⟩
      have hqeq : q = m + s := by
        dsimp [s]
        omega
      rw [hqeq, canonicalRechargeIterate_add, hprefix]
      exact hK

/-- A verified finite prehistory neither creates nor destroys an infinite
canonical future.  Thus a long record obtained solely by prepending history
has exactly the same infinite-survival status as the tail it reaches. -/
theorem hasInfiniteCanonicalOrbit_iff_after_prefix
    {m H J : ℕ}
    (hprefix : canonicalRechargeIterate m H = some J) :
    HasInfiniteCanonicalOrbit H ↔ HasInfiniteCanonicalOrbit J := by
  rw [canonicalOrbit_iff_all_iterates_defined,
    canonicalOrbit_iff_all_iterates_defined]
  constructor
  · intro hall r
    obtain ⟨K, hK⟩ := hall (m + r)
    rw [canonicalRechargeIterate_add, hprefix] at hK
    exact ⟨K, hK⟩
  · intro hall q
    by_cases hqm : q < m
    · have hmdecomp : q + (m - q) = m := Nat.add_sub_of_le hqm.le
      have hprefix' :
          canonicalRechargeIterate (q + (m - q)) H = some J := by
        simpa [hmdecomp] using hprefix
      obtain ⟨K, hK, _⟩ :=
        canonicalRechargeIterate_prefix_of_add_eq_some hprefix'
      exact ⟨K, hK⟩
    · have hmq : m ≤ q := Nat.le_of_not_gt hqm
      let r := q - m
      obtain ⟨K, hK⟩ := hall r
      refine ⟨K, ?_⟩
      have hqeq : q = m + r := by
        dsimp [r]
        omega
      rw [hqeq, canonicalRechargeIterate_add, hprefix]
      exact hK

/-- Meeting histories have the same infinite-survival status, regardless of
their different prefix lengths or starting charges. -/
theorem hasInfiniteCanonicalOrbit_iff_of_meeting
    {m n H K J : ℕ}
    (hleft : canonicalRechargeIterate m H = some J)
    (hright : canonicalRechargeIterate n K = some J) :
    HasInfiniteCanonicalOrbit H ↔ HasInfiniteCanonicalOrbit K := by
  exact (hasInfiniteCanonicalOrbit_iff_after_prefix hleft).trans
    (hasInfiniteCanonicalOrbit_iff_after_prefix hright).symm

end OutwardCanonicalTailMerger
end KontoroC

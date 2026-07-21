/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.FiniteCompiler

/-!
# The ordinary-integer gate for infinite programs

Every finite positive valuation word has a canonical ordinary seed in either
admissible class modulo six.  A compatible infinite tower need not represent
an ordinary natural number; generically it represents only a 2-adic integer.
This file makes the worker's stabilization diagnostic exact.
-/

namespace KontoroC

/-- The first `n` instructions of an infinite valuation stream. -/
def valuationPrefix (k : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map k

@[simp] theorem valuationPrefix_zero (k : ℕ → ℕ) :
    valuationPrefix k 0 = [] := by simp [valuationPrefix]

@[simp] theorem valuationPrefix_length (k : ℕ → ℕ) (n : ℕ) :
    (valuationPrefix k n).length = n := by simp [valuationPrefix]

theorem valuationPrefix_positive {k : ℕ → ℕ}
    (hk : ∀ i, 0 < k i) (n : ℕ) : PositiveWord (valuationPrefix k n) := by
  intro a ha
  simp only [valuationPrefix, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _hi, rfl⟩ := ha
  exact hk i

theorem valuationPrefix_totalValuation_ge {k : ℕ → ℕ}
    (hk : ∀ i, 0 < k i) (n : ℕ) :
    n ≤ totalValuation (valuationPrefix k n) := by
  have h := List.length_le_sum_of_one_le (valuationPrefix k n)
    (fun i hi ↦ (valuationPrefix_positive hk n) i hi)
  simpa [totalValuation] using h

theorem valuationPrefix_isPrefix (k : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    valuationPrefix k m <+: valuationPrefix k n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨(List.map (fun i ↦ k (m + i)) (List.range d)), ?_⟩
  simp [valuationPrefix, List.range_add, Function.comp_def]

theorem wordLegal_of_isPrefix {x : ℕ} {u v : List ℕ}
    (huv : u <+: v) (hv : WordLegal x v) : WordLegal x u := by
  obtain ⟨t, rfl⟩ := huv
  exact (wordLegal_append_iff x u t).mp hv |>.1

/-- An infinite instruction stream is literally realized by an ordinary seed
when every finite prefix is legal at that same seed. -/
def StreamLegal (x : ℕ) (k : ℕ → ℕ) : Prop :=
  ∀ n, WordLegal x (valuationPrefix k n)

/-- **Necessary integer gate.**  If one ordinary integer realizes every
prefix, then any canonical compiler representatives for those prefixes
eventually stabilize to that integer. -/
theorem canonical_seed_tower_eventually_eq
    {k c : ℕ → ℕ} {e x : ℕ}
    (hk : ∀ i, 0 < k i)
    (hxlegal : StreamLegal x k)
    (hxres : x % 6 = e)
    (hclt : ∀ n, c n < 6 * 2 ^ totalValuation (valuationPrefix k (n + 1)))
    (hcres : ∀ n, c n % 6 = e)
    (hclegal : ∀ n, WordLegal (c n) (valuationPrefix k (n + 1))) :
    ∃ N, ∀ n, N ≤ n → c n = x := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x (by norm_num : 1 < (2 : ℕ))
  refine ⟨N, fun n hn ↦ ?_⟩
  let w := valuationPrefix k (n + 1)
  have hw : w ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [w] at hlen
  have hpositive : PositiveWord w := valuationPrefix_positive hk _
  have hsum : N ≤ totalValuation w := by
    exact hn.trans (Nat.le_succ n) |>.trans (valuationPrefix_totalValuation_ge hk _)
  have hpow : 2 ^ N ≤ 2 ^ totalValuation w :=
    Nat.pow_le_pow_right (by omega) hsum
  have hxlt : x < 6 * 2 ^ totalValuation w := by
    exact hN.trans_le (hpow.trans (Nat.le_mul_of_pos_left _ (by omega)))
  have hmod6 : x ≡ c n [MOD 6] := hxres.trans (hcres n).symm
  have hmod := wordLegal_unique_mod_progression hw hpositive
    (hxlegal (n + 1)) (hclegal n) hmod6
  exact (hmod.eq_of_lt_of_lt hxlt (hclt n)).symm

/-- **Sufficient stabilization gate.**  If the exact prefix representatives
eventually equal one ordinary integer, that integer realizes the whole stream.
This direction needs no compactness or 2-adic argument. -/
theorem streamLegal_of_canonical_seed_tower_eventually_eq
    {k c : ℕ → ℕ} {x : ℕ}
    (hclegal : ∀ n, WordLegal (c n) (valuationPrefix k (n + 1)))
    (hstable : ∃ N, ∀ n, N ≤ n → c n = x) :
    StreamLegal x k := by
  obtain ⟨N, hN⟩ := hstable
  intro m
  let n := max N m
  have hn : N ≤ n := le_max_left _ _
  have hm : m ≤ n + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  have hlegal := hclegal n
  rw [hN n hn] at hlegal
  exact wordLegal_of_isPrefix (valuationPrefix_isPrefix k hm) hlegal

/-- For the compiler's canonical representatives, stabilization is exactly
the ordinary-natural realization criterion (within the selected class modulo
six). -/
theorem streamLegal_iff_canonical_seed_tower_stabilizes
    {k c : ℕ → ℕ} {e x : ℕ}
    (hk : ∀ i, 0 < k i)
    (hxres : x % 6 = e)
    (hclt : ∀ n, c n < 6 * 2 ^ totalValuation (valuationPrefix k (n + 1)))
    (hcres : ∀ n, c n % 6 = e)
    (hclegal : ∀ n, WordLegal (c n) (valuationPrefix k (n + 1))) :
    StreamLegal x k ↔ ∃ N, ∀ n, N ≤ n → c n = x := by
  constructor
  · intro hx
    exact canonical_seed_tower_eventually_eq hk hx hxres hclt hcres hclegal
  · exact streamLegal_of_canonical_seed_tower_eventually_eq hclegal

end KontoroC

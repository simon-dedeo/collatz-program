/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CollatzComponentHolonomy

/-!
# The component-holonomy bar

An ordinary positive integer cannot be the least element of its Syracuse
component if it is a non-leftmost member of an affine collision fiber.  Such
a fiber therefore deletes an entire binary cylinder from the possible
component minima.

This file packages the exact full-proof reduction suggested by that fact.  A
family of collision shadows which bars every positive ordinary integer other
than `1` proves that every positive integer merges with `1`.  The intended
infinite construction may leave the all-one 2-adic ray (`-1`) unbarred: every
positive natural has an eventually-zero binary expansion and so is a
different kind of boundary point.

The reduction and the first three shadow cylinders are kernel-checked here.
Existence of the complete bar is the open mathematical theorem.
-/

namespace KontoroC
namespace ComponentHolonomyBar

open CleanLean.Collatz
open CollatzComponentHolonomy

/-- A positive integer is the least positive point of its Syracuse
component. -/
def ComponentMinimum (m : ℕ) : Prop :=
  0 < m ∧ ∀ x : ℕ, 0 < x → Merge x m → m ≤ x

theorem componentMinimum_one : ComponentMinimum 1 := by
  refine ⟨by omega, ?_⟩
  intro x hx _
  omega

/-- Any explicitly smaller point in the same component excludes minimality. -/
theorem not_componentMinimum_of_smaller_merge {x m : ℕ}
    (hx : 0 < x) (hxm : Merge x m) (hlt : x < m) :
    ¬ ComponentMinimum m := by
  intro hm
  exact (Nat.not_le_of_lt hlt) (hm.2 x hx hxm)

/-- A component minimum cannot be the right member of a collision, even when
the two routes have different lengths. -/
theorem right_sibling_excludes_minimum {left right : ℕ}
    (hleft : 0 < left) (hlt : left < right)
    {i j : ℕ}
    (hcollision : syracuseStep^[i] left = syracuseStep^[j] right) :
    ¬ ComponentMinimum right := by
  apply not_componentMinimum_of_smaller_merge hleft _ hlt
  exact ⟨i, j, hcollision⟩

/-- A symbolic collision shadow.  For every tail `k`, the right affine source
`2^width*k+right` merges with the smaller source obtained by subtracting
`drop`.  The positivity hypotheses make the shadow valid even at `k=0`. -/
structure CollisionShadow where
  width : ℕ
  right : ℕ
  drop : ℕ
  leftSteps : ℕ
  rightSteps : ℕ
  right_lt : right < 2 ^ width
  drop_pos : 0 < drop
  drop_lt : drop < right
  collision : ∀ k : ℕ,
    syracuseStep^[leftSteps] (2 ^ width * k + (right - drop)) =
      syracuseStep^[rightSteps] (2 ^ width * k + right)

/-- Pull a collision shadow back through the odd Syracuse branch.  Restricting
the old tail to `k=3*h+c` makes both old sources `2 mod 3`; their odd
predecessors form a new binary cylinder of width one greater.  This is the
first symbolic shadow-production rule, and the division by `3` is the
multiplier-specific arithmetic absent from a parity-only argument. -/
def CollisionShadow.oddPullback (s : CollisionShadow) (c : ℕ) (hc : c < 3)
    (hleftMod :
      (2 ^ s.width * c + (s.right - s.drop)) % 3 = 2)
    (hrightMod : (2 ^ s.width * c + s.right) % 3 = 2) :
    CollisionShadow := by
  let leftBase := 2 ^ s.width * c + (s.right - s.drop)
  let rightBase := 2 ^ s.width * c + s.right
  let qLeft := leftBase / 3
  let qRight := rightBase / 3
  have hleftDecomp : leftBase = 3 * qLeft + 2 := by
    have h := Nat.mod_add_div leftBase 3
    dsimp [qLeft]
    omega
  have hrightDecomp : rightBase = 3 * qRight + 2 := by
    have h := Nat.mod_add_div rightBase 3
    dsimp [qRight]
    omega
  have hbaseLt : leftBase < rightBase := by
    dsimp [leftBase, rightBase]
    exact Nat.add_lt_add_left
      (Nat.sub_lt (Nat.zero_lt_of_lt s.drop_lt) s.drop_pos) _
  have hqLt : qLeft < qRight := by omega
  let newRight := 2 * qRight + 1
  let newDrop := 2 * (qRight - qLeft)
  have hrightBaseLt : rightBase < 3 * 2 ^ s.width := by
    dsimp [rightBase]
    have hcLe : c + 1 ≤ 3 := by omega
    have hsum : 2 ^ s.width * c + s.right <
        2 ^ s.width * c + 2 ^ s.width :=
      Nat.add_lt_add_left s.right_lt _
    calc
      2 ^ s.width * c + s.right <
          2 ^ s.width * c + 2 ^ s.width := hsum
      _ = 2 ^ s.width * (c + 1) := by ring
      _ ≤ 2 ^ s.width * 3 := Nat.mul_le_mul_left _ hcLe
      _ = 3 * 2 ^ s.width := by ring
  have hqRightLt : qRight < 2 ^ s.width := by omega
  have hnewRightLt : newRight < 2 ^ (s.width + 1) := by
    dsimp [newRight]
    rw [pow_succ]
    omega
  have hnewDropPos : 0 < newDrop := by
    dsimp [newDrop]
    omega
  have hnewDropLt : newDrop < newRight := by
    dsimp [newDrop, newRight]
    omega
  have hrightSub : newRight - newDrop = 2 * qLeft + 1 := by
    dsimp [newRight, newDrop]
    omega
  refine
    { width := s.width + 1
      right := newRight
      drop := newDrop
      leftSteps := s.leftSteps + 1
      rightSteps := s.rightSteps + 1
      right_lt := hnewRightLt
      drop_pos := hnewDropPos
      drop_lt := hnewDropLt
      collision := ?_ }
  intro h
  have hleftStep :
      syracuseStep (2 ^ (s.width + 1) * h + (newRight - newDrop)) =
        2 ^ s.width * (3 * h + c) + (s.right - s.drop) := by
    rw [hrightSub]
    have hsource :
        2 ^ (s.width + 1) * h + (2 * qLeft + 1) =
          2 * (2 ^ s.width * h + qLeft) + 1 := by
      rw [pow_succ]
      ring
    rw [hsource, syracuseStep_two_mul_add_one]
    dsimp [leftBase] at hleftDecomp
    calc
      3 * (2 ^ s.width * h + qLeft) + 2 =
          3 * 2 ^ s.width * h + (3 * qLeft + 2) := by ring
      _ = 3 * 2 ^ s.width * h +
          (2 ^ s.width * c + (s.right - s.drop)) := by
            rw [hleftDecomp]
      _ = 2 ^ s.width * (3 * h + c) + (s.right - s.drop) := by
            ring
  have hrightStep :
      syracuseStep (2 ^ (s.width + 1) * h + newRight) =
        2 ^ s.width * (3 * h + c) + s.right := by
    have hsource :
        2 ^ (s.width + 1) * h + newRight =
          2 * (2 ^ s.width * h + qRight) + 1 := by
      dsimp [newRight]
      rw [pow_succ]
      ring
    rw [hsource, syracuseStep_two_mul_add_one]
    dsimp [rightBase] at hrightDecomp
    calc
      3 * (2 ^ s.width * h + qRight) + 2 =
          3 * 2 ^ s.width * h + (3 * qRight + 2) := by ring
      _ = 3 * 2 ^ s.width * h + (2 ^ s.width * c + s.right) := by
            rw [hrightDecomp]
      _ = 2 ^ s.width * (3 * h + c) + s.right := by ring
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
    hleftStep, hrightStep]
  exact s.collision (3 * h + c)

/-- Membership in the binary cylinder cut out by a collision shadow. -/
def CollisionShadow.Covers (s : CollisionShadow) (n : ℕ) : Prop :=
  n % 2 ^ s.width = s.right

theorem CollisionShadow.decompose {s : CollisionShadow} {n : ℕ}
    (hcover : s.Covers n) :
    n = 2 ^ s.width * (n / 2 ^ s.width) + s.right := by
  have hmodPos : 0 < 2 ^ s.width := by positivity
  calc
    n = n % 2 ^ s.width + 2 ^ s.width * (n / 2 ^ s.width) :=
      (Nat.mod_add_div n (2 ^ s.width)).symm
    _ = 2 ^ s.width * (n / 2 ^ s.width) + s.right := by
      rw [hcover]
      omega

/-- Every point covered by a collision shadow has a strictly smaller positive
point in its component. -/
theorem CollisionShadow.descent {s : CollisionShadow} {n : ℕ}
    (hcover : s.Covers n) :
    ∃ x : ℕ, 0 < x ∧ x < n ∧ Merge x n := by
  let k := n / 2 ^ s.width
  let x := 2 ^ s.width * k + (s.right - s.drop)
  have hn : n = 2 ^ s.width * k + s.right := by
    simpa [k] using s.decompose hcover
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.add_pos_right _ (Nat.sub_pos_of_lt s.drop_lt)
  have hxLt : x < n := by
    dsimp [x]
    rw [hn]
    exact Nat.add_lt_add_left
      (Nat.sub_lt (Nat.zero_lt_of_lt s.drop_lt) s.drop_pos) _
  have hmerge : Merge x n := by
    refine ⟨s.leftSteps, s.rightSteps, ?_⟩
    dsimp [x]
    rw [hn]
    exact s.collision k
  exact ⟨x, hxPos, hxLt, hmerge⟩

theorem CollisionShadow.excludes_minimum {s : CollisionShadow} {n : ℕ}
    (hcover : s.Covers n) : ¬ ComponentMinimum n := by
  obtain ⟨x, hx, hlt, hmerge⟩ := s.descent hcover
  exact not_componentMinimum_of_smaller_merge hx hmerge hlt

/-- Every positive component has a least positive member. -/
theorem exists_componentMinimum {n : ℕ} (hn : 0 < n) :
    ∃ m : ℕ, ComponentMinimum m ∧ Merge m n := by
  classical
  let P : ℕ → Prop := fun x => 0 < x ∧ Merge x n
  have hex : ∃ x, P x := ⟨n, hn, merge_refl n⟩
  let m := Nat.find hex
  have hmP : P m := Nat.find_spec hex
  have hmLeast : ∀ x, P x → m ≤ x := by
    intro x hx
    exact Nat.find_min' hex hx
  refine ⟨m, ⟨hmP.1, ?_⟩, hmP.2⟩
  intro x hx hxm
  apply hmLeast x
  exact ⟨hx, merge_trans hxm hmP.2⟩

/-- A family of collision shadows is an ordinary holonomy bar when it covers
every positive natural other than `1`.  This asks only for eventually-zero
binary rays, not for the all-one 2-adic point. -/
def OrdinaryHolonomyBar {ι : Type} (shadow : ι → CollisionShadow) : Prop :=
  ∀ n : ℕ, 1 < n → ∃ a : ι, (shadow a).Covers n

/-- The full-proof reduction: an ordinary holonomy bar forces every positive
Syracuse component to be the component of `1`. -/
theorem merge_one_of_ordinaryHolonomyBar {ι : Type}
    (shadow : ι → CollisionShadow)
    (hbar : OrdinaryHolonomyBar shadow) {n : ℕ} (hn : 0 < n) :
    Merge n 1 := by
  obtain ⟨m, hm, hmn⟩ := exists_componentMinimum hn
  have hmOne : m = 1 := by
    by_contra hne
    have hmNeZero : m ≠ 0 := Nat.ne_of_gt hm.1
    have hmGt : 1 < m := by omega
    obtain ⟨a, ha⟩ := hbar m hmGt
    exact (shadow a).excludes_minimum ha hm
  rw [hmOne] at hmn
  exact merge_symm hmn

/-- The first collision deletes the odd cylinder `5 mod 8` from component
minima. -/
def shadow_five_mod_eight : CollisionShadow where
  width := 3
  right := 5
  drop := 1
  leftSteps := 3
  rightSteps := 3
  right_lt := by norm_num
  drop_pos := by norm_num
  drop_lt := by norm_num
  collision := by
    intro k
    simpa using (adjacent_pair_hits_mod_three_two k).1.trans
      (adjacent_pair_hits_mod_three_two k).2.symm

/-- The five-way fiber deletes `99 mod 256`. -/
def shadow_ninety_nine_mod_256 : CollisionShadow where
  width := 8
  right := 99
  drop := 1
  leftSteps := 8
  rightSteps := 8
  right_lt := by norm_num
  drop_pos := by norm_num
  drop_lt := by norm_num
  collision := by
    intro k
    exact (five_run_hits k 0 (by norm_num)).trans
      (five_run_hits k 1 (by norm_num)).symm

/-- The same fiber deletes `101 mod 256`, with the leftmost sibling three
units below. -/
def shadow_one_hundred_one_mod_256 : CollisionShadow where
  width := 8
  right := 101
  drop := 3
  leftSteps := 8
  rightSteps := 8
  right_lt := by norm_num
  drop_pos := by norm_num
  drop_lt := by norm_num
  collision := by
    intro k
    exact (five_run_hits k 0 (by norm_num)).trans
      (five_run_hits k 3 (by norm_num)).symm

/-- The first generated rather than independently discovered shadow: odd
pullback of `101 mod 256` along the tail class `0 mod 3`. -/
def shadow_sixty_seven_mod_512 : CollisionShadow :=
  shadow_one_hundred_one_mod_256.oddPullback 0 (by norm_num)
    (by change (2 ^ 8 * 0 + (101 - 3)) % 3 = 2; norm_num)
    (by change (2 ^ 8 * 0 + 101) % 3 = 2; norm_num)

theorem shadow_sixty_seven_parameters :
    shadow_sixty_seven_mod_512.width = 9 ∧
      shadow_sixty_seven_mod_512.right = 67 ∧
      shadow_sixty_seven_mod_512.drop = 2 := by
  norm_num [shadow_sixty_seven_mod_512, CollisionShadow.oddPullback,
    shadow_one_hundred_one_mod_256]

theorem minimum_not_five_mod_eight {m : ℕ} (hm : ComponentMinimum m) :
    m % 8 ≠ 5 := by
  intro h
  exact shadow_five_mod_eight.excludes_minimum h hm

theorem minimum_not_ninety_nine_mod_256 {m : ℕ}
    (hm : ComponentMinimum m) : m % 256 ≠ 99 := by
  intro h
  exact shadow_ninety_nine_mod_256.excludes_minimum h hm

theorem minimum_not_one_hundred_one_mod_256 {m : ℕ}
    (hm : ComponentMinimum m) : m % 256 ≠ 101 := by
  intro h
  exact shadow_one_hundred_one_mod_256.excludes_minimum h hm

theorem minimum_not_sixty_seven_mod_512 {m : ℕ}
    (hm : ComponentMinimum m) : m % 512 ≠ 67 := by
  intro h
  exact shadow_sixty_seven_mod_512.excludes_minimum h hm

end ComponentHolonomyBar
end KontoroC

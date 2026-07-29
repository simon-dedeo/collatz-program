/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ComponentHolonomyCondensedBoundary
import KontoroC.OutwardCodeCounterexample

/-!
# The arithmetic descent atlas

Binary cylinders alone forget an essential Archimedean datum.  If one point
of a parity cylinder has dropped, affine continuation gives descent on the
*ray above that point*, not necessarily on the smaller representatives of the
same `2`-adic cylinder.  The correct local object therefore combines a
profinite progression with an Archimedean initial point.

An `AffineDescentRay` gives two affine rays.  Every source point merges with
the corresponding, strictly smaller positive mate.  Rays restrict along
finite-index tail maps, giving the elementary presheaf operation on the
arithmetic `(2,3)`-adic cylinder site.  Existing constant-gap collision
shadows and ordinary forward stopping-time drops both produce rays.

The global atlas condition is proved equivalent to the Syracuse conjecture.
This is an exact reformulation and interface, not a proof of the atlas.
-/

namespace KontoroC
namespace ComponentDescentAtlas

open CleanLean.Collatz
open CollatzComponentHolonomy ComponentHolonomyBar
open ShortcutParityPeriodicNoGo OutwardCodeCompactness
  OutwardCodeCounterexample

/-- A proof-carrying affine ray of strict component descent. -/
structure AffineDescentRay where
  sourceBase : ℕ
  sourceStep : ℕ
  mateBase : ℕ
  mateStep : ℕ
  leftSteps : ℕ
  rightSteps : ℕ
  sourceBase_pos : 0 < sourceBase
  sourceStep_pos : 0 < sourceStep
  mateBase_pos : 0 < mateBase
  mateBase_lt : mateBase < sourceBase
  mateStep_le : mateStep ≤ sourceStep
  collision : ∀ k : ℕ,
    syracuseStep^[leftSteps] (mateBase + mateStep * k) =
      syracuseStep^[rightSteps] (sourceBase + sourceStep * k)

namespace AffineDescentRay

def source (r : AffineDescentRay) (k : ℕ) : ℕ :=
  r.sourceBase + r.sourceStep * k

def mate (r : AffineDescentRay) (k : ℕ) : ℕ :=
  r.mateBase + r.mateStep * k

def Covers (r : AffineDescentRay) (n : ℕ) : Prop :=
  ∃ k : ℕ, n = r.source k

theorem mate_pos (r : AffineDescentRay) (k : ℕ) : 0 < r.mate k := by
  exact Nat.add_pos_left r.mateBase_pos _

theorem mate_lt_source (r : AffineDescentRay) (k : ℕ) :
    r.mate k < r.source k := by
  exact Nat.add_lt_add_of_lt_of_le r.mateBase_lt
    (Nat.mul_le_mul_right k r.mateStep_le)

theorem merge_mate_source (r : AffineDescentRay) (k : ℕ) :
    Merge (r.mate k) (r.source k) := by
  exact ⟨r.leftSteps, r.rightSteps, r.collision k⟩

theorem descent {r : AffineDescentRay} {n : ℕ} (hcover : r.Covers n) :
    ∃ x : ℕ, 0 < x ∧ x < n ∧ Merge x n := by
  obtain ⟨k, rfl⟩ := hcover
  exact ⟨r.mate k, r.mate_pos k, r.mate_lt_source k,
    r.merge_mate_source k⟩

/-- Presheaf restriction along the tail embedding `k |-> digit + factor*k`.
The source and mate progressions are restricted simultaneously. -/
def restrict (r : AffineDescentRay) (factor digit : ℕ)
    (hfactor : 0 < factor) : AffineDescentRay where
  sourceBase := r.source digit
  sourceStep := r.sourceStep * factor
  mateBase := r.mate digit
  mateStep := r.mateStep * factor
  leftSteps := r.leftSteps
  rightSteps := r.rightSteps
  sourceBase_pos := Nat.add_pos_left r.sourceBase_pos _
  sourceStep_pos := Nat.mul_pos r.sourceStep_pos hfactor
  mateBase_pos := r.mate_pos digit
  mateBase_lt := r.mate_lt_source digit
  mateStep_le := Nat.mul_le_mul_right factor r.mateStep_le
  collision := by
    intro k
    have h := r.collision (digit + factor * k)
    convert h using 1 <;> congr 1 <;> simp [source, mate] <;> ring

theorem restrict_source (r : AffineDescentRay) (factor digit : ℕ)
    (hfactor : 0 < factor) (k : ℕ) :
    (r.restrict factor digit hfactor).source k =
      r.source (digit + factor * k) := by
  simp [restrict, source]
  ring

theorem restrict_mate (r : AffineDescentRay) (factor digit : ℕ)
    (hfactor : 0 < factor) (k : ℕ) :
    (r.restrict factor digit hfactor).mate k =
      r.mate (digit + factor * k) := by
  simp [restrict, mate]
  ring

theorem covers_of_restrict_covers {r : AffineDescentRay}
    {factor digit n : ℕ} {hfactor : 0 < factor}
    (h : (r.restrict factor digit hfactor).Covers n) : r.Covers n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨digit + factor * k, hk.trans
    (r.restrict_source factor digit hfactor k)⟩

end AffineDescentRay

/-- A descent atlas covers every ordinary positive integer above `1`. -/
def ArithmeticDescentAtlas (ray : ι → AffineDescentRay) : Prop :=
  ∀ n : ℕ, 1 < n → ∃ a : ι, (ray a).Covers n

/-- Any arithmetic descent atlas forces every positive integer into the
component of `1`, by strong induction on the ordinary Archimedean order. -/
theorem merge_one_of_arithmeticDescentAtlas {ray : ι → AffineDescentRay}
    (hatlas : ArithmeticDescentAtlas ray) :
    ∀ n : ℕ, 0 < n → Merge n 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hone : n = 1
      · subst n
        exact merge_refl 1
      · have hgt : 1 < n := by omega
        obtain ⟨a, ha⟩ := hatlas n hgt
        obtain ⟨x, hx, hxn, hmerge⟩ := (ray a).descent ha
        exact merge_trans (merge_symm hmerge) (ih x hxn hx)

/-- Every point on the orbit of `1` is either `1` or `2`. -/
theorem iterate_one_eq_one_or_two :
    ∀ j : ℕ, syracuseStep^[j] 1 = 1 ∨ syracuseStep^[j] 1 = 2 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]
        right
        norm_num [syracuseStep]
      · rw [h]
        left
        norm_num [syracuseStep]

theorem syracuseReachesOne_of_merge_one {n : ℕ} (h : Merge n 1) :
    SyracuseReachesOne n := by
  obtain ⟨i, j, hij⟩ := h
  rcases iterate_one_eq_one_or_two j with hj | hj
  · exact ⟨i, hij.trans hj⟩
  · refine ⟨i + 1, ?_⟩
    rw [Function.iterate_succ_apply', hij, hj]
    norm_num [syracuseStep]

theorem syracuseConjecture_of_arithmeticDescentAtlas
    {ray : ι → AffineDescentRay}
    (hatlas : ArithmeticDescentAtlas ray) : SyracuseConjecture := by
  intro n hn
  exact syracuseReachesOne_of_merge_one
    (merge_one_of_arithmeticDescentAtlas hatlas n hn)

/-- Existing constant-gap holonomy shadows are special affine descent rays. -/
def ofCollisionShadow (s : CollisionShadow) : AffineDescentRay where
  sourceBase := s.right
  sourceStep := 2 ^ s.width
  mateBase := s.right - s.drop
  mateStep := 2 ^ s.width
  leftSteps := s.leftSteps
  rightSteps := s.rightSteps
  sourceBase_pos := Nat.zero_lt_of_lt s.drop_lt
  sourceStep_pos := by positivity
  mateBase_pos := Nat.sub_pos_of_lt s.drop_lt
  mateBase_lt := Nat.sub_lt (Nat.zero_lt_of_lt s.drop_lt) s.drop_pos
  mateStep_le := le_rfl
  collision := by
    intro k
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using s.collision k

theorem ofCollisionShadow_covers {s : CollisionShadow} {n : ℕ}
    (h : s.Covers n) : (ofCollisionShadow s).Covers n := by
  refine ⟨n / 2 ^ s.width, ?_⟩
  rw [AffineDescentRay.source, ofCollisionShadow]
  simpa [Nat.add_comm] using s.decompose h

/-- Any literal parity-word execution which has already dropped produces an
entire affine descent ray.  The multiplier inequality is automatic: an
expanding homogeneous coefficient is incompatible with a smaller endpoint
because the affine defect is nonnegative. -/
def ofForwardDrop (w : List Bool) {start finish : ℕ}
    (hstart : 0 < start) (hfinish : 0 < finish)
    (hdrop : finish < start) (hexec : Executes w start finish) :
    AffineDescentRay := by
  let sourceStep := 2 ^ w.length
  let mateStep := 3 ^ w.count true
  have hstepLt : mateStep < sourceStep := by
    have hexact := program_exact w hexec
    rw [programData_S, programData_O] at hexact
    dsimp [sourceStep, mateStep]
    by_contra hnot
    have hle : 2 ^ w.length ≤ 3 ^ w.count true := by omega
    have hleft : 2 ^ w.length * finish < 2 ^ w.length * start :=
      Nat.mul_lt_mul_of_pos_left hdrop (by positivity)
    have hmiddle : 2 ^ w.length * start ≤
        3 ^ w.count true * start := Nat.mul_le_mul_right start hle
    have hright : 3 ^ w.count true * start ≤
        3 ^ w.count true * start + (programData w).A := Nat.le_add_right _ _
    omega
  refine
    { sourceBase := start
      sourceStep := sourceStep
      mateBase := finish
      mateStep := mateStep
      leftSteps := 0
      rightSteps := w.length
      sourceBase_pos := hstart
      sourceStep_pos := by dsimp [sourceStep]; positivity
      mateBase_pos := hfinish
      mateBase_lt := hdrop
      mateStep_le := hstepLt.le
      collision := ?_ }
  intro k
  have hshift := executes_shift w hexec k
  have hsem := executes_eq_syracuse_iterate w hshift
  simpa [sourceStep, mateStep] using hsem

/-- An explicit mixed `(2,3)`-arithmetic chart: every `6k+5` has the smaller
odd predecessor `4k+3` in its component. -/
def fiveModSixRay : AffineDescentRay where
  sourceBase := 5
  sourceStep := 6
  mateBase := 3
  mateStep := 4
  leftSteps := 1
  rightSteps := 0
  sourceBase_pos := by norm_num
  sourceStep_pos := by norm_num
  mateBase_pos := by norm_num
  mateBase_lt := by norm_num
  mateStep_le := by norm_num
  collision := by
    intro k
    change syracuseStep (3 + 4 * k) = 5 + 6 * k
    have hodd : (3 + 4 * k) % 2 ≠ 0 := by omega
    simp [syracuseStep, hodd]
    omega

/-- The ordinary even descent chart. -/
def evenRay : AffineDescentRay where
  sourceBase := 2
  sourceStep := 2
  mateBase := 1
  mateStep := 1
  leftSteps := 0
  rightSteps := 1
  sourceBase_pos := by norm_num
  sourceStep_pos := by norm_num
  mateBase_pos := by norm_num
  mateBase_lt := by norm_num
  mateStep_le := by norm_num
  collision := by
    intro k
    simp only [Function.iterate_zero_apply, Function.iterate_one]
    simp only [one_mul]
    have heven : (2 + 2 * k) % 2 = 0 := by omega
    simp [syracuseStep, heven]
    omega

/-- A natural has a strict positive forward Syracuse drop. -/
def HasForwardDrop (n : ℕ) : Prop :=
  ∃ length : ℕ, 0 < syracuseStep^[length] n ∧
    syracuseStep^[length] n < n

/-- Total stopping is equivalent to the Syracuse conjecture. -/
theorem syracuseConjecture_iff_forwardDrops :
    SyracuseConjecture ↔ ∀ n : ℕ, 1 < n → HasForwardDrop n := by
  constructor
  · intro h n hn
    obtain ⟨length, hlength⟩ := h n (by omega)
    exact ⟨length, by rw [hlength]; omega, by rw [hlength]; omega⟩
  · intro hdrops n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases hone : n = 1
        · subst n
          exact ⟨0, rfl⟩
        · have hgt : 1 < n := by omega
          obtain ⟨length, hpos, hlt⟩ := hdrops n hgt
          obtain ⟨tail, htail⟩ := ih (syracuseStep^[length] n) hlt hpos
          refine ⟨tail + length, ?_⟩
          rw [Function.iterate_add_apply, htail]

/-- The literal parity word written by the first `length` Syracuse steps. -/
def orbitWord : (start length : ℕ) → List Bool
  | _, 0 => []
  | start, length + 1 =>
      decide (start % 2 ≠ 0) :: orbitWord (syracuseStep start) length

@[simp] theorem orbitWord_length (start length : ℕ) :
    (orbitWord start length).length = length := by
  induction length generalizing start with
  | zero => rfl
  | succ length ih => simp [orbitWord, ih]

theorem orbitWord_executes (start length : ℕ) :
    Executes (orbitWord start length) start (syracuseStep^[length] start) := by
  induction length generalizing start with
  | zero => simp [orbitWord, Executes]
  | succ length ih =>
      simp only [orbitWord, Executes]
      refine ⟨syracuseStep start, ?_, ?_⟩
      · by_cases heven : start % 2 = 0
        · simp [heven, syracuseStep]
          omega
        · simp [heven, syracuseStep]
          have hodd : start % 2 = 1 := by omega
          omega
      · simpa [Function.iterate_succ_apply] using
          ih (syracuseStep start)

/-- Every strict forward drop canonically supplies a descent ray covering its
starting integer. -/
theorem exists_ray_of_forwardDrop {n : ℕ} (hn : 0 < n)
    (hdrop : HasForwardDrop n) :
    ∃ r : AffineDescentRay, r.Covers n := by
  obtain ⟨length, hfinish, hlt⟩ := hdrop
  let w := orbitWord n length
  let r := ofForwardDrop w hn hfinish hlt (orbitWord_executes n length)
  refine ⟨r, 0, ?_⟩
  change n =
    (ofForwardDrop w hn hfinish hlt (orbitWord_executes n length)).sourceBase +
      (ofForwardDrop w hn hfinish hlt (orbitWord_executes n length)).sourceStep * 0
  simp [ofForwardDrop]

/-- Exact endpoint: Collatz is equivalent to existence of an arithmetic
descent atlas.  The forward implication uses stopping-time rays; the reverse
implication permits the more general holonomy/component rays. -/
theorem exists_arithmeticDescentAtlas_iff_syracuseConjecture :
    (∃ ι : Type, ∃ ray : ι → AffineDescentRay,
      ArithmeticDescentAtlas ray) ↔ SyracuseConjecture := by
  constructor
  · rintro ⟨ι, ray, hatlas⟩
    exact syracuseConjecture_of_arithmeticDescentAtlas hatlas
  · intro hcollatz
    let ι := {n : ℕ // 1 < n}
    have hdrops : ∀ n : ℕ, 1 < n → HasForwardDrop n :=
      syracuseConjecture_iff_forwardDrops.mp hcollatz
    let ray : ι → AffineDescentRay := fun n =>
      Classical.choose (exists_ray_of_forwardDrop (by omega) (hdrops n n.property))
    refine ⟨ι, ray, ?_⟩
    intro n hn
    let a : ι := ⟨n, hn⟩
    refine ⟨a, ?_⟩
    exact Classical.choose_spec
      (exists_ray_of_forwardDrop (n := n) (by omega) (hdrops n hn))

end ComponentDescentAtlas
end KontoroC

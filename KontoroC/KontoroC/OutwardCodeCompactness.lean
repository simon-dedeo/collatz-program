/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardFirstPassage
import KontoroC.KLControllerReset
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite-window compactness for outward parity codes

This file formalizes the mass-to-ordinary-atom gate in QM155d.  The theorem
is deterministic and finitary: probability and Kraft mass do not occur.
-/

namespace KontoroC
namespace OutwardCodeCompactness

open ShortcutParityPeriodicNoGo

noncomputable section

def BoundedRange (f : ℕ → ℕ) : Prop := ∃ B, ∀ n, f n ≤ B

def EventuallyConstant (f : ℕ → ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → f n = f N

/-- A bounded monotone natural sequence is eventually constant.  The proof
uses infinite pigeonhole in the finite window rather than an analytic limit. -/
theorem eventuallyConstant_iff_boundedRange_of_monotone
    {f : ℕ → ℕ} (hf : Monotone f) :
    EventuallyConstant f ↔ BoundedRange f := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · exact (hN n hn).le
  · rintro ⟨B, hB⟩
    let bounded : ℕ → {x : ℕ // x ≤ B} := fun n => ⟨f n, hB n⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber bounded
    have hyset : (bounded ⁻¹' {y} : Set ℕ).Infinite :=
      Set.infinite_coe_iff.mp hy
    obtain ⟨N, hN⟩ := hyset.nonempty
    have hfN : bounded N = y := by simpa using hN
    refine ⟨N, fun n hNn => ?_⟩
    obtain ⟨k, hk, hnk⟩ := hyset.exists_gt n
    have hfk : bounded k = y := by simpa using hk
    apply le_antisymm
    · calc
        f n ≤ f k := hf hnk.le
        _ = f N := by
          exact congrArg Subtype.val (hfk.trans hfN.symm)
    · exact hf hNn

section Nested

variable (P : ℕ → ℕ → Prop) (h_nonempty : ∀ n, ∃ x, P n x)

noncomputable def leastWitness (n : ℕ) : ℕ := by
  classical
  exact Nat.find (h_nonempty n)

theorem leastWitness_spec (n : ℕ) : P n (leastWitness P h_nonempty n) :=
  by
    classical
    exact Nat.find_spec (h_nonempty n)

theorem leastWitness_le {n x : ℕ} (hx : P n x) :
    leastWitness P h_nonempty n ≤ x :=
  by
    classical
    exact Nat.find_min' (h_nonempty n) hx

variable (h_nested : ∀ n x, P (n + 1) x → P n x)
include h_nested

theorem nested_of_le {n k x : ℕ} (hnk : n ≤ k) (hk : P k x) : P n x := by
  induction k, hnk using Nat.le_induction with
  | base => exact hk
  | succ k hnk ih => exact ih (h_nested k x hk)

/-- QM156b in the form stated by the construction worker.  If every member
of a decreasing family of predicates has a witness in one fixed finite
window, then one ordinary natural witnesses every member simultaneously. -/
theorem finiteWindow_nested (B : ℕ)
    (h_window : ∀ n, ∃ x, x ≤ B ∧ P n x) :
    ∃ x, x ≤ B ∧ ∀ n, P n x := by
  let chosen : ℕ → {x : ℕ // x ≤ B} := fun n =>
    ⟨(h_window n).choose, (h_window n).choose_spec.1⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber chosen
  have hyset : (chosen ⁻¹' {y} : Set ℕ).Infinite :=
    Set.infinite_coe_iff.mp hy
  refine ⟨y.1, y.2, fun n => ?_⟩
  obtain ⟨k, hk, hnk⟩ := hyset.exists_gt n
  have hchosen : chosen k = y := by simpa using hk
  have hPk : P k y.1 := by
    have hs := (h_window k).choose_spec.2
    simpa [chosen] using hchosen ▸ hs
  exact nested_of_le P h_nested hnk.le hPk

theorem leastWitness_mono : Monotone (leastWitness P h_nonempty) := by
  apply monotone_nat_of_le_succ
  intro n
  apply leastWitness_le P h_nonempty
  exact h_nested n _ (leastWitness_spec P h_nonempty (n + 1))

/-- Compactness in a finite natural window: bounded least witnesses are
equivalent to one ordinary witness surviving every finite depth. -/
theorem exists_all_iff_bounded_least :
    (∃ x, ∀ n, P n x) ↔ BoundedRange (leastWitness P h_nonempty) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun n => leastWitness_le P h_nonempty (hx n)⟩
  · rintro ⟨B, hB⟩
    let bounded : ℕ → {x : ℕ // x ≤ B} :=
      fun n => ⟨leastWitness P h_nonempty n, hB n⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber bounded
    have hyset : (bounded ⁻¹' {y} : Set ℕ).Infinite :=
      Set.infinite_coe_iff.mp hy
    refine ⟨y.1, fun n => ?_⟩
    obtain ⟨k, hk, hnk⟩ := hyset.exists_gt n
    have hfk : bounded k = y := by simpa using hk
    have hPk : P k y.1 := by
      have hs := leastWitness_spec P h_nonempty k
      simpa [bounded] using hfk ▸ hs
    exact nested_of_le P h_nested hnk.le hPk

theorem exists_all_iff_eventuallyConstant_least :
    (∃ x, ∀ n, P n x) ↔ EventuallyConstant (leastWitness P h_nonempty) := by
  rw [eventuallyConstant_iff_boundedRange_of_monotone
    (leastWitness_mono P h_nonempty h_nested)]
  exact exists_all_iff_bounded_least P h_nonempty h_nested

end Nested

/-! ## Literal shortcut-code realization predicate -/

def ExecutesBlocks : List (List Bool) → ℕ → Prop
  | [], _ => True
  | w :: ws, start =>
      ∃ middle, Executes w start middle ∧ ExecutesBlocks ws middle

def WordsIn (C : Set (List Bool)) (ws : List (List Bool)) : Prop :=
  ∀ w ∈ ws, w ∈ C

def RealizesDepth (C : Set (List Bool)) (n start : ℕ) : Prop :=
  0 < start ∧ ∃ ws : List (List Bool),
    ws.length = n ∧ WordsIn C ws ∧ ExecutesBlocks ws start

def InfiniteExecution (C : Set (List Bool)) (start : ℕ) : Prop :=
  ∀ n, RealizesDepth C n start

theorem executes_append (u v : List Bool) {start finish : ℕ} :
    Executes (u ++ v) start finish ↔
      ∃ middle, Executes u start middle ∧ Executes v middle finish := by
  induction u generalizing start with
  | nil => simp [Executes]
  | cons odd u ih =>
      simp only [List.cons_append, Executes]
      constructor
      · rintro ⟨next, hstep, htail⟩
        obtain ⟨middle, hu, hv⟩ := ih.mp htail
        exact ⟨middle, ⟨next, hstep, hu⟩, hv⟩
      · rintro ⟨middle, ⟨next, hstep, hu⟩, hv⟩
        exact ⟨next, hstep, ih.mpr ⟨middle, hu, hv⟩⟩

/-- Translating the initial point by its parity-cylinder modulus translates
the endpoint by the corresponding ternary multiplier. -/
theorem executes_shift (w : List Bool) {start finish : ℕ}
    (h : Executes w start finish) (k : ℕ) :
    Executes w (start + 2 ^ w.length * k)
      (finish + 3 ^ w.count true * k) := by
  induction w generalizing start finish k with
  | nil =>
      simp only [List.length_nil, List.count_nil, pow_zero, one_mul,
        Executes] at h ⊢
      omega
  | cons odd w ih =>
      obtain ⟨middle, hstep, htail⟩ := h
      cases odd with
      | false =>
          simp only [List.length_cons, List.count_cons, Bool.false_eq_true,
            ↓reduceIte, Executes] at hstep ⊢
          refine ⟨middle + 2 ^ w.length * k, ?_, ?_⟩
          · rw [pow_succ]
            ring_nf at hstep ⊢
            omega
          · simpa using ih htail k
      | true =>
          simp only [List.length_cons, List.count_cons, ↓reduceIte,
            Executes] at hstep ⊢
          refine ⟨middle + 2 ^ w.length * (3 * k), ?_, ?_⟩
          · rw [pow_succ]
            ring_nf at hstep ⊢
            omega
          · have hshift := ih htail (3 * k)
            convert hshift using 1 <;> simp [pow_succ] <;> ring

/-- Every finite shortcut parity word has a positive ordinary realization.
This is the exact dyadic-cylinder existence fact needed to make the minimum
in QM155d unconditional for nonempty codes. -/
theorem exists_positive_executes (w : List Bool) :
    ∃ start finish : ℕ, 0 < start ∧ Executes w start finish := by
  induction w with
  | nil => exact ⟨1, 1, by omega, rfl⟩
  | cons odd w ih =>
      obtain ⟨middle, finish, hmiddle, htail⟩ := ih
      cases odd with
      | false =>
          exact ⟨2 * middle, finish, by positivity,
            ⟨middle, by simp, htail⟩⟩
      | true =>
          have hcop : (2 ^ w.length).Coprime 3 :=
            (by norm_num : Nat.Coprime 2 3).pow_left _
          obtain ⟨k, hk⟩ := KLControllerReset.exists_affine_modEq_of_coprime
            (2 ^ w.length) middle 2 3 (by omega) hcop
          let middle' := middle + 2 ^ w.length * k
          have hmiddleMod : middle' % 3 = 2 := by
            change (2 ^ w.length * k + middle) % 3 = 2 % 3 at hk
            change middle' % 3 = 2 % 3
            simpa [middle', Nat.add_comm] using hk
          have hmiddle' : 0 < middle' := by
            dsimp [middle']
            omega
          have hnumPos : 0 < 2 * middle' - 1 := by omega
          have hnumDiv : 3 ∣ 2 * middle' - 1 := by
            rw [Nat.dvd_iff_mod_eq_zero]
            omega
          let start := (2 * middle' - 1) / 3
          have hquot : 3 * start = 2 * middle' - 1 := by
            dsimp [start]
            exact Nat.mul_div_cancel' hnumDiv
          have hstart : 0 < start := by
            have hthree : 3 ≤ 2 * middle' - 1 := Nat.le_of_dvd hnumPos hnumDiv
            dsimp [start]
            exact Nat.div_pos hthree (by omega)
          let finish' := finish + 3 ^ w.count true * k
          have htail' : Executes w middle' finish' := by
            dsimp [middle', finish']
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              executes_shift w htail k
          refine ⟨start, finish', hstart, ⟨middle', ?_, htail'⟩⟩
          simp only [ite_true]
          omega

theorem executesBlocks_iff (ws : List (List Bool)) (start : ℕ) :
    ExecutesBlocks ws start ↔
      ∃ finish, Executes (ShortcutParityPeriodicNoGo.flattenWords ws)
        start finish := by
  induction ws generalizing start with
  | nil => simp [ExecutesBlocks, ShortcutParityPeriodicNoGo.flattenWords, Executes]
  | cons w ws ih =>
      simp only [ExecutesBlocks, ShortcutParityPeriodicNoGo.flattenWords]
      constructor
      · rintro ⟨middle, hw, hrest⟩
        obtain ⟨finish, hfinish⟩ := (ih middle).mp hrest
        exact ⟨finish, (executes_append w _).mpr ⟨middle, hw, hfinish⟩⟩
      · rintro ⟨finish, hfinish⟩
        obtain ⟨middle, hw, hrest⟩ := (executes_append w _).mp hfinish
        exact ⟨middle, hw, (ih middle).mpr ⟨finish, hrest⟩⟩

theorem executesBlocks_append_left {u v : List (List Bool)} {start : ℕ}
    (h : ExecutesBlocks (u ++ v) start) : ExecutesBlocks u start := by
  induction u generalizing start with
  | nil => trivial
  | cons w ws ih =>
      simp only [List.cons_append, ExecutesBlocks] at h ⊢
      obtain ⟨middle, hw, hrest⟩ := h
      exact ⟨middle, hw, ih hrest⟩

theorem executesBlocks_prefix {u v : List (List Bool)} {start : ℕ}
    (huv : u <+: v) (h : ExecutesBlocks v start) : ExecutesBlocks u start := by
  obtain ⟨tail, rfl⟩ := huv
  exact executesBlocks_append_left h

theorem realizesDepth_nested (C : Set (List Bool)) (n start : ℕ)
    (h : RealizesDepth C (n + 1) start) : RealizesDepth C n start := by
  obtain ⟨hstart, ws, hlen, hcode, hexec⟩ := h
  refine ⟨hstart, ws.take n, ?_, ?_, ?_⟩
  · simp [List.length_take, hlen]
  · intro w hw
    exact hcode w (List.mem_of_mem_take hw)
  · exact executesBlocks_prefix (List.take_prefix n ws) hexec

theorem finiteDepth_of_nonempty {C : Set (List Bool)} (hC : C.Nonempty) :
    ∀ n, ∃ start, RealizesDepth C n start := by
  obtain ⟨w, hw⟩ := hC
  intro n
  let ws := List.replicate n w
  obtain ⟨start, finish, hstart, hexec⟩ :=
    exists_positive_executes
      (ShortcutParityPeriodicNoGo.flattenWords ws)
  refine ⟨start, hstart, ws, ?_, ?_, ?_⟩
  · simp [ws]
  · intro u hu
    have : u = w := by
      change u ∈ List.replicate n w at hu
      exact (List.mem_replicate.mp hu).2
    simpa [this] using hw
  · exact (executesBlocks_iff ws start).mpr ⟨finish, hexec⟩

variable (C : Set (List Bool))
    (h_finite_depth : ∀ n, ∃ start, RealizesDepth C n start)

noncomputable def minimumStart (n : ℕ) : ℕ :=
  leastWitness (RealizesDepth C) h_finite_depth n

theorem minimumStart_mono : Monotone (minimumStart C h_finite_depth) :=
  leastWitness_mono (RealizesDepth C) h_finite_depth (realizesDepth_nested C)

/-- QM155d at the exact shortcut execution predicate. -/
theorem infiniteExecution_iff_bounded_minimum :
    (∃ start, InfiniteExecution C start) ↔
      BoundedRange (minimumStart C h_finite_depth) := by
  exact exists_all_iff_bounded_least
    (RealizesDepth C) h_finite_depth (realizesDepth_nested C)

/-- The second equivalence in QM155d. -/
theorem infiniteExecution_iff_eventuallyConstant_minimum :
    (∃ start, InfiniteExecution C start) ↔
      EventuallyConstant (minimumStart C h_finite_depth) := by
  exact exists_all_iff_eventuallyConstant_least
    (RealizesDepth C) h_finite_depth (realizesDepth_nested C)

/-- Canonical minimum for a nonempty code; finite-depth realizability is now
discharged by the exact dyadic-cylinder construction above. -/
noncomputable def canonicalMinimumStart
    (C : Set (List Bool)) (hC : C.Nonempty) (n : ℕ) : ℕ :=
  minimumStart C (finiteDepth_of_nonempty hC) n

theorem canonicalMinimumStart_mono
    (C : Set (List Bool)) (hC : C.Nonempty) :
    Monotone (canonicalMinimumStart C hC) :=
  minimumStart_mono C (finiteDepth_of_nonempty hC)

/-- QM155d without an auxiliary finite-realizability premise.  Finiteness,
prefix-freeness, and outwardness are needed by the later code/mass and growth
consumers, but not by this compactness equivalence itself. -/
theorem infiniteExecution_iff_bounded_canonicalMinimum
    (C : Set (List Bool)) (hC : C.Nonempty) :
    (∃ start, InfiniteExecution C start) ↔
      BoundedRange (canonicalMinimumStart C hC) :=
  infiniteExecution_iff_bounded_minimum C (finiteDepth_of_nonempty hC)

theorem infiniteExecution_iff_eventuallyConstant_canonicalMinimum
    (C : Set (List Bool)) (hC : C.Nonempty) :
    (∃ start, InfiniteExecution C start) ↔
      EventuallyConstant (canonicalMinimumStart C hC) :=
  infiniteExecution_iff_eventuallyConstant_minimum C
    (finiteDepth_of_nonempty hC)

theorem boundedRange_iff_eventuallyConstant_canonicalMinimum
    (C : Set (List Bool)) (hC : C.Nonempty) :
    BoundedRange (canonicalMinimumStart C hC) ↔
      EventuallyConstant (canonicalMinimumStart C hC) := by
  exact (infiniteExecution_iff_bounded_canonicalMinimum C hC).symm.trans
    (infiniteExecution_iff_eventuallyConstant_canonicalMinimum C hC)

end

end OutwardCodeCompactness
end KontoroC

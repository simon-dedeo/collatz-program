/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.Defs

/-!
# Exact valuation words

A list `[k₁, ..., k_N]` is legal at `x` when it records the exact two-adic
valuations encountered by the fully accelerated odd orbit.  The offset below
is the `A_N` in

`2^(k₁+...+k_N) T^N(x) = 3^N x + A_N`.
-/

namespace KontoroC

/-- Execute a finite instruction word, checking no legality. -/
def runWord : ℕ → List ℕ → ℕ
  | x, [] => x
  | x, _k :: ks => runWord (oddStep x) ks

/-- Exact valuation legality along the generated orbit. -/
def WordLegal : ℕ → List ℕ → Prop
  | _x, [] => True
  | x, k :: ks => LegalInstruction x k ∧ WordLegal (oddStep x) ks

instance wordLegalDecidable : ∀ x ks, Decidable (WordLegal x ks)
  | _x, [] => isTrue trivial
  | x, k :: ks =>
      @instDecidableAnd (LegalInstruction x k) (WordLegal (oddStep x) ks)
        (inferInstanceAs (Decidable (LegalInstruction x k)))
        (wordLegalDecidable (oddStep x) ks)

/-- Total exponent of two removed by a word. -/
def totalValuation (ks : List ℕ) : ℕ := ks.sum

/-- Affine offset attached to a valuation word.  This head recursion is
definitionally equal to
`sum_{j<N} 3^(N-1-j) * 2^(k₁+...+k_j)`. -/
def affineOffset : List ℕ → ℕ
  | [] => 0
  | k :: ks => 3 ^ ks.length + 2 ^ k * affineOffset ks

@[simp] theorem runWord_nil (x : ℕ) : runWord x [] = x := rfl

@[simp] theorem runWord_cons (x k : ℕ) (ks : List ℕ) :
    runWord x (k :: ks) = runWord (oddStep x) ks := rfl

@[simp] theorem totalValuation_nil : totalValuation [] = 0 := rfl

@[simp] theorem totalValuation_cons (k : ℕ) (ks : List ℕ) :
    totalValuation (k :: ks) = k + totalValuation ks := by
  simp [totalValuation]

@[simp] theorem affineOffset_nil : affineOffset [] = 0 := rfl

@[simp] theorem affineOffset_cons (k : ℕ) (ks : List ℕ) :
    affineOffset (k :: ks) = 3 ^ ks.length + 2 ^ k * affineOffset ks := rfl

theorem wordLegal_tail {x k : ℕ} {ks : List ℕ}
    (h : WordLegal x (k :: ks)) : WordLegal (oddStep x) ks := h.2

theorem wordLegal_head {x k : ℕ} {ks : List ℕ}
    (h : WordLegal x (k :: ks)) : LegalInstruction x k := h.1

theorem wordLegal_runWord_pos {x : ℕ} {ks : List ℕ}
    (hx : 0 < x) (h : WordLegal x ks) : 0 < runWord x ks := by
  induction ks generalizing x with
  | nil => simpa
  | cons k ks ih =>
      exact ih (oddStep_pos x) h.2

theorem runWord_append (x : ℕ) (u v : List ℕ) :
    runWord x (u ++ v) = runWord (runWord x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons k u ih => exact ih (oddStep x)

theorem wordLegal_append_iff (x : ℕ) (u v : List ℕ) :
    WordLegal x (u ++ v) ↔
      WordLegal x u ∧ WordLegal (runWord x u) v := by
  induction u generalizing x with
  | nil => simp [WordLegal]
  | cons k u ih =>
      simp only [List.cons_append, WordLegal, runWord_cons]
      rw [ih]
      tauto

theorem totalValuation_append (u v : List ℕ) :
    totalValuation (u ++ v) = totalValuation u + totalValuation v := by
  simp [totalValuation]

/-- Concatenation law used by compressed valuation-word search. -/
theorem affineOffset_append (u v : List ℕ) :
    affineOffset (u ++ v) =
      3 ^ v.length * affineOffset u +
        2 ^ totalValuation u * affineOffset v := by
  induction u with
  | nil => simp
  | cons k u ih =>
      rw [List.cons_append, affineOffset_cons, affineOffset_cons, ih,
        totalValuation_cons, Nat.pow_add, List.length_append, Nat.pow_add]
      ring

/-- The exact finite Kontorovich--Sinai affine identity. -/
theorem valuationWord_affine_identity {x : ℕ} {ks : List ℕ}
    (h : WordLegal x ks) :
    2 ^ totalValuation ks * runWord x ks =
      3 ^ ks.length * x + affineOffset ks := by
  induction ks generalizing x with
  | nil => simp
  | cons k ks ih =>
      have hstep : 2 ^ k * oddStep x = 3 * x + 1 :=
        legalInstruction_step_equation h.1
      have htail := ih h.2
      rw [totalValuation_cons, Nat.pow_add, runWord_cons, affineOffset_cons,
        List.length_cons, Nat.pow_succ]
      calc
        (2 ^ k * 2 ^ totalValuation ks) * runWord (oddStep x) ks =
            2 ^ k * (2 ^ totalValuation ks * runWord (oddStep x) ks) := by
              ac_rfl
        _ = 2 ^ k * (3 ^ ks.length * oddStep x + affineOffset ks) := by
              rw [htail]
        _ = 3 ^ ks.length * (2 ^ k * oddStep x) +
              2 ^ k * affineOffset ks := by ring
        _ = 3 ^ ks.length * (3 * x + 1) +
              2 ^ k * affineOffset ks := by rw [hstep]
        _ = (3 ^ ks.length * 3) * x +
              (3 ^ ks.length + 2 ^ k * affineOffset ks) := by ring

/-- A closing legal word satisfies the standard cycle divisibility equation. -/
theorem cycle_denominator_mul_seed {x : ℕ} {ks : List ℕ}
    (hx : 0 < x) (hlegal : WordLegal x ks) (hclose : runWord x ks = x) :
    (2 ^ totalValuation ks - 3 ^ ks.length) * x = affineOffset ks := by
  have hid := valuationWord_affine_identity hlegal
  rw [hclose] at hid
  have hle : 3 ^ ks.length ≤ 2 ^ totalValuation ks := by
    nlinarith [Nat.zero_le (affineOffset ks)]
  rw [Nat.sub_mul]
  omega

/-- Conversely, the affine cycle equation forces closure once legality and
the nonnegative denominator direction have been checked. -/
theorem runWord_eq_of_cycle_equation {x : ℕ} {ks : List ℕ}
    (hlegal : WordLegal x ks)
    (hle : 3 ^ ks.length ≤ 2 ^ totalValuation ks)
    (heq : (2 ^ totalValuation ks - 3 ^ ks.length) * x = affineOffset ks) :
    runWord x ks = x := by
  have hid := valuationWord_affine_identity hlegal
  have hsum : 3 ^ ks.length +
      (2 ^ totalValuation ks - 3 ^ ks.length) = 2 ^ totalValuation ks :=
    Nat.add_sub_of_le hle
  have hrhs : 3 ^ ks.length * x + affineOffset ks =
      2 ^ totalValuation ks * x := by
    rw [← heq, ← Nat.add_mul, hsum]
  rw [hrhs] at hid
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hid

end KontoroC

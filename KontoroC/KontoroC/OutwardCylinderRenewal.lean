/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardBoundaryRenewal

/-!
# Exact dyadic-to-triadic parity cylinders

This file proves QM158a.  The forward affine-family law was already present
as `executes_shift`; the important new direction peels a dyadic source lift
off a literal execution and obtains the corresponding triadic target lift.
-/

namespace KontoroC
namespace OutwardCylinderRenewal

open ShortcutParityPeriodicNoGo OutwardCodeCompactness

/-- Reverse of `executes_shift`: a source lift by its complete parity-cylinder
modulus can be peeled off any literal execution. -/
theorem executes_unshift (w : List Bool) {start finish k : ℕ}
    (h : Executes w (start + 2 ^ w.length * k) finish) :
    ∃ baseFinish,
      Executes w start baseFinish ∧
      finish = baseFinish + 3 ^ w.count true * k := by
  induction w generalizing start finish k with
  | nil =>
      simp only [List.length_nil, pow_zero, one_mul, List.count_nil, Executes] at h ⊢
      exact ⟨start, rfl, h⟩
  | cons b w ih =>
      obtain ⟨middle, hstep, htail⟩ := h
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          simp only [List.length_cons] at hstep
          have hpow : 2 ^ (w.length + 1) * k =
              2 * (2 ^ w.length * k) := by simp [pow_succ]; ring
          rw [hpow] at hstep
          let baseMiddle := middle - 2 ^ w.length * k
          have hle : 2 ^ w.length * k ≤ middle := by omega
          have hmiddle : middle = baseMiddle + 2 ^ w.length * k := by
            dsimp [baseMiddle]
            omega
          have hbaseStep : 2 * baseMiddle = start := by omega
          obtain ⟨baseFinish, hbaseTail, hfinish⟩ :=
            ih (start := baseMiddle) (finish := finish) (k := k) <| by
              simpa [hmiddle] using htail
          refine ⟨baseFinish, ?_, ?_⟩
          · exact ⟨baseMiddle, by simpa using hbaseStep, hbaseTail⟩
          · simpa using hfinish
      | true =>
          simp only [↓reduceIte] at hstep
          simp only [List.length_cons] at hstep
          have hpow : 2 ^ (w.length + 1) * k =
              2 * (2 ^ w.length * k) := by simp [pow_succ]; ring
          rw [hpow] at hstep
          let shift := 2 ^ w.length * (3 * k)
          let baseMiddle := middle - shift
          have hshift : 2 * shift = 3 * (2 * (2 ^ w.length * k)) := by
            dsimp [shift]
            ring
          have hle : shift ≤ middle := by omega
          have hmiddle : middle = baseMiddle + shift := by
            dsimp [baseMiddle]
            omega
          have hbaseStep : 2 * baseMiddle = 3 * start + 1 := by omega
          obtain ⟨baseFinish, hbaseTail, hfinish⟩ :=
            ih (start := baseMiddle) (finish := finish) (k := 3 * k) <| by
              simpa [shift, hmiddle] using htail
          refine ⟨baseFinish, ?_, ?_⟩
          · exact ⟨baseMiddle, by simpa using hbaseStep, hbaseTail⟩
          · rw [hfinish]
            norm_num [List.count_cons, pow_succ]
            ring

/-- Every literal execution has a unique affine-family decomposition whose
source coordinate lies in the canonical dyadic interval. -/
theorem execution_decompose_source (w : List Bool) {source target : ℕ}
    (h : Executes w source target) :
    ∃ r b t,
      r < 2 ^ w.length ∧
      source = r + 2 ^ w.length * t ∧
      Executes w r b ∧
      target = b + 3 ^ w.count true * t := by
  let modulus := 2 ^ w.length
  let r := source % modulus
  let t := source / modulus
  have hmodPos : 0 < modulus := by positivity
  have hr : r < modulus := Nat.mod_lt _ hmodPos
  have hsource : source = r + modulus * t := by
    dsimp [r, t, modulus]
    exact (Nat.mod_add_div source (2 ^ w.length)).symm
  obtain ⟨b, hb, htarget⟩ := executes_unshift w <| by
    rw [← hsource]
    exact h
  exact ⟨r, b, t, hr, hsource, hb, htarget⟩

/-- Two starts realizing the same parity word are congruent modulo its full
dyadic cylinder modulus. -/
theorem executes_source_modEq (w : List Bool)
    {x x' y y' : ℕ} (h : Executes w x y) (h' : Executes w x' y') :
    x ≡ x' [MOD 2 ^ w.length] := by
  induction w generalizing x x' with
  | nil => simp only [List.length_nil, pow_zero, Nat.ModEq, Nat.mod_one]
  | cons b w ih =>
      obtain ⟨m, hs, ht⟩ := h
      obtain ⟨m', hs', ht'⟩ := h'
      have hm := ih ht ht'
      have htwice : 2 * m ≡ 2 * m' [MOD 2 ^ (b :: w).length] := by
        have := hm.mul_left' 2
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hs hs'
          simpa [hs, hs'] using htwice
      | true =>
          simp only [↓reduceIte] at hs hs'
          have hadd : 3 * x + 1 ≡ 3 * x' + 1 [MOD 2 ^ (true :: w).length] := by
            simpa [hs, hs'] using htwice
          have hthree : 3 * x ≡ 3 * x' [MOD 2 ^ (true :: w).length] :=
            Nat.ModEq.add_right_cancel' 1 hadd
          have hcop : Nat.Coprime (2 ^ (true :: w).length) 3 :=
            Nat.Coprime.pow_left _ (by norm_num)
          exact hthree.cancel_left_of_coprime hcop.gcd_eq_one

/-- A source in the canonical dyadic interval always lands in the canonical
triadic interval.  This is the nontrivial target-range clause of QM158a. -/
theorem target_lt_threePow_of_source_lt_twoPow (w : List Bool)
    {source target : ℕ} (h : Executes w source target)
    (hsource : source < 2 ^ w.length) :
    target < 3 ^ w.count true := by
  induction w generalizing source target with
  | nil =>
      simp only [Executes] at h
      subst target
      norm_num at hsource ⊢
      exact hsource
  | cons bit w ih =>
      obtain ⟨middle, hstep, htail⟩ := h
      cases bit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          have hsource' : source < 2 * 2 ^ w.length := by
            simpa [pow_succ, mul_comm] using hsource
          have hmiddle : middle < 2 ^ w.length := by omega
          simpa using ih htail hmiddle
      | true =>
          simp only [↓reduceIte] at hstep
          have hsource' : source < 2 * 2 ^ w.length := by
            simpa [pow_succ, mul_comm] using hsource
          have hmiddle : middle < 3 * 2 ^ w.length := by omega
          let modulus := 2 ^ w.length
          let r := middle % modulus
          let t := middle / modulus
          have hmodPos : 0 < modulus := by positivity
          have hr : r < modulus := Nat.mod_lt _ hmodPos
          have hmiddleEq : middle = r + modulus * t := by
            dsimp [r, t, modulus]
            exact (Nat.mod_add_div middle (2 ^ w.length)).symm
          have ht : t < 3 := by
            dsimp [t, modulus]
            apply (Nat.div_lt_iff_lt_mul hmodPos).2
            simpa [mul_comm] using hmiddle
          obtain ⟨baseTarget, hbase, htarget⟩ :=
            executes_unshift w (start := r) (finish := target) (k := t) <| by
              rw [← hmiddleEq]
              exact htail
          have hb : baseTarget < 3 ^ w.count true := ih hbase hr
          rw [htarget]
          simp only [List.count_cons]
          norm_num
          rw [pow_succ]
          have ht2 : t ≤ 2 := by omega
          have hmul := Nat.mul_le_mul_left (3 ^ w.count true) ht2
          nlinarith

theorem executes_target_unique (w : List Bool) {source y y' : ℕ}
    (h : Executes w source y) (h' : Executes w source y') : y = y' := by
  have he := program_exact w h
  have he' := program_exact w h'
  have hmul : 2 ^ (programData w).S * y =
      2 ^ (programData w).S * y' := he.trans he'.symm
  exact Nat.mul_left_cancel (by positivity : 0 < 2 ^ (programData w).S) hmul

/-- Every word has exactly one canonical source/target residue pair. -/
theorem exists_unique_canonical_execution (w : List Bool) :
    ∃! p : ℕ × ℕ,
      p.1 < 2 ^ w.length ∧ p.2 < 3 ^ w.count true ∧
        Executes w p.1 p.2 := by
  obtain ⟨source, target, _, hexec⟩ := exists_positive_executes w
  obtain ⟨r, b, t, hr, _, hrb, _⟩ := execution_decompose_source w hexec
  have hb := target_lt_threePow_of_source_lt_twoPow w hrb hr
  refine ⟨(r, b), ⟨hr, hb, hrb⟩, ?_⟩
  intro p hp
  have hmod := executes_source_modEq w hp.2.2 hrb
  have hsource : p.1 = r := hmod.eq_of_lt_of_lt hp.1 hr
  subst hsource
  have htarget : p.2 = b := executes_target_unique w hp.2.2 hrb
  exact Prod.ext rfl htarget

noncomputable def canonicalExecution (w : List Bool) : ℕ × ℕ :=
  Classical.choose (exists_unique_canonical_execution w)

theorem canonicalExecution_spec (w : List Bool) :
    (canonicalExecution w).1 < 2 ^ w.length ∧
      (canonicalExecution w).2 < 3 ^ w.count true ∧
      Executes w (canonicalExecution w).1 (canonicalExecution w).2 :=
  (Classical.choose_spec (exists_unique_canonical_execution w)).1

theorem canonicalExecution_unique (w : List Bool) (p : ℕ × ℕ)
    (hp : p.1 < 2 ^ w.length ∧ p.2 < 3 ^ w.count true ∧
      Executes w p.1 p.2) :
    p = canonicalExecution w :=
  (Classical.choose_spec (exists_unique_canonical_execution w)).2 p hp

/-- Full affine-family characterization in QM158a. -/
theorem executes_iff_canonical_family (w : List Bool) {source target : ℕ} :
    Executes w source target ↔
      ∃ t : ℕ,
        source = (canonicalExecution w).1 + 2 ^ w.length * t ∧
        target = (canonicalExecution w).2 + 3 ^ w.count true * t := by
  constructor
  · intro h
    obtain ⟨r, b, t, hr, hsource, hrb, htarget⟩ :=
      execution_decompose_source w h
    have hb := target_lt_threePow_of_source_lt_twoPow w hrb hr
    have huniq := canonicalExecution_unique w (r, b) ⟨hr, hb, hrb⟩
    have hrEq : r = (canonicalExecution w).1 := congrArg Prod.fst huniq
    have hbEq : b = (canonicalExecution w).2 := congrArg Prod.snd huniq
    exact ⟨t, by simpa [hrEq] using hsource, by simpa [hbEq] using htarget⟩
  · rintro ⟨t, rfl, rfl⟩
    exact executes_shift w (canonicalExecution_spec w).2.2 t

/-- Exact affine equation for the canonical pair. -/
theorem canonical_affine_identity (w : List Bool) :
    2 ^ w.length * (canonicalExecution w).2 =
      3 ^ w.count true * (canonicalExecution w).1 + (programData w).A := by
  simpa only [programData_S, programData_O] using
    program_exact w (canonicalExecution_spec w).2.2

end OutwardCylinderRenewal
end KontoroC

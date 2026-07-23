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

/-- QM159a, reusable form: if the canonical source fails a desired extension
property, every execution of the same prefix which has that property must
use a strictly positive cylinder lift. -/
theorem positive_lift_of_canonical_fails
    (w : List Bool) (P : ℕ → Prop) {source target : ℕ}
    (hexec : Executes w source target)
    (hsource : P source) (hcanonical : ¬P (canonicalExecution w).1) :
    ∃ ell : ℕ, 0 < ell ∧
      source = (canonicalExecution w).1 + 2 ^ w.length * ell := by
  obtain ⟨ell, hsourceEq, _⟩ := (executes_iff_canonical_family w).1 hexec
  refine ⟨ell, ?_, hsourceEq⟩
  by_contra hell
  have hellZero : ell = 0 := by omega
  apply hcanonical
  simpa [hsourceEq, hellZero] using hsource

/-- Exact affine equation for the canonical pair. -/
theorem canonical_affine_identity (w : List Bool) :
    2 ^ w.length * (canonicalExecution w).2 =
      3 ^ w.count true * (canonicalExecution w).1 + (programData w).A := by
  simpa only [programData_S, programData_O] using
    program_exact w (canonicalExecution_spec w).2.2

/-! ## Growing triadic phase -/

noncomputable def rawPhaseParameter (w : List Bool) (k a : ℕ) : ℕ :=
  Classical.choose <| KLControllerReset.exists_affine_modEq_of_coprime
    (2 ^ w.length) (canonicalExecution w).1 a (3 ^ k)
    (by positivity)
    (Nat.Coprime.pow_right k <| Nat.Coprime.pow_left w.length (by norm_num))

noncomputable def phaseParameter (w : List Bool) (k a : ℕ) : ℕ :=
  rawPhaseParameter w k a % 3 ^ k

theorem rawPhaseParameter_spec (w : List Bool) (k a : ℕ) :
    2 ^ w.length * rawPhaseParameter w k a + (canonicalExecution w).1 ≡ a
      [MOD 3 ^ k] :=
  Classical.choose_spec <| KLControllerReset.exists_affine_modEq_of_coprime
    (2 ^ w.length) (canonicalExecution w).1 a (3 ^ k)
    (by positivity)
    (Nat.Coprime.pow_right k <| Nat.Coprime.pow_left w.length (by norm_num))

theorem phaseParameter_lt (w : List Bool) (k a : ℕ) :
    phaseParameter w k a < 3 ^ k :=
  Nat.mod_lt _ (by positivity)

theorem phaseParameter_spec (w : List Bool) (k a : ℕ) :
    (canonicalExecution w).1 + 2 ^ w.length * phaseParameter w k a ≡ a
      [MOD 3 ^ k] := by
  have hmod : phaseParameter w k a ≡ rawPhaseParameter w k a [MOD 3 ^ k] := by
    simp [phaseParameter, Nat.ModEq]
  have h := (hmod.mul_left (2 ^ w.length)).add_left (canonicalExecution w).1
  exact h.trans <| by
    simpa [Nat.add_comm] using rawPhaseParameter_spec w k a

/-- QM158e, input half: the source phase is equivalent to one parameter
phase because the dyadic multiplier is invertible modulo every power of
three. -/
theorem source_phase_iff_parameter_phase
    (w : List Bool) (k a t : ℕ) :
    (canonicalExecution w).1 + 2 ^ w.length * t ≡ a [MOD 3 ^ k] ↔
      t ≡ phaseParameter w k a [MOD 3 ^ k] := by
  let c := phaseParameter w k a
  have hc := phaseParameter_spec w k a
  have hcop : Nat.Coprime (3 ^ k) (2 ^ w.length) :=
    (Nat.Coprime.pow_right w.length <| Nat.Coprime.pow_left k (by norm_num))
  constructor
  · intro ht
    have hs :
        (canonicalExecution w).1 + 2 ^ w.length * t ≡
          (canonicalExecution w).1 + 2 ^ w.length * c [MOD 3 ^ k] :=
      ht.trans hc.symm
    have hmul : 2 ^ w.length * t ≡ 2 ^ w.length * c [MOD 3 ^ k] :=
      Nat.ModEq.add_left_cancel' _ hs
    exact hmul.cancel_left_of_coprime hcop.gcd_eq_one
  · intro ht
    exact ((ht.mul_left (2 ^ w.length)).add_left
      (canonicalExecution w).1).trans hc

noncomputable def outputPhase (w : List Bool) (k a : ℕ) : ℕ :=
  (canonicalExecution w).2 +
    3 ^ w.count true * phaseParameter w k a

theorem outputPhase_lt (w : List Bool) (k a : ℕ) :
    outputPhase w k a < 3 ^ (w.count true + k) := by
  have hb := (canonicalExecution_spec w).2.1
  have hc := phaseParameter_lt w k a
  dsimp [outputPhase]
  rw [pow_add]
  nlinarith [show 0 < 3 ^ w.count true by positivity]

/-- QM158e, output half: multiplying a parameter congruence by `3^O`
raises its precision from `k` to `O+k`, and conversely the common factor can
be cancelled exactly. -/
theorem target_phase_iff_parameter_phase
    (w : List Bool) (k a t : ℕ) :
    (canonicalExecution w).2 + 3 ^ w.count true * t ≡ outputPhase w k a
        [MOD 3 ^ (w.count true + k)] ↔
      t ≡ phaseParameter w k a [MOD 3 ^ k] := by
  let O := w.count true
  let c := phaseParameter w k a
  have hpow : 3 ^ (O + k) = 3 ^ O * 3 ^ k := pow_add 3 O k
  constructor
  · intro hy
    have hmul : 3 ^ O * t ≡ 3 ^ O * c [MOD 3 ^ (O + k)] := by
      apply Nat.ModEq.add_left_cancel' (canonicalExecution w).2
      simpa [outputPhase, O, c] using hy
    rw [hpow] at hmul
    exact hmul.mul_left_cancel' (by positivity)
  · intro ht
    have hmul := ht.mul_left' (3 ^ O)
    rw [← hpow] at hmul
    simpa [outputPhase, O, c] using hmul.add_left (canonicalExecution w).2

/-- Full phase equivalence along one literal execution family. -/
theorem execution_source_phase_iff_target_phase
    (w : List Bool) (k a : ℕ) {source target : ℕ}
    (h : Executes w source target) :
    source ≡ a [MOD 3 ^ k] ↔
      target ≡ outputPhase w k a [MOD 3 ^ (w.count true + k)] := by
  obtain ⟨t, hs, ht⟩ := (executes_iff_canonical_family w).1 h
  rw [hs, ht, source_phase_iff_parameter_phase,
    target_phase_iff_parameter_phase]

/-- Any natural in the canonical output phase has a unique nonnegative
target-family parameter in the corresponding input phase. -/
theorem outputPhase_modEq_decompose
    (w : List Bool) (k a m : ℕ)
    (hm : m ≡ outputPhase w k a [MOD 3 ^ (w.count true + k)]) :
    ∃ t : ℕ,
      m = (canonicalExecution w).2 + 3 ^ w.count true * t ∧
      t ≡ phaseParameter w k a [MOD 3 ^ k] ∧
      (m - (canonicalExecution w).2) / 3 ^ w.count true = t := by
  let O := w.count true
  let c := phaseParameter w k a
  let d := outputPhase w k a
  let M := 3 ^ (O + k)
  have hdlt : d < M := outputPhase_lt w k a
  have hrem : m % M = d := by
    have := hm
    change m % M = d % M at this
    rwa [Nat.mod_eq_of_lt hdlt] at this
  have hmEq : m = d + M * (m / M) := by
    rw [← hrem]
    exact (Nat.mod_add_div m M).symm
  let q := m / M
  let t := c + 3 ^ k * q
  have htarget : m = (canonicalExecution w).2 + 3 ^ O * t := by
    rw [hmEq]
    dsimp [d, outputPhase, M, t, q, O, c]
    rw [pow_add]
    ring
  have htphase : t ≡ c [MOD 3 ^ k] := by
    dsimp [t]
    simp [Nat.ModEq]
  refine ⟨t, by simpa [O] using htarget, by simpa [c] using htphase, ?_⟩
  rw [htarget]
  have hp : 0 < 3 ^ O := by positivity
  simp [Nat.mul_div_cancel_left _ hp, O]

def NextSource (F : Finset (List Bool)) (E : ℕ → Prop) (x : ℕ) : Prop :=
  ∃ w ∈ F, ∃ y, E y ∧ Executes w x y

def PhaseNextSource (F : Finset (List Bool)) (E : ℕ → Prop)
    (k a x : ℕ) : Prop :=
  NextSource F E x ∧ x ≡ a [MOD 3 ^ k]

/-- QM158f at the set level: source-phase preimages query the target profile
at precision `O+k` and phase `d=outputPhase`. -/
theorem phaseNextSource_iff_targetFibers
    (F : Finset (List Bool)) (E : ℕ → Prop) (k a x : ℕ) :
    PhaseNextSource F E k a x ↔
      ∃ w ∈ F, ∃ m,
        E m ∧ m ≡ outputPhase w k a [MOD 3 ^ (w.count true + k)] ∧
        x = (canonicalExecution w).1 + 2 ^ w.length *
          ((m - (canonicalExecution w).2) / 3 ^ w.count true) := by
  constructor
  · rintro ⟨⟨w, hwF, y, hyE, hxy⟩, hxphase⟩
    have hyphase := (execution_source_phase_iff_target_phase w k a hxy).1 hxphase
    obtain ⟨t, hx, hy⟩ := (executes_iff_canonical_family w).1 hxy
    refine ⟨w, hwF, y, hyE, hyphase, ?_⟩
    rw [hx, hy]
    have hp : 0 < 3 ^ w.count true := by positivity
    simp [Nat.mul_div_cancel_left _ hp]
  · rintro ⟨w, hwF, m, hmE, hmphase, rfl⟩
    obtain ⟨t, hm, htphase, hquot⟩ :=
      outputPhase_modEq_decompose w k a m hmphase
    rw [hquot]
    constructor
    · refine ⟨w, hwF, m, hmE, ?_⟩
      exact (executes_iff_canonical_family w).2 ⟨t, rfl, hm⟩
    · exact (source_phase_iff_parameter_phase w k a t).2 htphase

noncomputable def phaseCandidateValue (_k _a : ℕ)
    (m : List Bool → ℕ) (w : List Bool) : ℕ :=
  (canonicalExecution w).1 + 2 ^ w.length *
    ((m w - (canonicalExecution w).2) / 3 ^ w.count true)

noncomputable def phaseCandidateValues (F : Finset (List Bool)) (k a : ℕ)
    (m : List Bool → ℕ) : Finset ℕ :=
  F.image (phaseCandidateValue k a m)

theorem phaseCandidateValues_nonempty {F : Finset (List Bool)}
    (hF : F.Nonempty) (k a : ℕ) (m : List Bool → ℕ) :
    (phaseCandidateValues F k a m).Nonempty := by
  obtain ⟨w, hw⟩ := hF
  exact ⟨phaseCandidateValue k a m w,
    Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

noncomputable def minPhaseCandidate
    (F : Finset (List Bool)) (hF : F.Nonempty) (k a : ℕ)
    (m : List Bool → ℕ) : ℕ :=
  (phaseCandidateValues F k a m).min'
    (phaseCandidateValues_nonempty hF k a m)

/-- QM158f in minimum form for a finite active code.  `m w` is the least
old source in the exact output fiber of `w`; the minimum of the displayed
inverse images is the least new source in phase `a mod 3^k`. -/
theorem finite_phase_minPlus_renewal
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (E : ℕ → Prop) (k a : ℕ) (m : List Bool → ℕ)
    (hmE : ∀ w ∈ F, E (m w))
    (hmPhase : ∀ w ∈ F,
      m w ≡ outputPhase w k a [MOD 3 ^ (w.count true + k)])
    (hmLeast : ∀ w ∈ F, ∀ y, E y →
      y ≡ outputPhase w k a [MOD 3 ^ (w.count true + k)] → m w ≤ y) :
    PhaseNextSource F E k a (minPhaseCandidate F hF k a m) ∧
      ∀ x, PhaseNextSource F E k a x →
        minPhaseCandidate F hF k a m ≤ x := by
  have hmem : minPhaseCandidate F hF k a m ∈ phaseCandidateValues F k a m :=
    Finset.min'_mem _ _
  obtain ⟨w, hwF, hwEq⟩ := Finset.mem_image.mp hmem
  constructor
  · apply (phaseNextSource_iff_targetFibers F E k a _).2
    refine ⟨w, hwF, m w, hmE w hwF, hmPhase w hwF, ?_⟩
    simpa [phaseCandidateValue] using hwEq.symm
  · intro x hx
    obtain ⟨v, hvF, y, hyE, hyPhase, rfl⟩ :=
      (phaseNextSource_iff_targetFibers F E k a x).1 hx
    have hmin : minPhaseCandidate F hF k a m ≤ phaseCandidateValue k a m v := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨v, hvF, rfl⟩
    obtain ⟨tm, hmTarget, _, hmQuot⟩ :=
      outputPhase_modEq_decompose v k a (m v) (hmPhase v hvF)
    obtain ⟨ty, hyTarget, _, hyQuot⟩ :=
      outputPhase_modEq_decompose v k a y hyPhase
    have hmy : m v ≤ y := hmLeast v hvF y hyE hyPhase
    have ht : tm ≤ ty := by
      rw [hmTarget, hyTarget] at hmy
      have hmul : 3 ^ v.count true * tm ≤ 3 ^ v.count true * ty := by omega
      exact Nat.le_of_mul_le_mul_left hmul (by positivity)
    have hcand : phaseCandidateValue k a m v ≤
        (canonicalExecution v).1 + 2 ^ v.length *
          ((y - (canonicalExecution v).2) / 3 ^ v.count true) := by
      dsimp [phaseCandidateValue]
      rw [hmQuot, hyQuot]
      gcongr
    exact hmin.trans hcand

/-! ## Finite min-plus renewal -/

def AdmissibleParameter (E : ℕ → Prop) (w : List Bool) (t : ℕ) : Prop :=
  E ((canonicalExecution w).2 + 3 ^ w.count true * t)

noncomputable def candidateValue (tau : List Bool → ℕ) (w : List Bool) : ℕ :=
  (canonicalExecution w).1 + 2 ^ w.length * tau w

noncomputable def candidateValues (F : Finset (List Bool))
    (tau : List Bool → ℕ) : Finset ℕ :=
  F.image (candidateValue tau)

theorem candidateValues_nonempty {F : Finset (List Bool)}
    (hF : F.Nonempty) (tau : List Bool → ℕ) :
    (candidateValues F tau).Nonempty := by
  obtain ⟨w, hw⟩ := hF
  exact ⟨candidateValue tau w,
    Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

noncomputable def minCandidate (F : Finset (List Bool)) (hF : F.Nonempty)
    (tau : List Bool → ℕ) : ℕ :=
  (candidateValues F tau).min' (candidateValues_nonempty hF tau)

/-- Semantic form of the inverse renewal: the next-source set is exactly a
finite union of affine preimages of the target set. -/
theorem nextSource_iff_parameters (F : Finset (List Bool)) (E : ℕ → Prop)
    (x : ℕ) :
    NextSource F E x ↔
      ∃ w ∈ F, ∃ t,
        AdmissibleParameter E w t ∧
          x = (canonicalExecution w).1 + 2 ^ w.length * t := by
  constructor
  · rintro ⟨w, hwF, y, hyE, hxy⟩
    obtain ⟨t, hx, hy⟩ := (executes_iff_canonical_family w).mp hxy
    exact ⟨w, hwF, t, by simpa [AdmissibleParameter, hy] using hyE, hx⟩
  · rintro ⟨w, hwF, t, ht, rfl⟩
    refine ⟨w, hwF,
      (canonicalExecution w).2 + 3 ^ w.count true * t, ht, ?_⟩
    exact (executes_iff_canonical_family w).2 ⟨t, rfl, rfl⟩

/-- QM158b for a finite active code.  If `tau w` is the least target-family
parameter meeting `E` for every word in `F`, then the displayed min-plus
quantity is exactly the least next source. -/
theorem finite_minPlus_renewal
    (F : Finset (List Bool)) (hF : F.Nonempty)
    (E : ℕ → Prop) (tau : List Bool → ℕ)
    (hadm : ∀ w ∈ F, AdmissibleParameter E w (tau w))
    (hleast : ∀ w ∈ F, ∀ t, AdmissibleParameter E w t → tau w ≤ t) :
    NextSource F E (minCandidate F hF tau) ∧
      ∀ x, NextSource F E x → minCandidate F hF tau ≤ x := by
  have hmem : minCandidate F hF tau ∈ candidateValues F tau :=
    Finset.min'_mem _ _
  obtain ⟨w, hwF, hwEq⟩ := Finset.mem_image.mp hmem
  constructor
  · apply (nextSource_iff_parameters F E _).2
    refine ⟨w, hwF, tau w, hadm w hwF, ?_⟩
    simpa [candidateValue] using hwEq.symm
  · intro x hx
    obtain ⟨v, hvF, t, ht, rfl⟩ :=
      (nextSource_iff_parameters F E x).1 hx
    have hmin : minCandidate F hF tau ≤ candidateValue tau v := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨v, hvF, rfl⟩
    have htau : tau v ≤ t := hleast v hvF t ht
    have hcand : candidateValue tau v ≤
        (canonicalExecution v).1 + 2 ^ v.length * t := by
      dsimp [candidateValue]
      gcongr
    exact hmin.trans hcand

/-- QM158c: replacing the least family parameter by the least target in its
triadic residue class gives the expanded quotient formula. -/
theorem candidate_eq_targetFiber_quotient
    (w : List Bool) (tau m : ℕ)
    (hm : m = (canonicalExecution w).2 + 3 ^ w.count true * tau) :
    (canonicalExecution w).1 + 2 ^ w.length * tau =
      (canonicalExecution w).1 + 2 ^ w.length *
        ((m - (canonicalExecution w).2) / 3 ^ w.count true) := by
  rw [hm]
  have hpos : 0 < 3 ^ w.count true := by positivity
  simp [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hpos]

end OutwardCylinderRenewal
end KontoroC

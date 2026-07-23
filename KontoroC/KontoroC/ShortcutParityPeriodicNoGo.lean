/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.AffineQuotientNoGo

/-!
# Ultimately periodic outward shortcut-parity languages cannot be ordinary

This file is the adversarial endpoint for the finite thin language generated
by shortcut parity words.  Repeating any fixed outward parity block gives one
expanding coprime affine-gain recurrence, which cannot have a positive natural
orbit.  In particular every ultimately periodic path through the current
four-word signed-controller language is ruled out.
-/

namespace KontoroC
namespace ShortcutParityPeriodicNoGo

structure ParityData where
  S : ℕ
  O : ℕ
  A : ℕ
  deriving DecidableEq, Repr

def initialData : ParityData := ⟨0, 0, 0⟩

def ParityData.step (d : ParityData) (odd : Bool) : ParityData :=
  if odd then ⟨d.S + 1, d.O + 1, 3 * d.A + 2 ^ d.S⟩
  else ⟨d.S + 1, d.O, d.A⟩

def accumulate : List Bool → ParityData → ParityData
  | [], d => d
  | odd :: w, d => accumulate w (d.step odd)

def programData (w : List Bool) : ParityData := accumulate w initialData

/-- Exact execution of a shortcut parity word between natural endpoints. -/
def Executes : List Bool → ℕ → ℕ → Prop
  | [], start, finish => finish = start
  | odd :: w, start, finish =>
      ∃ middle : ℕ,
        2 * middle = (if odd then 3 * start + 1 else start) ∧
        Executes w middle finish

theorem ParityData.step_invariant (d : ParityData) (odd : Bool)
    {origin current next : ℕ}
    (hinv : 2 ^ d.S * current = 3 ^ d.O * origin + d.A)
    (hstep : 2 * next = if odd then 3 * current + 1 else current) :
    2 ^ (d.step odd).S * next =
      3 ^ (d.step odd).O * origin + (d.step odd).A := by
  cases odd with
  | false =>
    simp at hstep
    change 2 ^ (d.S + 1) * next = 3 ^ d.O * origin + d.A
    rw [pow_succ']
    calc
      2 * 2 ^ d.S * next = 2 ^ d.S * (2 * next) := by ring
      _ = 2 ^ d.S * current := by rw [hstep]
      _ = 3 ^ d.O * origin + d.A := hinv
  | true =>
    simp at hstep
    change 2 ^ (d.S + 1) * next =
      3 ^ (d.O + 1) * origin + (3 * d.A + 2 ^ d.S)
    rw [pow_succ', pow_succ']
    calc
      2 * 2 ^ d.S * next = 2 ^ d.S * (2 * next) := by ring
      _ = 2 ^ d.S * (3 * current + 1) := by rw [hstep]
      _ = 3 * (2 ^ d.S * current) + 2 ^ d.S := by ring
      _ = 3 * (3 ^ d.O * origin + d.A) + 2 ^ d.S := by rw [hinv]
      _ = 3 * 3 ^ d.O * origin + (3 * d.A + 2 ^ d.S) := by ring

theorem accumulate_invariant (w : List Bool) (d : ParityData)
    {origin current finish : ℕ}
    (hinv : 2 ^ d.S * current = 3 ^ d.O * origin + d.A)
    (hw : Executes w current finish) :
    let out := accumulate w d
    2 ^ out.S * finish = 3 ^ out.O * origin + out.A := by
  induction w generalizing d current with
  | nil =>
      simp only [Executes] at hw
      subst finish
      simpa [accumulate]
  | cons odd w ih =>
      obtain ⟨middle, hstep, htail⟩ := hw
      simpa only [accumulate] using
        ih (d.step odd) (d.step_invariant odd hinv hstep) htail

theorem program_exact (w : List Bool) {start finish : ℕ}
    (hw : Executes w start finish) :
    2 ^ (programData w).S * finish =
      3 ^ (programData w).O * start + (programData w).A := by
  simpa [programData, initialData] using
    accumulate_invariant w initialData
      (origin := start) (current := start) (finish := finish)
      (by simp [initialData]) hw

theorem accumulate_S (w : List Bool) (d : ParityData) :
    (accumulate w d).S = d.S + w.length := by
  induction w generalizing d with
  | nil => simp [accumulate]
  | cons odd w ih =>
      simp only [accumulate, ih, ParityData.step]
      split <;> simp <;> omega

theorem accumulate_O (w : List Bool) (d : ParityData) :
    (accumulate w d).O = d.O + w.count true := by
  induction w generalizing d with
  | nil => simp [accumulate]
  | cons odd w ih =>
      cases odd <;> simp [accumulate, ih, ParityData.step] <;> omega

theorem programData_S (w : List Bool) : (programData w).S = w.length := by
  simpa [programData, initialData] using accumulate_S w initialData

theorem programData_O (w : List Bool) :
    (programData w).O = w.count true := by
  simpa [programData, initialData] using accumulate_O w initialData

def WordOutward (w : List Bool) : Prop :=
  2 ^ w.length < 3 ^ w.count true

def flattenWords : List (List Bool) → List Bool
  | [] => []
  | w :: ws => w ++ flattenWords ws

theorem wordOutward_append {u v : List Bool}
    (hu : WordOutward u) (hv : WordOutward v) :
    WordOutward (u ++ v) := by
  simp only [WordOutward, List.length_append, List.count_append, pow_add] at hu hv ⊢
  exact mul_lt_mul hu hv.le (by positivity) (by positivity)

theorem wordOutward_join {period : List (List Bool)}
    (hne : period ≠ [])
    (hout : ∀ w ∈ period, WordOutward w) :
    WordOutward (flattenWords period) := by
  induction period with
  | nil => exact (hne rfl).elim
  | cons w ws ih =>
      cases ws with
      | nil => simpa [flattenWords] using hout w (by simp)
      | cons v vs =>
          have hw : WordOutward w := hout w (by simp)
          have hrest : WordOutward (flattenWords (v :: vs)) := by
            apply ih (by simp)
            intro z hz
            exact hout z (by simp [hz])
          simpa [flattenWords] using wordOutward_append hw hrest

/-- No positive natural sequence can execute one fixed nonempty outward
shortcut parity word forever. -/
theorem no_positive_repeated_outward_word
    (w : List Bool) (hne : w ≠ []) (hout : WordOutward w) :
    ¬ ∃ state : ℕ → ℕ,
      (∀ t, 0 < state t) ∧
      (∀ t, Executes w (state t) (state (t + 1))) := by
  rintro ⟨state, hpos, hexec⟩
  let o : PositiveAffineGainOrbit
      (3 ^ (programData w).O) (2 ^ (programData w).S)
        (programData w).A :=
    { value := state
      value_pos := hpos
      balance := fun t => program_exact w (hexec t) }
  have hS : 0 < (programData w).S := by
    rw [programData_S]
    have hlen : w.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    omega
  have hcop : (3 ^ (programData w).O).Coprime
      (2 ^ (programData w).S) :=
    (by norm_num : Nat.Coprime 3 2).pow _ _
  have hB : 1 < 2 ^ (programData w).S :=
    Nat.one_lt_pow hS.ne' (by omega)
  have hAB : 2 ^ (programData w).S < 3 ^ (programData w).O := by
    change 2 ^ w.length < 3 ^ w.count true at hout
    simpa only [programData_S, programData_O] using hout
  exact o.impossible hcop hB hAB

/-- The four minimal outward words found by the signed thin-residue worker. -/
def signedThinCode : List (List Bool) :=
  [[true], [false, true, true],
    [false, false, true, true, true, true],
    [false, true, false, true, true, true]]

theorem signedThinCode_outward {w : List Bool} (hw : w ∈ signedThinCode) :
    WordOutward w := by
  simp [signedThinCode] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> norm_num [WordOutward]

theorem signedThinCode_word_ne_nil {w : List Bool} (hw : w ∈ signedThinCode) :
    w ≠ [] := by
  simp [signedThinCode] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> simp

/-- Every nonempty periodic block schedule drawn from the worker's thin code
is impossible as a positive ordinary shortcut orbit.  Only genuinely
aperiodic thin paths remain live. -/
theorem no_positive_periodic_signedThinCode
    (period : List (List Bool)) (hne : period ≠ [])
    (hcode : ∀ w ∈ period, w ∈ signedThinCode) :
    ¬ ∃ state : ℕ → ℕ,
      (∀ t, 0 < state t) ∧
      (∀ t, Executes (flattenWords period) (state t) (state (t + 1))) := by
  apply no_positive_repeated_outward_word (flattenWords period)
  · cases period with
    | nil => exact (hne rfl).elim
    | cons w ws =>
        simp only [flattenWords]
        exact List.append_ne_nil_of_left_ne_nil
          (signedThinCode_word_ne_nil (hcode w (by simp))) _
  · apply wordOutward_join hne
    intro w hw
    exact signedThinCode_outward (hcode w hw)

/-- Tail form used by an ultimately periodic dispatcher: no finite prefix can
rescue a positive orbit once a nonempty thin-code period repeats forever. -/
theorem no_positive_eventually_periodic_signedThinCode
    (state : ℕ → ℕ) (t₀ : ℕ)
    (period : List (List Bool)) (hne : period ≠ [])
    (hcode : ∀ w ∈ period, w ∈ signedThinCode) :
    ¬ ((∀ t, 0 < state (t₀ + t)) ∧
      (∀ t, Executes (flattenWords period)
        (state (t₀ + t)) (state (t₀ + (t + 1))))) := by
  rintro ⟨hpos, hexec⟩
  apply no_positive_periodic_signedThinCode period hne hcode
  exact ⟨fun t => state (t₀ + t), hpos, hexec⟩

end ShortcutParityPeriodicNoGo
end KontoroC

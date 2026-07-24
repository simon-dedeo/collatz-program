/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardRechargeMatching
import KontoroC.OutwardCylinderRenewal

/-!
# Frozen target residues inside an exact parity cylinder

For one fixed parity word `w`, all literal sources lie in one class modulo
`2^|w|` and all literal targets lie in one class modulo `3^O`, where `O` is
the number of odd steps.  More sharply, changing a source by `inputDelta` and
the corresponding target by `outputDelta` forces

`3^O * inputDelta = 2^|w| * outputDelta`.

Consequently deeper dyadic choices cannot repair a frozen low ternary digit:
`outputDelta` must be divisible by `3^O`.  These are exact finite-word
coherence vetoes.  They do not provide an infinite compatible cylinder or an
ordinary counterexample seed.
-/

namespace KontoroC
namespace OutwardFrozenTernaryResidue

open ShortcutParityPeriodicNoGo OutwardCylinderRenewal

/-- All executions of a fixed parity word have the same target residue modulo
the full triadic output modulus. -/
theorem executes_target_modEq (w : List Bool)
    {source source' target target' : ℕ}
    (h : Executes w source target)
    (h' : Executes w source' target') :
    target ≡ target' [MOD 3 ^ w.count true] := by
  obtain ⟨t, _, htarget⟩ := (executes_iff_canonical_family w).mp h
  obtain ⟨t', _, htarget'⟩ := (executes_iff_canonical_family w).mp h'
  rw [htarget, htarget']
  simp [Nat.ModEq]

/-- Exact pullback law for simultaneous nonnegative source and target
increments inside one parity cylinder. -/
theorem execution_increment_balance (w : List Bool)
    {source target inputDelta outputDelta : ℕ}
    (h : Executes w source target)
    (h' : Executes w (source + inputDelta) (target + outputDelta)) :
    3 ^ w.count true * inputDelta = 2 ^ w.length * outputDelta := by
  have hbase := program_exact w h
  have hshift := program_exact w h'
  simp only [programData_S, programData_O] at hbase hshift
  simp only [Nat.mul_add] at hshift
  omega

/-- Any literal output correction between two realizations of the same word
is divisible by the word's full triadic modulus. -/
theorem threePow_dvd_targetIncrement (w : List Bool)
    {source source' target outputDelta : ℕ}
    (h : Executes w source target)
    (h' : Executes w source' (target + outputDelta)) :
    3 ^ w.count true ∣ outputDelta := by
  have hmod := executes_target_modEq w h h'
  have hzero : 0 ≡ outputDelta [MOD 3 ^ w.count true] := by
    apply Nat.ModEq.add_left_cancel' target
    simpa using hmod
  exact Nat.modEq_zero_iff_dvd.mp hzero.symm

/-- Dually, a source correction between two realizations is divisible by the
full dyadic input modulus. -/
theorem twoPow_dvd_sourceIncrement (w : List Bool)
    {source target target' inputDelta : ℕ}
    (h : Executes w source target)
    (h' : Executes w (source + inputDelta) target') :
    2 ^ w.length ∣ inputDelta := by
  have hmod := OutwardCylinderRenewal.executes_source_modEq w h h'
  have hzero : 0 ≡ inputDelta [MOD 2 ^ w.length] := by
    apply Nat.ModEq.add_left_cancel' source
    simpa using hmod
  exact Nat.modEq_zero_iff_dvd.mp hzero.symm

/-- The informal inverse-flow formula is exact once the required divisibility
holds: the input correction is `2^S` times the quotient of the output
correction by `3^O`. -/
theorem inputIncrement_eq_twoPow_mul_targetQuotient (w : List Bool)
    {source target inputDelta outputDelta : ℕ}
    (h : Executes w source target)
    (h' : Executes w (source + inputDelta) (target + outputDelta)) :
    inputDelta =
      2 ^ w.length * (outputDelta / 3 ^ w.count true) := by
  have hbalance := execution_increment_balance w h h'
  have hdvd := threePow_dvd_targetIncrement w h h'
  have hquotient :
      3 ^ w.count true * (outputDelta / 3 ^ w.count true) = outputDelta :=
    Nat.mul_div_cancel' hdvd
  have hcancel :
      3 ^ w.count true * inputDelta =
        3 ^ w.count true *
          (2 ^ w.length * (outputDelta / 3 ^ w.count true)) := by
    calc
      3 ^ w.count true * inputDelta =
          2 ^ w.length * outputDelta := hbalance
      _ = 2 ^ w.length *
          (3 ^ w.count true * (outputDelta / 3 ^ w.count true)) := by
            rw [hquotient]
      _ = 3 ^ w.count true *
          (2 ^ w.length * (outputDelta / 3 ^ w.count true)) := by ring
  exact Nat.mul_left_cancel (by positivity : 0 < 3 ^ w.count true) hcancel

/-- Exact rejection certificate: a requested target repair not divisible by
`3^O` cannot be implemented by choosing a deeper source in the same word
cylinder. -/
theorem no_targetRepair_of_not_threePow_dvd (w : List Bool)
    {source target outputDelta : ℕ}
    (h : Executes w source target)
    (hnot : ¬3 ^ w.count true ∣ outputDelta) :
    ¬∃ source', Executes w source' (target + outputDelta) := by
  rintro ⟨source', h'⟩
  exact hnot (threePow_dvd_targetIncrement w h h')

/-- In particular every correction smaller than the frozen triadic modulus
must be zero. -/
theorem targetIncrement_eq_zero_of_lt_threePow (w : List Bool)
    {source source' target outputDelta : ℕ}
    (h : Executes w source target)
    (h' : Executes w source' (target + outputDelta))
    (hlt : outputDelta < 3 ^ w.count true) :
    outputDelta = 0 :=
  Nat.eq_zero_of_dvd_of_lt (threePow_dvd_targetIncrement w h h') hlt

end OutwardFrozenTernaryResidue
end KontoroC

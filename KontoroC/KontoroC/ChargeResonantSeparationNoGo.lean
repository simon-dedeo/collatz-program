/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ChargeResonantConjugacy

/-!
# Resonant chart separation cannot replenish itself

A determinant-four resonant cell starts with separation `2622*k` and ends
with separation `2618*k`.  Linking its target chart to another resonant
source chart forces `1311*k_(i+1)=1309*k_i`.  Coprimality then makes every
power of `1311` divide the initial parameter of an infinite chain, which is
impossible for a positive natural.
-/

namespace KontoroC
namespace ChargeResonantSeparationNoGo

theorem coprime_1311_1309 : Nat.Coprime 1311 1309 := by norm_num

/-- Cancellation of the common factor two in the visible chart widths. -/
theorem halve_link {x y : ℕ} (h : 2622 * x = 2618 * y) :
    1311 * x = 1309 * y := by omega

/-- Iterating the separation-consumption equation. -/
theorem iterated_link (k : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n → 1311 * k (i + 1) = 1309 * k i) :
    1311 ^ n * k n = 1309 ^ n * k 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : ∀ i, i < n → 1311 * k (i + 1) = 1309 * k i := by
        intro i hi
        exact h i (by omega)
      have hi := ih hprev
      have hn := h n (by omega)
      rw [pow_succ, pow_succ]
      calc
        1311 ^ n * 1311 * k (n + 1) =
            1311 ^ n * (1311 * k (n + 1)) := by ring
        _ = 1311 ^ n * (1309 * k n) := by rw [hn]
        _ = 1309 * (1311 ^ n * k n) := by ring
        _ = 1309 * (1309 ^ n * k 0) := by rw [hi]
        _ = 1309 ^ n * 1309 * k 0 := by ring

/-- Quantitative finite obstruction: a linked prefix of length `n` forces
`1311^n` to divide its initial resonance parameter. -/
theorem pow_dvd_initial (k : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n → 1311 * k (i + 1) = 1309 * k i) :
    1311 ^ n ∣ k 0 := by
  have hprod : 1311 ^ n ∣ 1309 ^ n * k 0 := by
    use k n
    exact (iterated_link k n h).symm
  exact (coprime_1311_1309.pow n n).dvd_of_dvd_mul_left hprod

/-- Same finite divisibility theorem in the original `2622/2618` chart
widths. -/
theorem pow_dvd_initial_of_chart_links (k : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < n → 2622 * k (i + 1) = 2618 * k i) :
    1311 ^ n ∣ k 0 := by
  apply pow_dvd_initial k n
  intro i hi
  exact halve_link (h i hi)

/-- An infinite self-linked resonant rail must start with zero separation. -/
theorem initial_eq_zero_of_infinite_links (k : ℕ → ℕ)
    (h : ∀ i, 2622 * k (i + 1) = 2618 * k i) : k 0 = 0 := by
  by_contra hk
  have hkpos : 0 < k 0 := Nat.pos_of_ne_zero hk
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (k 0)
    (by norm_num : (1 : ℕ) < 1311)
  have hdvd : 1311 ^ n ∣ k 0 :=
    pow_dvd_initial_of_chart_links k n (fun i _ => h i)
  have hle : 1311 ^ n ≤ k 0 := Nat.le_of_dvd hkpos hdvd
  omega

/-- Therefore no positive-natural resonance parameter supports an infinite
chain of these conjugacies. -/
theorem no_positive_infinite_chain (k : ℕ → ℕ)
    (hk : ∀ i, 0 < k i)
    (h : ∀ i, 2622 * k (i + 1) = 2618 * k i) : False := by
  have hz := initial_eq_zero_of_infinite_links k h
  exact (Nat.ne_of_gt (hk 0)) hz

end ChargeResonantSeparationNoGo
end KontoroC

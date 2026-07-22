/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OddCatcherPrefix

/-!
# Parity-complete splash instructions

`EvenCleanupGate` is the zero-amplifier-safe counterpart of the stable
`TwoRailGate` API.  Together with `OddCatcherGate` it will form the complete
parity grammar.  This file also isolates the canonical power-of-two/odd
factorization used by the total decoder.
-/

namespace KontoroC

/-- Canonical existence of a power-of-two times odd factorization for every
positive natural. -/
theorem exists_twoPow_mul_odd_factor {N : ℕ} (hN : 0 < N) :
    ∃ k q : ℕ, 0 < q ∧ Odd q ∧ 2 ^ k * q = N := by
  let k := padicValNat 2 N
  let q := N.divMaxPow 2
  have hprod : 2 ^ k * q = N := by
    simpa [k, q] using Nat.pow_padicValNat_mul_divMaxPow 2 N
  have hqpos : 0 < q := by
    have hpow : 0 < 2 ^ k := Nat.pow_pos (by omega)
    nlinarith
  have hnot : ¬2 ∣ q := by
    dsimp [q]
    exact Nat.not_dvd_divMaxPow (by omega) (by omega)
  have hqodd : Odd q := by
    rw [Nat.odd_iff]
    have hlt := Nat.mod_lt q (by omega : 0 < 2)
    have hne : q % 2 ≠ 0 := by
      intro hz
      exact hnot (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  exact ⟨k, q, hqpos, hqodd, hprod⟩

/-- If the factored number is even, its power-of-two exponent is positive. -/
theorem twoPow_exponent_pos_of_even {N k q : ℕ}
    (hN : Even N) (hq : Odd q) (hfactor : 2 ^ k * q = N) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  simp only [pow_zero, one_mul] at hfactor
  subst N
  exact hq.not_two_dvd_nat (even_iff_two_dvd.mp hN)

/-- Even-gap cleanup gate allowing `ampTicks=0` and `outputGap=1`. -/
structure EvenCleanupGate where
  ampTicks : ℕ
  cleanTicks : ℕ
  toPlusExtra : ℕ
  toMinusExtra : ℕ
  outputGap : ℕ
  inputPayload : ℕ
  plusPayload : ℕ
  outputPayload : ℕ
  outputGap_pos : 0 < outputGap
  inputPayload_pos : 0 < inputPayload
  plusPayload_pos : 0 < plusPayload
  outputPayload_pos : 0 < outputPayload
  inputPayload_odd : Odd inputPayload
  plusPayload_odd : Odd plusPayload
  outputPayload_odd : Odd outputPayload
  toPlus_balance :
    2 ^ toPlusExtra * delayState plusPayload (2 * cleanTicks + 2) =
      3 ^ (ampTicks + 1) * inputPayload - 1
  toMinus_balance :
    2 ^ toMinusExtra * minusOneState outputPayload outputGap =
      1 + 3 ^ (cleanTicks + 1) * plusPayload

namespace EvenCleanupGate

def start (g : EvenCleanupGate) : ℕ :=
  minusOneState g.inputPayload (g.ampTicks + 1)

def plusState (g : EvenCleanupGate) : ℕ :=
  delayState g.plusPayload (2 * g.cleanTicks + 2)

def cleanupCollisionSource (g : EvenCleanupGate) : ℕ :=
  delayState (3 ^ g.cleanTicks * g.plusPayload) 2

def endpoint (g : EvenCleanupGate) : ℕ :=
  minusOneState g.outputPayload g.outputGap

def word (g : EvenCleanupGate) : List ℕ :=
  mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra ++
    (List.replicate g.cleanTicks 2 ++ [2 + g.toMinusExtra])

theorem amplifier_legal_and_endpoint (g : EvenCleanupGate) :
    WordLegal g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) ∧
      runWord g.start
        (mersenneMacroWord (g.ampTicks + 1) g.toPlusExtra) = g.plusState := by
  exact mersenneMacro_legal_of_packet_equation
    (by omega) g.inputPayload_pos
    (Nat.odd_iff.mp (delayState_odd (by omega))) g.toPlus_balance

theorem cleanup_legal_and_endpoint (g : EvenCleanupGate) :
    WordLegal g.plusState (List.replicate g.cleanTicks 2) ∧
      runWord g.plusState (List.replicate g.cleanTicks 2) =
        g.cleanupCollisionSource := by
  simpa [plusState, cleanupCollisionSource] using
    delayState_word g.plusPayload_pos g.plusPayload_odd
      (by omega : 2 * g.cleanTicks + 2 ≤ 2 * g.cleanTicks + 2)

theorem cleanup_collision_step (g : EvenCleanupGate) :
    LegalInstruction g.cleanupCollisionSource (2 + g.toMinusExtra) ∧
      oddStep g.cleanupCollisionSource = g.endpoint := by
  have hout := minusOneState_pos_odd g.outputPayload_pos g.outputGap_pos
  apply legalInstruction_of_step_equation
  · exact delayState_pos _ _
  · exact Nat.odd_iff.mp (delayState_odd (by omega))
  · exact Nat.odd_iff.mp hout.2
  · calc
      2 ^ (2 + g.toMinusExtra) * g.endpoint =
          4 * (2 ^ g.toMinusExtra * g.endpoint) := by
        rw [show 2 + g.toMinusExtra = g.toMinusExtra + 2 by omega,
          pow_add]
        norm_num
        ring
      _ = 4 * (1 + 3 ^ (g.cleanTicks + 1) * g.plusPayload) := by
        congr 1
        exact g.toMinus_balance
      _ = 3 * g.cleanupCollisionSource + 1 := by
        simp only [cleanupCollisionSource, delayState]
        rw [pow_succ]
        ring

theorem legal_and_endpoint (g : EvenCleanupGate) :
    WordLegal g.start g.word ∧ runWord g.start g.word = g.endpoint := by
  have hamp := g.amplifier_legal_and_endpoint
  have hclean := g.cleanup_legal_and_endpoint
  have hcollision := g.cleanup_collision_step
  rw [word, wordLegal_append_iff, runWord_append]
  constructor
  · refine ⟨hamp.1, ?_⟩
    rw [hamp.2, wordLegal_append_iff]
    refine ⟨hclean.1, ?_⟩
    rw [hclean.2]
    exact ⟨hcollision.1, trivial⟩
  · rw [hamp.2, runWord_append, hclean.2]
    simpa [runWord] using hcollision.2

theorem outward_iff (g : EvenCleanupGate) :
    g.start < g.endpoint ↔
      2 ^ (g.ampTicks + 1) * g.inputPayload <
        2 ^ g.outputGap * g.outputPayload := by
  have hin : 0 < 2 ^ (g.ampTicks + 1) * g.inputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.inputPayload_pos
  have hout : 0 < 2 ^ g.outputGap * g.outputPayload :=
    Nat.mul_pos (Nat.pow_pos (by omega)) g.outputPayload_pos
  simp only [start, endpoint, minusOneState]
  omega

/-- Stable old API embeds into the generalized even branch. -/
def ofTwoRailGate (g : TwoRailGate) : EvenCleanupGate where
  ampTicks := g.ampTicks
  cleanTicks := g.cleanTicks
  toPlusExtra := g.toPlusExtra
  toMinusExtra := g.toMinusExtra
  outputGap := g.outputGap
  inputPayload := g.inputPayload
  plusPayload := g.plusPayload
  outputPayload := g.outputPayload
  outputGap_pos := g.outputGap_pos
  inputPayload_pos := g.inputPayload_pos
  plusPayload_pos := g.plusPayload_pos
  outputPayload_pos := g.outputPayload_pos
  inputPayload_odd := g.inputPayload_odd
  plusPayload_odd := g.plusPayload_odd
  outputPayload_odd := g.outputPayload_odd
  toPlus_balance := g.toPlus_balance
  toMinus_balance := g.toMinus_balance

end EvenCleanupGate

/-- Explicit halting alternative: the first amplifier collision lands at
`1`. -/
structure SplashHalt (r P : ℕ) where
  collisionExtra : ℕ
  balance : 2 ^ collisionExtra = 3 ^ (r + 1) * P - 1

namespace SplashHalt

def start {r P : ℕ} (_h : SplashHalt r P) : ℕ :=
  minusOneState P (r + 1)

def word {r P : ℕ} (h : SplashHalt r P) : List ℕ :=
  mersenneMacroWord (r + 1) h.collisionExtra

theorem legal_and_endpoint {r P : ℕ} (h : SplashHalt r P)
    (hP : 0 < P) :
    WordLegal h.start h.word ∧ runWord h.start h.word = 1 := by
  exact mersenneMacro_legal_of_packet_equation
    (by omega) hP (by norm_num) (by simpa using h.balance)

end SplashHalt

/-- Output of the parity-complete decoder at fixed amplifier length and
positive odd input payload. -/
inductive CompleteSplashOutcome (r P : ℕ) : Type
  | halt (h : SplashHalt r P)
  | even (g : EvenCleanupGate)
      (hr : g.ampTicks = r) (hP : g.inputPayload = P)
  | odd (g : OddCatcherGate)
      (hr : g.ampTicks = r) (hP : g.inputPayload = P)

/-- Every positive odd payload either hits `1` at its first collision or
constructs one exact parity splash. -/
theorem exists_completeSplashOutcome (r P : ℕ) (hPpos : 0 < P)
    (hPodd : Odd P) : Nonempty (CompleteSplashOutcome r P) := by
  let A := 3 ^ (r + 1) * P - 1
  have hprodOdd : Odd (3 ^ (r + 1) * P) :=
    (by exact ((by norm_num : Odd 3).pow).mul hPodd)
  have hApos : 0 < A := by
    have hx : 0 < 3 ^ r * P := by positivity
    have hcoord : 3 ^ (r + 1) * P = 3 * (3 ^ r * P) := by
      rw [pow_succ]
      ring
    dsimp [A]
    rw [hcoord]
    omega
  obtain ⟨a, Y, hYpos, hYodd, hAfac⟩ := exists_twoPow_mul_odd_factor hApos
  by_cases hYone : Y = 1
  · refine ⟨CompleteSplashOutcome.halt ⟨a, ?_⟩⟩
    dsimp [A] at hAfac
    simpa [hYone] using hAfac
  · have hYgt : 1 < Y := by omega
    let D := Y - 1
    have hDpos : 0 < D := by simp [D, hYgt]
    obtain ⟨G, Q, hQpos, hQodd, hDfac⟩ := exists_twoPow_mul_odd_factor hDpos
    have hDeven : Even D := by
      rcases hYodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      dsimp [D]
      omega
    have hGpos : 0 < G := twoPow_exponent_pos_of_even hDeven hQodd hDfac
    have hYsplit : Y = 1 + 2 ^ G * Q := by
      dsimp [D] at hDfac
      omega
    rcases Nat.even_or_odd G with hGeven | hGodd
    · rcases hGeven with ⟨j, hj⟩
      have hjpos : 0 < j := by omega
      let s := j - 1
      have hGshape : G = 2 * s + 2 := by
        dsimp [s]
        omega
      let Z := 1 + 3 ^ (s + 1) * Q
      have hZpos : 0 < Z := by simp [Z]
      have hZeven : Even Z := by
        have hodd : Odd (3 ^ (s + 1) * Q) :=
          (by exact ((by norm_num : Odd 3).pow).mul hQodd)
        rcases hodd with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        dsimp [Z]
        omega
      obtain ⟨b, M, hMpos, hModd, hZfac⟩ :=
        exists_twoPow_mul_odd_factor hZpos
      have hbpos : 0 < b :=
        twoPow_exponent_pos_of_even hZeven hModd hZfac
      let W := M + 1
      have hWpos : 0 < W := by simp [W]
      have hWeven : Even W := by
        rcases hModd with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        dsimp [W]
        omega
      obtain ⟨L, P', hP'pos, hP'odd, hWfac⟩ :=
        exists_twoPow_mul_odd_factor hWpos
      have hLpos : 0 < L :=
        twoPow_exponent_pos_of_even hWeven hP'odd hWfac
      let g : EvenCleanupGate := {
        ampTicks := r
        cleanTicks := s
        toPlusExtra := a
        toMinusExtra := b
        outputGap := L
        inputPayload := P
        plusPayload := Q
        outputPayload := P'
        outputGap_pos := hLpos
        inputPayload_pos := hPpos
        plusPayload_pos := hQpos
        outputPayload_pos := hP'pos
        inputPayload_odd := hPodd
        plusPayload_odd := hQodd
        outputPayload_odd := hP'odd
        toPlus_balance := by
          rw [show 2 * s + 2 = G by omega]
          simp only [delayState]
          dsimp [A] at hAfac
          rw [← hAfac, hYsplit]
          ring
        toMinus_balance := by
          have hMstate : minusOneState P' L = M := by
            simp only [minusOneState]
            omega
          rw [hMstate]
          dsimp [Z] at hZfac
          exact hZfac
      }
      exact ⟨CompleteSplashOutcome.even g rfl rfl⟩
    · rcases hGodd with ⟨s, hs⟩
      let E := 2 + 3 ^ (s + 1) * Q
      have hEpos : 0 < E := by simp [E]
      have hEodd : Odd E := by
        have hodd : Odd (3 ^ (s + 1) * Q) :=
          (by exact ((by norm_num : Odd 3).pow).mul hQodd)
        rcases hodd with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        dsimp [E]
        omega
      let W := E + 1
      have hWpos : 0 < W := by simp [W]
      have hWeven : Even W := by
        rcases hEodd with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        dsimp [W]
        omega
      obtain ⟨L, P', hP'pos, hP'odd, hWfac⟩ :=
        exists_twoPow_mul_odd_factor hWpos
      have hLpos : 0 < L :=
        twoPow_exponent_pos_of_even hWeven hP'odd hWfac
      let g : OddCatcherGate := {
        ampTicks := r
        cleanTicks := s
        toPlusExtra := a
        outputGap := L
        inputPayload := P
        plusPayload := Q
        outputPayload := P'
        outputGap_pos := hLpos
        inputPayload_pos := hPpos
        plusPayload_pos := hQpos
        outputPayload_pos := hP'pos
        inputPayload_odd := hPodd
        plusPayload_odd := hQodd
        outputPayload_odd := hP'odd
        toPlus_balance := by
          rw [show 2 * s + 1 = G by omega]
          simp only [delayState]
          dsimp [A] at hAfac
          rw [← hAfac, hYsplit]
          ring
        catcher_balance := by
          have hEstate : minusOneState P' L = E := by
            simp only [minusOneState]
            omega
          rw [hEstate]
      }
      exact ⟨CompleteSplashOutcome.odd g rfl rfl⟩

end KontoroC

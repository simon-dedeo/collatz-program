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

/-- At fixed amplifier length and input payload, the generalized even branch
is uniquely decoded.  This includes the formerly missing zero-amplifier and
unit-output-gap boundary cases. -/
theorem eq_of_ampTicks_inputPayload (g h : EvenCleanupGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) : g = h := by
  have hfirst := twoPow_mul_odd_unique
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 2))
    (delayState_odd (by omega : 0 < 2 * h.cleanTicks + 2))
    (show 2 ^ g.toPlusExtra * g.plusState =
        2 ^ h.toPlusExtra * h.plusState by
      calc
        2 ^ g.toPlusExtra * g.plusState =
            3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := g.toPlus_balance
        _ = 3 ^ (h.ampTicks + 1) * h.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ h.toPlusExtra * h.plusState := h.toPlus_balance.symm)
  have hplus := TwoRailGate.delayState_unique g.plusPayload_odd
    h.plusPayload_odd hfirst.2
  have hs : g.cleanTicks = h.cleanTicks := by omega
  have hsecond := twoPow_mul_odd_unique
    (minusOneState_pos_odd g.outputPayload_pos g.outputGap_pos).2
    (minusOneState_pos_odd h.outputPayload_pos h.outputGap_pos).2
    (show 2 ^ g.toMinusExtra * g.endpoint =
        2 ^ h.toMinusExtra * h.endpoint by
      calc
        2 ^ g.toMinusExtra * g.endpoint =
            1 + 3 ^ (g.cleanTicks + 1) * g.plusPayload :=
              g.toMinus_balance
        _ = 1 + 3 ^ (h.cleanTicks + 1) * h.plusPayload := by
              rw [hs, hplus.2]
        _ = 2 ^ h.toMinusExtra * h.endpoint := h.toMinus_balance.symm)
  have hout := TwoRailGate.minusOneState_unique g.outputPayload_pos
    h.outputPayload_pos g.outputGap_pos h.outputGap_pos
    g.outputPayload_odd h.outputPayload_odd hsecond.2
  cases g
  cases h
  simp_all [plusState, endpoint]

/-- Odd-gap and generalized even-gap decoders cannot accept the same fixed
amplifier/payload pair. -/
theorem disjoint_odd_of_same_ampTicks_inputPayload
    (g : EvenCleanupGate) (h : OddCatcherGate)
    (hr : g.ampTicks = h.ampTicks)
    (hP : g.inputPayload = h.inputPayload) : False := by
  have hfactor := twoPow_mul_odd_unique
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 2))
    (delayState_odd (by omega : 0 < 2 * h.cleanTicks + 1))
    (show 2 ^ g.toPlusExtra * g.plusState =
        2 ^ h.toPlusExtra * h.plusState by
      calc
        2 ^ g.toPlusExtra * g.plusState =
            3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := g.toPlus_balance
        _ = 3 ^ (h.ampTicks + 1) * h.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ h.toPlusExtra * h.plusState := h.toPlus_balance.symm)
  have hgap := TwoRailGate.delayState_unique g.plusPayload_odd
    h.plusPayload_odd hfactor.2
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

theorem eq (h k : SplashHalt r P) : h = k := by
  have hu := twoPow_mul_odd_unique (by norm_num : Odd 1)
    (by norm_num : Odd 1)
    (show 2 ^ h.collisionExtra * 1 = 2 ^ k.collisionExtra * 1 by
      simpa [h.balance, k.balance])
  cases h
  cases k
  simp_all

theorem disjoint_even (h : SplashHalt r P) (g : EvenCleanupGate)
    (hr : g.ampTicks = r) (hP : g.inputPayload = P) : False := by
  have hfactor := twoPow_mul_odd_unique (by norm_num : Odd 1)
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 2))
    (show 2 ^ h.collisionExtra * 1 =
        2 ^ g.toPlusExtra * g.plusState by
      calc
        2 ^ h.collisionExtra * 1 = 3 ^ (r + 1) * P - 1 := by
          simpa using h.balance
        _ = 3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ g.toPlusExtra * g.plusState := g.toPlus_balance.symm)
  have hpos : 0 < g.plusPayload * 2 ^ (2 * g.cleanTicks + 2) :=
    Nat.mul_pos g.plusPayload_pos (Nat.pow_pos (by omega))
  have hone : 1 = g.plusState := hfactor.2
  simp only [EvenCleanupGate.plusState, delayState] at hone
  omega

theorem disjoint_odd (h : SplashHalt r P) (g : OddCatcherGate)
    (hr : g.ampTicks = r) (hP : g.inputPayload = P) : False := by
  have hfactor := twoPow_mul_odd_unique (by norm_num : Odd 1)
    (delayState_odd (by omega : 0 < 2 * g.cleanTicks + 1))
    (show 2 ^ h.collisionExtra * 1 =
        2 ^ g.toPlusExtra * g.plusState by
      calc
        2 ^ h.collisionExtra * 1 = 3 ^ (r + 1) * P - 1 := by
          simpa using h.balance
        _ = 3 ^ (g.ampTicks + 1) * g.inputPayload - 1 := by rw [hr, hP]
        _ = 2 ^ g.toPlusExtra * g.plusState := g.toPlus_balance.symm)
  have hpos : 0 < g.plusPayload * 2 ^ (2 * g.cleanTicks + 1) :=
    Nat.mul_pos g.plusPayload_pos (Nat.pow_pos (by omega))
  have hone : 1 = g.plusState := hfactor.2
  simp only [OddCatcherGate.plusState, delayState] at hone
  omega

end SplashHalt

/-- Output of the parity-complete decoder at fixed amplifier length and
positive odd input payload. -/
inductive CompleteSplashOutcome (r P : ℕ) : Type
  | halt (h : SplashHalt r P)
  | even (g : EvenCleanupGate)
      (hr : g.ampTicks = r) (hP : g.inputPayload = P)
  | odd (g : OddCatcherGate)
      (hr : g.ampTicks = r) (hP : g.inputPayload = P)

/-- The complete decoder is literal: at fixed `(r,P)` there is at most one
proof-carrying semantic outcome, not merely one branch label. -/
instance (r P : ℕ) : Subsingleton (CompleteSplashOutcome r P) where
  allEq x y := by
    cases x with
    | halt h =>
        cases y with
        | halt k => rw [h.eq k]
        | even g hr hP => exact (h.disjoint_even g hr hP).elim
        | odd g hr hP => exact (h.disjoint_odd g hr hP).elim
    | even g gr gP =>
        cases y with
        | halt h => exact (h.disjoint_even g gr gP).elim
        | even k kr kP =>
            have hgk := g.eq_of_ampTicks_inputPayload k
              (gr.trans kr.symm) (gP.trans kP.symm)
            subst k
            rfl
        | odd h hr hP =>
            exact (g.disjoint_odd_of_same_ampTicks_inputPayload h
              (gr.trans hr.symm) (gP.trans hP.symm)).elim
    | odd g gr gP =>
        cases y with
        | halt h => exact (h.disjoint_odd g gr gP).elim
        | even h hr hP =>
            exact (h.disjoint_odd_of_same_ampTicks_inputPayload g
              (hr.trans gr.symm) (hP.trans gP.symm)).elim
        | odd h hr hP =>
            have hgh := g.eq_of_ampTicks_inputPayload h
              (gr.trans hr.symm) (gP.trans hP.symm)
            subst h
            rfl

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

/-- Every positive odd payload has exactly one complete semantic outcome. -/
theorem existsUnique_completeSplashOutcome (r P : ℕ) (hPpos : 0 < P)
    (hPodd : Odd P) : ∃! x : CompleteSplashOutcome r P, True := by
  obtain ⟨x⟩ := exists_completeSplashOutcome r P hPpos hPodd
  exact ⟨x, trivial, fun y _ => Subsingleton.elim y x⟩

end KontoroC

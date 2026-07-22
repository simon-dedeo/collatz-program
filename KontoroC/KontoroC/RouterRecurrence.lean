/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.UniversalRouter
import KontoroC.CanonicalSplashDynamics

/-!
# Autonomous router payload recurrence

The public recurrence

`2^(r' + 3) * P' = 3^(r + 2) * P + 3`

constructs the unique complete splash of shape `(r,0,1,r'+1)`.  Consequently
an infinite positive-odd solution of this recurrence needs no separately
trusted branch, hidden payload, linkage, or growth fields: it is already a
canonical outward Collatz macro-orbit.
-/

namespace KontoroC

/-- One public recurrence step constructs an exact universal-router gate. -/
theorem exists_routerGate_of_payload_recurrence
    (r r' P P' : ℕ) (hPpos : 0 < P) (hPodd : Odd P)
    (hP'pos : 0 < P') (hP'odd : Odd P')
    (hrec : 2 ^ (r' + 3) * P' = 3 ^ (r + 2) * P + 3) :
    ∃ g : OddCatcherGate,
      g.ampTicks = r ∧ g.cleanTicks = 0 ∧ g.toPlusExtra = 1 ∧
      g.outputGap = r' + 1 ∧ g.inputPayload = P ∧
      g.outputPayload = P' := by
  let A := 3 ^ (r + 1) * P
  have hApos : 0 < A := by
    dsimp [A]
    exact Nat.mul_pos (Nat.pow_pos (by omega)) hPpos
  have hfactored : 8 * (2 ^ r' * P') = 3 * (A + 1) := by
    calc
      8 * (2 ^ r' * P') = 2 ^ (r' + 3) * P' := by
        rw [show r' + 3 = 3 + r' by omega, pow_add]
        norm_num
        ring
      _ = 3 ^ (r + 2) * P + 3 := hrec
      _ = 3 * (A + 1) := by
        dsimp [A]
        rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
        ring
  have hdvd8mul : 8 ∣ 3 * (A + 1) :=
    ⟨2 ^ r' * P', hfactored.symm⟩
  have hdvd8 : 8 ∣ A + 1 :=
    (by norm_num : Nat.Coprime 8 3).dvd_of_dvd_mul_left hdvd8mul
  obtain ⟨H, hH⟩ := hdvd8
  have hHpos : 0 < H := by omega
  have htail : 2 ^ r' * P' = 3 * H := by
    rw [hH] at hfactored
    omega
  let Q := 2 * H - 1
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hQodd : Odd Q := by
    rw [Nat.odd_iff]
    dsimp [Q]
    omega
  let g : OddCatcherGate := {
    ampTicks := r
    cleanTicks := 0
    toPlusExtra := 1
    outputGap := r' + 1
    inputPayload := P
    plusPayload := Q
    outputPayload := P'
    outputGap_pos := by omega
    inputPayload_pos := hPpos
    plusPayload_pos := hQpos
    outputPayload_pos := hP'pos
    inputPayload_odd := hPodd
    plusPayload_odd := hQodd
    outputPayload_odd := hP'odd
    toPlus_balance := by
      norm_num [delayState, Q]
      dsimp [A] at hH
      omega
    catcher_balance := by
      simp only [minusOneState, Q]
      rw [show r' + 1 = r' + 1 by rfl, pow_succ]
      have hleft : 2 ^ r' * 2 * P' = 2 * (2 ^ r' * P') := by ring
      rw [hleft, htail]
      norm_num
      omega
  }
  exact ⟨g, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The recurrence is exactly one step of the canonical partial decoder. -/
theorem completeSplashState_next_of_router_recurrence
    (x y : CompleteSplashState)
    (hrec : 2 ^ (y.railLength + 3) * y.payload =
      3 ^ (x.railLength + 2) * x.payload + 3) :
    x.next = some y := by
  obtain ⟨g, hgr, hgs, hga, hgL, hgP, hgP'⟩ :=
    exists_routerGate_of_payload_recurrence
      x.railLength y.railLength x.payload y.payload
      x.payload_pos x.payload_odd y.payload_pos y.payload_odd hrec
  let ox : CompleteSplashOutcome x.railLength x.payload :=
    .odd g hgr hgP
  have hdecoded : x.outcome = ox :=
    CompleteSplashOutcome.decoded_eq x.payload_pos x.payload_odd ox
  unfold CompleteSplashState.next
  rw [hdecoded]
  apply congrArg some
  cases x
  cases y
  simp_all [ox]

/-- The same recurrence step is strictly outward; no growth assumption is
needed in addition to the recurrence. -/
theorem completeSplashState_outward_of_router_recurrence
    (x y : CompleteSplashState)
    (hrec : 2 ^ (y.railLength + 3) * y.payload =
      3 ^ (x.railLength + 2) * x.payload + 3) :
    x.start < y.start := by
  obtain ⟨g, hgr, hgs, hga, hgL, hgP, hgP'⟩ :=
    exists_routerGate_of_payload_recurrence
      x.railLength y.railLength x.payload y.payload
      x.payload_pos x.payload_odd y.payload_pos y.payload_odd hrec
  have hgrows := g.outward_of_router_shape hgs hga
  simpa [CompleteSplashState.start, OddCatcherGate.start,
    OddCatcherGate.endpoint, hgr, hgL, hgP, hgP'] using hgrows

/-- The canonical decoder emits the literal universal-router word whenever
the public states satisfy the router recurrence. -/
theorem completeSplashState_word_eq_of_router_recurrence
    (x y : CompleteSplashState)
    (hrec : 2 ^ (y.railLength + 3) * y.payload =
      3 ^ (x.railLength + 2) * x.payload + 3) :
    x.word = List.replicate x.railLength 1 ++ [2, 1] := by
  obtain ⟨g, hgr, hgs, hga, hgL, hgP, hgP'⟩ :=
    exists_routerGate_of_payload_recurrence
      x.railLength y.railLength x.payload y.payload
      x.payload_pos x.payload_odd y.payload_pos y.payload_odd hrec
  let ox : CompleteSplashOutcome x.railLength x.payload :=
    .odd g hgr hgP
  have hdecoded : x.outcome = ox :=
    CompleteSplashOutcome.decoded_eq x.payload_pos x.payload_odd ox
  rw [CompleteSplashState.word, hdecoded]
  change g.word = List.replicate x.railLength 1 ++ [2, 1]
  simpa [hgr] using g.router_word_eq hgs hga

/-- Every next payload in the router recurrence is divisible by three. -/
theorem three_dvd_nextPayload_of_router_recurrence
    (r r' P P' : ℕ)
    (hrec : 2 ^ (r' + 3) * P' = 3 ^ (r + 2) * P + 3) :
    3 ∣ P' := by
  have hright : 3 ∣ 3 ^ (r + 2) * P + 3 := by
    refine ⟨3 ^ (r + 1) * P + 1, ?_⟩
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    ring
  have hprod : 3 ∣ 2 ^ (r' + 3) * P' := by
    rw [hrec]
    exact hright
  have hcop : Nat.Coprime 3 (2 ^ (r' + 3)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_left hprod

/-- After writing consecutive payloads as `3*Hprev` and `3*Hnext`, the
recurrence is exactly the deterministic valuation/odd-part update advertised
by the autonomous normal form. -/
theorem router_recurrence_normal_form
    (r r' Hprev Hnext : ℕ) (hHnextOdd : Odd Hnext)
    (hrec : 2 ^ (r' + 3) * (3 * Hnext) =
      3 ^ (r + 2) * (3 * Hprev) + 3) :
    let A := 3 ^ (r + 2) * Hprev + 1
    padicValNat 2 A = r' + 3 ∧ A.divMaxPow 2 = Hnext := by
  let A := 3 ^ (r + 2) * Hprev + 1
  have hHnextPos : 0 < Hnext := by
    have := Nat.odd_iff.mp hHnextOdd
    omega
  have hAeq : 2 ^ (r' + 3) * Hnext = A := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 3)
    calc
      3 * (2 ^ (r' + 3) * Hnext) =
          2 ^ (r' + 3) * (3 * Hnext) := by ring
      _ = 3 ^ (r + 2) * (3 * Hprev) + 3 := hrec
      _ = 3 * A := by dsimp [A]; ring
  have hAne : A ≠ 0 := by
    rw [← hAeq]
    positivity
  have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq hAne hAeq
    hHnextOdd.not_two_dvd_nat
  dsimp only
  constructor
  · change (Nat.maxPowDvdDiv 2 A).1 = r' + 3
    rw [hspec]
  · change (Nat.maxPowDvdDiv 2 A).2 = Hnext
    rw [hspec]

/-- A public all-level solution of the autonomous router recurrence. -/
structure InfiniteRouterPayloadRecurrence where
  railLength : ℕ → ℕ
  payload : ℕ → ℕ
  payload_pos : ∀ t, 0 < payload t
  payload_odd : ∀ t, Odd (payload t)
  recurrence : ∀ t,
    2 ^ (railLength (t + 1) + 3) * payload (t + 1) =
      3 ^ (railLength t + 2) * payload t + 3
  start_large : 4 < minusOneState (payload 0) (railLength 0 + 1)

namespace InfiniteRouterPayloadRecurrence

def state (g : InfiniteRouterPayloadRecurrence) (t : ℕ) :
    CompleteSplashState where
  railLength := g.railLength t
  payload := g.payload t
  payload_pos := g.payload_pos t
  payload_odd := g.payload_odd t

/-- The recurrence alone constructs the canonical surviving outward orbit. -/
noncomputable def toInfiniteCanonicalSplashOrbit
    (g : InfiniteRouterPayloadRecurrence) : InfiniteCanonicalSplashOrbit where
  state := g.state
  next_state t := completeSplashState_next_of_router_recurrence _ _
    (g.recurrence t)
  start_large := g.start_large
  outward t := completeSplashState_outward_of_router_recurrence _ _
    (g.recurrence t)

/-- Desired endpoint: an infinite positive-odd solution of `(R)` refutes the
literal standard Collatz conjecture. -/
theorem not_conjecture (g : InfiniteRouterPayloadRecurrence) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toInfiniteCanonicalSplashOrbit.not_conjecture

end InfiniteRouterPayloadRecurrence

end KontoroC

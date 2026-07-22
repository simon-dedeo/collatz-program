/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.NegativeShadow
import KontoroC.AffineBlock
import KontoroC.IntegerGate

/-!
# The `-1` (Mersenne) shadow grammar

This is the exact Lean endpoint for `search_mersenne_shadow.py`.  The signed
fixed point `-1` and its valuation word `[1]` are built into the interface;
all actual orbit states and valuation legality remain natural-number data.
-/

namespace KontoroC

/-- The worker's word at counter level `m` with final collision extra `e`.
It is deliberately defined through the general negative-shadow grammar, so
the generic endpoint and growth theorems apply without a second proof. -/
def mersenneMacroWord (m e : ℕ) : List ℕ :=
  shadowMacroWord [1] m e

@[simp] theorem repeatWord_singleton (k m : ℕ) :
    repeatWord [k] m = List.replicate m k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [repeatWord_succ, ih]
      calc
        List.replicate m k ++ [k] =
            List.replicate m k ++ List.replicate 1 k := by simp
        _ = List.replicate (m + 1) k :=
          (List.replicate_add m 1 k).symm

theorem bumpLast_append_singleton (u : List ℕ) (k e : ℕ) :
    bumpLast e (u ++ [k]) = u ++ [k + e] := by
  induction u with
  | nil => simp [bumpLast]
  | cons a u ih =>
      cases u with
      | nil => simp [bumpLast]
      | cons b bs =>
          change a :: bumpLast e ((b :: bs) ++ [k]) =
            a :: ((b :: bs) ++ [k + e])
          exact congrArg (List.cons a) ih

/-- Syntactic bridge to the Python worker's
`(1,) * (level - 1) + (1 + extra,)` representation. -/
theorem mersenneMacroWord_eq (m e : ℕ) (hm : 0 < m) :
    mersenneMacroWord m e =
      List.replicate (m - 1) 1 ++ [1 + e] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [mersenneMacroWord, shadowMacroWord, repeatWord_singleton]
  have hr : List.replicate (n + 1) 1 =
      List.replicate n 1 ++ [1] := by
    calc
      List.replicate (n + 1) 1 =
          List.replicate n 1 ++ List.replicate 1 1 :=
        List.replicate_add n 1 1
      _ = List.replicate n 1 ++ [1] := by simp
  rw [hr, bumpLast_append_singleton]
  simp

theorem mersenneMacroWord_succ (m e : ℕ) (hm : 0 < m) :
    mersenneMacroWord (m + 1) e = 1 :: mersenneMacroWord m e := by
  rw [mersenneMacroWord_eq _ _ (by omega), mersenneMacroWord_eq _ _ hm]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [List.replicate_succ]

@[simp] theorem mersenneMacroWord_length (m e : ℕ) (hm : 0 < m) :
    (mersenneMacroWord m e).length = m := by
  rw [mersenneMacroWord_eq m e hm]
  simp
  omega

@[simp] theorem mersenneMacroWord_totalValuation (m e : ℕ) (hm : 0 < m) :
    totalValuation (mersenneMacroWord m e) = m + e := by
  rw [mersenneMacroWord_eq m e hm]
  simp [totalValuation]
  omega

theorem repeatOne_affineOffset_balance (m : ℕ) :
    affineOffset (repeatWord [1] m) + 2 ^ m = 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [repeatWord_succ, affineOffset_append,
        repeatWord_totalValuation]
      rw [repeatWord_singleton] at ih
      simp only [List.length_cons, List.length_nil, zero_add, pow_one,
        repeatWord_singleton, totalValuation_cons, totalValuation_nil,
        add_zero, mul_one, affineOffset_cons, pow_zero, affineOffset_nil,
        mul_zero]
      rw [pow_succ, pow_succ]
      nlinarith

/-- The collision extra changes only the denominator.  The affine constant
of a level-`m` Mersenne block is exactly `3^m-2^m`. -/
@[simp] theorem mersenneMacroWord_affineOffset (m e : ℕ) (hm : 0 < m) :
    affineOffset (mersenneMacroWord m e) = 3 ^ m - 2 ^ m := by
  rw [mersenneMacroWord, shadowMacroWord,
    bumpLast_affineOffset (repeatWord_ne_nil (by simp) hm)]
  have hbalance := repeatOne_affineOffset_balance m
  omega

/-- Kernel-checked counterpart of the Python worker's compressed
`macro_block(level, extra)`. -/
theorem affineBlock_mersenneMacroWord (m e : ℕ) (hm : 0 < m) :
    AffineBlock.ofWord (mersenneMacroWord m e) =
      ⟨m, m + e, 3 ^ m - 2 ^ m⟩ := by
  ext <;> simp [AffineBlock.ofWord, hm]

theorem twoPow_mul_sub_one_pos_odd {m h : ℕ} (hm : 0 < m) (hh : 0 < h) :
    0 < 2 ^ m * h - 1 ∧ (2 ^ m * h - 1) % 2 = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let a := 2 ^ n * h
  have ha : 0 < a := by positivity
  have hbase : 2 ^ (n + 1) * h = 2 * a := by
    dsimp [a]
    rw [pow_succ]
    ring
  have hcoord : 2 ^ (n + 1) * h - 1 = 2 * (a - 1) + 1 := by
    rw [hbase]
    omega
  rw [hcoord]
  constructor
  · omega
  · simp

/-- The special grammar needs no independent legality oracle.  An exact
packet collision equation forces every nominal valuation to be one and the
last valuation to be `1+e`. -/
theorem mersenneMacro_legal_of_packet_equation {m e h y : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hyodd : y % 2 = 1)
    (hcollision : 2 ^ e * y = 3 ^ m * h - 1) :
    WordLegal (2 ^ m * h - 1) (mersenneMacroWord m e) ∧
      runWord (2 ^ m * h - 1) (mersenneMacroWord m e) = y := by
  induction m generalizing h with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          have hx := twoPow_mul_sub_one_pos_odd (m := 1) (h := h) (by omega) hh
          have hc : 2 ^ e * y = 3 * h - 1 := by
            simpa using hcollision
          have hstepEq : 2 ^ (1 + e) * y = 3 * (2 ^ 1 * h - 1) + 1 := by
            calc
              2 ^ (1 + e) * y = 2 * (2 ^ e * y) := by
                rw [pow_add]
                ring
              _ = 2 * (3 * h - 1) := by rw [hc]
              _ = 3 * (2 ^ 1 * h - 1) + 1 := by
                norm_num
                omega
          have hstep := legalInstruction_of_step_equation
            hx.1 hx.2 hyodd hstepEq
          simpa [mersenneMacroWord_eq 1 e (by omega), WordLegal, hstep.2]
            using hstep
      | succ n =>
          let x := 2 ^ (n + 2) * h - 1
          let z := 2 ^ (n + 1) * (3 * h) - 1
          have hx := twoPow_mul_sub_one_pos_odd
            (m := n + 2) (h := h) (by omega) hh
          have hz := twoPow_mul_sub_one_pos_odd
            (m := n + 1) (h := 3 * h) (by omega) (by positivity)
          let a := 2 ^ (n + 1) * h
          have ha : 0 < a := by positivity
          have hxcoord : x = 2 * a - 1 := by
            dsimp [x, a]
            congr 1
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            ring
          have hzcoord : z = 3 * a - 1 := by
            dsimp [z, a]
            congr 1
            ring
          have hstepEq : 2 * z = 3 * x + 1 := by
            rw [hxcoord, hzcoord]
            omega
          have hstep : LegalInstruction x 1 ∧ oddStep x = z :=
            legalInstruction_of_step_equation
              (by simpa [x] using hx.1) (by simpa [x] using hx.2)
              (by simpa [z] using hz.2) hstepEq
          have htailCollision :
              2 ^ e * y = 3 ^ (n + 1) * (3 * h) - 1 := by
            calc
              2 ^ e * y = 3 ^ (n + 2) * h - 1 := hcollision
              _ = 3 ^ (n + 1) * (3 * h) - 1 := by
                congr 1
                rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                ring
          have htail := ih (h := 3 * h)
            (by omega) (by positivity) htailCollision
          rw [mersenneMacroWord_succ (n + 1) e (by omega)]
          rw [show n + 1 + 1 = n + 2 by omega]
          change (LegalInstruction x 1 ∧ WordLegal (oddStep x)
              (mersenneMacroWord (n + 1) e)) ∧
            runWord (oddStep x) (mersenneMacroWord (n + 1) e) = y
          rw [hstep.2]
          exact ⟨⟨hstep.1, htail.1⟩, htail.2⟩

/-- Exact special case used by the Mersenne worker:
`x = 2^m h - 1` is sent to `(3^m h - 1) / 2^e`. -/
theorem mersenneShadow_endpoint {h x m e : ℕ} (hm : 0 < m)
    (hx : (x : ℤ) = -1 + (2 : ℤ) ^ m * h)
    (hlegal : WordLegal x (mersenneMacroWord m e)) :
    (2 ^ e : ℤ) * runWord x (mersenneMacroWord m e) =
      -1 + (3 : ℤ) ^ m * h := by
  have hfix : (2 ^ totalValuation [1] : ℤ) * (-1) =
      (3 ^ [1].length : ℤ) * (-1) + affineOffset [1] := by
    norm_num [totalValuation, affineOffset]
  simpa [mersenneMacroWord, totalValuation] using
    (negativeShadow_endpoint (c := (-1 : ℤ)) (h := (h : ℤ))
      (w := [1]) (x := x) (m := m) (e := e) (by simp) hm hfix hx hlegal)

/-- An infinite exact renewal program around the negative fixed point `-1`.
`packet_odd` and `extra_pos` preserve the search artifact's exact-coordinate
semantics, although the final soundness proof needs only positivity, legality,
renewal, and the uniform extra bound. -/
structure MersenneShadowOrbit where
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  extraBound : ℕ
  level0_pos : 0 < level0
  extra_pos : ∀ t, 0 < extra t
  packet_pos : ∀ t, 0 < packet t
  packet_odd : ∀ t, Odd (packet t)
  extra_le : ∀ t, extra t ≤ extraBound
  coordinate : ∀ t, (state t : ℤ) =
    -1 + (2 : ℤ) ^ (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (mersenneMacroWord (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) =
    -1 + (3 : ℤ) ^ (level0 + t) * packet t

namespace MersenneShadowOrbit

/-- Forget the `-1`-specific presentation and obtain the general bounded
phase-shadow certificate. -/
def toBoundedPhaseShadowOrbit (g : MersenneShadowOrbit) :
    BoundedPhaseShadowOrbit where
  controller := fun _ => -1
  word := fun _ => [1]
  level0 := g.level0
  extra := g.extra
  packet := g.packet
  state := g.state
  numerator := 3
  denominator := 2
  extraBound := g.extraBound
  controller_neg := by simp
  word_nonempty := by simp
  level0_pos := g.level0_pos
  packet_pos := g.packet_pos
  denominator_pos := by norm_num
  supercritical := by norm_num
  common_shape := by simp [totalValuation]
  extra_le := g.extra_le
  fixed_affine := by simp [totalValuation, affineOffset]
  coordinate := by
    intro t
    simpa [totalValuation] using g.coordinate t
  legal := by
    intro t
    simpa [mersenneMacroWord] using g.legal t
  renewal := by
    intro t
    simpa using g.renewal t

/-- An infinite bounded-extra Mersenne renewal is a literal counterexample to
the ordinary Collatz conjecture formalized in `CleanLean`. -/
theorem not_conjecture (g : MersenneShadowOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toBoundedPhaseShadowOrbit.not_conjecture

end MersenneShadowOrbit

/-- Pure Diophantine form of the Mersenne renewal.  Unlike
`MersenneShadowOrbit`, this artifact does not carry states, word legality, or
macro endpoints: all three are derived from the odd packet recurrence. -/
structure MersennePacketRenewal where
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  extraBound : ℕ
  level0_pos : 0 < level0
  extra_pos : ∀ t, 0 < extra t
  packet_pos : ∀ t, 0 < packet t
  packet_odd : ∀ t, Odd (packet t)
  extra_le : ∀ t, extra t ≤ extraBound
  collision : ∀ t,
    2 ^ extra t * (2 ^ (level0 + t + 1) * packet (t + 1) - 1) =
      3 ^ (level0 + t) * packet t - 1

namespace MersennePacketRenewal

/-- The positive natural state encoded by a packet. -/
def state (g : MersennePacketRenewal) (t : ℕ) : ℕ :=
  2 ^ (g.level0 + t) * g.packet t - 1

theorem state_coordinate (g : MersennePacketRenewal) (t : ℕ) :
    (g.state t : ℤ) =
      -1 + (2 : ℤ) ^ (g.level0 + t) * g.packet t := by
  have hp : 0 < 2 ^ (g.level0 + t) * g.packet t :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (g.packet_pos t)
  rw [state, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The packet collision alone synthesizes the exact natural valuation word
and its endpoint. -/
theorem legal_and_endpoint (g : MersennePacketRenewal) (t : ℕ) :
    WordLegal (g.state t)
        (mersenneMacroWord (g.level0 + t) (g.extra t)) ∧
      runWord (g.state t)
        (mersenneMacroWord (g.level0 + t) (g.extra t)) = g.state (t + 1) := by
  apply mersenneMacro_legal_of_packet_equation
  · exact Nat.add_pos_left g.level0_pos t
  · exact g.packet_pos t
  · simpa [state, Nat.add_assoc] using
      (twoPow_mul_sub_one_pos_odd
        (m := g.level0 + t + 1) (h := g.packet (t + 1))
        (Nat.add_pos_right (g.level0 + t) Nat.zero_lt_one)
        (g.packet_pos (t + 1))).2
  · simpa [state, Nat.add_assoc] using g.collision t

/-- Addition-only form of the packet collision. -/
theorem collision_balance (g : MersennePacketRenewal) (t : ℕ) :
    2 ^ g.extra t *
          (2 ^ (g.level0 + t + 1) * g.packet (t + 1)) + 1 =
      3 ^ (g.level0 + t) * g.packet t + 2 ^ g.extra t := by
  let C := 2 ^ g.extra t
  let A := 2 ^ (g.level0 + t + 1) * g.packet (t + 1)
  let B := 3 ^ (g.level0 + t) * g.packet t
  have hc := g.collision t
  have ha : 0 < A :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (g.packet_pos (t + 1))
  have hb : 0 < B :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (g.packet_pos t)
  have hC : 0 < C := Nat.pow_pos (by omega)
  change C * (A - 1) = B - 1 at hc
  have hdist : C * (A - 1) = C * A - C := by
    simpa using Nat.mul_sub_left_distrib C A 1
  change C * A + 1 = B + C
  rw [hdist] at hc
  have hCA : C ≤ C * A := Nat.le_mul_of_pos_right C ha
  calc
    C * A + 1 = (C * A - C) + C + 1 := by
      rw [Nat.sub_add_cancel hCA]
    _ = (B - 1) + C + 1 := by rw [hc]
    _ = (B - 1) + 1 + C := by omega
    _ = B + C := by rw [Nat.sub_add_cancel hb]

/-- Exact modular scheduler for the next packet.  At level `m`, the collision
forces `2^e * 2^(m+1) * h_next` to equal `2^e-1` modulo `3^m`. -/
theorem next_packet_mod_threePow (g : MersennePacketRenewal) (t : ℕ) :
    2 ^ g.extra t * (2 ^ (g.level0 + t + 1) * g.packet (t + 1)) ≡
      2 ^ g.extra t - 1 [MOD 3 ^ (g.level0 + t)] := by
  have hbalance := g.collision_balance t
  have hpow : 0 < 2 ^ g.extra t := Nat.pow_pos (by omega)
  have heq :
      2 ^ g.extra t * (2 ^ (g.level0 + t + 1) * g.packet (t + 1)) =
        3 ^ (g.level0 + t) * g.packet t + (2 ^ g.extra t - 1) := by
    omega
  simp [Nat.ModEq, heq]

/-- The modular scheduler selects at most one next-packet class modulo
`3^m`, because its power-of-two coefficient is invertible there. -/
theorem next_packet_unique_mod_threePow {m e u v r : ℕ}
    (hu : 2 ^ e * (2 ^ (m + 1) * u) ≡ r [MOD 3 ^ m])
    (hv : 2 ^ e * (2 ^ (m + 1) * v) ≡ r [MOD 3 ^ m]) :
    u ≡ v [MOD 3 ^ m] := by
  have hprod := hu.trans hv.symm
  have hcop : (3 ^ m).Coprime (2 ^ e * 2 ^ (m + 1)) := by
    have hp := (by norm_num : Nat.Coprime 3 2).pow m (e + (m + 1))
    simpa [pow_add] using hp
  apply Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one
  simpa [mul_assoc] using hprod

/-- Uniformly bounded collision extras force the positive packet sequence to
be strictly increasing from some point onward. -/
theorem eventually_packet_grows (g : MersennePacketRenewal) :
    ∃ T, ∀ t, T ≤ t → g.packet t < g.packet (t + 1) := by
  obtain ⟨N, hN⟩ := eventually_twoPow_mul_pow_lt_pow
    (P := 3) (Q := 2) (E := g.extraBound + 1) (by omega) (by omega)
  refine ⟨N, fun t ht => ?_⟩
  let m := g.level0 + t
  let e := g.extra t
  have hm : N ≤ m := by
    dsimp [m]
    omega
  have he : e + 1 ≤ g.extraBound + 1 := Nat.succ_le_succ (g.extra_le t)
  have hratio0 := hN m hm (e + 1) he
  have hratio : 2 ^ e * 2 ^ (m + 1) < 3 ^ m := by
    calc
      2 ^ e * 2 ^ (m + 1) = 2 ^ (e + 1) * 2 ^ m := by
        rw [pow_succ, pow_succ]
        ring
      _ < 3 ^ m := hratio0
  have hbalance := g.collision_balance t
  change 2 ^ e * (2 ^ (m + 1) * g.packet (t + 1)) + 1 =
      3 ^ m * g.packet t + 2 ^ e at hbalance
  have hepow : 2 ≤ 2 ^ e := by
    have := Nat.one_lt_pow (Nat.ne_of_gt (g.extra_pos t)) (by omega : 1 < 2)
    change 1 < 2 ^ e at this
    omega
  have hlower : 3 ^ m * g.packet t <
      (2 ^ e * 2 ^ (m + 1)) * g.packet (t + 1) := by
    have hlower' : 3 ^ m * g.packet t <
        2 ^ e * (2 ^ (m + 1) * g.packet (t + 1)) := by omega
    simpa [mul_assoc] using hlower'
  by_contra hnot
  have hpacket : g.packet (t + 1) ≤ g.packet t := by omega
  have hupper : (2 ^ e * 2 ^ (m + 1)) * g.packet (t + 1) <
      3 ^ m * g.packet t :=
    (Nat.mul_le_mul_left _ hpacket).trans_lt
      ((Nat.mul_lt_mul_right (g.packet_pos t)).2 hratio)
  omega

/-- Concatenate `n` successive Mersenne macros from a prescribed collision
stream, beginning at schedule time `t`. -/
def mersenneScheduleWord (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) :
    ℕ → List ℕ
  | 0 => []
  | n + 1 => mersenneMacroWord (level0 + t) (extra t) ++
      mersenneScheduleWord level0 extra (t + 1) n

@[simp] theorem mersenneScheduleWord_zero
    (level0 : ℕ) (extra : ℕ → ℕ) (t : ℕ) :
    mersenneScheduleWord level0 extra t 0 = [] := rfl

@[simp] theorem mersenneScheduleWord_succ
    (level0 : ℕ) (extra : ℕ → ℕ) (t n : ℕ) :
    mersenneScheduleWord level0 extra t (n + 1) =
      mersenneMacroWord (level0 + t) (extra t) ++
        mersenneScheduleWord level0 extra (t + 1) n := rfl

/-- The pure packet recurrence realizes every finite concatenated schedule
prefix, not just each macro in isolation. -/
theorem schedule_legal_and_endpoint (g : MersennePacketRenewal) (t n : ℕ) :
    WordLegal (g.state t)
        (mersenneScheduleWord g.level0 g.extra t n) ∧
      runWord (g.state t) (mersenneScheduleWord g.level0 g.extra t n) =
        g.state (t + n) := by
  induction n generalizing t with
  | zero =>
      constructor
      · trivial
      · rfl
  | succ n ih =>
      rw [mersenneScheduleWord_succ, wordLegal_append_iff, runWord_append]
      have hfirst := g.legal_and_endpoint t
      have htail := ih (t + 1)
      constructor
      · refine ⟨hfirst.1, ?_⟩
        rw [hfirst.2]
        exact htail.1
      · rw [hfirst.2, htail.2]
        congr 1
        omega

theorem schedule_totalValuation_ge (g : MersennePacketRenewal) (t n : ℕ) :
    n ≤ totalValuation (mersenneScheduleWord g.level0 g.extra t n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [mersenneScheduleWord_succ, totalValuation_append,
        mersenneMacroWord_totalValuation _ _
          (Nat.add_pos_left g.level0_pos t)]
      have htail := ih (t + 1)
      have hfirst : 0 < g.level0 + t + g.extra t :=
        Nat.add_pos_left (Nat.add_pos_left g.level0_pos t) (g.extra t)
      omega

/-- Exact compressed affine equation for one realized packet macro. -/
theorem block_affine_equation (g : MersennePacketRenewal) (t : ℕ) :
    2 ^ (g.level0 + t + g.extra t) * g.state (t + 1) =
      3 ^ (g.level0 + t) * g.state t +
        (3 ^ (g.level0 + t) - 2 ^ (g.level0 + t)) := by
  have h := valuationWord_affine_identity (g.legal_and_endpoint t).1
  rw [(g.legal_and_endpoint t).2,
    mersenneMacroWord_totalValuation _ _
      (Nat.add_pos_left g.level0_pos t),
    mersenneMacroWord_length _ _ (Nat.add_pos_left g.level0_pos t),
    mersenneMacroWord_affineOffset _ _
      (Nat.add_pos_left g.level0_pos t)] at h
  exact h

/-- Shifted-coordinate form around the fixed point `-1`.  This is the exact
finite identity whose backward iteration yields the lacunary 2-adic series. -/
theorem block_shifted_balance (g : MersennePacketRenewal) (t : ℕ) :
    2 ^ (g.level0 + t + g.extra t) * (g.state (t + 1) + 1) =
      3 ^ (g.level0 + t) * (g.state t + 1) +
        2 ^ (g.level0 + t) * (2 ^ g.extra t - 1) := by
  have haff := g.block_affine_equation t
  have hthree : 2 ^ (g.level0 + t) ≤ 3 ^ (g.level0 + t) :=
    Nat.pow_le_pow_left (by omega) _
  have hthree_cancel :
      3 ^ (g.level0 + t) - 2 ^ (g.level0 + t) +
          2 ^ (g.level0 + t) = 3 ^ (g.level0 + t) :=
    Nat.sub_add_cancel hthree
  have hextra_cancel :
      2 ^ (g.level0 + t) * (2 ^ g.extra t - 1) +
          2 ^ (g.level0 + t) =
        2 ^ (g.level0 + t) * 2 ^ g.extra t := by
    rw [Nat.mul_sub_left_distrib, mul_one, Nat.sub_add_cancel]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  rw [pow_add] at haff ⊢
  calc
    (2 ^ (g.level0 + t) * 2 ^ g.extra t) *
          (g.state (t + 1) + 1) =
        (2 ^ (g.level0 + t) * 2 ^ g.extra t) *
            g.state (t + 1) +
          2 ^ (g.level0 + t) * 2 ^ g.extra t := by ring
    _ = (3 ^ (g.level0 + t) * g.state t +
          (3 ^ (g.level0 + t) - 2 ^ (g.level0 + t))) +
        2 ^ (g.level0 + t) * 2 ^ g.extra t := by rw [haff]
    _ = 3 ^ (g.level0 + t) * (g.state t + 1) +
        2 ^ (g.level0 + t) * (2 ^ g.extra t - 1) := by
      rw [mul_add, mul_one]
      omega

def backwardCoeff (g : MersennePacketRenewal) (t : ℕ) : ℚ :=
  (2 : ℚ) ^ (g.level0 + t + g.extra t) /
    (3 : ℚ) ^ (g.level0 + t)

def backwardDefect (g : MersennePacketRenewal) (t : ℕ) : ℚ :=
  ((2 : ℚ) ^ (g.level0 + t) *
      ((2 ^ g.extra t - 1 : ℕ) : ℚ)) /
    (3 : ℚ) ^ (g.level0 + t)

/-- Division form of `block_shifted_balance`, suitable for finite backward
iteration in `ℚ` and later passage to `ℚ₂`. -/
theorem block_shifted_backward (g : MersennePacketRenewal) (t : ℕ) :
    (g.state t : ℚ) + 1 =
      g.backwardCoeff t * ((g.state (t + 1) : ℚ) + 1) -
        g.backwardDefect t := by
  have h :
      (2 : ℚ) ^ (g.level0 + t + g.extra t) *
          ((g.state (t + 1) : ℚ) + 1) =
        (3 : ℚ) ^ (g.level0 + t) * ((g.state t : ℚ) + 1) +
          (2 : ℚ) ^ (g.level0 + t) *
            ((2 ^ g.extra t - 1 : ℕ) : ℚ) := by
    exact_mod_cast g.block_shifted_balance t
  dsimp [backwardCoeff, backwardDefect]
  have hthree : (3 : ℚ) ^ (g.level0 + t) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Product of the first `n` coefficients in a backward affine recurrence. -/
def backwardPrefixProduct (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => backwardPrefixProduct a n * a n

/-- The defect accumulated while unrolling a backward affine recurrence. -/
def backwardPrefixDefect (a b : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 =>
      backwardPrefixDefect a b n + backwardPrefixProduct a n * b n

/-- Pure finite algebra behind the proposed 2-adic reduction.  No convergence
or infinitary assumption occurs here. -/
theorem backward_affine_unroll {y a b : ℕ → ℚ}
    (hstep : ∀ t, y t = a t * y (t + 1) - b t) (n : ℕ) :
    y 0 = backwardPrefixProduct a n * y n -
      backwardPrefixDefect a b n := by
  induction n with
  | zero => simp [backwardPrefixProduct, backwardPrefixDefect]
  | succ n ih =>
      calc
        y 0 = backwardPrefixProduct a n * y n -
            backwardPrefixDefect a b n := ih
        _ = backwardPrefixProduct a n *
              (a n * y (n + 1) - b n) -
            backwardPrefixDefect a b n := by rw [← hstep n]
        _ = backwardPrefixProduct a (n + 1) * y (n + 1) -
            backwardPrefixDefect a b (n + 1) := by
          simp only [backwardPrefixProduct, backwardPrefixDefect]
          ring

/-- Exact finite truncation formula for the unique Mersenne packet candidate.
The unresolved research step is to pass this identity to `ℚ₂` and exclude an
ordinary nonnegative integer for a chosen infinite extra stream. -/
theorem shifted_state_finite_series (g : MersennePacketRenewal) (n : ℕ) :
    (g.state 0 : ℚ) + 1 =
      backwardPrefixProduct g.backwardCoeff n * ((g.state n : ℚ) + 1) -
        backwardPrefixDefect g.backwardCoeff g.backwardDefect n := by
  exact backward_affine_unroll
    (y := fun t => (g.state t : ℚ) + 1)
    (a := g.backwardCoeff) (b := g.backwardDefect)
    (fun t => g.block_shifted_backward t) n

/-- Fixing the entire collision-extra stream leaves room for at most one
ordinary initial state satisfying the infinite Mersenne packet recurrence. -/
theorem initial_state_unique (g h : MersennePacketRenewal)
    (hlevel : g.level0 = h.level0) (hextra : g.extra = h.extra) :
    g.state 0 = h.state 0 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max (g.state 0) (h.state 0))
    (by norm_num : 1 < (2 : ℕ))
  let w := mersenneScheduleWord g.level0 g.extra 0 (N + 1)
  have hgw : WordLegal (g.state 0) w :=
    (g.schedule_legal_and_endpoint 0 (N + 1)).1
  have hhw : WordLegal (h.state 0) w := by
    have hh := (h.schedule_legal_and_endpoint 0 (N + 1)).1
    rw [← hlevel, ← hextra] at hh
    exact hh
  have hsum : N + 1 ≤ totalValuation w := by
    exact g.schedule_totalValuation_ge 0 (N + 1)
  have hw : w ≠ [] := by
    intro hw
    simp [hw] at hsum
  have hpositive : PositiveWord w := wordLegal_positive_entries hgw
  have hgcong := finalCongruence_of_wordLegal hw hpositive hgw
  have hhcong := finalCongruence_of_wordLegal hw hpositive hhw
  have hmod := finalCongruence_unique_mod w hgcong hhcong
  have hpow : 2 ^ N ≤ 2 ^ (totalValuation w + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hglt : g.state 0 < 2 ^ (totalValuation w + 1) :=
    (le_max_left _ _).trans_lt hN |>.trans_le hpow
  have hhlt : h.state 0 < 2 ^ (totalValuation w + 1) :=
    (le_max_right _ _).trans_lt hN |>.trans_le hpow
  exact hmod.eq_of_lt_of_lt hglt hhlt

/-- Consequently the initial odd packet itself is unique for a fixed level
and infinite extra stream. -/
theorem initial_packet_unique (g h : MersennePacketRenewal)
    (hlevel : g.level0 = h.level0) (hextra : g.extra = h.extra) :
    g.packet 0 = h.packet 0 := by
  have hs := g.initial_state_unique h hlevel hextra
  simp only [state, Nat.add_zero] at hs
  rw [hlevel] at hs
  have hgpos : 0 < 2 ^ h.level0 * g.packet 0 :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (g.packet_pos 0)
  have hhpos : 0 < 2 ^ h.level0 * h.packet 0 :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (h.packet_pos 0)
  have hprod : 2 ^ h.level0 * g.packet 0 =
      2 ^ h.level0 * h.packet 0 := by omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hprod

/-- In fact the entire positive packet sequence is determined by the level
and infinite collision-extra stream, whenever an ordinary solution exists. -/
theorem packet_function_unique (g h : MersennePacketRenewal)
    (hlevel : g.level0 = h.level0) (hextra : g.extra = h.extra) :
    g.packet = h.packet := by
  funext t
  let w := mersenneScheduleWord g.level0 g.extra 0 t
  have hgendpoint := (g.schedule_legal_and_endpoint 0 t).2
  have hhendpoint := (h.schedule_legal_and_endpoint 0 t).2
  rw [← hlevel, ← hextra] at hhendpoint
  simp only [zero_add] at hgendpoint hhendpoint
  have hstate0 := g.initial_state_unique h hlevel hextra
  have hstate : g.state t = h.state t := by
    simpa [w] using hgendpoint.symm.trans (hstate0 ▸ hhendpoint)
  simp only [state] at hstate
  rw [hlevel] at hstate
  have hgpos : 0 < 2 ^ (h.level0 + t) * g.packet t :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (g.packet_pos t)
  have hhpos : 0 < 2 ^ (h.level0 + t) * h.packet t :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (h.packet_pos t)
  have hprod : 2 ^ (h.level0 + t) * g.packet t =
      2 ^ (h.level0 + t) * h.packet t := by omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hprod

/-- Compile the pure recurrence into the earlier all-level orbit artifact. -/
def toMersenneShadowOrbit (g : MersennePacketRenewal) :
    MersenneShadowOrbit where
  level0 := g.level0
  extra := g.extra
  packet := g.packet
  state := g.state
  extraBound := g.extraBound
  level0_pos := g.level0_pos
  extra_pos := g.extra_pos
  packet_pos := g.packet_pos
  packet_odd := g.packet_odd
  extra_le := g.extra_le
  coordinate := g.state_coordinate
  legal := fun t => (g.legal_and_endpoint t).1
  renewal := by
    intro t
    have hendpoint := mersenneShadow_endpoint
      (m := g.level0 + t) (e := g.extra t) (h := g.packet t)
      (x := g.state t) (Nat.add_pos_left g.level0_pos t) (g.state_coordinate t)
      (g.legal_and_endpoint t).1
    rw [(g.legal_and_endpoint t).2] at hendpoint
    exact hendpoint

/-- A positive odd packet recurrence with uniformly bounded collision extras
is already a literal disproof certificate. -/
theorem not_conjecture (g : MersennePacketRenewal) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMersenneShadowOrbit.not_conjecture

/-- Direct endpoint for `search_mersenne_constants.py`.  A single positive
collision extra is repeated at every increasing counter level. -/
theorem not_conjecture_of_constant_extra
    {level0 e : ℕ} {packet : ℕ → ℕ}
    (hlevel0 : 0 < level0) (he : 0 < e)
    (hpacket_pos : ∀ t, 0 < packet t)
    (hpacket_odd : ∀ t, Odd (packet t))
    (hcollision : ∀ t,
      2 ^ e * (2 ^ (level0 + t + 1) * packet (t + 1) - 1) =
        3 ^ (level0 + t) * packet t - 1) :
    ¬CleanLean.Collatz.Conjecture := by
  let g : MersennePacketRenewal :=
    { level0 := level0
      extra := fun _ => e
      packet := packet
      extraBound := e
      level0_pos := hlevel0
      extra_pos := fun _ => he
      packet_pos := hpacket_pos
      packet_odd := hpacket_odd
      extra_le := by simp
      collision := hcollision }
  exact g.not_conjecture

end MersennePacketRenewal

end KontoroC

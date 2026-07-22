/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.NegativeShadow

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
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            ring
          have hzcoord : z = 3 * a - 1 := by
            dsimp [z, a]
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

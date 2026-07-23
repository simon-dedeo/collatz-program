/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLDyadicReset

/-!
# Finite covering dispatchers

This file isolates the abstract affine content of a proposed finite
counterexample certificate.  It deliberately contains no claim that an edge
is a genuine signed-Syracuse macro.  That semantic bridge must be proved in a
separate module for any concrete macro library.
-/

namespace KontoroC
namespace KLCoveringDispatcher

structure Edge (Q : Type*) where
  target : Q
  N : ℕ
  O : ℕ
  delta : ℤ

structure ModeData where
  center : ℤ
  shadowLength : ℕ

/-- A finite table covering every mode and every `B`-bit payload residue.

`realize` is the finite certificate boundary: for each covered cylinder and
each payload above the common threshold, it supplies the next natural
payload, the exact affine reset recurrence, and the desired state
positivity/growth inequalities. -/
structure CoveringDispatcher (Q : Type*) [Fintype Q] where
  B : ℕ
  H : ℕ
  modeData : Q → ModeData
  edge : Q → Fin (2 ^ B) → Edge Q
  width_le : ∀ q r, (edge q r).N ≤ B
  target_length : ∀ q r,
    (modeData (edge q r).target).shadowLength = (edge q r).N
  realize : ∀ (q : Q) (r : Fin (2 ^ B)) (m : ℕ),
    m % 2 ^ B = r.val → H ≤ m →
      ∃ mNext : ℕ,
        H ≤ mNext ∧
        (2 : ℤ) ^ (edge q r).N * mNext =
          (3 : ℤ) ^ (edge q r).O * m + (edge q r).delta ∧
        0 < (modeData q).center +
          (2 : ℤ) ^ (modeData q).shadowLength * m ∧
        (modeData (edge q r).target).center +
            (2 : ℤ) ^ (edge q r).N * mNext >
          (modeData q).center +
            (2 : ℤ) ^ (modeData q).shadowLength * m

variable {Q : Type*} [Fintype Q]

namespace CoveringDispatcher

structure Config (Q : Type*) where
  mode : Q
  payload : ℕ

def payloadResidue (D : CoveringDispatcher Q) (m : ℕ) : Fin (2 ^ D.B) :=
  ⟨m % 2 ^ D.B, Nat.mod_lt _ (by positivity)⟩

def selectedEdge (D : CoveringDispatcher Q) (c : Config Q) : Edge Q :=
  D.edge c.mode (payloadResidue D c.payload)

theorem payloadResidue_spec (D : CoveringDispatcher Q) (m : ℕ) :
    m % 2 ^ D.B = (payloadResidue D m).val := rfl

noncomputable def nextPayload (D : CoveringDispatcher Q) (c : Config Q)
    (hc : D.H ≤ c.payload) : ℕ :=
  (D.realize c.mode (payloadResidue D c.payload) c.payload rfl hc).choose

theorem nextPayload_spec (D : CoveringDispatcher Q) (c : Config Q)
    (hc : D.H ≤ c.payload) :
    D.H ≤ D.nextPayload c hc ∧
    (2 : ℤ) ^ (D.selectedEdge c).N * D.nextPayload c hc =
      (3 : ℤ) ^ (D.selectedEdge c).O * c.payload +
        (D.selectedEdge c).delta ∧
    0 < (D.modeData c.mode).center +
      (2 : ℤ) ^ (D.modeData c.mode).shadowLength * c.payload ∧
    (D.modeData (D.selectedEdge c).target).center +
        (2 : ℤ) ^ (D.selectedEdge c).N * D.nextPayload c hc >
      (D.modeData c.mode).center +
        (2 : ℤ) ^ (D.modeData c.mode).shadowLength * c.payload := by
  exact (D.realize c.mode (payloadResidue D c.payload) c.payload rfl hc).choose_spec

abbrev GoodConfig (D : CoveringDispatcher Q) :=
  {c : Config Q // D.H ≤ c.payload}

noncomputable def nextGood (D : CoveringDispatcher Q) (c : D.GoodConfig) :
    D.GoodConfig :=
  ⟨⟨(D.selectedEdge c.1).target, D.nextPayload c.1 c.2⟩,
    (D.nextPayload_spec c.1 c.2).1⟩

/-- The recursive orbit is an iterate on threshold-certified configurations,
so no partial division or default branch enters the construction. -/
noncomputable def goodOrbit (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) : D.GoodConfig :=
  (D.nextGood^[n]) ⟨⟨q0, M⟩, hM⟩

noncomputable def orbit (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) : Config Q :=
  (D.goodOrbit q0 M hM n).1

theorem goodOrbit_succ (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    D.goodOrbit q0 M hM (n + 1) =
      D.nextGood (D.goodOrbit q0 M hM n) := by
  unfold goodOrbit
  rw [show n + 1 = n.succ by omega, Function.iterate_succ_apply']

theorem orbit_zero (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) :
    D.orbit q0 M hM 0 = ⟨q0, M⟩ := rfl

theorem orbit_payload_ge (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    D.H ≤ (D.orbit q0 M hM n).payload := by
  exact (D.goodOrbit q0 M hM n).2

theorem orbit_succ (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    D.orbit q0 M hM (n + 1) =
      ⟨(D.selectedEdge (D.orbit q0 M hM n)).target,
        D.nextPayload (D.orbit q0 M hM n)
          (D.orbit_payload_ge q0 M hM n)⟩ := by
  change (D.goodOrbit q0 M hM (n + 1)).1 = _
  rw [goodOrbit_succ]
  rfl

def resetState (D : CoveringDispatcher Q) (c : Config Q) : ℤ :=
  (D.modeData c.mode).center +
    (2 : ℤ) ^ (D.modeData c.mode).shadowLength * c.payload

/-- QM142a, the exact reset recurrence along the table-generated orbit. -/
theorem orbit_reset_exact (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    let c := D.orbit q0 M hM n
    let e := D.selectedEdge c
    (2 : ℤ) ^ e.N * (D.orbit q0 M hM (n + 1)).payload =
      (3 : ℤ) ^ e.O * c.payload + e.delta := by
  rw [orbit_succ]
  exact (D.nextPayload_spec _ (D.orbit_payload_ge q0 M hM n)).2.1

theorem orbit_resetState_pos (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    0 < D.resetState (D.orbit q0 M hM n) := by
  exact (D.nextPayload_spec _ (D.orbit_payload_ge q0 M hM n)).2.2.1

/-- QM142c, strict growth of the literal reset-state expression certified by
the table. -/
theorem orbit_resetState_strictMono
    (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ)
    (hM : D.H ≤ M) (n : ℕ) :
    D.resetState (D.orbit q0 M hM n) <
      D.resetState (D.orbit q0 M hM (n + 1)) := by
  rw [orbit_succ]
  unfold resetState
  rw [show (D.modeData
      (D.selectedEdge (D.orbit q0 M hM n)).target).shadowLength =
      (D.selectedEdge (D.orbit q0 M hM n)).N by
    exact D.target_length _ _]
  exact
    (D.nextPayload_spec _ (D.orbit_payload_ge q0 M hM n)).2.2.2

/-- Abstract finite-certificate consumer.  It produces an infinite natural
payload chain with exact affine resets and positive, strictly increasing
reset-state expressions.  It intentionally makes no Syracuse claim. -/
theorem exists_infinite_growing_orbit
    (D : CoveringDispatcher Q) (q0 : Q) (M : ℕ) (hM : D.H ≤ M) :
    ∃ c : ℕ → Config Q,
      c 0 = ⟨q0, M⟩ ∧
      (∀ n, D.H ≤ (c n).payload) ∧
      (∀ n, 0 < D.resetState (c n)) ∧
      (∀ n, D.resetState (c n) < D.resetState (c (n + 1))) := by
  refine ⟨D.orbit q0 M hM, rfl, ?_, ?_, ?_⟩
  · exact D.orbit_payload_ge q0 M hM
  · exact D.orbit_resetState_pos q0 M hM
  · exact D.orbit_resetState_strictMono q0 M hM

end CoveringDispatcher

end KLCoveringDispatcher
end KontoroC

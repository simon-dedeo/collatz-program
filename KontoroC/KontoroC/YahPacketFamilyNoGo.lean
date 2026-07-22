/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahPerpetualGrowthNoGo

/-!
# The first QM7 packet family is not closed

The proposed packet family

`P(s,q) = 2 (0012)^s (01)^q`

always begins with trit two.  Its head-two macro is `Q₀(Q₁(tail))`.
If the tail is nonempty then it begins with zero, and the two sweeps turn that
first zero into one and then zero.  If the tail is empty, the terminal deposits
produce the singleton word `1`.  Thus the endpoint never begins with two and
cannot be another member of the same packet family.

This is a one-step family nonclosure theorem, not a termination theorem: a
larger compiler could route the endpoint through other packet types before
returning.
-/

namespace KontoroC
namespace YahPacketFamilyNoGo

open YahQueueMacro
open YahPerpetualGrowthNoGo
open Carry Trit

def repeatBlock (block : List Trit) : ℕ → List Trit
  | 0 => []
  | n + 1 => block ++ repeatBlock block n

def packetTail (s q : ℕ) : List Trit :=
  repeatBlock [Trit.zero, Trit.zero, Trit.one, Trit.two] s ++
    repeatBlock [Trit.zero, Trit.one] q

def packet (s q : ℕ) : List Trit := Trit.two :: packetTail s q

@[simp] theorem packet_ne_nil (s q : ℕ) : packet s q ≠ [] := by
  simp [packet]

@[simp] theorem queueMacro_packet_zero_zero :
    queueMacro (packet 0 0) = [Trit.one] := by
  rfl

theorem queueMacro_packet_succ_head_zero (s q : ℕ) :
    ∃ rest, queueMacro (packet (s + 1) q) = Trit.zero :: rest := by
  simp [packet, packetTail, repeatBlock, queueMacro, carrySweep, transition]

theorem queueMacro_packet_zero_succ_head_zero (q : ℕ) :
    ∃ rest, queueMacro (packet 0 (q + 1)) = Trit.zero :: rest := by
  simp [packet, packetTail, repeatBlock, queueMacro, carrySweep, transition]

/-- The QM7 packet is never sent to another packet of the same two-parameter
family, for any source or target coordinates. -/
theorem queueMacro_packet_ne_packet (s q s' q' : ℕ) :
    queueMacro (packet s q) ≠ packet s' q' := by
  cases s with
  | zero =>
      cases q with
      | zero =>
          rw [queueMacro_packet_zero_zero]
          simp [packet]
      | succ q =>
          obtain ⟨rest, hrest⟩ := queueMacro_packet_zero_succ_head_zero q
          rw [hrest]
          simp [packet]
  | succ s =>
      obtain ⟨rest, hrest⟩ := queueMacro_packet_succ_head_zero s q
      rw [hrest]
      simp [packet]

end YahPacketFamilyNoGo
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.MersenneShadow

/-!
# A delocalized dyadic--triadic packet instruction

One gate describes infinitely many packets: a fixed low binary address plus
an arbitrary high-bit payload.  The theorems here are universal in that
payload, so their cost does not depend on the number of digits in a candidate.
-/

namespace KontoroC

/-- Exact recurrence tested by the Mersenne packet worker. -/
def PacketCollision (m e h next : ℕ) : Prop :=
  2 ^ e * (2 ^ (m + 1) * next - 1) = 3 ^ m * h - 1

/-- Addition-only form of `PacketCollision`. -/
def PacketBalance (m e h next : ℕ) : Prop :=
  2 ^ e * (2 ^ (m + 1) * next) + 1 = 3 ^ m * h + 2 ^ e

theorem packetCollision_iff_balance {m e h next : ℕ}
    (hh : 0 < h) (hnext : 0 < next) :
    PacketCollision m e h next ↔ PacketBalance m e h next := by
  let C := 2 ^ e
  let A := 2 ^ (m + 1) * next
  let B := 3 ^ m * h
  have hC : 0 < C := Nat.pow_pos (by omega)
  have hA : 0 < A := Nat.mul_pos (Nat.pow_pos (by omega)) hnext
  have hB : 0 < B := Nat.mul_pos (Nat.pow_pos (by omega)) hh
  have hCA : C ≤ C * A := Nat.le_mul_of_pos_right C hA
  have hdist : C * (A - 1) = C * A - C := by
    simpa using Nat.mul_sub_left_distrib C A 1
  change C * (A - 1) = B - 1 ↔ C * A + 1 = B + C
  rw [hdist]
  constructor <;> intro h
  · calc
      C * A + 1 = (C * A - C) + C + 1 := by
        rw [Nat.sub_add_cancel hCA]
      _ = (B - 1) + C + 1 := by rw [h]
      _ = B + C := by omega
  · omega

/-- A collision records the exact power of two removed: `2^e` divides the
raw numerator, but `2^(e+1)` does not. -/
theorem packetCollision_exact_twoAdic {m e h next : ℕ}
    (hnext : 0 < next) (hcollision : PacketCollision m e h next) :
    2 ^ e ∣ 3 ^ m * h - 1 ∧ ¬2 ^ (e + 1) ∣ 3 ^ m * h - 1 := by
  let y := 2 ^ (m + 1) * next - 1
  have hyOdd : y % 2 = 1 := by
    exact (twoPow_mul_sub_one_pos_odd
      (m := m + 1) (h := next) (by omega) hnext).2
  have hc : 2 ^ e * y = 3 ^ m * h - 1 := hcollision
  constructor
  · exact ⟨y, hc.symm⟩
  · rintro ⟨q, hq⟩
    have hpow : 2 ^ (e + 1) = 2 ^ e * 2 := by rw [pow_succ]
    have heq : 2 ^ e * y = 2 ^ e * (2 * q) := by
      rw [hc, hq, hpow]
      ring
    have hy : y = 2 * q :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) heq
    rw [hy] at hyOdd
    simp at hyOdd

/-- The same collision supplies the triadic scheduler for the next packet. -/
theorem packetCollision_next_mod_threePow {m e h next : ℕ}
    (hh : 0 < h) (hnext : 0 < next)
    (hcollision : PacketCollision m e h next) :
    2 ^ (m + e + 1) * next ≡ 2 ^ e - 1 [MOD 3 ^ m] := by
  have hbalance := (packetCollision_iff_balance hh hnext).mp hcollision
  have hpow : 2 ^ e * 2 ^ (m + 1) = 2 ^ (m + e + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmodAdd :
      2 ^ (m + e + 1) * next + 1 ≡ 2 ^ e [MOD 3 ^ m] := by
    calc
      2 ^ (m + e + 1) * next + 1 =
          3 ^ m * h + 2 ^ e := by
        rw [← hbalance, ← mul_assoc, hpow]
      _ ≡ 2 ^ e [MOD 3 ^ m] := Nat.ModEq.modulus_mul_add
  have hsub := hmodAdd.sub (by omega) Nat.one_le_two_pow
    (Nat.ModEq.rfl : 1 ≡ 1 [MOD 3 ^ m])
  simpa using hsub

/-- Multiplication by `2^k` remembers exactly the parity bit modulo
`2^(k+1)`. -/
theorem twoPow_mul_odd_modEq (k u : ℕ) (hu : Odd u) :
    2 ^ k * u ≡ 2 ^ k [MOD 2 ^ (k + 1)] := by
  obtain ⟨q, hq⟩ := hu
  calc
    2 ^ k * u = 2 ^ (k + 1) * q + 2 ^ k := by
      rw [hq, pow_succ]
      ring
    _ ≡ 2 ^ k [MOD 2 ^ (k + 1)] := Nat.ModEq.modulus_mul_add

/-- Kernel-facing data emitted by the exact packet-gate compiler.  The base
collision is checked once; the payload theorem covers every `q : ℕ`. -/
structure PacketGate where
  level : ℕ
  extra : ℕ
  residue : ℕ
  nextOffset : ℕ
  level_pos : 0 < level
  extra_pos : 0 < extra
  residue_pos : 0 < residue
  residue_lt : residue < 2 ^ (level + extra + 2)
  nextOffset_pos : 0 < nextOffset
  residue_odd : Odd residue
  nextOffset_odd : Odd nextOffset
  base : PacketCollision level extra residue nextOffset

namespace PacketGate

/-- Attach an arbitrary high-bit payload to the gate's low address. -/
def packet (g : PacketGate) (q : ℕ) : ℕ :=
  g.residue + 2 ^ (g.level + g.extra + 2) * q

/-- The exact affine image of that payload. -/
def nextPacket (g : PacketGate) (q : ℕ) : ℕ :=
  g.nextOffset + 2 * 3 ^ g.level * q

theorem packet_pos (g : PacketGate) (q : ℕ) : 0 < g.packet q := by
  simp [packet, g.residue_pos]

theorem packet_odd (g : PacketGate) (q : ℕ) : Odd (g.packet q) := by
  rw [packet]
  apply g.residue_odd.add_even
  have heq : 2 ^ (g.level + g.extra + 2) * q =
      2 * (2 ^ (g.level + g.extra + 1) * q) := by
    rw [show g.level + g.extra + 2 =
      (g.level + g.extra + 1) + 1 by omega, pow_succ]
    ring
  rw [heq]
  exact even_two_mul _

theorem packet_injective (g : PacketGate) : Function.Injective g.packet := by
  intro q r h
  rw [packet, packet] at h
  have hmul : 2 ^ (g.level + g.extra + 2) * q =
      2 ^ (g.level + g.extra + 2) * r := Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hmul

theorem nextPacket_pos (g : PacketGate) (q : ℕ) :
    0 < g.nextPacket q := by
  simp [nextPacket, g.nextOffset_pos]

theorem nextPacket_odd (g : PacketGate) (q : ℕ) : Odd (g.nextPacket q) := by
  rw [nextPacket]
  simpa [mul_assoc] using
    g.nextOffset_odd.add_even (even_two_mul (3 ^ g.level * q))

/-- Every payload gives a literal exact collision. -/
theorem collision_apply (g : PacketGate) (q : ℕ) :
    PacketCollision g.level g.extra (g.packet q) (g.nextPacket q) := by
  rw [packetCollision_iff_balance (g.packet_pos q) (g.nextPacket_pos q)]
  have hbase : PacketBalance g.level g.extra g.residue g.nextOffset :=
    (packetCollision_iff_balance g.residue_pos g.nextOffset_pos).mp g.base
  rw [PacketBalance] at hbase ⊢
  simp only [packet, nextPacket]
  have hpow :
      2 ^ g.extra * 2 ^ (g.level + 1) =
        2 ^ (g.level + g.extra + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hsucc :
      2 ^ (g.level + g.extra + 2) =
        2 * 2 ^ (g.level + g.extra + 1) := by
    rw [show g.level + g.extra + 2 =
      (g.level + g.extra + 1) + 1 by omega, pow_succ]
    ring
  rw [show 2 ^ g.extra * (2 ^ (g.level + 1) *
      (g.nextOffset + 2 * 3 ^ g.level * q)) =
        (2 ^ g.extra * 2 ^ (g.level + 1)) *
          (g.nextOffset + 2 * 3 ^ g.level * q) by ring,
    hpow, hsucc]
  nlinarith

theorem collision_apply_exact_twoAdic (g : PacketGate) (q : ℕ) :
    2 ^ g.extra ∣ 3 ^ g.level * g.packet q - 1 ∧
      ¬2 ^ (g.extra + 1) ∣ 3 ^ g.level * g.packet q - 1 :=
  packetCollision_exact_twoAdic (g.nextPacket_pos q) (g.collision_apply q)

theorem collision_apply_next_mod_threePow (g : PacketGate) (q : ℕ) :
    2 ^ (g.level + g.extra + 1) * g.nextPacket q ≡
      2 ^ g.extra - 1 [MOD 3 ^ g.level] :=
  packetCollision_next_mod_threePow (g.packet_pos q) (g.nextPacket_pos q)
    (g.collision_apply q)

/-- Gate membership is also necessary: every positive odd collision has the
gate's low address and a unique nonnegative payload. -/
theorem collision_iff_exists_payload (g : PacketGate) {h next : ℕ}
    (hh : 0 < h) (hnext : 0 < next) (hnextOdd : Odd next) :
    PacketCollision g.level g.extra h next ↔
      ∃ q : ℕ, h = g.packet q ∧ next = g.nextPacket q := by
  constructor
  · intro hcollision
    have hbalance := (packetCollision_iff_balance hh hnext).mp hcollision
    have hbaseBalance :=
      (packetCollision_iff_balance g.residue_pos g.nextOffset_pos).mp g.base
    let k := g.level + g.extra + 1
    let modulus := 2 ^ (k + 1)
    have hpow :
        2 ^ g.extra * 2 ^ (g.level + 1) = 2 ^ k := by
      dsimp [k]
      rw [← pow_add]
      congr 1
      omega
    have hnextMod :
        2 ^ k * next + 1 ≡ 2 ^ k + 1 [MOD modulus] :=
      (twoPow_mul_odd_modEq k next hnextOdd).add_right 1
    have hoffsetMod :
        2 ^ k * g.nextOffset + 1 ≡ 2 ^ k + 1 [MOD modulus] :=
      (twoPow_mul_odd_modEq k g.nextOffset g.nextOffset_odd).add_right 1
    have hhSum :
        3 ^ g.level * h + 2 ^ g.extra ≡
          2 ^ k + 1 [MOD modulus] := by
      rw [← hbalance, show 2 ^ g.extra *
        (2 ^ (g.level + 1) * next) = 2 ^ k * next by
          rw [← mul_assoc, hpow]]
      exact hnextMod
    have hrSum :
        3 ^ g.level * g.residue + 2 ^ g.extra ≡
          2 ^ k + 1 [MOD modulus] := by
      rw [← hbaseBalance, show 2 ^ g.extra *
        (2 ^ (g.level + 1) * g.nextOffset) =
          2 ^ k * g.nextOffset by rw [← mul_assoc, hpow]]
      exact hoffsetMod
    have hscaled :
        3 ^ g.level * h ≡ 3 ^ g.level * g.residue [MOD modulus] :=
      Nat.ModEq.add_right_cancel' (2 ^ g.extra) (hhSum.trans hrSum.symm)
    have hcop : modulus.Coprime (3 ^ g.level) := by
      dsimp [modulus, k]
      exact (by norm_num : Nat.Coprime 2 3).pow _ _
    have hmod : h ≡ g.residue [MOD modulus] :=
      Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hscaled
    have hmodulus : modulus = 2 ^ (g.level + g.extra + 2) := by
      simp [modulus, k]
    have hrlt : g.residue < modulus := by simpa [hmodulus] using g.residue_lt
    have hrle : g.residue ≤ h :=
      hmod.symm.le_of_lt_add (hrlt.trans_le (Nat.le_add_left _ _))
    obtain ⟨q, hq⟩ :=
      (Nat.modEq_iff_exists_eq_add hrle).mp hmod.symm
    refine ⟨q, ?_, ?_⟩
    · simpa [packet, hmodulus, mul_comm] using hq
    · have hconstructed := g.collision_apply q
      have hpacket : h = g.packet q := by
        simpa [packet, hmodulus, mul_comm] using hq
      have hconstructedBalance :=
        (packetCollision_iff_balance (g.packet_pos q) (g.nextPacket_pos q)).mp
          hconstructed
      rw [hpacket] at hbalance
      rw [PacketBalance] at hbalance hconstructedBalance
      have heq :
          2 ^ g.extra * (2 ^ (g.level + 1) * next) =
            2 ^ g.extra * (2 ^ (g.level + 1) * g.nextPacket q) := by
        omega
      have heq' : 2 ^ (g.level + 1) * next =
          2 ^ (g.level + 1) * g.nextPacket q :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) heq'
  · rintro ⟨q, rfl, rfl⟩
    exact g.collision_apply q

theorem collision_payload_unique (g : PacketGate) {h next q r : ℕ}
    (hq : h = g.packet q ∧ next = g.nextPacket q)
    (hr : h = g.packet r ∧ next = g.nextPacket r) : q = r :=
  g.packet_injective (hq.1.symm.trans hr.1)

end PacketGate

end KontoroC

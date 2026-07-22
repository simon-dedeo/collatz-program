/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.YahPacketFamilyNoGo
import Mathlib.NumberTheory.Multiplicity

/-!
# Dyadic recharge battery for the YAH queue macro

For a pure ternary word `w`, set

`D(w) = value(w)+1`,
`Battery(w) = 2*length(w) + v₂(D(w))`.

Every reproducing macro satisfies `4*D(next)=9*D(w)`.  Since nine is odd,
the gained cell consumes exactly two units of dyadic valuation, so the
battery is exactly invariant.  This turns the finite `-1 mod 4^r` obstruction
into a local conserved quantity and isolates what a neutral or shrinking
"recharge" macro would have to replenish.
-/

namespace KontoroC
namespace YahBattery

open YahQueueMacro
open YahPerpetualGrowthNoGo

def defect (w : List Trit) : ℕ := tritEvalFrom 1 w + 1

def battery (w : List Trit) : ℕ :=
  2 * w.length + padicValNat 2 (defect w)

theorem defect_pos (w : List Trit) : 0 < defect w := by
  simp [defect]

/-- The fixed-point balance removes exactly two powers of two from the
positive defect. -/
theorem padicVal_defect_growth {D E : ℕ} (hD : 0 < D) (hE : 0 < E)
    (hbalance : 4 * E = 9 * D) :
    padicValNat 2 E + 2 = padicValNat 2 D := by
  have hfour : 4 ≠ 0 := by norm_num
  have hnine : 9 ≠ 0 := by norm_num
  have hv := congrArg (padicValNat 2) hbalance
  rw [padicValNat.mul hfour hE.ne',
      padicValNat.mul hnine hD.ne'] at hv
  have hvalFour : padicValNat 2 4 = 2 := by
    rw [show 4 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hvalNine : padicValNat 2 9 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    norm_num
  rw [hvalFour, hvalNine] at hv
  omega

/-- QM9: every `+1` queue macro conserves the dyadic recharge battery. -/
theorem battery_invariant_of_growth (w : List Trit) (hnonempty : w ≠ [])
    (hgrows : (queueMacro w).length = w.length + 1) :
    battery (queueMacro w) = battery w := by
  have hbalance := queueMacro_growth_balance w hnonempty hgrows
  have hval := padicVal_defect_growth
    (defect_pos w) (defect_pos (queueMacro w)) (by
      simpa [defect] using hbalance)
  simp only [battery]
  rw [hgrows]
  omega

end YahBattery
end KontoroC

/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OddCatcherPrefix
import KontoroC.SaturatedBridge

/-!
# Saturated-map bridges between odd-catcher cylinders

This file gives the odd branch the same coefficientwise compiler interface as
the original even two-rail branch.  It kernel-checks the first small bridge

`U^3 (7 + 8*t) = 26 + 27*t`

between two complete odd-catcher prefix cylinders.  Both selected cylinders
are outward.  The certificate is one finite compiler primitive, not an
infinite renewal claim.
-/

namespace KontoroC

/-- A coefficientwise handoff between two complete odd-catcher cylinders. -/
structure AffineOddCatcherLink (source target : OddCatcherGate) where
  sourceIndexBase : ℕ
  sourceIndexStride : ℕ
  targetIndexBase : ℕ
  targetIndexStride : ℕ
  gap_link : source.outputGap = target.ampTicks + 1
  payload_base_link :
    source.outputPayload + source.prefixOutputStride * sourceIndexBase =
      target.inputPayload + target.prefixInputStride * targetIndexBase
  payload_stride_link :
    source.prefixOutputStride * sourceIndexStride =
      target.prefixInputStride * targetIndexStride

namespace AffineOddCatcherLink

def sourceIndex {source target : OddCatcherGate}
    (g : AffineOddCatcherLink source target) (u : ℕ) : ℕ :=
  g.sourceIndexBase + g.sourceIndexStride * u

def targetIndex {source target : OddCatcherGate}
    (g : AffineOddCatcherLink source target) (u : ℕ) : ℕ :=
  g.targetIndexBase + g.targetIndexStride * u

theorem payload_link {source target : OddCatcherGate}
    (g : AffineOddCatcherLink source target) (u : ℕ) :
    (source.prefixMember (g.sourceIndex u)).outputPayload =
      (target.prefixMember (g.targetIndex u)).inputPayload := by
  change source.outputPayload + source.prefixOutputStride *
        (g.sourceIndexBase + g.sourceIndexStride * u) =
      target.inputPayload + target.prefixInputStride *
        (g.targetIndexBase + g.targetIndexStride * u)
  calc
    source.outputPayload + source.prefixOutputStride *
          (g.sourceIndexBase + g.sourceIndexStride * u) =
        (source.outputPayload +
            source.prefixOutputStride * g.sourceIndexBase) +
          (source.prefixOutputStride * g.sourceIndexStride) * u := by ring
    _ = (target.inputPayload +
            target.prefixInputStride * g.targetIndexBase) +
          (target.prefixInputStride * g.targetIndexStride) * u := by
      rw [g.payload_base_link, g.payload_stride_link]
    _ = target.inputPayload + target.prefixInputStride *
          (g.targetIndexBase + g.targetIndexStride * u) := by ring

/-- Every selected source endpoint is literally the selected target start. -/
theorem endpoint_link {source target : OddCatcherGate}
    (g : AffineOddCatcherLink source target) (u : ℕ) :
    (source.prefixMember (g.sourceIndex u)).endpoint =
      (target.prefixMember (g.targetIndex u)).start := by
  simp only [OddCatcherGate.endpoint, OddCatcherGate.start]
  rw [show (source.prefixMember (g.sourceIndex u)).outputGap =
      source.outputGap by rfl,
    show (target.prefixMember (g.targetIndex u)).ampTicks =
      target.ampTicks by rfl,
    g.gap_link, g.payload_link u]

end AffineOddCatcherLink

/-- A fixed saturated address block whose two sides are odd-catcher prefix
cylinders. -/
structure OddSaturatedAffineBridge (source target : OddCatcherGate) where
  link : AffineOddCatcherLink source target
  addressBits : ℕ
  source_stride : link.sourceIndexStride = 2 ^ addressBits
  target_base : link.targetIndexBase =
    saturatedStep^[addressBits] link.sourceIndexBase
  target_stride : link.targetIndexStride = 3 ^ addressBits

namespace OddSaturatedAffineBridge

theorem targetIndex_eq_iterate {source target : OddCatcherGate}
    (g : OddSaturatedAffineBridge source target) (t : ℕ) :
    g.link.targetIndex t =
      saturatedStep^[g.addressBits] (g.link.sourceIndex t) := by
  simp only [AffineOddCatcherLink.sourceIndex,
    AffineOddCatcherLink.targetIndex]
  rw [g.source_stride, saturatedStep_iterate_dyadic_cylinder,
    g.target_base, g.target_stride]

theorem endpoint_eq_iterate_start {source target : OddCatcherGate}
    (g : OddSaturatedAffineBridge source target) (t : ℕ) :
    (source.prefixMember (g.link.sourceIndex t)).endpoint =
      (target.prefixMember
        (saturatedStep^[g.addressBits] (g.link.sourceIndex t))).start := by
  rw [← g.targetIndex_eq_iterate t]
  exact g.link.endpoint_link t

end OddSaturatedAffineBridge

/-- Base cylinder for shape `(r,s,a,L)=(1,0,1,1)`. -/
def firstOddBridgeSource : OddCatcherGate where
  ampTicks := 1
  cleanTicks := 0
  toPlusExtra := 1
  outputGap := 1
  inputPayload := 15
  plusPayload := 33
  outputPayload := 51
  outputGap_pos := by norm_num
  inputPayload_pos := by norm_num
  plusPayload_pos := by norm_num
  outputPayload_pos := by norm_num
  inputPayload_odd := by norm_num
  plusPayload_odd := by norm_num
  outputPayload_odd := by norm_num
  toPlus_balance := by norm_num [delayState]
  catcher_balance := by norm_num [minusOneState]

/-- Target cylinder for shape `(r,s,a,L)=(0,0,1,1)`. -/
def firstOddBridgeTarget : OddCatcherGate where
  ampTicks := 0
  cleanTicks := 0
  toPlusExtra := 1
  outputGap := 1
  inputPayload := 13
  plusPayload := 9
  outputPayload := 15
  outputGap_pos := by norm_num
  inputPayload_pos := by norm_num
  plusPayload_pos := by norm_num
  outputPayload_pos := by norm_num
  inputPayload_odd := by norm_num
  plusPayload_odd := by norm_num
  outputPayload_odd := by norm_num
  toPlus_balance := by norm_num [delayState]
  catcher_balance := by norm_num [minusOneState]

def firstOddBridgeLink :
    AffineOddCatcherLink firstOddBridgeSource firstOddBridgeTarget where
  sourceIndexBase := 7
  sourceIndexStride := 8
  targetIndexBase := 26
  targetIndexStride := 27
  gap_link := by norm_num [firstOddBridgeSource, firstOddBridgeTarget]
  payload_base_link := by
    norm_num [firstOddBridgeSource, firstOddBridgeTarget,
      OddCatcherGate.prefixOutputStride,
      OddCatcherGate.prefixInputStride, OddCatcherGate.codeExponent]
  payload_stride_link := by
    norm_num [firstOddBridgeSource, firstOddBridgeTarget,
      OddCatcherGate.prefixOutputStride,
      OddCatcherGate.prefixInputStride, OddCatcherGate.codeExponent]

def firstOddBridgeCompiler :
    OddSaturatedAffineBridge firstOddBridgeSource firstOddBridgeTarget where
  link := firstOddBridgeLink
  addressBits := 3
  source_stride := by norm_num [firstOddBridgeLink]
  target_base := by
    norm_num [firstOddBridgeLink, saturatedStep,
      Function.iterate_succ_apply]
  target_stride := by norm_num [firstOddBridgeLink]

/-- The exact saturated word on the selected unbounded address cylinder. -/
theorem saturatedStep_iterate_three_odd_bridge (t : ℕ) :
    saturatedStep^[3] (7 + 8 * t) = 26 + 27 * t := by
  simpa [firstOddBridgeCompiler, firstOddBridgeLink,
    AffineOddCatcherLink.sourceIndex, AffineOddCatcherLink.targetIndex] using
      (firstOddBridgeCompiler.targetIndex_eq_iterate t).symm

theorem firstOddBridge_source_outward (t : ℕ) :
    (firstOddBridgeSource.prefixMember (7 + 8 * t)).start <
      (firstOddBridgeSource.prefixMember (7 + 8 * t)).endpoint := by
  rw [OddCatcherGate.outward_iff]
  norm_num [firstOddBridgeSource, OddCatcherGate.prefixMember,
    OddCatcherGate.prefixInputStride, OddCatcherGate.prefixOutputStride,
    OddCatcherGate.codeExponent]
  omega

theorem firstOddBridge_target_outward (t : ℕ) :
    (firstOddBridgeTarget.prefixMember (26 + 27 * t)).start <
      (firstOddBridgeTarget.prefixMember (26 + 27 * t)).endpoint := by
  rw [OddCatcherGate.outward_iff]
  norm_num [firstOddBridgeTarget, OddCatcherGate.prefixMember,
    OddCatcherGate.prefixInputStride, OddCatcherGate.prefixOutputStride,
    OddCatcherGate.codeExponent]
  omega

/-- The source splash lands exactly at the target splash selected by `U^3`. -/
theorem firstOddBridge_endpoint (t : ℕ) :
    (firstOddBridgeSource.prefixMember (7 + 8 * t)).endpoint =
      (firstOddBridgeTarget.prefixMember
        (saturatedStep^[3] (7 + 8 * t))).start := by
  simpa [firstOddBridgeCompiler, firstOddBridgeLink,
    AffineOddCatcherLink.sourceIndex] using
      firstOddBridgeCompiler.endpoint_eq_iterate_start t

end KontoroC

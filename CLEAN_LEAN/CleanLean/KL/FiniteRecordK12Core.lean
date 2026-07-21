/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.ScaledCertificate
import CleanLean.KL.ResidueSystem
import CleanLean.KL.FiniteRecordK12Data

/-!
# Chunked kernel checking for the exact level-12 record

This file defines the semantic map from certificate coordinate `s.val` to the
concrete KL state representing the paper residue `2 + 3 * s.val`.  The
generated companion module proves the normalization and row inequalities in
2,768 disjoint 64-row blocks.  A bounded-depth grouping theorem assembles
them using ordinary Lean logic and does not re-run one monolithic computation.
-/

namespace CleanLean.KL

namespace FiniteRecordK12

abbrev State := ResidueSystem.State 12

def recordStateCount : ℕ := 177147
def chunkSize : ℕ := 64
def chunkCount : ℕ := 2768
def chunksPerGroup : ℕ := 64
def groupCount : ℕ := 44

/-- Coordinate lookup in the order `m = 2 + 3 * state.val`.  An out-of-range
lookup returns zero and therefore cannot pass the certificate normalization
check. -/
def certificateValue (s : State) : ℕ :=
  valueAt s.val

/-- Exact integer encoding of the certified parameter
`lambda = 18064231 / 10000000`. -/
def certificate : (ResidueSystem.system 12).ScaledCertificate where
  lambdaNum := 18064231
  lambdaScale := 10000000
  retardedNum := 782366571504816
  advancedNum := 1413285047434102
  weightScale := 1000000000000000
  valueScale := 1000000000000
  value := certificateValue

/-- Direct natural-number transport coordinate, equivalent to the affine
`ZMod` transport on canonical representatives. -/
def directTransport (i : ℕ) : ℕ :=
  (4 * i + 2) % recordStateCount

def coarseStateCount : ℕ := 59049

/-- Direct canonical representative of the branch-dependent coarse target. -/
def directCoarseTarget (i : ℕ) : ℕ :=
  match i % 3 with
  | 0 => (4 * (i / 3)) % coarseStateCount
  | 1 => 0
  | _ => (1 + 2 * (i / 3)) % coarseStateCount

def directFiberMin (i : ℕ) : ℕ :=
  let r := directCoarseTarget i
  min (valueAt r)
    (min (valueAt (r + coarseStateCount))
      (valueAt (r + 2 * coarseStateCount)))

/-- Specialized integer RHS of one level-12 row.  Keeping the finite checker
in canonical natural coordinates avoids repeatedly evaluating generic `ZMod`
structure while the semantic equivalence is proved once below. -/
def directRowRhs (i : ℕ) : ℕ :=
  valueAt (directTransport i) * 10000000 ^ 2 * 1000000000000000 +
    match i % 3 with
    | 0 => 782366571504816 * 18064231 ^ 2 * directFiberMin i
    | 1 => 0
    | _ => 1413285047434102 * 18064231 ^ 2 * directFiberMin i

/-- Normalization and the exact scaled KL inequality in direct coordinates. -/
def DirectRowValid (i : ℕ) : Prop :=
  1000000000000 ≤ valueAt i ∧
    valueAt i * 18064231 ^ 2 * 1000000000000000 ≤ directRowRhs i

instance directRowValidDecidable (i : ℕ) : Decidable (DirectRowValid i) := by
  unfold DirectRowValid
  infer_instance

/-- One fixed-size block of coordinate inequalities.  Indices beyond the
final state are ignored only in the last block. -/
def ChunkValid
    (chunk : Fin chunkCount) : Prop :=
  ∀ offset : Fin chunkSize,
    let i := chunk.val * chunkSize + offset.val
    i < recordStateCount → DirectRowValid i

/-- A bounded assembly unit for 64 consecutive checked blocks.  The final
group has only 16 in-range blocks; its remaining offsets have an impossible
`idx < chunkCount` premise. -/
def ChunkGroupValid
    (group : Fin groupCount) : Prop :=
  ∀ offset : Fin chunksPerGroup,
    ∀ hidx : group.val * chunksPerGroup + offset.val < chunkCount,
      ChunkValid ⟨group.val * chunksPerGroup + offset.val, hidx⟩

/-- Executable Boolean form of one chunk.  The explicit `Finset.univ`
quantifier is the finite kernel-reduction boundary. -/
def checkChunk
    (chunk : Fin chunkCount) : Bool :=
  decide (∀ offset ∈ (Finset.univ : Finset (Fin chunkSize)),
    let i := chunk.val * chunkSize + offset.val
    i < recordStateCount → DirectRowValid i)

theorem checkChunk_eq_true_iff
    (chunk : Fin chunkCount) :
    checkChunk chunk = true ↔ ChunkValid chunk := by
  simp [checkChunk, ChunkValid]

/-- Assemble bounded groups into coverage of every certificate block. -/
theorem allChunksValid_of_groups
    (hgroups : ∀ group : Fin groupCount, ChunkGroupValid group) :
    ∀ chunk : Fin chunkCount, ChunkValid chunk := by
  intro chunk
  let groupNat : ℕ := chunk.val / chunksPerGroup
  have hgroupNat : groupNat < groupCount := by
    dsimp [groupNat, chunksPerGroup, groupCount, chunkCount] at *
    omega
  let group : Fin groupCount := ⟨groupNat, hgroupNat⟩
  let offset : Fin chunksPerGroup :=
    ⟨chunk.val % chunksPerGroup,
      Nat.mod_lt _ (by norm_num [chunksPerGroup])⟩
  have hdecomp :
      group.val * chunksPerGroup + offset.val = chunk.val := by
    dsimp [group, offset, groupNat]
    exact Nat.div_add_mod' chunk.val chunksPerGroup
  have hidx :
      group.val * chunksPerGroup + offset.val < chunkCount := by
    rw [hdecomp]
    exact chunk.isLt
  have hvalid := hgroups group offset hidx
  have hchunk :
      (⟨group.val * chunksPerGroup + offset.val, hidx⟩ :
        Fin chunkCount) = chunk := by
    apply Fin.ext
    exact hdecomp
  simpa [hchunk] using hvalid

theorem state_val_lt_recordStateCount (state : State) :
    state.val < recordStateCount := by
  have h := ZMod.val_lt state
  norm_num [recordStateCount] at h ⊢
  exact h

theorem transport_val_eq_direct (state : State) :
    (ResidueSystem.transport 12 state).val = directTransport state.val := by
  rw [ResidueSystem.transport_apply]
  have hz : 4 * state + 2 = ((4 * state.val + 2 : ℕ) : State) := by
    rw [← ZMod.natCast_zmod_val state]
    norm_num
  rw [hz, ZMod.val_natCast]
  rfl

theorem refinementTarget_val_eq_direct (state : State) :
    (ResidueSystem.refinementTarget 12 state).val =
      directCoarseTarget state.val := by
  unfold ResidueSystem.refinementTarget directCoarseTarget
  unfold ResidueSystem.branch
  have hlt := Nat.mod_lt state.val (by norm_num : 0 < 3)
  generalize hrem : state.val % 3 = rem at hlt ⊢
  interval_cases rem
  · simp only
    unfold ResidueSystem.retardedTarget
    change (((4 * (state.val / 3) : ℕ) : ResidueSystem.Coarse 12).val) = _
    rw [ZMod.val_natCast]
    rfl
  · simp
  · simp only
    unfold ResidueSystem.advancedTarget
    change (((1 + 2 * (state.val / 3) : ℕ) :
      ResidueSystem.Coarse 12).val) = _
    rw [ZMod.val_natCast]
    rfl

theorem fiberMinValue_eq_direct (state : State) :
    certificate.fiberMinValue
      (ResidueSystem.refinementTarget 12 state) =
      directFiberMin state.val := by
  unfold FiniteSystem.ScaledCertificate.fiberMinValue
  rw [directFiberMin]
  rw [← refinementTarget_val_eq_direct state]
  have h0 := ResidueSystem.fiber_val 12 (by norm_num)
    (ResidueSystem.refinementTarget 12 state) (0 : Fin 3)
  have h1 := ResidueSystem.fiber_val 12 (by norm_num)
    (ResidueSystem.refinementTarget 12 state) (1 : Fin 3)
  have h2 := ResidueSystem.fiber_val 12 (by norm_num)
    (ResidueSystem.refinementTarget 12 state) (2 : Fin 3)
  unfold ResidueSystem.system
  simp [certificate, certificateValue, h0, h1, h2, coarseStateCount]

theorem certificate_rowLhs_eq_direct (state : State) :
    certificate.rowLhs state =
      valueAt state.val * 18064231 ^ 2 * 1000000000000000 := by
  rfl

theorem certificate_rowRhs_eq_direct (state : State) :
    certificate.rowRhs state = directRowRhs state.val := by
  unfold FiniteSystem.ScaledCertificate.rowRhs
  change (certificate.value (ResidueSystem.transport 12 state) *
      certificate.lambdaScale ^ 2 * certificate.weightScale +
      match ResidueSystem.branch 12 state with
      | .retarded => certificate.retardedNum * certificate.lambdaNum ^ 2 *
          certificate.fiberMinValue (ResidueSystem.refinementTarget 12 state)
      | .neutral => 0
      | .advanced => certificate.advancedNum * certificate.lambdaNum ^ 2 *
          certificate.fiberMinValue (ResidueSystem.refinementTarget 12 state)) = _
  have htransport :
      certificate.value (ResidueSystem.transport 12 state) =
        valueAt (directTransport state.val) := by
    change valueAt (ResidueSystem.transport 12 state).val = _
    rw [transport_val_eq_direct]
  rw [directRowRhs, htransport, fiberMinValue_eq_direct]
  unfold ResidueSystem.branch
  have hlt := Nat.mod_lt state.val (by norm_num : 0 < 3)
  generalize hrem : state.val % 3 = rem at hlt ⊢
  interval_cases rem <;>
    simp [certificate]

theorem directRowValid_iff_state (state : State) :
    DirectRowValid state.val ↔
      certificate.valueScale ≤ certificate.value state ∧
        certificate.rowLhs state ≤ certificate.rowRhs state := by
  rw [DirectRowValid, certificate_rowLhs_eq_direct,
    certificate_rowRhs_eq_direct]
  rfl

/-- The block decomposition covers every concrete residue state exactly. -/
theorem rowValidAt_state_of_allChunks
    (hchunks : ∀ chunk : Fin chunkCount, ChunkValid chunk)
    (state : State) :
    certificate.valueScale ≤ certificate.value state ∧
      certificate.rowLhs state ≤ certificate.rowRhs state := by
  have hi : state.val < recordStateCount :=
    state_val_lt_recordStateCount state
  let chunkNat : ℕ := state.val / chunkSize
  have hchunkNat : chunkNat < chunkCount := by
    dsimp [chunkNat, chunkSize, chunkCount, recordStateCount] at *
    omega
  let chunk : Fin chunkCount := ⟨chunkNat, hchunkNat⟩
  let offset : Fin chunkSize :=
    ⟨state.val % chunkSize, Nat.mod_lt _ (by norm_num [chunkSize])⟩
  have hdecomp :
      chunk.val * chunkSize + offset.val = state.val := by
    dsimp [chunk, offset, chunkNat]
    exact Nat.div_add_mod' state.val chunkSize
  have hindexLt :
      chunk.val * chunkSize + offset.val < recordStateCount := by
    rwa [hdecomp]
  have hrow := hchunks chunk offset hindexLt
  rw [hdecomp] at hrow
  exact (directRowValid_iff_state state).1 hrow

/-- The 2,768 disjoint block theorems assemble into the exact `Valid` predicate
consumed by `ScaledCertificate` soundness. -/
theorem certificate_valid_of_allChunks
    (hchunks : ∀ chunk : Fin chunkCount, ChunkValid chunk) :
    certificate.Valid := by
  refine ⟨by norm_num [certificate], by norm_num [certificate],
    by norm_num [certificate], by norm_num [certificate], ?_, ?_⟩
  · intro state
    exact (rowValidAt_state_of_allChunks hchunks state).1
  · intro state
    exact (rowValidAt_state_of_allChunks hchunks state).2

end FiniteRecordK12

end CleanLean.KL

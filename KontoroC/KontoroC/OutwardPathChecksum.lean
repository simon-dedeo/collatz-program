/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardJacobianRigidityGap
import Mathlib.Data.LawfulXor
import Mathlib.Data.List.Perm.Basic

/-!
# Exact XOR endpoint checksum for a distributed directed path

For one directed path, XORing both endpoints of every edge cancels every
internal vertex and leaves `start XOR finish`.  Commutativity makes the result
independent of edge order, and XORing the checksums of arbitrary shards is the
same as XORing the flattened edge list.  Hence a known start recovers the
unknown terminal vertex exactly.

This is a finite audit tool for distributed counterexample searches: a shard
boundary cannot hide the endpoint of one known-start path.  The hypothesis
that the data form exactly one path is essential.  For branching data or
several open paths the checksum retains the XOR of all odd-incidence boundary
vertices and does not identify a distinguished terminal by itself.
-/

namespace KontoroC
namespace OutwardPathChecksum

/-- Consecutive directed edges of a vertex list. -/
def pathEdges : List ℕ → List (ℕ × ℕ)
  | source :: target :: rest =>
      (source, target) :: pathEdges (target :: rest)
  | _ => []

/-- XOR of both endpoints of every edge in a finite edge list. -/
def edgeChecksum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | edge :: rest =>
      (edge.1 ^^^ edge.2) ^^^ edgeChecksum rest

/-- Edge checksums compose under list concatenation. -/
theorem edgeChecksum_append (left right : List (ℕ × ℕ)) :
    edgeChecksum (left ++ right) =
      edgeChecksum left ^^^ edgeChecksum right := by
  induction left with
  | nil => simp [edgeChecksum]
  | cons edge left ih =>
      simp only [List.cons_append, edgeChecksum, ih]
      ac_rfl

/-- Reordering the edge table does not change its XOR checksum. -/
theorem edgeChecksum_eq_of_perm
    {left right : List (ℕ × ℕ)} (hperm : left.Perm right) :
    edgeChecksum left = edgeChecksum right := by
  induction hperm with
  | nil => rfl
  | cons edge hperm ih => simp [edgeChecksum, ih]
  | swap left right tail =>
      simp only [edgeChecksum]
      ac_rfl
  | trans _ _ ihleft ihrigh => exact ihleft.trans ihrigh

/-- Internal vertices telescope: the path checksum is exactly the XOR of its
two endpoints.  The explicit middle list permits repeated vertices and loops;
no simplicity assumption is needed. -/
theorem pathChecksum_eq_start_xor_finish
    (start finish : ℕ) (middle : List ℕ) :
    edgeChecksum (pathEdges (start :: middle ++ [finish])) =
      start ^^^ finish := by
  induction middle generalizing start with
  | nil => simp [pathEdges, edgeChecksum]
  | cons vertex middle ih =>
      simp only [List.cons_append, pathEdges, edgeChecksum]
      rw [show vertex :: (middle ++ [finish]) =
        (vertex :: middle) ++ [finish] by simp]
      rw [ih vertex]
      rw [← xor_assoc (start ^^^ vertex) vertex finish,
        xor_assoc start vertex vertex]
      rw [LawfulXor.xor_self, xor_zero]

/-- Distributed checksum: XOR each shard locally and then XOR the shard
results. -/
def shardChecksum : List (List (ℕ × ℕ)) → ℕ
  | [] => 0
  | shard :: rest =>
      edgeChecksum shard ^^^ shardChecksum rest

/-- Sharding changes no information in the total XOR checksum. -/
theorem shardChecksum_eq_flatten
    (shards : List (List (ℕ × ℕ))) :
    shardChecksum shards = edgeChecksum shards.flatten := by
  induction shards with
  | nil => simp [shardChecksum, edgeChecksum]
  | cons shard shards ih =>
      simp only [shardChecksum, List.flatten_cons, ih,
        edgeChecksum_append]

/-- Exact endpoint recovery for arbitrary shards and arbitrary edge order.
The sole structural certificate is that the flattened shard table is a
permutation of the consecutive edges of one declared path. -/
theorem known_start_recovers_finish
    (start finish : ℕ) (middle : List ℕ)
    (shards : List (List (ℕ × ℕ)))
    (hpartition : shards.flatten.Perm
      (pathEdges (start :: middle ++ [finish]))) :
    start ^^^ shardChecksum shards = finish := by
  rw [shardChecksum_eq_flatten]
  rw [edgeChecksum_eq_of_perm hpartition]
  rw [pathChecksum_eq_start_xor_finish]
  exact xor_cancel_left start finish

/-- Consequently the same known-start, same-shard certificate cannot encode
two different terminal vertices as one-path decompositions. -/
theorem finish_unique_of_two_path_certificates
    (start finish₁ finish₂ : ℕ)
    (middle₁ middle₂ : List ℕ)
    (shards : List (List (ℕ × ℕ)))
    (hpartition₁ : shards.flatten.Perm
      (pathEdges (start :: middle₁ ++ [finish₁])))
    (hpartition₂ : shards.flatten.Perm
      (pathEdges (start :: middle₂ ++ [finish₂]))) :
    finish₁ = finish₂ := by
  rw [← known_start_recovers_finish start finish₁ middle₁ shards hpartition₁]
  exact known_start_recovers_finish start finish₂ middle₂ shards hpartition₂

end OutwardPathChecksum
end KontoroC

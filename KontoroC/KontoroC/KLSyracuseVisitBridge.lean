/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.KLRechargeLedger

/-!
# Successive `2 mod 3` Syracuse visits are exactly the KL principal edges

The KL predecessor graph is not an analogy imposed on a Collatz trace.  If a
positive one-halving Syracuse trajectory is sampled whenever it lies in the
class `2 mod 3`, then every pair of consecutive sampled states, read
backwards, is exactly one of the transport, retarded, or advanced KL edges.

This file proves the local classification without any finite trace or
certificate data.  A literal compiled macro therefore only has to prove its
Syracuse replay; its sampled path automatically has KL semantics.
-/

namespace KontoroC
namespace KLSyracuseVisitBridge

open CleanLean.Collatz

/-- The three exact principal KL predecessor relations.  `source` is the
later Syracuse visit and `target` the earlier visit, so the relation is read
backwards along the forward trajectory.  Addition is used instead of
truncated natural subtraction in the two chord equations. -/
inductive PrincipalEdge (source target : ℕ) : Prop
  | transport (h : target = 4 * source)
  | retarded (hsource : source % 9 = 2)
      (h : 3 * target + 2 = 4 * source)
  | advanced (hsource : source % 9 = 8)
      (h : 3 * target + 1 = 2 * source)

/-- The next visit to the residue class `2 mod 3`: it occurs after one
Syracuse step from an odd state and after two from an even state. -/
def nextTwoModThreeVisit (n : ℕ) : ℕ :=
  if n % 2 = 1 then syracuseStep n else syracuseStep^[2] n

theorem nextTwoModThreeVisit_of_odd {n : ℕ} (hodd : n % 2 = 1) :
    nextTwoModThreeVisit n = (3 * n + 1) / 2 := by
  simp [nextTwoModThreeVisit, syracuseStep, hodd]

theorem nextTwoModThreeVisit_of_even {n : ℕ} (heven : n % 2 = 0) :
    nextTwoModThreeVisit n = syracuseStep (n / 2) := by
  simp [nextTwoModThreeVisit, syracuseStep, heven,
    Function.iterate_succ_apply]

/-- An odd `2 mod 3` state reaches an `8 mod 9` state in one step, giving an
advanced KL edge when read backwards. -/
theorem odd_visit_advanced {n : ℕ} (hn3 : n % 3 = 2)
    (hodd : n % 2 = 1) :
    let a := nextTwoModThreeVisit n
    a % 9 = 8 ∧ 3 * n + 1 = 2 * a := by
  rw [nextTwoModThreeVisit_of_odd hodd]
  have heven : (3 * n + 1) % 2 = 0 := by omega
  have hdiv := Nat.mod_add_div (3 * n + 1) 2
  have hnmod := Nat.mod_add_div n 6
  have hamod := Nat.mod_add_div ((3 * n + 1) / 2) 9
  constructor <;> omega

/-- A `0 mod 4`, `2 mod 3` state reaches its quarter in two halving steps,
giving a transport edge backwards. -/
theorem four_dvd_visit_transport {n : ℕ} (hn4 : n % 4 = 0) :
    nextTwoModThreeVisit n = n / 4 := by
  have hn2 : n % 2 = 0 := by omega
  rw [nextTwoModThreeVisit_of_even hn2]
  have hhalf2 : (n / 2) % 2 = 0 := by omega
  simp [syracuseStep, hhalf2]
  omega

/-- A `2 mod 4`, `2 mod 3` state takes one halving and one odd step.  The
next sampled state is `2 mod 9`, giving a retarded KL edge backwards. -/
theorem two_mod_four_visit_retarded {n : ℕ} (hn3 : n % 3 = 2)
    (hn4 : n % 4 = 2) :
    let a := nextTwoModThreeVisit n
    a % 9 = 2 ∧ 3 * n + 2 = 4 * a := by
  have hn2 : n % 2 = 0 := by omega
  rw [nextTwoModThreeVisit_of_even hn2]
  have hhalfOdd : (n / 2) % 2 = 1 := by omega
  simp [syracuseStep, hhalfOdd]
  have hnum4 : (3 * n + 2) % 4 = 0 := by omega
  have hdiv := Nat.mod_add_div (3 * n + 2) 4
  have hnmod := Nat.mod_add_div n 12
  have hamod := Nat.mod_add_div ((3 * (n / 2) + 1) / 2) 9
  constructor <;> omega

/-- Universal semantic bridge used by the literal glider/KL audit. -/
theorem next_visit_principalEdge {n : ℕ} (hn3 : n % 3 = 2) :
    PrincipalEdge (nextTwoModThreeVisit n) n := by
  by_cases hodd : n % 2 = 1
  · have h := odd_visit_advanced hn3 hodd
    exact .advanced h.1 h.2
  · have heven : n % 2 = 0 := by omega
    have hn4lt : n % 4 < 4 := Nat.mod_lt _ (by omega)
    have hn4even : n % 4 % 2 = 0 := by omega
    interval_cases h4 : n % 4
    · have h := four_dvd_visit_transport h4
      exact .transport (by rw [h]; omega)
    · omega
    · have h := two_mod_four_visit_retarded hn3 h4
      exact .retarded h.1 h.2
    · omega

/-- The next sampled state is again in the `2 mod 3` class. -/
theorem next_visit_mod_three {n : ℕ} (hn3 : n % 3 = 2) :
    nextTwoModThreeVisit n % 3 = 2 := by
  have h := next_visit_principalEdge hn3
  cases h with
  | transport heq =>
      have hnmod := Nat.mod_add_div n 3
      have hamod := Nat.mod_add_div (nextTwoModThreeVisit n) 3
      omega
  | retarded hmod _ => omega
  | advanced hmod _ => omega

/-- An even sampled state does not return to `2 mod 3` after only one step;
the second step used by `nextTwoModThreeVisit` is genuinely the next visit. -/
theorem even_first_step_not_two_mod_three {n : ℕ} (hn3 : n % 3 = 2)
    (heven : n % 2 = 0) :
    syracuseStep n % 3 ≠ 2 := by
  simp [syracuseStep, heven]
  have hnmod := Nat.mod_add_div n 6
  have hhmod := Nat.mod_add_div (n / 2) 3
  omega

end KLSyracuseVisitBridge
end KontoroC

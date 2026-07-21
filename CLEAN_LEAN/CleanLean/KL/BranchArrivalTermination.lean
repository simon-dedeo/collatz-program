/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.SymbolicShift
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Order
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Termination from branch-arrival compactness

This file isolates the proposed repair of the Krasikov--Lagarias tree
termination argument.  The central finite-state fact is that an irrational
constant cannot be an integer-valued coboundary on a finite deterministic
system.  Subsequent lemmas connect this obstruction to limits of recurrent
branch-arrival types.
-/

namespace CleanLean.KL

/-- The KL drift `alpha = log_2 3` is irrational.  A rational identity would,
after clearing signs and exponentiating, give `3^m = 2^n` for positive
natural exponents, contradicting divisibility by two. -/
theorem alpha_irrational : Irrational alpha := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have halphaPos : 0 < alpha := lt_trans (by norm_num) one_lt_alpha
  have hratioPos : 0 < (a : ℝ) / (b : ℝ) := by
    rw [← hab]
    exact halphaPos
  have ha : a ≠ 0 := by
    intro ha
    subst a
    norm_num at hratioPos
  have hA : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hB : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have habsratio : |(a : ℝ) / (b : ℝ)| = (a : ℝ) / (b : ℝ) :=
    abs_of_pos hratioPos
  have hnatabs : (a.natAbs : ℝ) / (b.natAbs : ℝ) = alpha := by
    calc
      (a.natAbs : ℝ) / (b.natAbs : ℝ) = |(a : ℝ)| / |(b : ℝ)| := by
        rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      _ = |(a : ℝ) / (b : ℝ)| := (abs_div _ _).symm
      _ = (a : ℝ) / (b : ℝ) := habsratio
      _ = alpha := hab.symm
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hB0 : (b.natAbs : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hlogs : (b.natAbs : ℝ) * Real.log (3 : ℝ) =
      (a.natAbs : ℝ) * Real.log (2 : ℝ) := by
    rw [alpha] at hnatabs
    field_simp at hnatabs
    nlinarith
  have hpowsR : (3 : ℝ) ^ b.natAbs = (2 : ℝ) ^ a.natAbs := by
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_nat_mul, Real.exp_nat_mul] at hexp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
    exact hexp
  have hpowsN : 3 ^ b.natAbs = 2 ^ a.natAbs := by
    exact_mod_cast hpowsR
  have hdiv : 2 ∣ 3 ^ b.natAbs := by
    rw [hpowsN]
    exact dvd_pow_self 2 hA.ne'
  have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdiv
  norm_num at this

/-- A value occurs infinitely often in a one-sided sequence. -/
def OccursInfinitely {A : Type*} (u : ℕ → A) (a : A) : Prop :=
  (u ⁻¹' {a}).Infinite

/-- The total integer cost along the first `n` steps of the orbit of `q`. -/
def orbitCost {Q : Type*} (next : Q → Q) (cost : Q → ℕ) (q : Q) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, cost (next^[i] q)

/-- Iterating a real coboundary equation telescopes to an exact orbit sum. -/
theorem coboundary_iterate {Q : Type*} (next : Q → Q) (cost : Q → ℕ)
    (limit : Q → ℝ) (a : ℝ)
    (hstep : ∀ q, limit (next q) - limit q = a - cost q) (q : Q) (n : ℕ) :
    limit (next^[n] q) - limit q = (n : ℝ) * a - orbitCost next cost q n := by
  induction n with
  | zero => simp [orbitCost]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        limit (next (next^[n] q)) - limit q =
            (limit (next (next^[n] q)) - limit (next^[n] q)) +
              (limit (next^[n] q) - limit q) := by ring
        _ = (a - cost (next^[n] q)) +
              ((n : ℝ) * a - orbitCost next cost q n) := by rw [hstep, ih]
        _ = ((n + 1 : ℕ) : ℝ) * a - orbitCost next cost q (n + 1) := by
          simp only [orbitCost, Finset.sum_range_succ, Nat.cast_add, Nat.cast_sum]
          push_cast
          ring

/-- An irrational real cannot be an integer-valued coboundary over a finite
self-map.  Every finite self-map has a repeated orbit segment, and telescoping
around that segment would make a positive natural multiple of `a` an integer. -/
theorem no_finite_integer_coboundary_of_irrational
    {Q : Type*} [Finite Q] [Nonempty Q] (next : Q → Q) (cost : Q → ℕ)
    (limit : Q → ℝ) {a : ℝ} (ha : Irrational a)
    (hstep : ∀ q, limit (next q) - limit q = a - cost q) : False := by
  classical
  let q : Q := Classical.choice (inferInstance : Nonempty Q)
  obtain ⟨i, j, hij, heq⟩ :=
    Set.finite_univ.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => next^[n] q) (fun _ => Set.mem_univ _)
  let d := j - i
  let x := next^[i] q
  have hd : d ≠ 0 := Nat.sub_ne_zero_of_lt hij
  have hcycle : next^[d] x = x := by
    change next^[j - i] (next^[i] q) = next^[i] q
    rw [← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel hij.le]
    exact heq.symm
  have htel := coboundary_iterate next cost limit a hstep x d
  rw [hcycle, sub_self] at htel
  have hnat : (d : ℝ) * a = (orbitCost next cost x d : ℝ) := by
    linarith
  have hirr : Irrational ((d : ℝ) * a) :=
    irrational_natCast_mul_iff.mpr ⟨hd, ha⟩
  exact hirr.ne_nat (orbitCost next cost x d) hnat

/-- Every state which occurs infinitely often has an outgoing edge type which
also occurs infinitely often.  This is the infinite pigeonhole principle,
with source compatibility retained explicitly. -/
theorem exists_recurrent_outgoing_edge
    {Q E : Type*} [Finite E]
    (state : ℕ → Q) (edge : ℕ → E) (source : E → Q)
    (hsource : ∀ n, source (edge n) = state n) {q : Q}
    (hq : OccursInfinitely state q) :
    ∃ e, OccursInfinitely edge e ∧ source e = q := by
  classical
  let I := {n : ℕ // state n = q}
  letI : Infinite I := by
    exact hq.to_subtype
  let edgeOn : I → E := fun n => edge n
  obtain ⟨e, he⟩ := Finite.exists_infinite_fiber edgeOn
  let J := edgeOn ⁻¹' {e}
  letI : Infinite J := he
  let inclusion : J → ℕ := fun n => n.1.1
  have hinclusion : Function.Injective inclusion := by
    intro m n hmn
    exact Subtype.ext (Subtype.ext hmn)
  have hrange : (Set.range inclusion).Infinite :=
    Set.infinite_range_of_injective hinclusion
  have hedge : OccursInfinitely edge e := by
    apply hrange.mono
    rintro n ⟨j, rfl⟩
    exact j.2
  refine ⟨e, hedge, ?_⟩
  let j : J := Classical.choice (inferInstance : Nonempty J)
  calc
    source e = source (edge j.1.1) := by rw [show edge j.1.1 = e by exact j.2]
    _ = state j.1.1 := hsource _
    _ = q := j.1.2

/-- The target of an infinitely recurring compatible edge is itself an
infinitely recurring state. -/
theorem recurrent_edge_target
    {Q E : Type*} (state : ℕ → Q) (edge : ℕ → E) (target : E → Q)
    (htarget : ∀ n, target (edge n) = state (n + 1)) {e : E}
    (he : OccursInfinitely edge e) : OccursInfinitely state (target e) := by
  have himage : (Nat.succ '' (edge ⁻¹' {e})).Infinite :=
    he.image Nat.succ_injective.injOn
  apply himage.mono
  rintro n ⟨m, hm, rfl⟩
  have hedge : edge m = e := hm
  change state (m + 1) = target e
  rw [← htarget m, hedge]

/-- Epsilon-form convergence of the heights restricted to visits to one
state.  This avoids assigning any meaning to states which occur only finitely
often. -/
def ConvergesAlongOccurrences {Q : Type*} (state : ℕ → Q)
    (height : ℕ → ℝ) (q : Q) (limit : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → state n = q → |height n - limit| < ε

/-- A nonnegative sequence which is nonincreasing on each return to a fixed
state converges along the occurrences of every recurrent state. -/
theorem exists_limit_along_occurrences
    {Q : Type*} (state : ℕ → Q) (height : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hmono : ∀ ⦃i j⦄, i ≤ j → state i = state j → height j ≤ height i)
    {q : Q} (hq : OccursInfinitely state q) :
    ∃ limit, ConvergesAlongOccurrences state height q limit := by
  classical
  let S : Set ℕ := state ⁻¹' {q}
  letI : Infinite S := by
    exact hq.to_subtype
  let enumerate : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
  let values : ℕ → ℝ := fun n => height (enumerate n).1
  have hvalues_antitone : Antitone values := by
    intro i j hij
    apply hmono (enumerate.monotone hij)
    exact (enumerate i).2.trans (enumerate j).2.symm
  have hvalues_bdd : BddBelow (Set.range values) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hnonneg _
  let limit : ℝ := ⨅ n, values n
  have hlimit : Filter.Tendsto values Filter.atTop (nhds limit) :=
    tendsto_atTop_ciInf hvalues_antitone hvalues_bdd
  refine ⟨limit, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlimit ε hε
  refine ⟨(enumerate N).1, ?_⟩
  intro n hn hnq
  let sn : S := ⟨n, hnq⟩
  let k : ℕ := enumerate.symm sn
  have hk : N ≤ k := by
    apply enumerate.le_iff_le.mp
    rw [show enumerate k = sn by simp [k]]
    change (enumerate N).1 ≤ sn.1
    exact hn
  have hclose := hN k hk
  simpa [values, k, sn, Real.dist_eq] using hclose

/-- Limits along the endpoints of an infinitely recurring edge inherit the
exact one-step drift equation. -/
theorem recurrent_edge_limit_equation
    {Q E : Type*} (state : ℕ → Q) (edge : ℕ → E)
    (height : ℕ → ℝ) (source target : E → Q) (cost : E → ℕ)
    (limit : Q → ℝ) {a : ℝ}
    (hsource : ∀ n, source (edge n) = state n)
    (htarget : ∀ n, target (edge n) = state (n + 1))
    (hstep : ∀ n, height (n + 1) - height n = a - cost (edge n))
    {e : E} (he : OccursInfinitely edge e)
    (hsource_limit : ConvergesAlongOccurrences state height (source e) (limit (source e)))
    (htarget_limit : ConvergesAlongOccurrences state height (target e) (limit (target e))) :
    limit (target e) - limit (source e) = a - cost e := by
  by_contra hne
  let discrepancy :=
    (limit (target e) - limit (source e)) - (a - cost e)
  have hdisc : 0 < |discrepancy| := abs_pos.mpr (by
    simpa [discrepancy, sub_eq_zero] using hne)
  let ε := |discrepancy| / 3
  have hε : 0 < ε := div_pos hdisc (by norm_num)
  obtain ⟨Ns, hNs⟩ := hsource_limit ε hε
  obtain ⟨Nt, hNt⟩ := htarget_limit ε hε
  obtain ⟨n, hnedge, hnlarge⟩ := he.exists_gt (max Ns Nt)
  have hnNs : Ns ≤ n := le_trans (le_max_left _ _) hnlarge.le
  have hnNt : Nt ≤ n + 1 :=
    le_trans (le_max_right _ _) (Nat.le_succ_of_le hnlarge.le)
  have hs : |height n - limit (source e)| < ε := by
    apply hNs n hnNs
    rw [← hsource n]
    exact congrArg source (show edge n = e from hnedge)
  have ht : |height (n + 1) - limit (target e)| < ε := by
    apply hNt (n + 1) hnNt
    rw [← htarget n]
    exact congrArg target (show edge n = e from hnedge)
  have hrewrite : discrepancy =
      (limit (target e) - height (n + 1)) +
        (height n - limit (source e)) := by
    dsimp [discrepancy]
    have hstep' : height (n + 1) - height n = a - cost e := by
      simpa [show edge n = e from hnedge] using hstep n
    rw [← hstep']
    ring
  have hsmall : |discrepancy| < ε + ε := by
    rw [hrewrite]
    refine (abs_add_le _ _).trans_lt (add_lt_add ?_ hs)
    simpa [abs_sub_comm] using ht
  dsimp [ε] at hsmall
  linarith

/-- If every infinitely recurring edge type induces an exact integer
coboundary equation between its source and target limits, a finite-state
infinite path is impossible for irrational drift. -/
theorem no_finite_recurrent_integer_transition_system
    {Q E : Type*} [Finite Q] [Finite E]
    (state : ℕ → Q) (edge : ℕ → E)
    (source target : E → Q) (cost : E → ℕ) (limit : Q → ℝ)
    {a : ℝ} (ha : Irrational a)
    (hsource : ∀ n, source (edge n) = state n)
    (htarget : ∀ n, target (edge n) = state (n + 1))
    (hlimit : ∀ e, OccursInfinitely edge e →
      limit (target e) - limit (source e) = a - cost e) : False := by
  classical
  let RecurrentState := {q : Q // OccursInfinitely state q}
  have hnonempty : Nonempty RecurrentState := by
    obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber state
    exact ⟨⟨q, Set.infinite_coe_iff.mp hq⟩⟩
  let chosen : RecurrentState → E := fun q =>
    Classical.choose (exists_recurrent_outgoing_edge state edge source hsource q.2)
  have hchosen_recurrent (q : RecurrentState) :
      OccursInfinitely edge (chosen q) :=
    (Classical.choose_spec
      (exists_recurrent_outgoing_edge state edge source hsource q.2)).1
  have hchosen_source (q : RecurrentState) : source (chosen q) = q.1 :=
    (Classical.choose_spec
      (exists_recurrent_outgoing_edge state edge source hsource q.2)).2
  let next : RecurrentState → RecurrentState := fun q =>
    ⟨target (chosen q),
      recurrent_edge_target state edge target htarget (hchosen_recurrent q)⟩
  let recurrentCost : RecurrentState → ℕ := fun q => cost (chosen q)
  let recurrentLimit : RecurrentState → ℝ := fun q => limit q.1
  letI : Nonempty RecurrentState := hnonempty
  apply no_finite_integer_coboundary_of_irrational next recurrentCost recurrentLimit ha
  intro q
  change limit (target (chosen q)) - limit q.1 = a - cost (chosen q)
  rw [← hchosen_source q]
  exact hlimit (chosen q) (hchosen_recurrent q)

/-- Abstract branch-arrival termination theorem.  There is no infinite path
with finitely many typed transitions, irrational drift, nonnegative heights,
and nonincreasing surviving heights on returns to each state. -/
theorem no_infinite_finite_typed_branch_arrivals
    {Q E : Type*} [Finite Q] [Finite E]
    (state : ℕ → Q) (edge : ℕ → E) (height : ℕ → ℝ)
    (source target : E → Q) (cost : E → ℕ) {a : ℝ}
    (ha : Irrational a)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hmono : ∀ ⦃i j⦄, i ≤ j → state i = state j → height j ≤ height i)
    (hsource : ∀ n, source (edge n) = state n)
    (htarget : ∀ n, target (edge n) = state (n + 1))
    (hstep : ∀ n, height (n + 1) - height n = a - cost (edge n)) : False := by
  classical
  let limit : Q → ℝ := fun q =>
    if hq : OccursInfinitely state q then
      Classical.choose (exists_limit_along_occurrences state height hnonneg hmono hq)
    else 0
  have hlimit (q : Q) (hq : OccursInfinitely state q) :
      ConvergesAlongOccurrences state height q (limit q) := by
    dsimp [limit]
    rw [dif_pos hq]
    exact Classical.choose_spec
      (exists_limit_along_occurrences state height hnonneg hmono hq)
  apply no_finite_recurrent_integer_transition_system state edge source target cost limit ha
    hsource htarget
  intro e he
  apply recurrent_edge_limit_equation state edge height source target cost limit
    hsource htarget hstep he
  · exact hlimit (source e) <|
      (he.mono fun n hn => by
        change state n = source e
        rw [← hsource n]
        exact congrArg source (show edge n = e from hn))
  · exact hlimit (target e) <| recurrent_edge_target state edge target htarget he

/-- Statewise antitonicity over a finite state space gives a global upper
bound.  For each visited state, its first occurrence bounds all later
occurrences of that state. -/
theorem heights_bddAbove_of_statewise_antitone
    {Q : Type*} [Finite Q] (state : ℕ → Q) (height : ℕ → ℝ)
    (hmono : ∀ ⦃i j⦄, i ≤ j → state i = state j → height j ≤ height i) :
    BddAbove (Set.range height) := by
  classical
  let Visited := {q : Q // ∃ n, state n = q}
  let first : Visited → ℕ := fun q => Nat.find q.2
  obtain ⟨H, hH⟩ := Finite.bddAbove_range (fun q : Visited => height (first q))
  refine ⟨H, ?_⟩
  rintro y ⟨n, rfl⟩
  let q : Visited := ⟨state n, ⟨n, rfl⟩⟩
  calc
    height n ≤ height (first q) := by
      apply hmono (Nat.find_min' q.2 rfl)
      exact (Nat.find_spec q.2).trans rfl
    _ ≤ H := hH ⟨q, rfl⟩

/-- Full abstract branch-arrival compactness theorem.  The cost alphabet need
not be assumed finite: nonnegative heights and the exact drift equation bound
all costs, after which the finite-typed theorem applies. -/
theorem no_infinite_branch_arrivals
    {Q : Type*} [Finite Q]
    (state : ℕ → Q) (height : ℕ → ℝ) (cost : ℕ → ℕ) {a : ℝ}
    (ha : Irrational a)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hmono : ∀ ⦃i j⦄, i ≤ j → state i = state j → height j ≤ height i)
    (hstep : ∀ n, height (n + 1) - height n = a - cost n) : False := by
  classical
  obtain ⟨H, hH⟩ := heights_bddAbove_of_statewise_antitone state height hmono
  obtain ⟨C, hC⟩ := exists_nat_ge (a + H)
  have hcost (n : ℕ) : cost n ≤ C := by
    have hheight : height n ≤ H := hH ⟨n, rfl⟩
    have hnext : 0 ≤ height (n + 1) := hnonneg (n + 1)
    have hcostR : (cost n : ℝ) ≤ (C : ℝ) := by
      have hCR : a + H ≤ (C : ℝ) := hC
      linarith [hstep n]
    exact_mod_cast hcostR
  let TypedEdge := Q × Q × Fin (C + 1)
  let typedEdge : ℕ → TypedEdge := fun n =>
    ⟨state n, state (n + 1), ⟨cost n, Nat.lt_succ_of_le (hcost n)⟩⟩
  exact no_infinite_finite_typed_branch_arrivals
    state typedEdge height
    (fun e : TypedEdge => e.1) (fun e : TypedEdge => e.2.1)
    (fun e : TypedEdge => e.2.2.1) ha hnonneg hmono
    (fun _ => rfl) (fun _ => rfl) (fun n => by simpa [typedEdge] using hstep n)

/-- Specialization of the abstract theorem to the exact KL drift. -/
theorem no_infinite_KL_branch_arrivals
    {Q : Type*} [Finite Q]
    (state : ℕ → Q) (height : ℕ → ℝ) (cost : ℕ → ℕ)
    (hnonneg : ∀ n, 0 ≤ height n)
    (hmono : ∀ ⦃i j⦄, i ≤ j → state i = state j → height j ≤ height i)
    (hstep : ∀ n, height (n + 1) - height n = alpha - cost n) : False :=
  no_infinite_branch_arrivals state height cost alpha_irrational hnonneg hmono hstep

/-- The two possible refinement edges at the end of a compressed branch
arrival. -/
inductive ArrivalKind where
  | retarded
  | advanced
  deriving DecidableEq, Repr

namespace ArrivalKind

/-- Integer part of the drift after `transports` transport edges and one
refinement edge. -/
def cost (kind : ArrivalKind) (transports : ℕ) : ℕ :=
  match kind with
  | .retarded => 2 * transports + 2
  | .advanced => 2 * transports + 1

/-- Apply the compressed word consisting of `transports` transport edges and
then one refinement edge. -/
def follow (kind : ArrivalKind) (transports : ℕ) (shift : SymbolicShift) :
    SymbolicShift :=
  let transported := SymbolicShift.transport^[transports] shift
  match kind with
  | .retarded => transported.retarded
  | .advanced => transported.advanced

theorem value_transport_iterate (transports : ℕ) (shift : SymbolicShift) :
    (SymbolicShift.transport^[transports] shift).value =
      shift.value - 2 * transports := by
  induction transports with
  | zero => simp
  | succ transports ih =>
      rw [Function.iterate_succ_apply', SymbolicShift.value_transport, ih]
      push_cast
      ring

/-- Exact compressed-arrival increment used by the compactness theorem. -/
theorem value_follow_sub (kind : ArrivalKind) (transports : ℕ)
    (shift : SymbolicShift) :
    (kind.follow transports shift).value - shift.value =
      alpha - kind.cost transports := by
  cases kind <;>
    simp [follow, cost, SymbolicShift.value_retarded,
      SymbolicShift.value_advanced, value_transport_iterate] <;> ring

end ArrivalKind

end CleanLean.KL

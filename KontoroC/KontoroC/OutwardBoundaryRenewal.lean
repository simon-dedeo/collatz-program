/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.OutwardCarryThreshold
import KontoroC.OutwardFirstPassage

/-!
# Exact boundary defect calculus for outward first-passage words

This file formalizes the arithmetic compression requested in QM157d--f.
It deliberately stops before asserting that recharge words can be chosen
indefinitely: all statements concern one literal executable parity word.
-/

namespace KontoroC
namespace OutwardBoundaryRenewal

open ShortcutParityPeriodicNoGo OutwardFirstPassage

theorem accumulate_append (u v : List Bool) (d : ParityData) :
    accumulate (u ++ v) d = accumulate v (accumulate u d) := by
  induction u generalizing d with
  | nil => simp [accumulate]
  | cons b u ih => simp [accumulate, ih]

theorem programData_append_singleton (w : List Bool) (b : Bool) :
    programData (w ++ [b]) = (programData w).step b := by
  simp [programData, accumulate_append, accumulate]

/-- The affine offset compensates for every possible slope deficit. -/
theorem slope_le_affine (w : List Bool) :
    3 ^ (programData w).O ≤ (programData w).A + 2 ^ (programData w).S := by
  induction w using List.reverseRecOn with
  | nil => norm_num [programData, initialData, accumulate]
  | append_singleton w b ih =>
      rw [programData_append_singleton]
      cases b with
      | false =>
          change 3 ^ (programData w).O ≤
            (programData w).A + 2 ^ ((programData w).S + 1)
          rw [pow_succ]
          have hpos : 0 < 2 ^ (programData w).S := by positivity
          have hp : 2 ^ (programData w).S ≤ 2 * 2 ^ (programData w).S := by
            omega
          omega
      | true =>
          change 3 ^ ((programData w).O + 1) ≤
            (3 * (programData w).A + 2 ^ (programData w).S) +
              2 ^ ((programData w).S + 1)
          rw [pow_succ, pow_succ]
          nlinarith

/-- The nonnegative affine defect `A + 2^S - 3^O`. -/
def rawDefect (w : List Bool) : ℕ :=
  (programData w).A + 2 ^ (programData w).S - 3 ^ (programData w).O

theorem rawDefect_add_threePow (w : List Bool) :
    rawDefect w + 3 ^ (programData w).O =
      (programData w).A + 2 ^ (programData w).S := by
  exact Nat.sub_add_cancel (slope_le_affine w)

/-- Appending an even instruction adds the current dyadic scale. -/
theorem rawDefect_append_false (w : List Bool) :
    rawDefect (w ++ [false]) = rawDefect w + 2 ^ (programData w).S := by
  rw [rawDefect, programData_append_singleton]
  change (programData w).A + 2 ^ ((programData w).S + 1) -
      3 ^ (programData w).O = rawDefect w + 2 ^ (programData w).S
  rw [pow_succ]
  have h := rawDefect_add_threePow w
  omega

/-- Appending an odd instruction triples the defect. -/
theorem rawDefect_append_true (w : List Bool) :
    rawDefect (w ++ [true]) = 3 * rawDefect w := by
  rw [rawDefect, programData_append_singleton]
  change (3 * (programData w).A + 2 ^ (programData w).S) +
      2 ^ ((programData w).S + 1) - 3 ^ ((programData w).O + 1) =
        3 * rawDefect w
  rw [pow_succ, pow_succ]
  have h := rawDefect_add_threePow w
  omega

theorem rawDefect_pos_of_false_mem {w : List Bool} (hfalse : false ∈ w) :
    0 < rawDefect w := by
  induction w using List.reverseRecOn with
  | nil => simp at hfalse
  | append_singleton w b ih =>
      cases b with
      | false =>
          rw [rawDefect_append_false]
          positivity
      | true =>
          rw [rawDefect_append_true]
          have : false ∈ w := by simpa using hfalse
          exact Nat.mul_pos (by omega) (ih this)

/-- A first-passage word beginning with `true` is the one-letter word. -/
theorem firstPassage_cons_true_eq_singleton {tail : List Bool}
    (hw : FirstPassage (true :: tail)) : tail = [] := by
  by_contra htail
  have hp : ProperPrefix [true] (true :: tail) := by
    constructor
    · simpa only [List.singleton_append] using
        (List.prefix_append [true] tail)
    · intro heq
      have := congrArg List.length heq
      simp at this
      exact htail this
  exact hw.2 [true] hp (by norm_num [WordOutward])

theorem firstPassage_nontrivial_head_false {w : List Bool}
    (hw : FirstPassage w) (hne : w ≠ [true]) : w.head? = some false := by
  cases w with
  | nil => exact (firstPassage_ne_nil hw rfl).elim
  | cons b tail =>
      cases b with
      | false => rfl
      | true =>
          have htail := firstPassage_cons_true_eq_singleton hw
          subst tail
          exact (hne rfl).elim

/-- The penultimate bit of a first-passage word cannot be even. -/
theorem firstPassage_not_terminal_false_true (u : List Bool)
    (hw : FirstPassage (u ++ [false, true])) : False := by
  have hup : ProperPrefix u (u ++ [false, true]) := by
    exact ⟨List.prefix_append _ _, by simp⟩
  have hnon : 3 ^ u.count true ≤ 2 ^ u.length :=
    Nat.le_of_not_gt (hw.2 u hup)
  have hout := hw.1
  simp only [WordOutward, List.length_append, List.count_append] at hout
  norm_num [pow_add] at hout
  nlinarith [show 0 < 2 ^ u.length by positivity]

/-- Every nontrivial first-passage word ends in `11`. -/
theorem firstPassage_nontrivial_ends_true_true {w : List Bool}
    (hw : FirstPassage w) (hne : w ≠ [true]) :
    ∃ u, w = u ++ [true, true] := by
  let hn := firstPassage_ne_nil hw
  let p := w.dropLast
  have hlast := firstPassage_last_eq_true hw
  have hwp : w = p ++ [true] := by
    symm
    calc
      p ++ [true] = p ++ [w.getLast hn] := by rw [hlast]
      _ = w := List.dropLast_append_getLast hn
  have hpne : p ≠ [] := by
    intro hp
    rw [hp] at hwp
    simpa using hne hwp
  let u := p.dropLast
  let b := p.getLast hpne
  have hpu : p = u ++ [b] := (List.dropLast_append_getLast hpne).symm
  have hshape : w = u ++ [b, true] := by
    rw [hwp, hpu]
    simp
  cases hb : b with
  | false =>
      exfalso
      apply firstPassage_not_terminal_false_true u
      simpa [hshape, hb] using hw
  | true =>
      exact ⟨u, by simpa [hshape, hb]⟩

theorem rawDefect_terminal_true_true (u : List Bool) :
    rawDefect (u ++ [true, true]) = 9 * rawDefect u := by
  rw [show u ++ [true, true] = (u ++ [true]) ++ [true] by simp,
    rawDefect_append_true, rawDefect_append_true]
  ring

/-- The boundary error is one third of the raw defect. -/
def boundaryError (w : List Bool) : ℕ := rawDefect w / 3

/-- Regression for the shallow recharge word `011`: its compressed error is
exactly three, as used in QM157j. -/
theorem boundaryError_false_true_true :
    boundaryError [false, true, true] = 3 := by
  norm_num [boundaryError, rawDefect, programData, accumulate, initialData,
    ParityData.step]

/-- QM157f, intrinsic part: a nontrivial first-passage boundary has positive
error, and that error is itself divisible by three. -/
theorem firstPassage_boundaryError_pos_and_three_dvd {w : List Bool}
    (hw : FirstPassage w) (hne : w ≠ [true]) :
    0 < boundaryError w ∧ 3 ∣ boundaryError w := by
  obtain ⟨u, rfl⟩ := firstPassage_nontrivial_ends_true_true hw hne
  have hhead := firstPassage_nontrivial_head_false hw hne
  have hfalse : false ∈ u ++ [true, true] := by
    cases u with
    | nil => simp at hhead
    | cons b tail =>
        cases b <;> simp_all
  have hpos : 0 < rawDefect (u ++ [true, true]) :=
    rawDefect_pos_of_false_mem hfalse
  rw [rawDefect_terminal_true_true] at hpos
  simp only [boundaryError]
  rw [rawDefect_terminal_true_true]
  refine ⟨?_, ⟨rawDefect u, ?_⟩⟩ <;>
    norm_num <;> omega

/-- QM157f, semantic balance: an execution between completed boundaries
obeys the compressed recharge equation. -/
theorem boundary_balance {w : List Bool} {H K : ℕ}
    (hw : Executes w (3 * H - 1) (3 * K - 1))
    (hH : 0 < H) (hK : 0 < K)
    (hdiv : 3 ∣ rawDefect w) :
    2 ^ (programData w).S * K =
      3 ^ (programData w).O * H + boundaryError w := by
  have hexact := program_exact w hw
  have hraw := rawDefect_add_threePow w
  obtain ⟨e, he⟩ := hdiv
  have herr : boundaryError w = e := by
    simp [boundaryError, he]
  have hKsub : 3 * K - 1 + 1 = 3 * K := Nat.sub_add_cancel (by omega)
  have hHsub : 3 * H - 1 + 1 = 3 * H := Nat.sub_add_cancel (by omega)
  have hKmul :
      2 ^ (programData w).S * (3 * K - 1) + 2 ^ (programData w).S =
        3 * (2 ^ (programData w).S * K) := by
    calc
      2 ^ (programData w).S * (3 * K - 1) + 2 ^ (programData w).S =
          2 ^ (programData w).S * ((3 * K - 1) + 1) := by ring
      _ = 2 ^ (programData w).S * (3 * K) := by rw [hKsub]
      _ = 3 * (2 ^ (programData w).S * K) := by ring
  have hHmul :
      3 ^ (programData w).O * (3 * H - 1) + 3 ^ (programData w).O =
        3 * (3 ^ (programData w).O * H) := by
    calc
      3 ^ (programData w).O * (3 * H - 1) + 3 ^ (programData w).O =
          3 ^ (programData w).O * ((3 * H - 1) + 1) := by ring
      _ = 3 ^ (programData w).O * (3 * H) := by rw [hHsub]
      _ = 3 * (3 ^ (programData w).O * H) := by ring
  have hmain :
      3 * (2 ^ (programData w).S * K) =
        3 * (3 ^ (programData w).O * H) + rawDefect w := by
    rw [← hKmul, hexact]
    omega
  rw [herr]
  rw [he] at hmain
  omega

/-- Full QM157f package for one nontrivial first-passage execution. -/
theorem firstPassage_boundary_package {w : List Bool} {H K : ℕ}
    (hfirst : FirstPassage w) (hne : w ≠ [true])
    (hw : Executes w (3 * H - 1) (3 * K - 1))
    (hH : 0 < H) (hK : 0 < K) :
    0 < boundaryError w ∧ 3 ∣ boundaryError w ∧
      2 ^ (programData w).S * K =
        3 ^ (programData w).O * H + boundaryError w := by
  obtain ⟨hpos, hdiv⟩ := firstPassage_boundaryError_pos_and_three_dvd hfirst hne
  refine ⟨hpos, hdiv, boundary_balance hw hH hK ?_⟩
  obtain ⟨u, rfl⟩ := firstPassage_nontrivial_ends_true_true hfirst hne
  rw [rawDefect_terminal_true_true]
  exact ⟨3 * rawDefect u, by ring⟩

/-! ## The forced one-letter drain -/

/-- QM157e, one step: an even boundary coordinate `2J` executes the
one-letter first-passage word and becomes `3J`. -/
theorem even_boundary_executes_true (J : ℕ) (hJ : 0 < J) :
    Executes [true] (3 * (2 * J) - 1) (3 * (3 * J) - 1) := by
  simp only [Executes]
  refine ⟨3 * (3 * J) - 1, ?_, rfl⟩
  simp only [if_pos]
  omega

/-- Literal parity forces the first word at an even boundary coordinate to
be `[true]`; this is not merely a slope argument. -/
theorem firstPassage_from_even_boundary_eq_true {w : List Bool}
    {J finish : ℕ} (hJ : 0 < J)
    (hfirst : FirstPassage w)
    (hw : Executes w (3 * (2 * J) - 1) finish) :
    w = [true] ∧ finish = 3 * (3 * J) - 1 := by
  cases w with
  | nil => exact (firstPassage_ne_nil hfirst rfl).elim
  | cons b tail =>
      obtain ⟨middle, hstep, htail⟩ := hw
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          omega
      | true =>
          have ht : tail = [] := firstPassage_cons_true_eq_singleton hfirst
          subst tail
          simp only [Executes] at htail
          subst finish
          constructor
          · rfl
          · simp only [↓reduceIte] at hstep
            omega

/-- `a` consecutive forced one-letter blocks drain the dyadic factor of a
boundary coordinate and replace it by the same power of three. -/
theorem drain_executes (a u : ℕ) (hu : 0 < u) :
    Executes (List.replicate a true)
      (3 * (2 ^ a * u) - 1) (3 * (3 ^ a * u) - 1) := by
  induction a generalizing u with
  | zero => simp [Executes]
  | succ a ih =>
      rw [List.replicate_succ]
      simp only [Executes]
      let middle := 3 * (2 ^ a * (3 * u)) - 1
      refine ⟨middle, ?_, ?_⟩
      · dsimp [middle]
        rw [pow_succ]
        have hp : 0 < 2 ^ a * u := by positivity
        have he : (2 ^ a * 2) * u = 2 * (2 ^ a * u) := by ring
        have hm : 2 ^ a * (3 * u) = 3 * (2 ^ a * u) := by ring
        rw [he, hm]
        omega
      · have hu3 : 0 < 3 * u := by positivity
        simpa [middle, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          ih (3 * u) hu3

/-- Canonical form of the complete drain: for positive `H`, exactly its
two-adic valuation many `[true]` bits lead to an odd boundary coordinate. -/
theorem canonical_drain (H : ℕ) (hH : 0 < H) :
    let a := padicValNat 2 H
    let u := H.divMaxPow 2
    Odd u ∧ 2 ^ a * u = H ∧
      Executes (List.replicate a true)
        (3 * H - 1) (3 * (3 ^ a * u) - 1) ∧
      Odd (3 ^ a * u) := by
  let a := padicValNat 2 H
  let u := H.divMaxPow 2
  have hfactor : 2 ^ a * u = H := by
    simpa [a, u] using Nat.pow_padicValNat_mul_divMaxPow 2 H
  have hupos : 0 < u := by
    have hp : 0 < 2 ^ a := by positivity
    nlinarith
  have hunot : ¬2 ∣ u := by
    exact Nat.not_dvd_divMaxPow (by omega) hH.ne'
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    have hmod := Nat.mod_lt u (by omega : 0 < 2)
    have hne : u % 2 ≠ 0 := fun hz => hunot (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  have hexec : Executes (List.replicate a true)
      (3 * H - 1) (3 * (3 ^ a * u) - 1) := by
    rw [← hfactor]
    exact drain_executes a u hupos
  have hfinalOdd : Odd (3 ^ a * u) :=
    (Odd.pow (n := a) (by norm_num : Odd 3)).mul huodd
  dsimp only
  exact ⟨huodd, hfactor, hexec, hfinalOdd⟩

/-! ## Odd recharge followed by its forced drain -/

/-- A nontrivial first-passage recharge between boundaries always lands at
a boundary coordinate divisible by three. -/
theorem three_dvd_boundary_target {w : List Bool} {H K : ℕ}
    (hfirst : FirstPassage w) (hne : w ≠ [true])
    (hw : Executes w (3 * H - 1) (3 * K - 1))
    (hH : 0 < H) (hK : 0 < K) : 3 ∣ K := by
  obtain ⟨_, hediv, hbalance⟩ :=
    firstPassage_boundary_package hfirst hne hw hH hK
  obtain ⟨u, hshape⟩ := firstPassage_nontrivial_ends_true_true hfirst hne
  have hO : 0 < (programData w).O := by
    rw [programData_O, hshape]
    simp
  have hpow : 3 ∣ 3 ^ (programData w).O :=
    dvd_pow (dvd_refl 3) hO.ne'
  have hrhs : 3 ∣ 3 ^ (programData w).O * H + boundaryError w :=
    dvd_add (dvd_mul_of_dvd_left hpow H) hediv
  have hprod : 3 ∣ 2 ^ (programData w).S * K := by
    rw [hbalance]
    exact hrhs
  have hcop : Nat.Coprime 3 (2 ^ (programData w).S) :=
    Nat.Coprime.pow_right _ (by norm_num)
  exact hcop.dvd_of_dvd_mul_left hprod

theorem sub_one_modEq_neg_one_of_dvd {m x : ℕ}
    (hm : 0 < m) (hx : 0 < x) (hd : m ∣ x) :
    x - 1 ≡ m - 1 [MOD m] := by
  have hxm : x ≡ m [MOD m] := by
    simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd]
  exact hxm.sub (by omega) (by omega) (Nat.ModEq.refl 1)

/-- QM157g--h without an existence leap.  Given one literal nontrivial
recharge, its canonical forced drain produces a larger positive odd
coordinate `R`.  It also satisfies the cross-prime divisibility statement
equivalent to `3*R-1 ≡ -1 (mod 3^(a+2))`. -/
theorem recharge_then_drain_properties {w : List Bool} {H K : ℕ}
    (hfirst : FirstPassage w) (hne : w ≠ [true])
    (hw : Executes w (3 * H - 1) (3 * K - 1))
    (hH : 0 < H) (hK : 0 < K) :
    let a := padicValNat 2 K
    let u := K.divMaxPow 2
    let R := 3 ^ a * u
    2 ^ a * u = K ∧ Odd u ∧ Odd R ∧ H < R ∧
      3 ^ (a + 1) ∣ R ∧ 3 ^ (a + 2) ∣ 3 * R ∧
      3 * R - 1 ≡ 3 ^ (a + 2) - 1 [MOD 3 ^ (a + 2)] ∧
      Executes (List.replicate a true) (3 * K - 1) (3 * R - 1) := by
  let a := padicValNat 2 K
  let u := K.divMaxPow 2
  let R := 3 ^ a * u
  have hfactor : 2 ^ a * u = K := by
    simpa [a, u] using Nat.pow_padicValNat_mul_divMaxPow 2 K
  have hupos : 0 < u := by
    have hp : 0 < 2 ^ a := by positivity
    nlinarith
  have hunot : ¬2 ∣ u :=
    Nat.not_dvd_divMaxPow (by omega) hK.ne'
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    have hmod := Nat.mod_lt u (by omega : 0 < 2)
    have hneMod : u % 2 ≠ 0 :=
      fun hz => hunot (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  have hRodd : Odd R :=
    (Odd.pow (n := a) (by norm_num : Odd 3)).mul huodd
  have hthreeK : 3 ∣ K :=
    three_dvd_boundary_target hfirst hne hw hH hK
  have hcop : Nat.Coprime 3 (2 ^ a) :=
    Nat.Coprime.pow_right _ (by norm_num)
  have hthreeU : 3 ∣ u := by
    apply hcop.dvd_of_dvd_mul_left
    rwa [hfactor]
  obtain ⟨q, hq⟩ := hthreeU
  have hRdiv : 3 ^ (a + 1) ∣ R := by
    refine ⟨q, ?_⟩
    dsimp [R]
    rw [hq, pow_succ]
    ring
  have hthreeRdiv : 3 ^ (a + 2) ∣ 3 * R := by
    obtain ⟨qR, hqR⟩ := hRdiv
    refine ⟨qR, ?_⟩
    rw [hqR, show a + 2 = (a + 1) + 1 by omega, pow_succ]
    ring
  have hstatePos : 0 < 3 * H - 1 := by omega
  have hHK : H < K := by
    have hs := OutwardCodeCounterexample.executes_lt_of_outward
      hstatePos hfirst.1 hw
    omega
  have hpowle : 2 ^ a ≤ 3 ^ a :=
    Nat.pow_le_pow_left (by omega) a
  have hKR : K ≤ R := by
    rw [← hfactor]
    exact Nat.mul_le_mul_right u hpowle
  have hHR : H < R := hHK.trans_le hKR
  have hnegOne :
      3 * R - 1 ≡ 3 ^ (a + 2) - 1 [MOD 3 ^ (a + 2)] :=
    sub_one_modEq_neg_one_of_dvd (by positivity) (by positivity) hthreeRdiv
  have hdrain : Executes (List.replicate a true)
      (3 * K - 1) (3 * R - 1) := by
    rw [← hfactor]
    exact drain_executes a u hupos
  dsimp only
  exact ⟨hfactor, huodd, hRodd, hHR, hRdiv, hthreeRdiv, hnegOne, hdrain⟩

/-! ## The shallow `011` normal form -/

/-- QM157j in algebraic normal form.  The exponent after the shallow
recharge is not free: if `K=2^a*v` with `v` odd, then `v` has exactly one
factor of three.  Writing `H=3^c*u` produces the advertised two-counter
equation with `c'=a+1`. -/
theorem shallow_recharge_normal_form
    {H K a v c u : ℕ}
    (hbalance : 8 * K = 9 * H + 3)
    (hKfactor : 2 ^ a * v = K) (hvOdd : Odd v)
    (hHfactor : 3 ^ c * u = H) :
    ∃ u' : ℕ,
      Odd u' ∧ ¬3 ∣ u' ∧ v = 3 * u' ∧
      2 ^ ((a + 1) + 2) * u' = 3 ^ (c + 1) * u + 1 := by
  have hthreeRhs : 3 ∣ 9 * H + 3 := by
    refine ⟨3 * H + 1, by ring⟩
  have hthreeProd : 3 ∣ 8 * K := by
    rw [hbalance]
    exact hthreeRhs
  have hthreeK : 3 ∣ K :=
    (by norm_num : Nat.Coprime 3 8).dvd_of_dvd_mul_left hthreeProd
  have hthreeV : 3 ∣ v := by
    have hprod : 3 ∣ 2 ^ a * v := by rwa [hKfactor]
    exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left hprod
  obtain ⟨u', hv⟩ := hthreeV
  have huOdd : Odd u' := by
    rw [Nat.odd_iff] at hvOdd ⊢
    rw [hv] at hvOdd
    simpa [Nat.mul_mod] using hvOdd
  have heq : 2 ^ (a + 3) * u' = 3 * H + 1 := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 3)
    calc
      3 * (2 ^ (a + 3) * u') = 8 * (2 ^ a * (3 * u')) := by
        rw [pow_add]
        norm_num
        ring
      _ = 8 * K := by rw [← hv, hKfactor]
      _ = 9 * H + 3 := hbalance
      _ = 3 * (3 * H + 1) := by ring
  have huNotThree : ¬3 ∣ u' := by
    intro hthree
    have hleft : 3 ∣ 2 ^ (a + 3) * u' := dvd_mul_of_dvd_right hthree _
    rw [heq] at hleft
    obtain ⟨q, hq⟩ := hleft
    omega
  refine ⟨u', huOdd, huNotThree, hv, ?_⟩
  rw [show (a + 1) + 2 = a + 3 by omega, heq, ← hHfactor]
  rw [pow_succ]
  ring

end OutwardBoundaryRenewal
end KontoroC

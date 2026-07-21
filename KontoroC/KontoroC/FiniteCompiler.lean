/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.ValuationWord

/-!
# The exact finite-word compiler criterion

The compiler solves one final affine congruence.  The load-bearing statement
is that, for a word of positive valuations, this final condition recovers
*every* intermediate exact valuation.  We formulate it as factorization by
`2^S` with an odd final quotient; the modular form follows separately.
-/

namespace KontoroC

/-- Every claimed valuation in a compiler word is positive. -/
def PositiveWord (w : List ℕ) : Prop :=
  ∀ k ∈ w, 0 < k

instance (w : List ℕ) : Decidable (PositiveWord w) := by
  unfold PositiveWord
  infer_instance

/-- The affine numerator has exact two-adic valuation `sum w`, with odd
quotient `z`. -/
def AffineOddFactor (x : ℕ) (w : List ℕ) : Prop :=
  ∃ z : ℕ, z % 2 = 1 ∧
    3 ^ w.length * x + affineOffset w = 2 ^ totalValuation w * z

/-- The single final congruence solved by the finite compiler. -/
def FinalCongruence (x : ℕ) (w : List ℕ) : Prop :=
  (3 ^ w.length * x + affineOffset w) %
      2 ^ (totalValuation w + 1) = 2 ^ totalValuation w

theorem positiveWord_tail {k : ℕ} {w : List ℕ}
    (h : PositiveWord (k :: w)) : PositiveWord w := by
  intro j hj
  exact h j (List.mem_cons_of_mem k hj)

theorem positiveWord_head {k : ℕ} {w : List ℕ}
    (h : PositiveWord (k :: w)) : 0 < k :=
  h k (by simp)

/-- Exactness of the final affine valuation is equivalent to literal replay
of every claimed valuation and an odd final endpoint. -/
theorem affineOddFactor_iff_wordLegal (x : ℕ) (w : List ℕ)
    (hpositive : PositiveWord w) :
    AffineOddFactor x w ↔
      WordLegal x w ∧ runWord x w % 2 = 1 := by
  induction w generalizing x with
  | nil =>
      simp [AffineOddFactor, WordLegal, runWord, totalValuation, affineOffset]
  | cons k w ih =>
      have hk : 0 < k := positiveWord_head hpositive
      have hposTail : PositiveWord w := positiveWord_tail hpositive
      constructor
      · rintro ⟨z, hzOdd, hzEq⟩
        have hexpanded :
            3 ^ w.length * (3 * x + 1) + 2 ^ k * affineOffset w =
              2 ^ k * (2 ^ totalValuation w * z) := by
          rw [List.length_cons, affineOffset_cons, totalValuation_cons,
            Nat.pow_succ, Nat.pow_add] at hzEq
          calc
            3 ^ w.length * (3 * x + 1) + 2 ^ k * affineOffset w =
                (3 ^ w.length * 3) * x +
                  (3 ^ w.length + 2 ^ k * affineOffset w) := by ring
            _ = 2 ^ k * 2 ^ totalValuation w * z := hzEq
            _ = 2 ^ k * (2 ^ totalValuation w * z) := by ring
        have hsumDvd : 2 ^ k ∣
            3 ^ w.length * (3 * x + 1) + 2 ^ k * affineOffset w := by
          rw [hexpanded]
          exact dvd_mul_right _ _
        have hrightDvd : 2 ^ k ∣ 2 ^ k * affineOffset w :=
          dvd_mul_right _ _
        have hfirstDvd : 2 ^ k ∣ 3 ^ w.length * (3 * x + 1) :=
          (Nat.dvd_add_left hrightDvd).mp hsumDvd
        have hcop : (2 ^ k).Coprime (3 ^ w.length) :=
          (by norm_num : Nat.Coprime 2 3).pow _ _
        have hstepDvd : 2 ^ k ∣ 3 * x + 1 :=
          hcop.dvd_of_dvd_mul_left hfirstDvd
        let y := (3 * x + 1) / 2 ^ k
        have hstepEq : 2 ^ k * y = 3 * x + 1 := by
          exact Nat.mul_div_cancel' hstepDvd
        have htailEq :
            3 ^ w.length * y + affineOffset w =
              2 ^ totalValuation w * z := by
          have hcancel :
              2 ^ k * (3 ^ w.length * y + affineOffset w) =
                2 ^ k * (2 ^ totalValuation w * z) := by
            calc
              2 ^ k * (3 ^ w.length * y + affineOffset w) =
                  3 ^ w.length * (2 ^ k * y) +
                    2 ^ k * affineOffset w := by ring
              _ = 3 ^ w.length * (3 * x + 1) +
                    2 ^ k * affineOffset w := by rw [hstepEq]
              _ = 2 ^ k * (2 ^ totalValuation w * z) := hexpanded
          exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hcancel
        have htailFactor : AffineOddFactor y w := ⟨z, hzOdd, htailEq⟩
        have htail := (ih y hposTail).mp htailFactor
        have hyOdd : y % 2 = 1 := by
          cases w with
          | nil => simpa [runWord] using htail.2
          | cons j js => exact htail.1.1.2.1
        have hyNotDvd : ¬2 ∣ y := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have hsource : 3 * x + 1 ≠ 0 := by omega
        have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq
          (p := 2) (n := 3 * x + 1) (k := k) (l := y)
          hsource hstepEq hyNotDvd
        have hval : oddValuation x = k := by
          have := congrArg Prod.fst hmax
          simpa [oddValuation] using this
        have hyPos : 0 < y := by
          have : y ≠ 0 := by
            intro hy
            simp [hy] at hyOdd
          exact Nat.pos_of_ne_zero this
        have hxPos : 0 < x := by
          by_contra hx
          have hx0 : x = 0 := by omega
          have hoddPow : 2 ≤ 2 ^ k :=
            Nat.one_lt_pow hk.ne' (by omega)
          rw [hx0] at hstepEq
          norm_num at hstepEq
          nlinarith
        have hxOdd : x % 2 = 1 := by
          have hpowEven : 2 ∣ 2 ^ k := by
            exact dvd_pow_self 2 hk.ne'
          have hsourceEven : 2 ∣ 3 * x + 1 := by
            rw [← hstepEq]
            exact dvd_mul_of_dvd_left hpowEven y
          rw [Nat.dvd_iff_mod_eq_zero] at hsourceEven
          omega
        have hstepOut : oddStep x = y := by
          have := congrArg Prod.snd hmax
          simpa [oddStep] using this
        constructor
        · constructor
          · exact ⟨hxPos, hxOdd, hval.symm⟩
          · simpa [hstepOut] using htail.1
        · simpa [runWord_cons, hstepOut] using htail.2
      · rintro ⟨hlegal, hrunOdd⟩
        have htail : WordLegal (oddStep x) w := hlegal.2
        have htailOdd : runWord (oddStep x) w % 2 = 1 := by
          simpa [runWord_cons] using hrunOdd
        obtain ⟨z, hzOdd, hzEq⟩ :=
          (ih (oddStep x) hposTail).mpr ⟨htail, htailOdd⟩
        refine ⟨z, hzOdd, ?_⟩
        have hstepEq := legalInstruction_step_equation hlegal.1
        rw [List.length_cons, affineOffset_cons, totalValuation_cons,
          Nat.pow_succ, Nat.pow_add]
        calc
          (3 ^ w.length * 3) * x +
              (3 ^ w.length + 2 ^ k * affineOffset w) =
              3 ^ w.length * (3 * x + 1) +
                2 ^ k * affineOffset w := by ring
          _ = 3 ^ w.length * (2 ^ k * oddStep x) +
                2 ^ k * affineOffset w := by rw [hstepEq]
          _ = 2 ^ k *
                (3 ^ w.length * oddStep x + affineOffset w) := by ring
          _ = 2 ^ k * (2 ^ totalValuation w * z) := by rw [hzEq]
          _ = 2 ^ k * 2 ^ totalValuation w * z := by ring

/-- Exact factorization by `2^S` with odd quotient is equivalent to the
compiler's one congruence modulo `2^(S+1)`. -/
theorem affineOddFactor_iff_finalCongruence (x : ℕ) (w : List ℕ) :
    AffineOddFactor x w ↔ FinalCongruence x w := by
  let B := 2 ^ totalValuation w
  let N := 3 ^ w.length * x + affineOffset w
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.pow_pos (by omega)
  have hmodulus : 2 ^ (totalValuation w + 1) = B * 2 := by
    simp [B, Nat.pow_succ]
  constructor
  · rintro ⟨z, hzOdd, hzEq⟩
    unfold FinalCongruence
    rw [hzEq, hmodulus, Nat.mul_mod_mul_left, hzOdd]
    simp
  · intro hcong
    have hmod : N % (B * 2) = B := by
      simpa [FinalCongruence, N, hmodulus] using hcong
    have hdiv : B ∣ N := by
      have hm := Nat.mod_mod_of_dvd N (dvd_mul_right B 2)
      rw [hmod] at hm
      have hzero : N % B = 0 := by simpa using hm.symm
      exact Nat.dvd_of_mod_eq_zero hzero
    obtain ⟨z, hzEq⟩ := hdiv
    have hzOdd : z % 2 = 1 := by
      rw [hzEq, Nat.mul_mod_mul_left] at hmod
      apply Nat.eq_of_mul_eq_mul_left hB
      simpa using hmod
    exact ⟨z, hzOdd, by simpa [N, B] using hzEq⟩

/-- The final congruence is neither a heuristic nor merely a necessary
condition: for positive words it is equivalent to exact instruction-by-
instruction replay with an odd endpoint. -/
theorem finalCongruence_iff_wordLegal (x : ℕ) (w : List ℕ)
    (hpositive : PositiveWord w) :
    FinalCongruence x w ↔
      WordLegal x w ∧ runWord x w % 2 = 1 := by
  rw [← affineOddFactor_iff_finalCongruence,
    affineOddFactor_iff_wordLegal x w hpositive]

/-- The final linear congruence has a solution, represented canonically below
its power-of-two modulus. -/
theorem exists_finalCongruence (w : List ℕ) :
    ∃ r : ℕ, r < 2 ^ (totalValuation w + 1) ∧ FinalCongruence r w := by
  let S := totalValuation w
  let M := 2 ^ (S + 1)
  let C := 3 ^ w.length
  let B := 2 ^ S
  let A := affineOffset w
  have hM : 0 < M := by simp [M]
  letI : NeZero M := ⟨hM.ne'⟩
  have hcop : C.Coprime M := by
    dsimp [C, M]
    exact (by norm_num : Nat.Coprime 3 2).pow _ _
  have hunit : IsUnit (C : ZMod M) :=
    (ZMod.isUnit_iff_coprime C M).2 hcop
  let rz : ZMod M :=
    (C : ZMod M)⁻¹ * ((B : ZMod M) - (A : ZMod M))
  let r := rz.val
  have hrcast : (r : ZMod M) = rz := ZMod.natCast_zmod_val rz
  have heqZ :
      (C : ZMod M) * (r : ZMod M) + (A : ZMod M) = (B : ZMod M) := by
    rw [hrcast]
    dsimp [rz]
    calc
      (C : ZMod M) *
            ((C : ZMod M)⁻¹ * ((B : ZMod M) - (A : ZMod M))) + A =
          ((C : ZMod M) * (C : ZMod M)⁻¹) *
            ((B : ZMod M) - A) + A := by ring
      _ = 1 * ((B : ZMod M) - A) + A := by
        rw [ZMod.mul_inv_of_unit _ hunit]
      _ = B := by ring
  have hcast : ((C * r + A : ℕ) : ZMod M) = (B : ZMod M) := by
    simpa using heqZ
  have hmods : (C * r + A) % M = B % M :=
    (ZMod.natCast_eq_natCast_iff' (C * r + A) B M).mp hcast
  have hBlt : B < M := by
    dsimp [B, M]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hBmod : B % M = B := Nat.mod_eq_of_lt hBlt
  refine ⟨r, ZMod.val_lt rz, ?_⟩
  simpa [FinalCongruence, S, M, C, B, A, hBmod] using hmods

/-- Final-congruence solutions form one residue class modulo `2^(S+1)`. -/
theorem finalCongruence_unique_mod (w : List ℕ) {x y : ℕ}
    (hx : FinalCongruence x w) (hy : FinalCongruence y w) :
    x ≡ y [MOD 2 ^ (totalValuation w + 1)] := by
  let M := 2 ^ (totalValuation w + 1)
  let C := 3 ^ w.length
  let A := affineOffset w
  let B := 2 ^ totalValuation w
  have hBlt : B < M := by
    dsimp [B, M]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hx' : C * x + A ≡ B [MOD M] := by
    change (C * x + A) % M = B % M
    simpa [FinalCongruence, M, C, A, B, Nat.mod_eq_of_lt hBlt] using hx
  have hy' : C * y + A ≡ B [MOD M] := by
    change (C * y + A) % M = B % M
    simpa [FinalCongruence, M, C, A, B, Nat.mod_eq_of_lt hBlt] using hy
  have hsum : C * x + A ≡ C * y + A [MOD M] := hx'.trans hy'.symm
  have hprod : C * x ≡ C * y [MOD M] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl A) hsum
  have hcop : M.Coprime C := by
    dsimp [M, C]
    exact (by norm_num : Nat.Coprime 2 3).pow _ _
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hprod

/-- Final congruence is preserved when replacing the seed by a congruent
representative. -/
theorem FinalCongruence.of_modEq (w : List ℕ) {x y : ℕ}
    (hxy : x ≡ y [MOD 2 ^ (totalValuation w + 1)])
    (hx : FinalCongruence x w) : FinalCongruence y w := by
  let M := 2 ^ (totalValuation w + 1)
  let C := 3 ^ w.length
  let A := affineOffset w
  have hprod : C * x ≡ C * y [MOD M] := (Nat.ModEq.refl C).mul hxy
  have hsum : C * x + A ≡ C * y + A [MOD M] :=
    hprod.add (Nat.ModEq.refl A)
  unfold FinalCongruence at hx ⊢
  change (C * y + A) % M = 2 ^ totalValuation w
  change (C * x + A) % M = 2 ^ totalValuation w at hx
  rw [← hx]
  exact hsum.symm

/-- Combining the unique program class modulo `2^(S+1)` with one class
modulo three gives the full worker progression modulus `6*2^S`. -/
theorem finalCongruence_unique_mod_progression (w : List ℕ) {x y : ℕ}
    (hx : FinalCongruence x w) (hy : FinalCongruence y w)
    (hxy3 : x ≡ y [MOD 3]) :
    x ≡ y [MOD 6 * 2 ^ totalValuation w] := by
  have hM := finalCongruence_unique_mod w hx hy
  have hcop : (2 ^ (totalValuation w + 1)).Coprime 3 :=
    (by norm_num : Nat.Coprime 2 3).pow_left _
  have hcombined :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hM, hxy3⟩
  have hmodulus :
      2 ^ (totalValuation w + 1) * 3 = 6 * 2 ^ totalValuation w := by
    rw [Nat.pow_succ]
    ring
  rw [← hmodulus]
  exact hcombined

theorem runWord_mod_two_of_wordLegal_ne_nil {x : ℕ} {w : List ℕ}
    (hw : w ≠ []) (hlegal : WordLegal x w) : runWord x w % 2 = 1 := by
  induction w generalizing x with
  | nil => exact (hw rfl).elim
  | cons k w ih =>
      cases w with
      | nil => simpa [runWord] using oddStep_mod_two x
      | cons j js =>
          exact ih (by simp) hlegal.2

theorem finalCongruence_of_wordLegal {x : ℕ} {w : List ℕ}
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (hlegal : WordLegal x w) : FinalCongruence x w :=
  (finalCongruence_iff_wordLegal x w hpositive).mpr
    ⟨hlegal, runWord_mod_two_of_wordLegal_ne_nil hw hlegal⟩

/-- Any two legal realizations in the same class modulo six differ by a
multiple of the full compiler modulus. -/
theorem wordLegal_unique_mod_progression {w : List ℕ} {x y : ℕ}
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (hx : WordLegal x w) (hy : WordLegal y w)
    (hxy6 : x ≡ y [MOD 6]) :
    x ≡ y [MOD 6 * 2 ^ totalValuation w] := by
  have hxy3 : x ≡ y [MOD 3] :=
    Nat.ModEq.of_dvd (by norm_num : 3 ∣ 6) hxy6
  exact finalCongruence_unique_mod_progression w
    (finalCongruence_of_wordLegal hw hpositive hx)
    (finalCongruence_of_wordLegal hw hpositive hy) hxy3

/-- CRT combines the unique power-of-two program residue with either desired
class modulo three. -/
theorem exists_finalCongruence_mod_three (w : List ℕ) (e : ℕ) :
    ∃ x : ℕ, x < 2 ^ (totalValuation w + 1) * 3 ∧
      FinalCongruence x w ∧ x ≡ e [MOD 3] := by
  obtain ⟨r, _hrlt, hr⟩ := exists_finalCongruence w
  let M := 2 ^ (totalValuation w + 1)
  have hcop : M.Coprime 3 := by
    dsimp [M]
    exact (by norm_num : Nat.Coprime 2 3).pow_left _
  let c := Nat.chineseRemainder hcop r e
  refine ⟨c, ?_, ?_, c.property.2⟩
  · exact Nat.chineseRemainder_lt_mul hcop r e (by simp [M]) (by norm_num)
  · exact FinalCongruence.of_modEq w c.property.1.symm hr

/-- Every positive finite instruction word occurs in either admissible class
modulo six. -/
theorem exists_compiled_seed (w : List ℕ) (e : ℕ)
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (he : e = 1 ∨ e = 5) :
    ∃ x : ℕ, 0 < x ∧ x < 6 * 2 ^ totalValuation w ∧
      x % 6 = e ∧ WordLegal x w := by
  obtain ⟨x, hxlt, hxcong, hx3⟩ := exists_finalCongruence_mod_three w e
  have hxfull := (finalCongruence_iff_wordLegal x w hpositive).mp hxcong
  have hxlegal := hxfull.1
  have hxpos : 0 < x := by
    cases w with
    | nil => exact (hw rfl).elim
    | cons k ks => exact hxlegal.1.1
  have hxodd : x % 2 = 1 := by
    cases w with
    | nil => exact (hw rfl).elim
    | cons k ks => exact hxlegal.1.2.1
  have hx2 : x ≡ e [MOD 2] := by
    change x % 2 = e % 2
    rcases he with rfl | rfl <;> norm_num [hxodd]
  have hx6 : x ≡ e [MOD 6] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul
      (by norm_num : Nat.Coprime 2 3)).mp ⟨hx2, hx3⟩
    norm_num at this ⊢
    exact this
  have he6 : e < 6 := by rcases he with rfl | rfl <;> omega
  have hxlt' : x < 6 * 2 ^ totalValuation w := by
    have hmodulus :
        2 ^ (totalValuation w + 1) * 3 = 6 * 2 ^ totalValuation w := by
      rw [Nat.pow_succ]
      ring
    rwa [← hmodulus]
  exact ⟨x, hxpos, hxlt', Nat.mod_eq_of_modEq hx6 he6, hxlegal⟩

/-- There is exactly one legal representative in the canonical positive
range for each admissible class. -/
theorem canonical_compiled_seed_unique {w : List ℕ} {e x y : ℕ}
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (hxlt : x < 6 * 2 ^ totalValuation w)
    (hylt : y < 6 * 2 ^ totalValuation w)
    (hxe : x % 6 = e) (hye : y % 6 = e)
    (hx : WordLegal x w) (hy : WordLegal y w) : x = y := by
  have hxy6 : x ≡ y [MOD 6] := by
    exact hxe.trans hye.symm
  exact (wordLegal_unique_mod_progression hw hpositive hx hy hxy6).eq_of_lt_of_lt
    hxlt hylt

/-- Every representative of a legal seed's full progression realizes the
same valuation word. -/
theorem wordLegal_of_mod_progression {w : List ℕ} {x y : ℕ}
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (hx : WordLegal x w)
    (hxy : x ≡ y [MOD 6 * 2 ^ totalValuation w]) :
    WordLegal y w := by
  have hdiv : 2 ^ (totalValuation w + 1) ∣
      6 * 2 ^ totalValuation w := by
    refine ⟨3, ?_⟩
    rw [Nat.pow_succ]
    ring
  have hxy' : x ≡ y [MOD 2 ^ (totalValuation w + 1)] :=
    Nat.ModEq.of_dvd hdiv hxy
  have hxcong := finalCongruence_of_wordLegal hw hpositive hx
  exact (finalCongruence_iff_wordLegal y w hpositive).mp
    (FinalCongruence.of_modEq w hxy' hxcong) |>.1

/-- The endpoint arithmetic progression has stride `6*3^N`, exactly as in
`collatz-k-path-v1`. -/
theorem runWord_add_seedModulus {w : List ℕ} {x : ℕ} (t : ℕ)
    (hw : w ≠ []) (hpositive : PositiveWord w)
    (hx : WordLegal x w) :
    runWord (x + (6 * 2 ^ totalValuation w) * t) w =
      runWord x w + (6 * 3 ^ w.length) * t := by
  let B := 2 ^ totalValuation w
  let C := 3 ^ w.length
  let A := affineOffset w
  let y := x + (6 * B) * t
  have hxy : x ≡ y [MOD 6 * B] := by
    change x % (6 * B) = (x + (6 * B) * t) % (6 * B)
    simp [Nat.add_mod]
  have hy : WordLegal y w := by
    exact wordLegal_of_mod_progression hw hpositive hx (by simpa [B] using hxy)
  have hxEq := valuationWord_affine_identity hx
  have hyEq := valuationWord_affine_identity hy
  have hB : 0 < B := by simp [B]
  apply Nat.eq_of_mul_eq_mul_left hB
  change B * runWord y w = B * (runWord x w + (6 * C) * t)
  calc
    B * runWord y w = C * y + A := by simpa [B, C, A] using hyEq
    _ = (C * x + A) + B * ((6 * C) * t) := by
      dsimp [y]
      ring
    _ = B * runWord x w + B * ((6 * C) * t) := by
      rw [← show B * runWord x w = C * x + A by
        simpa [B, C, A] using hxEq]
    _ = B * (runWord x w + (6 * C) * t) := by ring

end KontoroC

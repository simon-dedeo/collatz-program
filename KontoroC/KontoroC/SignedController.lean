/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.NegativeShadow

/-!
# Exact signed controllers

Negative cycles are not counterexamples to the positive Collatz conjecture.
They can, however, be checked exactly as finite controllers.  This module
closes the provenance gap between a signed accelerated cycle and the affine
fixed equation consumed by `NegativeShadow`.
-/

namespace KontoroC

/-- Execute one signed accelerated instruction with a claimed valuation. -/
def signedStepAt (n : ℤ) (k : ℕ) : ℤ :=
  (3 * n + 1) / 2 ^ k

/-- Exact signed instruction: positive valuation, exact division, and odd
states on both sides.  Oddness of the quotient makes the valuation maximal. -/
def SignedLegalInstruction (n : ℤ) (k : ℕ) : Prop :=
  Odd n ∧ 0 < k ∧
    3 * n + 1 = (2 ^ k : ℤ) * signedStepAt n k ∧
    Odd (signedStepAt n k)

instance (n : ℤ) (k : ℕ) : Decidable (SignedLegalInstruction n k) := by
  unfold SignedLegalInstruction
  infer_instance

def signedRunWord : ℤ → List ℕ → ℤ
  | n, [] => n
  | n, k :: ks => signedRunWord (signedStepAt n k) ks

def SignedWordLegal : ℤ → List ℕ → Prop
  | _, [] => True
  | n, k :: ks => SignedLegalInstruction n k ∧
      SignedWordLegal (signedStepAt n k) ks

instance signedWordLegalDecidable : ∀ n ks, Decidable (SignedWordLegal n ks)
  | _, [] => inferInstanceAs (Decidable True)
  | n, k :: ks =>
      @instDecidableAnd (SignedLegalInstruction n k)
        (SignedWordLegal (signedStepAt n k) ks)
        (inferInstanceAs (Decidable (SignedLegalInstruction n k)))
        (signedWordLegalDecidable (signedStepAt n k) ks)

@[simp] theorem signedRunWord_nil (n : ℤ) : signedRunWord n [] = n := rfl

@[simp] theorem signedRunWord_cons (n : ℤ) (k : ℕ) (ks : List ℕ) :
    signedRunWord n (k :: ks) = signedRunWord (signedStepAt n k) ks := rfl

theorem signedRunWord_append (n : ℤ) (u v : List ℕ) :
    signedRunWord n (u ++ v) = signedRunWord (signedRunWord n u) v := by
  induction u generalizing n with
  | nil => rfl
  | cons k u ih => simpa using ih (signedStepAt n k)

theorem signedWordLegal_append_iff (n : ℤ) (u v : List ℕ) :
    SignedWordLegal n (u ++ v) ↔
      SignedWordLegal n u ∧ SignedWordLegal (signedRunWord n u) v := by
  induction u generalizing n with
  | nil => simp [SignedWordLegal]
  | cons k u ih =>
      simp only [List.cons_append, SignedWordLegal, signedRunWord_cons]
      rw [ih]
      tauto

/-- Signed analogue of the finite valuation-word affine identity. -/
theorem signedValuationWord_affine_identity {x : ℤ} {ks : List ℕ}
    (h : SignedWordLegal x ks) :
    (2 ^ totalValuation ks : ℤ) * signedRunWord x ks =
      (3 ^ ks.length : ℤ) * x + affineOffset ks := by
  induction ks generalizing x with
  | nil => simp
  | cons k ks ih =>
      have hstep : (2 ^ k : ℤ) * signedStepAt x k = 3 * x + 1 :=
        h.1.2.2.1.symm
      have htail := ih h.2
      rw [totalValuation_cons, pow_add, signedRunWord_cons,
        affineOffset_cons, List.length_cons, pow_succ]
      push_cast
      calc
        ((2 : ℤ) ^ k * (2 : ℤ) ^ totalValuation ks) *
            signedRunWord (signedStepAt x k) ks =
            (2 : ℤ) ^ k *
              ((2 : ℤ) ^ totalValuation ks *
                signedRunWord (signedStepAt x k) ks) := by ring
        _ = (2 : ℤ) ^ k *
              ((3 : ℤ) ^ ks.length * signedStepAt x k + affineOffset ks) := by
                rw [htail]
        _ = (3 : ℤ) ^ ks.length *
              ((2 : ℤ) ^ k * signedStepAt x k) +
              (2 : ℤ) ^ k * affineOffset ks := by ring
        _ = (3 : ℤ) ^ ks.length * (3 * x + 1) +
              (2 : ℤ) ^ k * affineOffset ks := by rw [hstep]
        _ = ((3 : ℤ) ^ ks.length * 3) * x +
              ((3 : ℤ) ^ ks.length + (2 : ℤ) ^ k * affineOffset ks) := by ring

theorem signedCycle_affine_fixed {c : ℤ} {w : List ℕ}
    (hlegal : SignedWordLegal c w) (hclose : signedRunWord c w = c) :
    (2 ^ totalValuation w : ℤ) * c =
      (3 ^ w.length : ℤ) * c + affineOffset w := by
  simpa [hclose] using signedValuationWord_affine_identity hlegal

/-- Every nonempty negative signed cycle is supercritical: its affine
multiplier satisfies `3^N > 2^S`. -/
theorem signedNegativeCycle_shape_strict {c : ℤ} {w : List ℕ}
    (hc : c < 0) (hw : w ≠ [])
    (hlegal : SignedWordLegal c w) (hclose : signedRunWord c w = c) :
    2 ^ totalValuation w < 3 ^ w.length := by
  have hfixed := signedCycle_affine_fixed hlegal hclose
  have hA : (0 : ℤ) < affineOffset w := by
    exact_mod_cast affineOffset_pos_of_ne_nil hw
  by_contra hnot
  have hle : (3 ^ w.length : ℤ) ≤ 2 ^ totalValuation w := by
    exact_mod_cast (Nat.le_of_not_gt hnot)
  nlinarith

/-- Every cyclic rotation of an exact signed cycle is an exact signed cycle
at the corresponding phase state. -/
theorem signedCycle_rotate {c : ℤ} {u v : List ℕ}
    (hlegal : SignedWordLegal c (u ++ v))
    (hclose : signedRunWord c (u ++ v) = c) :
    SignedWordLegal (signedRunWord c u) (v ++ u) ∧
      signedRunWord (signedRunWord c u) (v ++ u) = signedRunWord c u := by
  have huv := (signedWordLegal_append_iff c u v).mp hlegal
  have hvc : signedRunWord (signedRunWord c u) v = c := by
    rw [← signedRunWord_append]
    exact hclose
  constructor
  · apply (signedWordLegal_append_iff (signedRunWord c u) v u).mpr
    refine ⟨huv.2, ?_⟩
    rw [hvc]
    exact huv.1
  · rw [signedRunWord_append, hvc]

theorem signedCycle_rotate_affine_fixed {c : ℤ} {u v : List ℕ}
    (hlegal : SignedWordLegal c (u ++ v))
    (hclose : signedRunWord c (u ++ v) = c) :
    (2 ^ totalValuation (v ++ u) : ℤ) * signedRunWord c u =
      (3 ^ (v ++ u).length : ℤ) * signedRunWord c u +
        affineOffset (v ++ u) := by
  have hr := signedCycle_rotate hlegal hclose
  exact signedCycle_affine_fixed hr.1 hr.2

/-- Portable exact negative-controller certificate. -/
structure SignedCycleCertificate where
  seed : ℤ
  word : List ℕ
deriving Repr, DecidableEq

def SignedCycleCertificate.Valid (c : SignedCycleCertificate) : Prop :=
  c.seed < 0 ∧ c.word ≠ [] ∧
    SignedWordLegal c.seed c.word ∧ signedRunWord c.seed c.word = c.seed

instance SignedCycleCertificate.instDecidableValid
    (c : SignedCycleCertificate) : Decidable c.Valid := by
  unfold SignedCycleCertificate.Valid
  infer_instance

def SignedCycleCertificate.check (c : SignedCycleCertificate) : Bool :=
  decide c.Valid

theorem SignedCycleCertificate.valid_of_check {c : SignedCycleCertificate}
    (h : c.check = true) : c.Valid := by
  simpa [SignedCycleCertificate.check] using h

theorem SignedCycleCertificate.affine_fixed {c : SignedCycleCertificate}
    (h : c.check = true) :
    (2 ^ totalValuation c.word : ℤ) * c.seed =
      (3 ^ c.word.length : ℤ) * c.seed + affineOffset c.word := by
  have hv := c.valid_of_check h
  exact signedCycle_affine_fixed hv.2.2.1 hv.2.2.2

theorem SignedCycleCertificate.supercritical {c : SignedCycleCertificate}
    (h : c.check = true) :
    2 ^ totalValuation c.word < 3 ^ c.word.length := by
  have hv := c.valid_of_check h
  exact signedNegativeCycle_shape_strict hv.1 hv.2.1 hv.2.2.1 hv.2.2.2

/-- The negative fixed point used by the Mersenne-shadow worker. -/
def minusOneController : SignedCycleCertificate := ⟨-1, [1]⟩

/-- The `-5` controller used by the shadow workers. -/
def minusFiveController : SignedCycleCertificate := ⟨-5, [1, 2]⟩

/-- The `-17` controller used by the shadow workers. -/
def minusSeventeenController : SignedCycleCertificate :=
  ⟨-17, [1, 1, 1, 2, 1, 1, 4]⟩

theorem minusOneController_check : minusOneController.check = true := by
  norm_num [minusOneController, SignedCycleCertificate.check,
    SignedCycleCertificate.Valid, SignedWordLegal, SignedLegalInstruction,
    signedRunWord, signedStepAt]

theorem minusFiveController_check : minusFiveController.check = true := by
  norm_num [minusFiveController, SignedCycleCertificate.check,
    SignedCycleCertificate.Valid, SignedWordLegal, SignedLegalInstruction,
    signedRunWord, signedStepAt] <;> simp

theorem minusSeventeenController_check :
    minusSeventeenController.check = true := by
  norm_num [minusSeventeenController, SignedCycleCertificate.check,
    SignedCycleCertificate.Valid, SignedWordLegal, SignedLegalInstruction,
    signedRunWord, signedStepAt] <;> simp

/-- High-level all-level search certificate.  Each phase is represented by a
split `prefix ++ suffix` of one checked negative cycle; the active controller
word is the rotation `suffix ++ prefix`. -/
structure CertifiedCyclePhaseShadowOrbit where
  cert : SignedCycleCertificate
  cert_ok : cert.check = true
  phasePrefix : ℕ → List ℕ
  phaseSuffix : ℕ → List ℕ
  phase_split : ∀ t, cert.word = phasePrefix t ++ phaseSuffix t
  phase_neg : ∀ t, signedRunWord cert.seed (phasePrefix t) < 0
  level0 : ℕ
  extra : ℕ → ℕ
  packet : ℕ → ℕ
  state : ℕ → ℕ
  extraBound : ℕ
  level0_pos : 0 < level0
  packet_pos : ∀ t, 0 < packet t
  extra_le : ∀ t, extra t ≤ extraBound
  coordinate : ∀ t, (state t : ℤ) =
    signedRunWord cert.seed (phasePrefix t) +
      (2 ^ totalValuation (phaseSuffix t ++ phasePrefix t) : ℤ) ^
        (level0 + t) * packet t
  legal : ∀ t, WordLegal (state t)
    (shadowMacroWord (phaseSuffix t ++ phasePrefix t)
      (level0 + t) (extra t))
  renewal : ∀ t, (2 ^ extra t : ℤ) * state (t + 1) =
    signedRunWord cert.seed (phasePrefix t) +
      (3 ^ (phaseSuffix t ++ phasePrefix t).length : ℤ) ^
        (level0 + t) * packet t

namespace CertifiedCyclePhaseShadowOrbit

theorem rotatedWord_nonempty (g : CertifiedCyclePhaseShadowOrbit) (t : ℕ) :
    g.phaseSuffix t ++ g.phasePrefix t ≠ [] := by
  intro hrot
  have hparts := List.append_eq_nil_iff.mp hrot
  have hv := g.cert.valid_of_check g.cert_ok
  apply hv.2.1
  rw [g.phase_split t, hparts.2, hparts.1]
  rfl

theorem rotated_fixed_affine (g : CertifiedCyclePhaseShadowOrbit) (t : ℕ) :
    (2 ^ totalValuation (g.phaseSuffix t ++ g.phasePrefix t) : ℤ) *
        signedRunWord g.cert.seed (g.phasePrefix t) =
      (3 ^ (g.phaseSuffix t ++ g.phasePrefix t).length : ℤ) *
        signedRunWord g.cert.seed (g.phasePrefix t) +
          affineOffset (g.phaseSuffix t ++ g.phasePrefix t) := by
  have hv := g.cert.valid_of_check g.cert_ok
  have hlegal : SignedWordLegal g.cert.seed
      (g.phasePrefix t ++ g.phaseSuffix t) := by
    rw [← g.phase_split t]
    exact hv.2.2.1
  have hclose : signedRunWord g.cert.seed
      (g.phasePrefix t ++ g.phaseSuffix t) = g.cert.seed := by
    rw [← g.phase_split t]
    exact hv.2.2.2
  exact signedCycle_rotate_affine_fixed hlegal hclose

/-- All low-level controller provenance fields are derived from one checked
base cycle. -/
def toBoundedPhaseShadowOrbit (g : CertifiedCyclePhaseShadowOrbit) :
    BoundedPhaseShadowOrbit where
  controller := fun t => signedRunWord g.cert.seed (g.phasePrefix t)
  word := fun t => g.phaseSuffix t ++ g.phasePrefix t
  level0 := g.level0
  extra := g.extra
  packet := g.packet
  state := g.state
  numerator := 3 ^ g.cert.word.length
  denominator := 2 ^ totalValuation g.cert.word
  extraBound := g.extraBound
  controller_neg := g.phase_neg
  word_nonempty := g.rotatedWord_nonempty
  level0_pos := g.level0_pos
  packet_pos := g.packet_pos
  denominator_pos := by positivity
  supercritical := g.cert.supercritical g.cert_ok
  common_shape := fun t => by
    constructor
    · congr 1
      rw [g.phase_split t]
      simp only [List.length_append]
      omega
    · congr 1
      rw [g.phase_split t, totalValuation_append, totalValuation_append]
      omega
  extra_le := g.extra_le
  fixed_affine := g.rotated_fixed_affine
  coordinate := g.coordinate
  legal := g.legal
  renewal := g.renewal

/-- A bounded infinite phase program over one checked negative controller is
a literal disproof certificate. -/
theorem not_conjecture (g : CertifiedCyclePhaseShadowOrbit) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toBoundedPhaseShadowOrbit.not_conjecture

end CertifiedCyclePhaseShadowOrbit

/-- The shadow endpoint can consume a checked signed controller directly. -/
theorem negativeShadow_endpoint_of_signedController
    {cert : SignedCycleCertificate} {h : ℤ} {x m e : ℕ}
    (hcert : cert.check = true) (hm : 0 < m)
    (hx : (x : ℤ) = cert.seed +
      (2 ^ totalValuation cert.word : ℤ) ^ m * h)
    (hlegal : WordLegal x (shadowMacroWord cert.word m e)) :
    (2 ^ e : ℤ) * runWord x (shadowMacroWord cert.word m e) =
      cert.seed + (3 ^ cert.word.length : ℤ) ^ m * h := by
  have hv := cert.valid_of_check hcert
  exact negativeShadow_endpoint hv.2.1 hm (cert.affine_fixed hcert) hx hlegal

end KontoroC

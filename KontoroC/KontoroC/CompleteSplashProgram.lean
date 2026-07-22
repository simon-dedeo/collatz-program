/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import KontoroC.CompleteSplash

/-!
# The deterministic complete-splash macro system

The parity-complete decoder is not merely existential.  This file exposes its
unique result as a canonical macro transition with a uniform start, word, and
endpoint.  It then states the exact infinite object still needed for a Collatz
counterexample: linked, outward iterations of these canonical transitions.

This interface is designed for compressed certificates.  A producer need only
give rail lengths and odd payloads together with linkage and growth; it never
chooses or trusts branch labels or hidden gate payloads.
-/

namespace KontoroC

namespace CompleteSplashOutcome

def start {r P : ℕ} : CompleteSplashOutcome r P → ℕ
  | .halt h => h.start
  | .even g _ _ => g.start
  | .odd g _ _ => g.start

def word {r P : ℕ} : CompleteSplashOutcome r P → List ℕ
  | .halt h => h.word
  | .even g _ _ => g.word
  | .odd g _ _ => g.word

def endpoint {r P : ℕ} : CompleteSplashOutcome r P → ℕ
  | .halt _ => 1
  | .even g _ _ => g.endpoint
  | .odd g _ _ => g.endpoint

/-- Every branch starts at the same sparse state determined by the public
decoder inputs. -/
theorem start_eq {r P : ℕ} (x : CompleteSplashOutcome r P) :
    x.start = minusOneState P (r + 1) := by
  cases x with
  | halt h => rfl
  | even g hr hP =>
      change minusOneState g.inputPayload (g.ampTicks + 1) =
        minusOneState P (r + 1)
      rw [hr, hP]
  | odd g hr hP =>
      change minusOneState g.inputPayload (g.ampTicks + 1) =
        minusOneState P (r + 1)
      rw [hr, hP]

/-- Uniform end-to-end semantic theorem for all three decoder outcomes. -/
theorem legal_and_endpoint {r P : ℕ} (x : CompleteSplashOutcome r P)
    (hPpos : 0 < P) :
    WordLegal x.start x.word ∧ runWord x.start x.word = x.endpoint := by
  cases x with
  | halt h => exact h.legal_and_endpoint hPpos
  | even g _ _ => exact g.legal_and_endpoint
  | odd g _ _ => exact g.legal_and_endpoint

theorem word_nonempty {r P : ℕ} (x : CompleteSplashOutcome r P) :
    x.word ≠ [] := by
  cases x with
  | halt h => simp [word, SplashHalt.word, mersenneMacroWord_eq]
  | even g _ _ => simp [word, EvenCleanupGate.word]
  | odd g _ _ => simp [word, OddCatcherGate.word]

/-- The canonical complete splash selected by a positive odd payload.  The
choice is harmless: the outcome type is a subsingleton. -/
noncomputable def decoded (r P : ℕ) (hPpos : 0 < P) (hPodd : Odd P) :
    CompleteSplashOutcome r P :=
  Classical.choice (exists_completeSplashOutcome r P hPpos hPodd)

theorem decoded_eq {r P : ℕ} (hPpos : 0 < P) (hPodd : Odd P)
    (x : CompleteSplashOutcome r P) : decoded r P hPpos hPodd = x :=
  Subsingleton.elim _ _

@[simp] theorem decoded_start {r P : ℕ} (hPpos : 0 < P)
    (hPodd : Odd P) :
    (decoded r P hPpos hPodd).start = minusOneState P (r + 1) :=
  start_eq _

end CompleteSplashOutcome

/-- An infinite program in the complete splash language.  Because the decoder
is total and unique, the only substantive obligations are linkage and outward
growth of the public `(railLength,payload)` sequence.  In particular, the
`outward` field automatically rules out the halting decoder branch. -/
structure InfiniteCompleteSplashProgram where
  railLength : ℕ → ℕ
  payload : ℕ → ℕ
  payload_pos : ∀ t, 0 < payload t
  payload_odd : ∀ t, Odd (payload t)
  start_large : 4 < (CompleteSplashOutcome.decoded
    (railLength 0) (payload 0) (payload_pos 0) (payload_odd 0)).start
  linked : ∀ t,
    (CompleteSplashOutcome.decoded
      (railLength t) (payload t) (payload_pos t) (payload_odd t)).endpoint =
    (CompleteSplashOutcome.decoded
      (railLength (t + 1)) (payload (t + 1))
      (payload_pos (t + 1)) (payload_odd (t + 1))).start
  outward : ∀ t,
    (CompleteSplashOutcome.decoded
      (railLength t) (payload t) (payload_pos t) (payload_odd t)).start <
    (CompleteSplashOutcome.decoded
      (railLength t) (payload t) (payload_pos t) (payload_odd t)).endpoint

namespace InfiniteCompleteSplashProgram

noncomputable def outcome (g : InfiniteCompleteSplashProgram) (t : ℕ) :
    CompleteSplashOutcome (g.railLength t) (g.payload t) :=
  CompleteSplashOutcome.decoded _ _ (g.payload_pos t) (g.payload_odd t)

/-- A linked outward complete-splash program is a literal Collatz glider. -/
noncomputable def toMacroGlider (g : InfiniteCompleteSplashProgram) :
    MacroGlider where
  state t := (g.outcome t).start
  word t := (g.outcome t).word
  start_large := g.start_large
  word_nonempty t := (g.outcome t).word_nonempty
  legal t := (g.outcome t).legal_and_endpoint (g.payload_pos t) |>.1
  transition t :=
    ((g.outcome t).legal_and_endpoint (g.payload_pos t)).2.trans (g.linked t)
  grows t := (g.outward t).trans_le (Nat.le_of_eq (g.linked t))

theorem not_conjecture (g : InfiniteCompleteSplashProgram) :
    ¬CleanLean.Collatz.Conjecture :=
  g.toMacroGlider.not_conjecture

end InfiniteCompleteSplashProgram

end KontoroC

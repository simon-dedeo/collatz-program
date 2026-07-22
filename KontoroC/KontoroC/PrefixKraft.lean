/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import Mathlib.InformationTheory.Coding.KraftMcMillan

/-!
# Prefix-free valuation codes and two exact Kraft measures

This file compiles positive valuation letters into self-delimiting uniform
codes.  The ordinary law uses a binary terminal alphabet.  The tilted law
decorates every letter with one of three terminals inside a four-symbol
alphabet.  Mathlib's Kraft--McMillan theorem then gives both nonuniform Kraft
bounds without a probabilistic axiom or an informal cylinder argument.
-/

namespace KontoroC
namespace PrefixKraft

def PrefixFree {α : Type*} (S : Set (List α)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u <+: v → u = v

theorem comparable_of_common_prefix {α : Type*} {u v z : List α}
    (hu : u <+: z) (hv : v <+: z) : u <+: v ∨ v <+: u := by
  rcases le_total u.length v.length with huv | hvu
  · left
    rw [List.prefix_iff_eq_take]
    rw [List.prefix_iff_eq_take] at hu hv
    calc
      u = z.take u.length := hu
      _ = (z.take v.length).take u.length := by
        rw [List.take_take, min_eq_left huv]
      _ = v.take u.length := by rw [← hv]
  · right
    rw [List.prefix_iff_eq_take]
    rw [List.prefix_iff_eq_take] at hu hv
    calc
      v = z.take v.length := hv
      _ = (z.take u.length).take v.length := by
        rw [List.take_take, min_eq_left hvu]
      _ = u.take v.length := by rw [← hu]

theorem uniquelyDecodable_of_prefixFree {α : Type*} {S : Set (List α)}
    (hpf : PrefixFree S) (hne : [] ∉ S) :
    InformationTheory.UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
      intro L₂ _ hL₂ hflat
      cases L₂ with
      | nil => rfl
      | cons v vs =>
          have hv : v ∈ S := hL₂ v (by simp)
          have : v = [] := by
            have happ : v ++ vs.flatten = [] := by simpa using hflat.symm
            simp at happ
            exact happ.1
          exact (hne (this ▸ hv)).elim
  | cons u us ih =>
      intro L₂ hL₁ hL₂ hflat
      cases L₂ with
      | nil =>
          have hu : u ∈ S := hL₁ u (by simp)
          have : u = [] := by
            have happ : u ++ us.flatten = [] := by simpa using hflat
            simp at happ
            exact happ.1
          exact (hne (this ▸ hu)).elim
      | cons v vs =>
          have hu : u ∈ S := hL₁ u (by simp)
          have hv : v ∈ S := hL₂ v (by simp)
          have hup : u <+: (u :: us).flatten := by
            simpa using List.prefix_append u us.flatten
          have hvp : v <+: (u :: us).flatten := by
            rw [hflat]
            simpa using List.prefix_append v vs.flatten
          have huv : u = v := by
            rcases comparable_of_common_prefix hup hvp with huv | hvu
            · exact hpf hu hv huv
            · exact (hpf hv hu hvu).symm
          subst v
          congr 1
          apply ih
          · intro w hw
            exact hL₁ w (by simp [hw])
          · intro w hw
            exact hL₂ w (by simp [hw])
          · apply List.append_cancel_left (as := u)
            simpa using hflat

namespace Terminal

def encLetter {β : Type*} (x : ℕ × β) : List (Option β) :=
  List.replicate x.1 none ++ [some x.2]

def enc {β : Type*} (w : List (ℕ × β)) : List (Option β) :=
  w.flatMap encLetter

def decAux {β : Type*} : ℕ → List (Option β) → List (ℕ × β)
  | _, [] => []
  | n, none :: xs => decAux (n + 1) xs
  | n, some b :: xs => (n, b) :: decAux 0 xs

def dec {β : Type*} : List (Option β) → List (ℕ × β) := decAux 0

lemma decAux_replicate_none_some {β : Type*} (c n : ℕ) (b : β)
    (z : List (Option β)) :
    decAux c (List.replicate n none ++ (some b :: z)) =
      (c + n, b) :: decAux 0 z := by
  induction n generalizing c with
  | zero => simp [decAux]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, decAux]
      rw [ih]
      congr 2
      omega

lemma decAux_enc_append {β : Type*} (c : ℕ) (w : List (ℕ × β))
    (z : List (Option β)) :
    decAux c (enc w ++ z) =
      match w with
      | [] => decAux c z
      | x :: xs => (c + x.1, x.2) :: decAux 0 (enc xs ++ z) := by
  cases w with
  | nil => simp [enc]
  | cons x xs =>
      simp only [enc, List.flatMap_cons, List.append_assoc, encLetter,
        List.singleton_append]
      exact decAux_replicate_none_some c x.1 x.2 (enc xs ++ z)

lemma dec_enc {β : Type*} (w : List (ℕ × β)) : dec (enc w) = w := by
  induction w with
  | nil => simp [dec, enc, decAux]
  | cons x xs ih =>
      simp only [dec, enc, List.flatMap_cons, encLetter, List.append_assoc,
        List.singleton_append]
      calc
        decAux 0 (List.replicate x.1 none ++
            (some x.2 :: List.flatMap encLetter xs)) =
            (x.1, x.2) :: decAux 0 (List.flatMap encLetter xs) := by
              simpa using decAux_replicate_none_some 0 x.1 x.2
                (List.flatMap encLetter xs)
        _ = x :: xs := by simpa [dec, enc] using congrArg (List.cons x) ih

lemma dec_enc_append {β : Type*} (w : List (ℕ × β)) (z : List (Option β)) :
    dec (enc w ++ z) = w ++ dec z := by
  induction w with
  | nil => simp [enc]
  | cons x xs ih =>
      simp only [dec, enc, List.flatMap_cons, encLetter, List.append_assoc,
        List.singleton_append]
      calc
        decAux 0 (List.replicate x.1 none ++
            (some x.2 :: List.flatMap encLetter xs ++ z)) =
            (x.1, x.2) :: decAux 0 (List.flatMap encLetter xs ++ z) := by
              simpa using decAux_replicate_none_some 0 x.1 x.2
                (List.flatMap encLetter xs ++ z)
        _ = x :: xs ++ decAux 0 z := by
          simpa [dec, enc] using congrArg (List.cons x) ih

lemma enc_prefix_reflect {β : Type*} {u v : List (ℕ × β)}
    (h : enc u <+: enc v) : u <+: v := by
  rcases h with ⟨z, hz⟩
  refine ⟨dec z, ?_⟩
  have hdec := congrArg dec hz
  rw [dec_enc_append, dec_enc] at hdec
  exact hdec

lemma enc_length {β : Type*} (w : List (ℕ × β)) :
    (enc w).length = (w.map fun x => x.1 + 1).sum := by
  induction w with
  | nil => simp [enc]
  | cons x xs ih =>
      simp [enc, encLetter, ih]
      omega

end Terminal

open scoped BigOperators

def lowerP (w : List ℕ) : List (ℕ × Unit) :=
  w.map fun k => (k - 1, ())

def raiseP (w : List (ℕ × Unit)) : List ℕ :=
  w.map fun x => x.1 + 1

lemma raiseP_lowerP {w : List ℕ} (hpos : ∀ k ∈ w, 0 < k) :
    raiseP (lowerP w) = w := by
  induction w with
  | nil => simp [raiseP, lowerP]
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hks : ∀ j ∈ ks, 0 < j := by
        intro j hj
        exact hpos j (by simp [hj])
      change (k - 1 + 1) :: raiseP (lowerP ks) = k :: ks
      rw [ih hks]
      congr
      omega

def pEnc (w : List ℕ) : List (Option Unit) := Terminal.enc (lowerP w)

lemma pEnc_prefix_reflect {u v : List ℕ}
    (hupos : ∀ k ∈ u, 0 < k) (hvpos : ∀ k ∈ v, 0 < k)
    (h : pEnc u <+: pEnc v) : u <+: v := by
  have hlower : lowerP u <+: lowerP v := Terminal.enc_prefix_reflect h
  have hu := raiseP_lowerP hupos
  have hv := raiseP_lowerP hvpos
  have hmapped := hlower.map (fun x : ℕ × Unit => x.1 + 1)
  change raiseP (lowerP u) <+: raiseP (lowerP v) at hmapped
  simpa only [hu, hv] using hmapped

lemma pEnc_injective_on_positive {u v : List ℕ}
    (hupos : ∀ k ∈ u, 0 < k) (hvpos : ∀ k ∈ v, 0 < k)
    (h : pEnc u = pEnc v) : u = v := by
  have huv : u <+: v := pEnc_prefix_reflect hupos hvpos (h ▸ List.prefix_refl _)
  have hlen : u.length = v.length := by
    have he := congrArg List.length h
    -- Encoding equality alone gives equal encoded length; use both prefix directions instead.
    have hvu : v <+: u := pEnc_prefix_reflect hvpos hupos (h ▸ List.prefix_refl _)
    exact Nat.le_antisymm huv.length_le hvu.length_le
  rw [List.prefix_iff_eq_take] at huv
  simpa [hlen] using huv

lemma pEnc_length {w : List ℕ} (hpos : ∀ k ∈ w, 0 < k) :
    (pEnc w).length = w.sum := by
  rw [pEnc, Terminal.enc_length]
  induction w with
  | nil => simp [lowerP]
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have hks : ∀ j ∈ ks, 0 < j := by
        intro j hj
        exact hpos j (by simp [hj])
      simp only [lowerP, List.map_cons, List.sum_cons]
      change k - 1 + 1 + ((lowerP ks).map (fun x => x.1 + 1)).sum =
        k + ks.sum
      rw [ih hks]
      omega

theorem pKraft_finite (C : Finset (List ℕ))
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixFree (C : Set (List ℕ))) :
    ∑ w ∈ C, (1 / 2 : ℝ) ^ w.sum ≤ 1 := by
  classical
  let E : Finset (List (Option Unit)) := C.image pEnc
  have hinj : Set.InjOn pEnc (C : Set (List ℕ)) := by
    intro u hu v hv huv
    exact pEnc_injective_on_positive (hpos u hu) (hpos v hv) huv
  have hEpf : PrefixFree (E : Set (List (Option Unit))) := by
    intro eu heu ev hev hpref
    rcases Finset.mem_image.mp heu with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hev with ⟨v, hv, rfl⟩
    have huv : u <+: v := pEnc_prefix_reflect (hpos u hu) (hpos v hv) hpref
    exact congrArg pEnc (hpf hu hv huv)
  have hEne : [] ∉ (E : Set (List (Option Unit))) := by
    intro hempty
    rcases Finset.mem_image.mp hempty with ⟨w, hw, henc⟩
    cases w with
    | nil => exact hne [] hw rfl
    | cons k ks =>
        simp [pEnc, lowerP, Terminal.enc, Terminal.encLetter] at henc
  have hk := InformationTheory.kraft_mcmillan_inequality
    (uniquelyDecodable_of_prefixFree hEpf hEne)
  have hsum : (∑ e ∈ E, (1 / 2 : ℝ) ^ e.length) =
      ∑ w ∈ C, (1 / 2 : ℝ) ^ w.sum := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    rw [pEnc_length (hpos w hw)]
  rw [← hsum]
  simpa [E] using hk

abbrev Decorations (C : Finset (List ℕ)) :=
  (w : C) × (Fin w.val.length → Fin 3)

def decoratedWord {C : Finset (List ℕ)} (d : Decorations C) :
    List (ℕ × Fin 3) :=
  List.ofFn fun i => (d.1.val.get i - 1, d.2 i)

def baseWord {C : Finset (List ℕ)} (d : Decorations C) : List ℕ :=
  (decoratedWord d).map fun x => x.1 + 1

lemma baseWord_eq {C : Finset (List ℕ)} (d : Decorations C)
    (hpos : ∀ k ∈ d.1.val, 0 < k) : baseWord d = d.1.val := by
  rw [← List.ofFn_get d.1.val]
  simp only [baseWord, decoratedWord, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, Prod.fst]
  have hk : 0 < d.1.val.get i := hpos _ (List.get_mem _ _)
  omega

def qEnc {C : Finset (List ℕ)} (d : Decorations C) : List (Option (Fin 3)) :=
  Terminal.enc (decoratedWord d)

lemma qEnc_length {C : Finset (List ℕ)} (d : Decorations C)
    (hpos : ∀ k ∈ d.1.val, 0 < k) :
    (qEnc d).length = d.1.val.sum := by
  rw [qEnc, Terminal.enc_length]
  change (baseWord d).sum = d.1.val.sum
  rw [baseWord_eq d hpos]

lemma qEnc_injective {C : Finset (List ℕ)}
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k) : Function.Injective (@qEnc C) := by
  intro d e hde
  have hword : decoratedWord d = decoratedWord e := by
    rw [← Terminal.dec_enc (decoratedWord d), ← Terminal.dec_enc (decoratedWord e)]
    exact congrArg Terminal.dec hde
  have hbase : d.1.val = e.1.val := by
    rw [← baseWord_eq d (hpos d.1.val d.1.prop),
      ← baseWord_eq e (hpos e.1.val e.1.prop)]
    exact congrArg (List.map fun x : ℕ × Fin 3 => x.1 + 1) hword
  cases d with
  | mk dw dc =>
    cases e with
    | mk ew ec =>
      simp only at hbase
      have hwsub : dw = ew := Subtype.ext hbase
      subst ew
      simp only [decoratedWord] at hword
      have hfn := List.ofFn_injective hword
      have hc : dc = ec := by
        funext i
        have hi := congrArg (fun f => (f i).2) hfn
        simpa using hi
      subst ec
      rfl

lemma qEnc_prefix_reflect_base {C : Finset (List ℕ)} {d e : Decorations C}
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (h : qEnc d <+: qEnc e) : d.1.val <+: e.1.val := by
  have hdecor : decoratedWord d <+: decoratedWord e :=
    Terminal.enc_prefix_reflect h
  have hmapped := hdecor.map (fun x : ℕ × Fin 3 => x.1 + 1)
  change baseWord d <+: baseWord e at hmapped
  simpa only [baseWord_eq d (hpos d.1.val d.1.prop),
    baseWord_eq e (hpos e.1.val e.1.prop)] using hmapped

theorem qKraft_finite (C : Finset (List ℕ))
    (hpos : ∀ w ∈ C, ∀ k ∈ w, 0 < k)
    (hne : ∀ w ∈ C, w ≠ [])
    (hpf : PrefixFree (C : Set (List ℕ))) :
    ∑ w ∈ C, (3 : ℝ) ^ w.length / (4 : ℝ) ^ w.sum ≤ 1 := by
  classical
  let E : Finset (List (Option (Fin 3))) :=
    Finset.univ.image (@qEnc C)
  have hqin : Function.Injective (@qEnc C) := qEnc_injective hpos
  have hEpf : PrefixFree (E : Set (List (Option (Fin 3)))) := by
    intro ed hed ee hee hpref
    rcases Finset.mem_image.mp hed with ⟨d, _, rfl⟩
    rcases Finset.mem_image.mp hee with ⟨e, _, rfl⟩
    have hbase : d.1.val = e.1.val := hpf d.1.prop e.1.prop
      (qEnc_prefix_reflect_base hpos hpref)
    have hdecor : decoratedWord d <+: decoratedWord e :=
      Terminal.enc_prefix_reflect hpref
    have hlen : (decoratedWord d).length = (decoratedWord e).length := by
      simp [decoratedWord, hbase]
    rw [List.prefix_iff_eq_take] at hdecor
    have hde : decoratedWord d = decoratedWord e := by
      simpa [hlen] using hdecor
    exact congrArg Terminal.enc hde
  have hEne : [] ∉ (E : Set (List (Option (Fin 3)))) := by
    intro hempty
    rcases Finset.mem_image.mp hempty with ⟨d, _, henc⟩
    have hsum : d.1.val.sum = 0 := by
      have := congrArg List.length henc
      rw [qEnc_length d (hpos d.1.val d.1.prop)] at this
      simpa using this
    obtain ⟨k, ks, hw⟩ := List.exists_cons_of_ne_nil (hne d.1.val d.1.prop)
    have hk : 0 < k := hpos d.1.val d.1.prop k (by simp [hw])
    rw [hw] at hsum
    simp only [List.sum_cons] at hsum
    omega
  have hk := InformationTheory.kraft_mcmillan_inequality
    (uniquelyDecodable_of_prefixFree hEpf hEne)
  have himage : (∑ e ∈ E, (1 / 4 : ℝ) ^ e.length) =
      ∑ d : Decorations C, (1 / 4 : ℝ) ^ (qEnc d).length := by
    rw [Finset.sum_image]
    exact Set.injOn_of_injective hqin
  have hdecorSum : (∑ d : Decorations C, (1 / 4 : ℝ) ^ (qEnc d).length) =
      ∑ w ∈ C, (3 : ℝ) ^ w.length / (4 : ℝ) ^ w.sum := by
    rw [show (∑ d : Decorations C, (1 / 4 : ℝ) ^ (qEnc d).length) =
        ∑ w : C, ∑ c : Fin w.val.length → Fin 3,
          (1 / 4 : ℝ) ^ (qEnc ⟨w, c⟩).length by
      exact Fintype.sum_sigma'
        (fun w c => (1 / 4 : ℝ) ^ (qEnc ⟨w, c⟩).length)]
    rw [← Finset.sum_coe_sort C]
    apply Fintype.sum_congr
    intro w
    have hlen (c : Fin w.val.length → Fin 3) :
        (qEnc ⟨w, c⟩).length = w.val.sum :=
      qEnc_length ⟨w, c⟩ (hpos w.val w.prop)
    simp_rw [hlen]
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    have hcard : (Finset.univ : Finset (Fin w.val.length → Fin 3)).card =
        3 ^ w.val.length := by simp
    rw [hcard]
    push_cast
    field_simp
    rw [one_div, inv_pow]
    exact inv_mul_cancel₀ (by positivity)
  rw [← hdecorSum, ← himage]
  simpa [E] using hk

end PrefixKraft
end KontoroC

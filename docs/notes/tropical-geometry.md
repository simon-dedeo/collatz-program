# Tropical geometry proper vs. the KL adversarial operator: a scouting verdict

2026-07-20. Status: **theory-scout with one verified computation, one new named tool,
and a mostly-negative honest verdict.** Companion to `kl-limit-object.md` [LIM],
`adversarial-operator.md` [ADV], `tropical-iwasawa.md` [TI]. Object: the level-k KL
operator F_λ^{(k)} on Y=2+3ℤ₃ (base ×4 = 3-adic odometer), thresholds λ_k↑λ∞∈(1.87,2],
dichotomy λ∞=2 vs <2. α:=log₂3, β:=log₂λ.

**Ledger.** PROVED/VERIFIED here: §2 (the special values β=1,2 are Archimedean, not
tropical — numeric, `tropical_checks.py`). REPORTED (external, cross-checked): §3 tool
map. CALIBRATED-NEGATIVE (with gpt-5.6-sol as adversary, its overclaim-flags honored):
§3 no tropical-positivity obstruction, §5 box-ball non-result stated as *no evidence*,
not *proof*. LEAD: §3.3 ambitropical geometry (Gaubert 2021), a named tool not yet used.

## 0. Verdict

Tropical geometry **proper** adds **little to the central question and one concrete
lead**. The reason is structural and, I think, decisive: **the arithmetic of Collatz
lives in the Archimedean balancing of the KL characteristic, not in its tropical
skeleton.** The genuinely tropical layer of the object is only the *adversary* (the min),
which the program already handles under other names (lower spectral radius, mean-payoff,
topical maps). Tropicalizing the *whole* operator destroys exactly what matters (§2).
Box-ball/ultradiscrete integrability is the wrong shape for Collatz (§5).

## 1. The object is HALF-dequantized, not tropical

Write B:=log₂∘F∘2^(·) (the topical/Shapley form, [ADV] Prop 1.3). Its two nonlinearities
sit at *opposite* ends of the Maslov dequantization scale:
- **branching** (two predecessor families add): a **log-sum-exp** = Maslov-deformed sum
  ⊕_h at inverse-temperature h≈1/ln2 = O(1). This is the *quantized* (Archimedean) corner.
- **adversary** (lost 3-adic digit): a genuine **min** = the h→0 (tropical) corner.

So B is not a point on a one-parameter dequantization family heading to tropical; it is a
*fixed hybrid* — quantized for the counter, tropical for the digit player. "Take the
tropical limit" is ambiguous here (gpt caveat, honored): sending the branching's h→0 too
gives a *different* operator, and that operator is arithmetically blind (§2).

## 2. The special values β=1,2 are Archimedean — invisible to tropicalization [VERIFIED]

Annealed characteristic s(β)=4^{−β}+⅓(4/3)^{−β}+⅓(2/3)^{−β}, with s(1)=s(2)=1 *exactly*
(because 2^α=3). Written in 2-powers the three monomials have log₂-exponents
e₁=−2β, e₂=−α−(2−α)β, e₃=(α−1)β−α. Two facts (`tropical_checks.py`):

- At β=1 the term **magnitudes** are (¼, ¼, ½), summing to 1: a genuine **three-term
  Archimedean balance**. Tropically only e₃=½ dominates (e₁=e₂=¼ tie *below* it), so the
  max-plus "value" is ½≠1.
- The tropical equation max(e₁,e₂,e₃)=0 has corners at **β=0 and β=α/(α−1)=2.7095** —
  **not** at 1,2.

**Conclusion.** Tropicalizing the KL characteristic sends its two arithmetically special
roots to two arithmetically meaningless ones. The identity that pins λ=2 (density
exponent 1) is a non-degenerate sum-balance of *three* comparable terms — precisely the
configuration a tropical (two-term-domination) skeleton cannot resolve. This is the sharp
reason tropical geometry proper cannot, from the tropicalized object alone, recover λ=2.
(Not a claim that no *enriched/signed* tropical data could encode it — only that the naive
tropical curve does not.)

## 3. Where tropical geometry IS the right frame: the adversary (and its limits)

3.1 **Named tools that genuinely apply** (verified external):
- Adversary value at fixed k = a **min over policies of Archimedean Perron roots** =
  Protasov *lower spectral radius* of a product family ([ADV] Prop 1.3(ii)). Its
  min-plus/mean-payoff character is real; **tropical convexity ⟺ mean-payoff games**
  (Akian–Gaubert–Guterman, IJAC 2012). *Caveat (gpt, honored):* this is essentially a
  **one-player** (robust-control) mean-payoff problem — the counter is a log-sum-exp, not
  a genuine max — so "two-player game value" is imprecise; it is min-side optimization.
- The cone-spectral-radius / Collatz–Wielandt machinery is **Akian–Gaubert–Nussbaum**
  (nonlinear Collatz–Wielandt). *Curiosity [verified]:* the "Collatz" of Collatz–Wielandt
  is **Lothar Collatz**, the same man who posed 3n+1 — the min-plus Collatz–Wielandt
  theory applied to the Collatz conjecture closes a genuine nominal loop.
- **Akian–Bapat–Gaubert** tropical eigenvalue bounds / log-majorization (Handbook of
  Linear Algebra, "Max-plus algebras"; arXiv:1309.7319, 1908.08234) are the natural home
  for "tropical value ≤ Archimedean value" — morally the direction of the proved
  λ∞≤2. *Honest:* the actual proof ([LIM] Prop 1.4) is the elementary min≤average, not a
  log-majorization invocation; I do not dress it up as more.

3.2 **The dichotomy as tropical tightness.** λ∞=2 ⟺ the tropical relaxation becomes
asymptotically tight along the tower ⟺ δ_k→0, where δ_k is the **eigenvector-weighted**
mean fiber oscillation ([LIM] Thm 3.2 — an *exact* identity, so this equivalence is
proved *here*, unlike the generic case gpt rightly warns is not automatic; tightness is
measured against the actual extremal eigenvector, i.e. exactly the "calibrated states"
where spectral tightness lives).

3.3 **Is there a tropical POSITIVITY / obstruction forcing λ∞=2 or λ∞<2?**
**No — and this is itself the finding.** There is no tropical-positivity theorem that
forces the min-plus tower value up to its Archimedean ceiling, nor one that forces a gap.
Tropical cycle certificates prove finite-level inequalities; tower-limit tightness is an
Archimedean-uniformity question (persistence of δ_k), which tropical geometry does not
see (§2). This *explains* why the dichotomy is hard: it is an Archimedean gap wearing a
tropical mask. **LEAD (new, unused):** the fixed-point set of the Shapley operator B is,
by **Gaubert's ambitropical geometry** (arXiv:2108.07748), a *hyperconvex sup-norm
nonexpansive retract* carrying a polyhedral complex whose cells are adversary policies.
The program has used eigenvector *existence* (Gaubert–Gunawardena) but not this *geometry
of the eigenspace*. Whether its cell structure constrains the tower limit is open;
my honest guess is modest payoff (it is finite-k structure), but it is the one tropical
tool not yet tried.

## 4. Newton polygon of (2,3)

The multipliers {4,4/3,2/3}=2^ℤ3^ℤ give a Newton polygon = the thin triangle with
vertices (2,0),(2,−1),(1,−1) in the (v₂,v₃)-grading ([TI] §1.3), and the dynamics forces
evaluation along the **irrational** slope-α ray 3^{−β}=2^{−αβ}. So a (2,3)-Newton-polygon
*exists* and encodes the multiplier lattice — but its tropical curve does **not** encode
the special values (§2): the triangle is nearly degenerate and the roots β=1,2 are
Archimedean. The Newton polygon carries the *kinematics* of (2,3); the arithmetic is off
the tropical skeleton.

## 5. Box-ball / ultradiscrete integrable systems — the wrong shape

Superficially the arctic string-rewriting picture (`arctic-prethink-gpt.md`: h/s/t
carries sweeping over 1^n, t inserting two 1s per 1 = the ×3) resembles a **box-ball
system** (BBS = ultradiscrete KdV; Takahashi–Satsuma; Tokihiro et al.; Kuniba–Okado
review arXiv:1109.5349; tropical spectral curves for periodic BBS, Inoue–Takenawa
arXiv:0704.2471). But the defining property of BBS/uKdV is **integrability**: solitons,
infinitely many conserved quantities, a **tropical spectral curve + tropical Jacobian**
that *linearizes* the flow. Collatz is the opposite kind of system:

- The ×3 branch is number-**multiplying**, not number-**conserving**; the
  Hattori–Takesue (1991) number-conserving-CA criterion is *about the case Collatz is
  not in*, and (gpt, honored) does not directly apply — Collatz is not a
  translation-invariant finite-alphabet local CA in the first place.
- No soliton decomposition, tropical spectral curve, or Jacobian linearization is known.

**Honest non-result:** there is **no evidence** of integrable/soliton structure and every
structural expectation (the conjectured mixing of orbits) points against it — but this is
*not a proof of absence*. The single genuine crossover already exploited is the **max-plus
cyclicity theorem** (ultimate arithmetic-periodicity of powers of one max-plus matrix),
which is the linear-algebra layer under both BBS and the arctic termination argument
(`arctic-prethink-gpt.md` §2.1) — and it is tropical *algebra*, not geometry.

## 6. Net

Tropical geometry proper: **(i)** cannot see λ=2 (§2, the decisive negative); **(ii)**
correctly names the adversary side and, via §3.2, restates the dichotomy as tropical
tightness — clarifying but not resolving, and it supplies **no** positivity forcing either
way (§3.3); **(iii)** offers one untried tool, ambitropical geometry of the eigenspace
(§3.3 LEAD); **(iv)** box-ball integrability is the wrong shape (§5). The program's
instinct — treat the object as min-plus *linear algebra / mean-payoff*, keep the counter
Archimedean — was already the right level of tropicalization. Genuine tropical *geometry*
adds a vocabulary and one lead, not a new obstruction.

**Refs (verified):** Akian–Gaubert–Guterman, *Tropical polyhedra are equivalent to mean
payoff games*, IJAC 22 (2012). Akian–Bapat–Gaubert, *Max-plus algebras* (Handbook of
Linear Algebra); *Tropical bounds for eigenvalues*, arXiv:1309.7319. Gaubert et al.,
*Ambitropical geometry, hyperconvexity and zero-sum games*, arXiv:2108.07748.
Kuniba–Okado, arXiv:1109.5349; Inoue–Takenawa, arXiv:0704.2471; Hattori–Takesue,
Physica D 49 (1991). Repro: `experiments/kl/tropical_checks.py` (§2 arithmetic).

> **SUPERSEDED AUDIT (2026-07-21).** This file preserves an earlier external
> review as historical evidence, but its end-to-end verdict is no longer
> current. Exact successor checks found three defects in the published
> advanced-elimination construction (`TERMINATION_AUDIT.md`) and the exact
> `k=2` counterexample `φ^7_2(1)=3≠2=φ^{14}_2(0)` to printed equation (2.1)
> (`verify_equation_2_1_obstruction.py`). The finite LP certificates remain
> exact. The equality error has an audited one-sided repair that preserves the
> exponent transfer, but the corrected retarded witness and actual
> predecessor-count instantiation are not yet both kernel-checked. Read
> `RESULT.md` and `THEOREM.md` for current status.

VERDICT: CONFIRMED (historical; superseded as an end-to-end verdict)

1) THEOREM FIDELITY
- Match to paper:
  - Objects and definitions match §2 exactly: T(n), πa, π∗a, φk m(y) with the “a not in a cycle” qualifier, and properties (P1)–(P3) (lines 100–135 in the text extract).
  - Proposition 2.1 (Ik) is correctly transcribed: the three cases (D1)–(D3) with the shifts y−2 and y+α−2 (retarded) and y+α−1 (advanced), and the minimization (2.6) over three lifts (lines 136–158, 160–174).
  - The LP family L^NT_k(λ), constraints (L0)–(L4), and inequality directions are correctly stated (lines 180–224). The superscripts “3k” in the pdftotext artifacts for (2.12)–(2.14) are indeed 3^(k−1), as made explicit in (2.6), (2.15), and in §4 (lines 777–784).
  - Theorem 2.2 is restated faithfully: hypothesis “1 ≤ λ ≤ 2” and conclusion φk m(y) ≥ Δ1 c^m_k λ^y with Δ1 = 1/(4 max c^m_k) (lines 263–275, 932–946). The role of ν ≤ 2 and λ ≤ 2 in recovering Δ1 is correctly described.
  - Hidden hypotheses: none omitted. The dependence on k is for all k ≥ 2; positivity and monotonicity of Φk are used in §3–§5 as in the paper; the “a not in a cycle” clause is part of the definition of φk m and is handled explicitly downstream.
- Minor wording nit:
  - THEOREM.md at one point says “(D1) and (D3) contain advanced terms”; only (D3) has an advanced term (α−1 > 0) while (D1) has a retarded shift (α−2 < 0). This is a harmless phrasing slip and does not affect any construction or proof (see (2.3)–(2.5), lines 146–158).

2) AUXILIARY ELIMINATION
- The paper’s own reduction to set auxiliaries to their maxima c̄k−1 m := min of the three lifts (2.15) is correctly used (lines 236–253). With (L4) these values are feasible and maximize the RHS of (L1), (L3), hence only weaken those inequalities. Therefore feasibility is equivalent to the “one-line” constraints on principal variables:
  - c^m ≥ 1 (L0 lower bound),
  - and for each m ∈ [3^k], the single inequality
    c^m ≤ λ^(−2) c^{4m mod 3^k} + [if m ≡ 2 (mod 9)] λ^(α−2) min over the 3 lifts of (4m−2)/3;
    [if m ≡ 8 (mod 9)] λ^(α−1) min over the 3 lifts of (2m−1)/3;
    and no extra term if m ≡ 5 (mod 9).
  - This is exactly what THEOREM.md states, matching (2.9)–(2.11) with (2.6). The “min-over-three-lifts” and which residue classes get which weight are correct.

3) TIGHTENING DIRECTION AND EXACT CHECKS
- Logical direction: Replacing λ^(α−2) and λ^(α−1) by any certified lower bounds W2 ≤ λ^(α−2), W8 ≤ λ^(α−1) tightens the ≤-side constraints since these coefficients multiply nonnegative terms on the RHS. Exact feasibility of the tightened system implies feasibility of the true LP at the same λ. This is airtight.
- Integer certification:
  - The code enforces 2^P < 3^Q (P/Q = 50508/31867 < log₂3 = α), which is equivalent to P/Q < α.
  - It verifies W2 ≤ λ^(P/Q−2) and W8 ≤ λ^(P/Q−1) via the integer inequalities
    B2^Q A^(2Q−P) ≤ SC_W^Q SC_L^(2Q−P) and
    B8^Q SC_L^(P−Q) ≤ A^(P−Q) SC_W^Q,
    which are the correct cross-multiplied forms of W2 ≤ (A/SC_L)^(P/Q−2) and W8 ≤ (A/SC_L)^(P/Q−1).
  - λ^(−2) is handled exactly by clearing denominators: the verified inequality is
    C[i]·A^2·SC_W ≤ C[i4m]·SC_L^2·SC_W + B·A^2·min₃(C),
    which is algebraically equivalent to c ≤ λ^(−2) c(4m) + W·min₃ c.
- No off-by-one or sign inversions are present in exponent handling. The “seed then decrement” logic only affects speed; the final acceptance uses exact integer comparisons.

4) CONCLUSION TRANSFER TO πa(x) (SUPERSEDED; retained verbatim below)
- [SUPERSEDED CLAIM] Theorem 2.2 gives φk m(y) ≥ Δ1 c^m_k λ^y for all y ≥ 0. Since by definition φk m(y) = inf over a ≡ m (mod 3^k), a not in a cycle, of π∗a(2^y a), one has for any fixed such a: π∗a(2^y a) ≥ φk m(y), hence πa(x) ≥ Δ1 c^m_k (x/a)^γ with γ = log₂ λ, for all x ≥ a. Equation (2.1) transfers m ≡ 1 (mod 3) to m′ ≡ 2 (mod 3) at the cost of a factor λ^(−1) in Δ; and for cycle elements (1, 2) one uses π1 ≥ π8, π2 ≥ π8. This is exactly the implicit step behind Theorem 6.1. Therefore “for every fixed γ < log₂(λ_cert)” one can absorb constants and state πa(x) ≥ x^γ for all sufficiently large x ≥ x0(a), for each a ≢ 0 (mod 3), as in the claim.

5) ANY OTHER GAP
- Normalizations and domains:
  - πa, π∗a are defined on real x and are monotone in x, so evaluating at x = 2^y a with real y is legitimate.
  - The ν ≤ 2 bound used to get Δ1 is established in §3 (all right-side time shifts are ≥ −2; line 346) and used in the proof of Theorem 2.2 (lines 932–946).
  - k is unrestricted (k ≥ 2) in all theorems; the paper’s computations up to k = 11 are not a hypothesis.
- Implementation correspondence:
  - The solver/certifier’s index maps for 4m mod 3^k and for the three lifts of (4m−2)/3 and (2m−1)/3 mod 3^(k−1) match the paper’s formulas.
  - The direction of all LP inequalities (principal variable on the “small” side) matches (2.9)–(2.14).

No substantive contradictions with the paper were found. The only minor imprecision is the offhand remark in THEOREM.md implying (D1) has an advanced term; (D1) is purely retarded, while (D3) has the advanced term. This has no effect on the logic or certification.

Summary: The restatement of Theorem 2.2 and the LP family is faithful; the auxiliary-variable elimination is exactly as in the paper; the coefficient tightening via certified lower bounds is logically correct and verified by exact integer arithmetic; and the transfer to πa(x) is as in the paper’s §6. The claimed certified λ values at k = 12, 13, 14 legitimately yield exponents strictly larger than the published 0.84 bound.

# HISTORICAL / OBSOLETE ARCTIC PRE-THINK

> **Do not use this file as a result or proof source.** It analyzes the wrong
> blank-free rewrite system, overclaims context closure, and uses a false
> single-eventual-slope assertion for reducible max-plus matrices. The current
> calibrated statement, counterexamples, exact system, and provisional
> weighted-walk repair are in `docs/notes/arctic-nogo.md`.

Short answer up front (retracted): yes, the “max-plus/cyclicity” route can be made to work. One can pin the growth slope for the 1-blocks to zero using only weak compatibility of Z’s rules, and then force an unbounded strict drop along suitably pumped derivation families if any single rule is made strict—contradicting the boundedness implied by slope 0 and ultimate periodicity. The reducible case and the “strict-only-for-removed-rule” regime can be handled uniformly, provided you adopt the standard Koprowski–Waldmann arctic side-conditions that make strictness context-closed (so a fixed integer gap δ ≥ 1 propagates through all contexts).

Details below.

0) Sanity check of Z and the correction I assume
The extracted second rule is garbled. With the intended semantics “h sweeps right; s and t sweep left; s leaves the 1-count unchanged; t inserts two 1’s per 1 it crosses (which implements (3n+1)/2 on odd input)”, the standard 7-rule SRS is:

- h11 -> 1h
- 1h -> 1s          [right-to-left handoff at the right end]
- 1s -> s1          [s moves left]
- s -> h            [left-to-right handoff at the left end]
- h1 -> t11         [odd case trigger]
- 1t -> t111        [t moves left and leaves two extra 1’s per move]
- t -> h            [left-to-right handoff at the left end]

These 7 rules do implement, on states of the form h 1^n, the macro-step C(n) = n/2 if n is even, and C(n) = (3n+1)/2 if n is odd. In particular:
- odd n: after floor(n/2) uses of h11 -> 1h, one use of h1 -> t11, then floor(n/2) uses of 1t -> t111, finally t -> h; net effect h 1^n =>* h 1^{(3n+1)/2}.
- even n: after n/2 uses of h11 -> 1h, one use of 1h -> 1s, then (n/2−1) uses of 1s -> s1, and s -> h; net effect h 1^n =>* h 1^{n/2}.

I proceed with this corrected rule set.

1) Assessment of the strategy

- Core idea: Replace Berstel’s N-rational series structure by the max-plus cyclicity theorem: for any fixed letter 1 interpreted by a max-plus matrix M := M_1, the scalar series n ↦ u^T M^n v is ultimately linear with an arithmetic-periodic offset, i.e., u^T M^{n+p} v = u^T M^n v + p·λ for n large on each residue class, where λ is a maximum cycle mean determined by the support of u, v and the critical graph of M. For reducible M one still has that u^T M^n v is a maximum of finitely many ultimately arithmetic-periodic affine functions; in particular, it has an eventual slope λ(u,v) and an eventually periodic intercept.
- Weak point (a): reducibility/multi-slope. We avoid needing a global unique slope by working with a single scalar function F(n) = [h 1^n] and deriving two independent infinite families of inequalities on F: F(n+2) ≥ F(n+1) and F(8n+1) ≥ F(9n+2). Each of these alone restricts the eventual slope λ_F; together they force λ_F = 0. This argument only uses that F is ultimately arithmetic-periodic-affine. It does not rely on irreducibility nor on comparing different contexts’ slopes.
- Weak point (b): “strict on removed rule only.” We handle this by choosing, for each of the 7 candidate rules, a derivation family Start(m) =>* End(m) in which that particular rule is used Θ(m) (or Θ(log m), but unbounded) times while the endpoints are of the special form h 1^{L(m)}. With λ_F = 0, |F(Start(m)) − F(End(m))| is bounded (eventually periodic), but strictness forces an unbounded accumulated decrease—contradiction. We give concrete families and exact use-counts below.
- Weak point (c): dependency-pair variant. For SRS Z, the DP framework essentially reproduces the same constraints because there is no nested structure–each rule’s DP reflects moving the head marker across 1’s. The arguments below are phrased at the level of the original rules and their concatenation-closure; the same scalar inequalities appear in the DP constraints. In particular, the “no rule removable” conclusion transfers to the DP setting.

Conclusion: the strategy survives scrutiny, provided we work with the scalar interpretation [·] = l ⊗ M(·) ⊗ r (max-plus product) and the standard Koprowski–Waldmann arctic side-conditions that make “>” context-closed with a uniform integer gap δ ≥ 1.

2) Proof skeleton

2.1) Max-plus structure theorem to invoke
Let A ∈ (Z ∪ {−∞})^{d×d}, with max-plus operations ⊕ = max and ⊗ = +. Let λ(A) be the maximum cycle mean of the weighted digraph of A (max over cycles of average weight). Then:

Theorem (max-plus cyclicity; e.g., Baccelli–Cohen–Olsder–Quadrat 1992, Chap. 3; Butkovič 2010, Theorems 3.101, 3.64). For any fixed i, j, the sequence a_n := (A^n)_{ij} is ultimately arithmetic-periodic affine on each residue class modulo the cyclicity p of the critical graph. Precisely, there exist p ≥ 1, N ∈ N, and offsets β_{ij}(r) ∈ Z (for r ∈ {0,…,p−1}) such that for all n ≥ N with n ≡ r (mod p):
- Either a_n = −∞ eventually (no walk from i to j of that length), or
- a_n = n·λ_ij + β_{ij}(r), where λ_ij is the maximum cycle mean along critical components reachable from i and co-reachable to j. In particular, for any row u and column v, the scalar series f(n) = u^T ⊗ A^n ⊗ v is ultimately of the form f(n) = n·λ(u,v) + π(n), with π periodic and λ(u,v) a maximum of accessible cycle means; across different contexts u,v the value of λ(u,v) can only decrease from the global λ(A).

We also use the simple corollary: slope zero (λ(u,v) = 0) implies that f is ultimately periodic (hence bounded on any arithmetic progression).

For references: F. Baccelli, G. Cohen, G. J. Olsder, J.-P. Quadrat, Synchronization and Linearity, Springer, 1992; P. Butkovič, Max-linear Systems: Theory and Algorithms, Springer, 2010. Classical antecedents include Cohen–Dubois–Quadrat–Viot (1985) and Cuninghame-Green/Karp.

2.2) Setup: arctic matrix interpretation for Z
- Domain: A = Z ∪ {−∞}, with ⊕ = max, ⊗ = +. Order ≥ is the natural order on A (−∞ is the least element).
- Interpretation: fix dimension d and, for each a ∈ {1,h,s,t}, a matrix M_a ∈ A^{d×d}. Fix l ∈ A^{1×d}, r ∈ A^{d×1} (start/finish vectors satisfying the usual “below zero”/monotonicity conditions that make strictness context-closed; e.g., [KW08]).
- Word value: [a_1…a_k] := l ⊗ M_{a_1} ⊗ … ⊗ M_{a_k} ⊗ r ∈ A.
- Weak compatibility: for each rule L -> R and all contexts U, V ∈ Σ*, [U L V] ≥ [U R V].
- Strict compatibility for the removed rule: there exists a fixed δ ≥ 1 such that for all U, V, [U L V] ≥ [U R V] + δ. (Because values are integers, δ can be taken ≥ 1.)

Define M := M_1 and F(n) := [h 1^n] = l ⊗ M_h ⊗ M^n ⊗ r.

2.3) Two universal inequality families on F

- Even/left-to-right handoff enforces monotone drift F(n+2) ≥ F(n+1). Indeed, for all n ≥ 0 we have
  [h 1^{n+2}] ≥ [1h 1^n]      by h11 -> 1h,
  [1h 1^n] ≥ [1s 1^n]         by 1h -> 1s,
  [1s 1^n] ≥ [s 1^{n+1}]      by 1s -> s1,
  [s 1^{n+1}] ≥ [h 1^{n+1}]   by s -> h.
  Chaining yields F(n+2) ≥ F(n+1) for all n.

- Three macro-steps from 8n+1 to 9n+2 (odd, even, odd) give F(8n+1) ≥ F(9n+2). Precisely:
  8n+1 is odd, so h 1^{8n+1} =>* h 1^{12n+2};
  12n+2 is even, so h 1^{12n+2} =>* h 1^{6n+1};
  6n+1 is odd, so h 1^{6n+1} =>* h 1^{9n+2}.
  By weak compatibility, [·] is nonincreasing along each step, so F(8n+1) ≥ F(9n+2), for all n.

2.4) From max-plus structure + (2.3) to λ_F = 0
By the cyclicity theorem, F is ultimately of the form F(n) = n·λ_F + π(n) for large n (on residue classes), where π is periodic. If λ_F < 0 then for n large, F(n+2) < F(n+1), contradicting F(n+2) ≥ F(n+1). Hence λ_F ≥ 0.
From F(8n+1) ≥ F(9n+2) for all large n, dividing by n and letting n → ∞ forces 8·λ_F ≥ 9·λ_F, so λ_F ≤ 0. Therefore λ_F = 0.

Consequently, F is ultimately periodic; in particular, there exists C and p ≥ 1 such that for all n large, |F(n+p) − F(n)| ≤ C and, more generally, the difference between F evaluated on any two fixed arithmetic progressions is bounded. In particular, there is a constant C_8,9 with
  |F(8n+1) − F(9n+2)| ≤ C_8,9  for all large n.                 (⋆)

2.5) Strictness contradiction, per rule
Fix δ ≥ 1 witnessing strictness for the removed rule (context-closed). For each of the 7 rules, we exhibit a family of derivations Start(m) =>* End(m) in which that specific rule is used k(m) times with k(m) → ∞, while Start(m) = h 1^{A(m)} and End(m) = h 1^{B(m)} so that |F(A(m)) − F(B(m))| is bounded in m (by ultimate periodicity at slope 0). Along that derivation, strictness contributes at least k(m)·δ total drop, while boundedness gives an O(1) right-hand side—contradiction.

We write “uses(X)” for the number of times rule X is applied in the derivation.

- Rules with Θ(n) uses along 8n+1 ⇒ 9n+2:
  Let Start(n) := h 1^{8n+1}, End(n) := h 1^{9n+2}. A standard sweep accounting yields:
  • uses(h11 -> 1h) = 4n + (6n+1) + 3n = 13n+1.
  • uses(1s -> s1) = 6n.
  • uses(1t -> t111) = 4n + 3n = 7n.
  All other rules are used O(1) times: 1h->1s once, s->h once (even pass), h1->t11 twice, t->h twice.
  If the removed rule is any of: h11 -> 1h, 1s -> s1, 1t -> t111, then along this derivation we have
    F(8n+1) ≥ F(9n+2) + k(n)·δ,  with k(n) = 13n+1, 6n, 7n respectively.
  But (⋆) says the left-hand minus right-hand side is bounded; contradiction as n → ∞.

- Rules with Θ(m) uses along long even chains (1h -> 1s and s -> h):
  Take Start(m) := h 1^{2^m}, End(m) := h 1. The unique even-macro sequence performs m even sweeps; thus
    uses(1h -> 1s) = m, uses(s -> h) = m,
  and all other rules are used but we do not require strictness on them. Hence
    F(2^m) ≥ F(1) + m·δ.
  With λ_F = 0, F is ultimately periodic, so |F(2^m) − F(1)| is bounded; contradiction as m → ∞.

- Rules with Θ(m) uses along long odd chains (h1 -> t11 and t -> h):
  Take Start(m) := h 1^{2^m − 1}. Then the next m Collatz macro-steps are odd:
    n_0 = 2^m − 1, n_{k+1} = (3 n_k + 1)/2, and n_k = 3^k·2^{m−k} − 1 (odd) for k=0,…,m−1.
  Each odd macro uses h1 -> t11 once and t -> h once; hence
    uses(h1 -> t11) = m, uses(t -> h) = m
  along h 1^{2^m−1} =>* h 1^{3^m − 1}. Therefore
    F(2^m − 1) ≥ F(3^m − 1) + m·δ.
  With λ_F = 0 both sequences F(2^m − 1) and F(3^m − 1) are bounded (each is ultimately periodic in m modulo the cyclicities inherited through powers of 2 and 3), so their difference is bounded; contradiction.

In all seven cases we arrive at a contradiction. Hence, under the standard arctic conditions, no max-plus matrix interpretation (of any dimension) can make any single rule of Z strict while keeping the others weak, both in the plain and dependency-pair settings.

3) What could make the theorem false?

- Strictness not context-closed: If the arctic order used does not guarantee a uniform integer gap δ that survives arbitrary contexts (u, v), then one cannot safely sum gaps along a derivation. Koprowski–Waldmann’s arctic interpretations impose precisely the “below zero/positivity” conditions to ensure this. If a tool uses a weaker notion of “>” (e.g., only some matrix entry strictly larger, without the closure conditions), then multiplying by context matrices may erase strictness and the counting argument collapses. The result might then be false under that weaker notion.

- Non-scalar interpretations: If one compares matrix tuples or vector norms other than the l ⊗ · ⊗ r scalar, the inequalities could pick different coordinates along a derivation and avoid accumulation. Standard arctic MIs for SRS use a scalar (or monotone aggregating) projection; if a custom projection is used, it must still be context-closed for the argument to go through.

- Pathological reducibility exploiting disjoint critical components: The proof above only uses F(n) = [h 1^n], so reducibility per se is harmless. But if one were to attempt a variant proof comparing different contexts’ slopes, it could fail if distinct contexts select different critical components. Our proof avoids this.

- Mis-specified Z: If the 2nd rule were really 11h -> 11s without 1h -> 1s, Z would get stuck at 1h on even length 2, and the encoded macro-steps wouldn’t exist; our derivation families wouldn’t apply. With the corrected 1h -> 1s, the macro steps are sound.

Given these, I do not expect a max-plus interpretation to exist under the standard arctic setting (KW08). If your SAT-side search finds one for dims 1–6, check first whether the strictness notion is truly context-closed and whether 1h -> 1s is enforced—violations there could produce spurious models.

4) Difficulty estimate and first lemmas to prove

- Effort: 8–12 person-days for a competent formalizer to write a complete, checkable paper proof with all constants and counts, including an appendix stating and citing the cyclicity theorem in the exact form used. Another 2–3 days if you also formalize (in a proof assistant) the max-plus periodicity facts in the needed generality.

- Lemma 1 (Cyclicity-instantiated). For the chosen l, r, M := M_1, the scalar F(n) := l ⊗ M_h ⊗ M^n ⊗ r is ultimately arithmetic-periodic affine; in particular, there exists λ_F ∈ Q and a periodic π with F(n) = n·λ_F + π(n) for n large.

- Lemma 2 (Two universal inequalities). For all n ≥ 0:
  (i) F(n+2) ≥ F(n+1) (chain h11 -> 1h -> (1s -> s1) -> s -> h).
  (ii) F(8n+1) ≥ F(9n+2) (three macro-steps odd-even-odd).
  Conclude λ_F = 0. Therefore F is ultimately periodic and |F(a n + b) − F(c n + d)| is bounded in n for any fixed integers a,c ≥ 0, b,d.

- Lemma 3 (Strictness accumulation). Under the Koprowski–Waldmann arctic side-conditions, there exists δ ≥ 1 such that for the removed rule L -> R and all contexts U, V, [U L V] ≥ [U R V] + δ. Consequently, along any derivation W_0 ⇒ W_1 ⇒ … ⇒ W_k that uses the removed rule m times, [W_0] ≥ [W_k] + m·δ.

- Lemma 4 (Use-counts). For the families:
  (A) h 1^{8n+1} ⇒* h 1^{9n+2}: uses(h11) = 13n+1; uses(1s -> s1) = 6n; uses(1t -> t111) = 7n; the other rules occur O(1) times.
  (B) h 1^{2^m} ⇒* h 1: uses(1h -> 1s) = uses(s -> h) = m.
  (C) h 1^{2^m−1} ⇒* h 1^{3^m−1}: uses(h1 -> t11) = uses(t -> h) = m.
  These counts are strategy-independent.

Each case (A–C) plugged into Lemma 3 contradicts boundedness from Lemma 2.

References to cite
- F. Baccelli, G. Cohen, G. J. Olsder, J.-P. Quadrat, Synchronization and Linearity, Springer, 1992 (max-plus spectral theory, cyclicity).
- P. Butkovič, Max-linear Systems: Theory and Algorithms, Springer, 2010 (ultimate periodicity of powers of max-plus matrices).
- D. Koprowski, J. Waldmann, “Automated Termination Proofs with Matrix Interpretations,” RTA 2008 (arctic interpretations, context-closed strictness).
- Y. Yolcu, S. Aaronson, M. Heule, “An Automated Approach to the Collatz Conjecture,” CADE 2021 (for the natural-semirings no-go).

Remark on DP setting
Z is an SRS with one non-data symbol sweeping over a unary alphabet; the DP pairs mirror the same head-movement rules. The scalar inequalities (2.3) are the only ingredients needed to deduce λ_F = 0 and then to run the strictness-counting contradictions. Hence the “no rule removable” conclusion carries over verbatim to DP-based arctic interpretations.

Summary
- Using only weak compatibility for Z, one derives F(n+2) ≥ F(n+1) and F(8n+1) ≥ F(9n+2). Max-plus cyclicity then forces λ_F = 0 and F ultimately periodic.
- If any rule is strict (context-closed δ ≥ 1), one of the three derivation families above accumulates an unbounded strict drop m·δ while the endpoints’ values differ by at most a constant—contradiction.
- Hence, no arctic matrix interpretation of any dimension can remove any rule of Z (plain or DP).

# The address repetition bound: Liouville quality, and what subspace would buy

A new elementary theorem constraining every infinite three-word orbit, one
Diophantine grade above the audited aperiodicity theorem.  Research-side;
proposed for formalization as QM186 (all ingredients are in the audited
stack: cylinder structure, BA3, the periodic point).

## 1. Theorem (cylinder repetition bound)

Let `V` be a nonempty A/B/C word with composed data
`(A_V, D_V, C_V) = (3^(t_V), 2^(s_V), C_V)` and let `V'` be a prefix of `V`
of width `s'`.  The unique 2-adic point with address `V^infinity` is
`xi_V = C_V/(D_V - A_V) <= 0`.  If a positive integer `H` has branch address
beginning `V V'`, then `H == xi_V (mod 2^(s_V + s'))`, hence

```text
N := (A_V - D_V) H + C_V  satisfies  2^(s_V+s') | N,  N > 0,
```

and with the kernel-checked budget `C_V <= 7 (A_V - D_V)` (BA3),

```text
(s_V + s') log 2 <= t_V log 3 + log(H + 7).         (RB)
```

Since `t_V <= s_V` (equality only for all-A words), a repetition constrains
`H` exactly when `s' > s_V (log2(3) - 1) ~ 0.585 s_V`: **the critical
repetition exponent of in-lane integer addresses, in the width metric, is
`log2(3)`.**  Applying (RB) at time `n` (where `H_n <= (3/2)^(s_n)(H_0+7)`)
bounds every later repetition:

```text
s' <= 0.585 (s_V + s_n) + log2(H_0 + 7) + O(1).
```

Verification: [experiments/repetition-bound/verify_bound.py]
(../../experiments/repetition-bound/verify_bound.py) checks cylinders,
`xi_V` membership at depth, the divisibility on whole cylinders, and (RB) on
200 randomized `(V, V')` pairs, exactly.

Three consequences.

1. Eventual periodicity is the `s' -> infinity` case, so (RB) quantitatively
   implies the audited `no_eventuallyPeriodic_branch_orbit`.
2. The bound is **sharp**: minimal cylinder elements achieve the Liouville
   floor (tightness ratio 1.00 occurs in the random sample; e.g. the `CC`
   cylinder has minimum `1201` against floor `237` with the same 2-power
   `2^12 | 17*1201+63`).  So no bookkeeping improvement can push the
   exponent below `log2(3)`; passing it requires genuinely new input.
3. Any address whose initial repetitions have width-exponent exceeding
   `log2(3)` infinitely often is excluded outright — the first exclusion of
   a positive-complexity address class in this lane.

## 2. The automatic-address target and the exact gap

Goal (open): no positive integer with an infinite three-word orbit has a
k-automatic A/B/C address.  This is the Adamczewski--Bell dichotomy shape,
transported through the charge conjugacy rather than through digit
expansions — which is why the literature theorem does not apply as-is.

What the classical route needs and what we have:

- Automatic (more generally, linear-complexity) sequences begin in
  infinitely many `U V^(1+delta)` with `|U| = O(|V|)` and a fixed
  `delta > 0` depending on the complexity constant
  (Adamczewski--Bugeaud combinatorial lemma).  The available `delta` is
  small.
- (RB) only bites at exponent `1 + delta > log2(3)`, i.e. `delta > 0.585`.
  Sharpness (consequence 2) shows this is a real wall, not slack.
- Adamczewski--Bell cross it with the Schmidt/Schlickewei subspace theorem:
  many places, linear forms in several variables, replacing the Liouville
  pigeonhole.  Here the natural data is: the place `2` (where the cylinder
  pins `H`), the place `3` (where `A_V = 3^(t_V)` lives), and infinity
  (where `H` has its size).  The missing step is a subspace-grade
  replacement for the single inequality (RB) — several repetition events
  consumed jointly as small values of integer linear forms in
  `(H, 1, ...)` at the places `{infinity, 2, 3}`.

Per current budget policy this lemma was recorded, not dispatched.  Either
outcome would matter: success excludes the automatic class (a theorem about
Collatz certificates independent of the conjecture, in the line of the DFA
exclusion); a principled failure would locate exactly which subspace
hypothesis the charge conjugacy breaks.

## 3. Scope

(RB) constrains integers with infinite in-lane orbits; it says nothing about
orbits that exit the three-word language.  For the same bound in the full
valuation-word language — where contracting words exist and the constant
degrades to the linear-forms quantity `|2^S - 3^n|` — see
[near-critical-shadowing.md](near-critical-shadowing.md).

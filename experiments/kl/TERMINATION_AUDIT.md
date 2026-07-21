# Audit of the KL advanced-term termination proof

**Status (2026-07-21): exact obstruction to the published proof; termination
itself remains open in this audit.** Run:

```sh
python3 verify_termination_obstruction.py
```

The checker uses integer arithmetic only. It verifies a legal `k=5` path in
the Krasikov--Lagarias back-substitution tree:

```text
188 -B8-> 206 -B8-> 137 -B2-> 182 -B2-> 161
    -B8-> 107 -B8-> 71 -B8-> 47 -T-> 188.
```

Writing every shift as the exact pair `(a,b)` for `a+b log_2(3)`, the
successive shifts are

```text
(-1,1), (-2,2), (-4,3), (-6,4),
(-7,5), (-8,6), (-9,7), (-11,7).
```

All are nonnegative by exact comparisons of powers of two and three. All seven
three-lift destinations are new on their ancestor paths and therefore survive
the deletion test. The closing edge is a transport edge, to which the paper's
deletion rule is not applied. It returns to residue `188` at the strictly
larger shift

```text
7 log_2(3) - 11 > 0  iff  3^7 = 2187 > 2048 = 2^11.
```

This invalidates the deletion-rule inference used to derive equation (3.2) in
the printed proof of Theorem 3.1: a finite legal return to the same residue can
have larger shift. (Equation (3.2) itself is stated only after assuming an
infinite path, which this finite certificate does not supply.) The return also
directly falsifies the next history-free self-similarity claim. When the returned `188`
is split, its `B8` child `206` is now above the earlier `206` and is deleted;
that child survived below the original root. The pruned subtree depends on the
ancestor history, not only on the root residue and a translated shift.

This certificate is **not** a nontermination lasso. The re-expanded subtree is
different, and the path cannot simply repeat. The precise remaining theorem is
that the finitely branching tree of legal histories has no infinite path for
every `k>=2` and every advanced root. A fixed breadth-first schedule would
suffice downstream; a proof of confluence for arbitrary schedules is not
needed for existence of the final retarded witness.

## Consequence for the record certificate

The `k=19` feasible point and its 387,420,489 inequalities remain exactly
verified. The inference from that feasible point to the predecessor-counting
bound uses KL Theorem 2.2, whose published supporting chain invokes Theorem
3.1. Until termination is repaired (or an alternative retarded-elimination
witness is constructed), the numerical certificate is exact but the headline
exponent is conditional on an unclosed literature-proof gap. This is a trust-
chain correction, not evidence that the bound or Theorem 3.1 is false.

## Adjacent repair target

The deletion-invariant gap may be separable from termination. A promising
candidate is a critical-assignment lifting lemma: under global `NoCriticalUse`,
every critical assignment after deleting an alternative canonically lifts to
one before deletion. A context induction through sums and minima appears to
prevent newly tied critical assignments from escaping the maintained bound.
This candidate is not yet kernel-checked and does not solve termination.

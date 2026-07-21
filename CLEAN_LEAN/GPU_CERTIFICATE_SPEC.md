# Certificate artifacts needed from computation

Last updated: 2026-07-20 after reading `docs/FOR_CLEAN_LEAN.md` and
`docs/notes/pressure-certificate.md`.

## Two different jobs

### Finite record certificates

The existing integer KL feasibility certificates through level 19 prove
finite predecessor-counting exponents.  A level-20 candidate eigenvector is
useful for the next record, but it is not needed for the limit proof.

A portable level-20 record certificate consists of:

- `cert_k20.json`, including all scales, rational weight lower bounds, and the
  SHA-256 digest of the vector sidecar;
- `cert_k20_C.npy`, containing the scaled `int64` vector;
- `cert_k20_report.json`, produced by a fresh exact streaming verification;
- preferably a second independently implemented verification report.

The local folder currently contains only the floating-point `eigvec_k20.npy`.

### The limit certificate

To prove `lambda_k -> 2`, another large Perron vector is not the required
artifact.  The missing object is a uniform localization-plus-pressure
certificate for a combined state space

`low 3-adic window × top-digit window × product-cone/profile cell`.

It must cover every sufficiently large level, every minimizing policy, and a
certified interval of `lambda` values.  The current ball-only pressure
automaton certifies its own row inequalities, but the single-profile
localization model fails structurally on aligned top-digit classes.

## Required mathematical content

The final artifact must provide all of the following.

1. **State semantics.**  A finite definition of every low-window, top-window,
   memory, and cone-cell component.  The union of the cells must cover every
   admissible collection of input profiles, including boundary/near-zero
   faces unless a separate invariant lower bound excludes them.

2. **Exact transitions.**  For each state and every admissible minimizing
   policy, a transition list containing the target, exceptional charge, and
   an outward rational upper bound for the normalized mass multiplier.
   Cross-fiber inputs must remain independent; they may not be silently
   identified with one common profile.

3. **Cone invariance.**  Exact rational inequalities proving that every
   transition maps its source cell into the declared target cells.  Any
   claimed contraction must be for the actual product map, including all
   sibling-fiber imports.

4. **Pathwise localization.**  Rational constants showing that a fiber with
   oscillation above any fixed positive threshold must incur a positive
   asymptotic density of exceptional charges.  A sufficient form is a finite
   oscillation-envelope recurrence with good-block contraction `tau < 1` and
   bounded bad-block amplification.

5. **Tilted pressure.**  A positive rational potential `h`, rational `z > 1`,
   rational row bound `R`, and a rational charge density `theta = a/b` such
   that every tilted row satisfies `K_z h <= R h` and the exact gap
   `R^b < z^a` holds.

6. **Uniformity metadata.**  The covered `lambda` intervals, exact rational
   enclosures for all three KL weights, the minimum supported level, and all
   refinement/index conventions.  If multiple interval potentials are used,
   each interval needs its own complete certificate.

## Self-contained file format

The regenerated `lemma5_exact_cert.json` now uses
`pressure-cert/lemma5-portable-v2` and contains the potential, complete sparse
edge table, exact interval weights, and payload hash.  The independent Python
checker passes all 2,187 rows.  The corresponding Lean adjacency-edge checker
and generated payload are now in `PressureCertificate.lean` and
`PortablePressureData.lean`; Lean kernel-checks positivity and all 2,187
tilted rows.  A portable certificate contains:

- every entry of `h` as numerator/denominator;
- every edge multiplier bound as numerator/denominator, or exact parameters
  sufficient to regenerate it;
- the complete exceptional-charge field;
- the exact alpha and lambda endpoint proofs;
- `R`, `z`, and integers `a,b`;
- hashes for any sidecars;
- checker version and state-count/edge-count checksums.

The Lean project now has sound executable checkers for rational KL
feasibility rows, dense or sparse rational pressure rows, and the
integer-power Chernoff gap.  Both Lemma-5 gaps are kernel-checked exactly.
What computation must discover is the finite state decomposition and
potential; what the mathematical proof must establish is that those rows
dominate the real nonlinear KL genealogy uniformly.

## Current pressure result: useful but conditional

The ball automaton has produced an exact uniform interval instance at `J=6`,
`z=3/2`, `theta=1/4`, with an exact `R` satisfying the integer-power gap.
This proves a large-deviation statement for that automaton once the omitted
potential is supplied.  It does not yet prove C1' because no valid pathwise
localization theorem connects high fiber oscillation to a charge density of
`1/4`; the current single-profile contraction search explicitly fails on
aligned top-digit classes.

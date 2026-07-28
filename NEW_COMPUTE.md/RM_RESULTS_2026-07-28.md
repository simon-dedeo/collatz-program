# Bridges-2 RM campaign: proof-facing results

Date: 2026-07-28.  Charged usage for the campaign jobs was approximately
12,374.36 RM core-hours (Bridges-2 SUs).  The persistent files are under
`/ocean/projects/mth260010p/sdedeo/new_compute/results/`; proof-facing copies
were transferred through `data.bridges2.psc.edu`, never through the login
node.  Every quoted output with a sidecar passed its SHA-256 check.

This note separates three kinds of evidence:

- **Lean theorem:** kernel-checked exact implication;
- **exact finite computation:** exhaustive only in the displayed bounds; and
- **floating diagnostic:** a target for certification or a structural
  conjecture, not a theorem.

No job found a Collatz counterexample.  All candidate artifacts retain
`counterexample=null`.

## KL lane

### Cold subeigenvectors

K1b timed out at three hours per shard, but its append-only output retained 16
complete parameter rows per lambda.  At `lambda=1.89`, the floating
Collatz--Wielandt midpoint first clears `3^(1/beta)` at:

| level | beta | midpoint `r` | `3^(1/beta)` | status |
|---:|---:|---:|---:|---|
| 21 | 1024 | 1.0013943781 | 1.0010734393 | floating crossing |
| 21 | 2048 | 1.0010452780 | 1.0005365757 | floating crossing |
| 22 | 256 | 1.0049297307 | 1.0043006757 | floating crossing |
| 22 | 512 | 1.0037386085 | 1.0021480308 | floating crossing |

The most attractive exact-promotion target is `(k,lambda,beta)=(22,1.89,256)`:
it has the largest displayed margin at the warmer temperature.  The timed-out
worker did not save a promotable rational vector, so this is not yet a KL
certificate.  The six result-file digests, ordered by lambdas
`1.84,...,1.89`, are:

```text
44eae65f  lambda=1.84
08ba217c  lambda=1.85
a7681a5b  lambda=1.86
6097906d  lambda=1.87
2c7dc82f  lambda=1.88
e39edc4e  lambda=1.89
```

These eight-character K1b digest prefixes are identification aids, not
sidecar-verification claims: the timed-out shards did not write `.sha256`
files.  Full locally computed digests remain in the transfer/audit log rather
than being promoted as PSC-produced certificates.

`KontoroC.KLColdPowerCertificate` now supplies the exact downstream gate.
For natural `beta`, it turns the finite inequality `3 < r^beta` plus an exact
positive cold subeigenvector into `LevelFeasible`, and composes a cofinal
sequence of such certificates to almost-linear predecessor counting.  Thus a
future rational certificate need not formalize a floating transcendental
threshold comparison.

### Hard-min coercivity

K2b's repaired cold columns are finite floating diagnostics.  At the top
stage, the conservative rowwise-safe quantity is first positive at
`beta=1024`: `0.5275959460` target units at `k=19` and `0.3440792082` at
`k=20`.  The output digests are
`0bcf889b8007233921e9d78880cea839a2d54402299dbcd7ab3f3f0ab6c1296e`
and
`ae5b94d8c87e454205e3ded7307c5a09d5a47d436bf5a19b380f99233de06d64`.

The 81-edge cyclic transport blocks have the following minimum/mean ratios:

| level | hard | frustration |
|---:|---:|---:|
| 16 | 0.286519 | 0.265139 |
| 17 | 0.249593 | 0.247912 |
| 18 | 0.219920 | 0.211899 |
| 19 | 0.214809 | 0.224344 |
| 20 | 0.195612 | 0.178754 |

All ten numbers exceed `1/6`.  Shorter blocks have exact floating zeros (even
length 27 at `k=19`), so any local pointwise coercivity statement is false on
these profiles.  The high-leverage structural conjecture is instead an
all-level selected-profile 81-block bound of at least one sixth of the mean.
Five floating levels do not prove it; an exact finite-level replay and a
refinement-compatible analytic argument are still required.

## Counterexample lane

### Exact bounded searches

C1 exactly exhausts the following finite-subcode carry boxes:

| word bound | carry budget | deepest nonempty | first empty |
|---:|---:|---:|---:|
| 50 | 28, 29, 30 | 120, 122, 129 | 121, 123, 130 |
| 100 | 28, 29 | 164, 168 | 165, 169 |
| 250 | 28, 29 | 164, 168 | 165, 169 |
| 500 | 28, 29 | 164, 170 | 165, 171 |

These are finite lower bounds on the carry budget, not evidence of a uniform
bound.  C2b exactly exhausts sources through `B=5.5*10^12`; its selected
slice is nonnull through depth 87 and null from depth 88 through 160.  Its
digest is
`50b11849ac88dc297a7608d5bb6514256844c6da3ec43154d81d21c5c70a83f3`.

C3's completed depth-26 prefix search found champion total survival 87 at
seed `12629171449094760170027126`; digest
`111e50afb22385d7980e9677abe59e78a1f7da6f325af02af9afb18ea89ec335`.
The more ambitious C3b shards timed out without writing their promised
checkpoint, so their dependent collector never ran.  No exhaustive conclusion
is available from C3b.

The bouncer backward-cylinder atlas retained an exact partial checkpoint:
87,040 of 248,832 prefix tasks, 259,900,047,360 depth-five paths, and zero
finite stabilizations, decreases, nonoutward links, or link failures.  Its
combined digest is
`8ee7727c664bad0ac15839a841e851860462a367ced4ce3f12d2648ad666a89c`.
This is exact on the processed prefix interval only.

### Policy-potential extraction

B2's four 8,192-row corpora were independently rebuilt exactly by
`verify_carry_policy.py`; combined digest
`1e62a3499d1f6c0414f291a5c61b41078600edd54ec2a3da7d763c4b446f4890`.
The relaxed fits cover both held-out corpora but are not lower-bounded, so
they cannot telescope to bounded carry.  The strict fits miss only five
held-out rows:

- the three-word code misses `(D,c,z)=(7,5,5)` twice and `(6,3,11)` once;
- the 13-word code misses `(6,3,11)` twice;
- in every miss the best available word has carry `q=1`, while the fitted
  potential change has the wrong sign.

Run `python3 verify_carry_policy.py RESULT.tsv --diagnose` to reproduce the
exact miss states.  These rows isolate a small-unit-spike correction problem;
they do not validate the fitted linear potential.

`KontoroC.OutwardCarryPolicyPotential` is the exact proof refinement.  It
shows that a natural-valued potential satisfying

```text
extensionCarry(pre,w) + V(pre++[w]) <= V(pre)
```

for some legal child of every reachable prefix telescopes to a uniform carry
budget, then to an eventual zero-carry tail and an ordinary infinite
execution.  For a finite first-passage subcode it conditionally refutes the
Collatz conjecture.  None of the finite B2 fits satisfies the all-prefix
premise, so the next construction target is a symbolic, globally
nonnegative potential with an exact bounded correction at the two displayed
states—not a larger unconstrained regression.

## Promotion priorities

1. Save and rationalize the K1b `(22,1.89,256)` vector, then exact-check every
   cold subeigenvector row and `3 < r^256` against the new Lean consumer.
2. Seek a refinement-stable proof of the selected 81-block `1/6` coercivity
   conjecture; first reproduce levels 16--20 in exact or interval arithmetic.
3. Analyze the B2 Bellman inequalities symbolically near `(7,5,5)` and
   `(6,3,11)`, searching for a globally natural small-unit correction.
4. If C3b is rerun, checkpoint completed prefix ranks periodically; its first
   version consumed time without leaving a promotable bounded result.

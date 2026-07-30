# PSC difference-map counter-language program

Status: exact Python pilot complete locally; fixed-word production launch
cancelled on mathematical grounds; the autonomous 17-adic place-value
counter is the sole B3 launch target.

## Result of the pilot

The implemented pilot is
`experiments/cyclic_descent/difference_map_programs.py`, with committed audit
`experiments/cyclic_descent/difference_map_program_audit.json`. It constructs
the expanded exact positive-time power-chart library, represents a candidate
macro-cycle in four product-space copies, and applies the Elser difference
map between the componentwise constraint product and the consensus diagonal.
Every reported discrete candidate is replayed with exact rational symbolic
arithmetic.

The exhaustive length-six run contains 102,111 based cycles. There are 95,424
cycles in the structural reproductive projection and 102,106 with exact
depth-32 ordinary cylinders. The latter need 188--193 binary digits. No
nontrivial ordinary periodic point or invariant arithmetic ray exists.

This is not a negative numerical hunch. Every fixed positive-time word in the
current atlas has composite tail slope

```text
A / 2^L,   L > 0,   A odd.
```

If it preserved a full arithmetic ray `a+M*t`, comparison of free-parameter
coefficients would give `A*M=2^L*M*u`, hence `2^L | A`, a contradiction.
Longer fixed words cannot evade this obstruction. Therefore no PSC allocation
will be spent extending fixed-word cycle length.

The old cap-12 forward-closure collapse was also a truncation artifact. At
depth 6/cap 64 the engine has 621 canonical positive-time edges and its
greatest closed chart kernel is `48 -> 36 -> 24`, retaining the root. Closure
alone recodes Syracuse and includes terminal configurations; it is not a
counterexample language.

## B3 launch target: autonomous 17-adic place-value counter

The next worker is no longer a generic counter-table search. It must compile
one specific surviving architecture. An evolving public payload stores an
unbounded base-17 odometer state `n`; one exact program epoch performs

```text
n -> n+1,
carryHeight = v_17(n+1),
m = j + 8*17^carryHeight,            1 <= j <= 8,
```

and uses `m` as the next exact EC17/public-payload branch. The schedule is
aperiodic because base-17 carries occur at every scale. More importantly, it
must be **endogenous**: using loop time to print the already-audited sequence
is forbidden. The current ordinary state must decode the counter, execute its
increment, and write the payload from which the next counter and branch are
decoded.

The external schedule is already mathematically organized. With

```text
A_n = sum_(1<=t<=n) 17^v_17(t),
H(C,Z) = sum_(n>=0) C^A_n Z^n,
```

exact arithmetic gives

```text
A_(17n+r) = 17*A_n + 16*n + r,
H(C,Z) = P_17(CZ) H(C^17,C^16 Z^17).
```

The monomial map `(C,Z)->(C^17,C^16 Z^17)` is a genuine rank-two defective
Jordan system. The slower ruler `j+8*v_17(n+1)`, every fixed phase increment,
and fixed words are closed; this place-value ruler survives those exact
obstructions and the public height gate. `RankTwoRulerMahler.lean` already
kernel-checks its block law, convergent functional equation, Jordan iterates,
and multiplicative-rank determinant. What remains open is not another prefix
of that schedule but its autonomous realization and ordinary root.

The four difference-map copies are therefore fixed as follows:

1. `S` — **semantic compiler:** every selected production is a nonempty exact
   forward Syracuse/EC17 macro with a literal positive duration;
2. `C` — **odometer closure:** the public payload implements base-17
   increment with exact carry propagation and regenerates the same decoder;
3. `R` — **place-value reproduction:** the carry height emits exactly
   `j+8*17^v17(n+1)`, while the decoded ordinary height is proper and
   unbounded;
4. `O` — **ordinary root:** one finite positive input initializes the public
   counter, every later instruction is computed from evolved state, and no
   fresh low bits or independently chosen CRT residues are introduced.

Projection `P_C` is a local carry repair on a candidate base-17 transducer;
`P_R` repairs its branch-emission and public-height identities; `P_S` selects
from versioned exact macro fragments; and `P_O` minimizes the canonical
dyadic lift but accepts only literal eventual stabilization. A candidate is a
small public transducer plus exact arithmetic annotations, not a long opcode
word.

Candidate extraction writes the transducer, its counter encoding/decoder,
all exact macro paths, one root, and a proper-height certificate. A separate
Python checker must rebuild the edge grammar, replay the counter update and
every macro with integers, prove that emitted branches equal the place-value
ruler, and apply the ordinary-root gate. Lean promotion uses QM199 together
with `RankTwoRulerMahler.lean`; neither the numerical difference-map residual
nor the externally generated ruler is a certificate.

## Parallel and checkpoint contract

The intended production shape is four RM nodes for four hours, one OpenMP
thread per physical core (2,048 SU hard cap). Restarts are independent across
512 cores. Each thread appends a checkpoint after every completed restart;
the checkpoint contains the RNG seed, four residuals, best exact-discrete
table, first failed exact condition, and SHA-256 of the edge grammar. A
pre-wall-time signal stops new restarts and flushes all completed records.
Interrupted shards remain useful but are labelled `partial`.

A one-core collector checks grammar hashes and disjoint seed ranges, merges
the Pareto frontier, and runs the independent exact verifier on every emitted
candidate. It must leave `counterexample=null` unless a literal QM199-style
infinite certificate is present and verified. Numerical residuals are never
promoted.

Outputs live under
`/ocean/projects/mth260010p/sdedeo/new_compute/results/`. The laptop may be
closed after `sbatch`: Slurm and project storage are independent of the SSH
session. Retrieval is later initiated locally through
`data.bridges2.psc.edu`, never through the login node. The collector produces
a compact Git-safe JSON/Markdown summary, but PSC will not push to GitHub by
itself.

## Launch gate

Do not queue B3 until all of the following exist:

- a C implementation of the four specialized odometer projections, including
  exact base-17 carry and a proper decoded height;
- a planted public base-17 incrementer recovered from scrambled local carry
  rules, followed by exact rejection when its decoder or carry write is
  corrupted;
- rejection tests for a 2-adic-only root and a dummy growing exponent;
- a rejection test for an externally indexed ruler with no public `n->n+1`
  implementation;
- an independent exact replay of the counter, emitted place-value schedule,
  and multi-state macro candidate;
- a shared-node smoke test showing all 128 threads write disjoint checkpoints.

The gate deliberately prevents spending the new allocation on the already
closed fixed-word or affine-tail-catalyst lanes.

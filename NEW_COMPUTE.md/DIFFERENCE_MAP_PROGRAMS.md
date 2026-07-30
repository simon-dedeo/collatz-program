# PSC difference-map counter-language program

Status: exact Python pilot complete locally; fixed-word production launch
cancelled on mathematical grounds; branching C worker is the next launch
gate.

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

## B3 launch target: branching counter language

The next worker must search a finite **counter transducer**, not a repeated
word. A state contains a power chart, an ordinary counter domain, and a
resource coordinate. Its two productions are selected by the regenerated low
bit of the current natural counter. A candidate table must satisfy four
separate projections:

1. `S`: every selected production is a nonempty exact forward Syracuse macro;
2. `C`: both regenerated-bit branches of every reachable state return to the
   selected language;
3. `R`: a proper decoded-height resource has positive gain on every recurrent
   kernel, certified by an exact cycle-potential dual;
4. `O`: one explicit finite root reaches the kernel, every macro duration is
   positive, and no completion-only tail is introduced.

Unlike a fixed path, a counter transducer can split cylinders and later
regroup them. The changing state can therefore generate a nonperiodic opcode
language and is not covered by the odd-over-`2^L` lemma. It is the minimal
architecture worth sending to PSC.

The C worker will use the Python miner only to emit a versioned exact edge
table. Each RM core runs an independent difference-map restart over discrete
rule logits and rationalized resource weights. Candidate extraction writes a
small certificate containing the selected table, root, exact macro paths,
and cycle-potential dual. A separate Python checker rebuilds the edge table,
replays every path, recomputes reachable closure, and verifies the dual with
integer/rational arithmetic. Lean promotion uses QM199 in
`docs/FOR_CLEAN_LEAN.md`.

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

- a C implementation of all four projections, including a proper resource;
- a tiny grammar with a planted branching recurrent program recovered by the
  numerical search;
- rejection tests for a 2-adic-only root and a dummy growing exponent;
- an independent exact replay of a multi-state candidate;
- a shared-node smoke test showing all 128 threads write disjoint checkpoints.

The gate deliberately prevents spending the new allocation on the already
closed fixed-word or affine-tail-catalyst lanes.

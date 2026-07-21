# wfar — weighted (arctic / WFAR-style) divergence-exclusion certificates for Collatz

Next rung above `../dfacert` (Boolean regular certificates, exhausted at small
sizes): instead of asking for a regular set that is *invariant* under the
Collatz map, we ask for a regular-state **weight function that strictly
decreases** along every step taken inside a regular domain. This is the
scalar collapse of constrained-JSR multinorms (docs/SMELL.md §1 #5) and the
LP rung of the WFAR generalization ladder (docs/REVERSE-MINING.md §2B.2).

Everything below is over the LSB-first binary encoding of `dfacert`:
`enc(n)` is `n ≥ 1` written least-significant-bit first, so every valid
encoding is a nonempty word over `{0,1}` ending in `'1'`;
`C = {w : w ends in '1'}` is in bijection with the positive integers.
`T(n) = n/2` (n even) = drop the first character; `T(n) = 3n+1` (n odd) =
the carry transducer with carry `c ∈ {0,1,2}` initialized to 1, flushing 1
or 2 extra output bits at word end (dfacert.c, validated there and re-tested
here).

## 1. The object

A **weighted certificate** is a tuple `(A, w, β, δ; A', L₀)` where

* `A` is a complete DFA over `{0,1}` (start state 0) — the *value automaton*;
* `w : states(A) → ℚ` is a weight vector and `β ∈ ℚ`, `β ≥ 0`, is a length
  coefficient, defining the **configuration weight**

      V(n) = w( δ_A(0, enc(n)) ) + β · |enc(n)|     (|enc(n)| = len(n) = ⌊log₂ n⌋ + 1);

* `δ > 0` is a rational drift threshold;
* `A'` (with accepting set `F'`) is a second DFA defining the regular
  **domain** `D = { n ≥ 1 : δ_{A'}(0, enc(n)) ∈ F' }`;
* `L₀ ≥ 1` is a length cutoff, i.e. `N₀ = 2^{L₀−1}` (`len(n) ≥ L₀ ⟺ n ≥ N₀`).

**Certificate condition (one-step drift).**

    (†)   for every n ∈ D with n ≥ N₀ :   V(T(n)) ≤ V(n) − δ.

Note `T(n)` is *not* required to stay in `D`; the drift must hold at every
domain point, unconditionally on where the step lands.

## 2. Soundness

**Lemma 1 (relativized soundness).** Suppose `(A, w, β, δ; A', L₀)` satisfies
(†) with finite rational weights, `β ≥ 0` and `δ > 0`. Then no Collatz orbit
has a tail contained in `D ∩ [N₀, ∞)`: there is no `n ≥ 1` and `K ≥ 0` with
`T^k(n) ∈ D` and `T^k(n) ≥ N₀` for all `k ≥ K`.

*Proof.* `V` is bounded below on all of ℕ: `V(m) ≥ min_s w(s) + β·1 =: B > −∞`,
since `A` has finitely many states, `len(m) ≥ 1`, and `β ≥ 0`. Suppose a tail
existed; write `m_k = T^{K+k}(n)`, so `m_k ∈ D` and `m_k ≥ N₀` for all `k ≥ 0`,
and `m_{k+1} = T(m_k)`. Applying (†) at each `m_k` and telescoping,
`V(m_k) ≤ V(m_0) − kδ → −∞` as `k → ∞`, contradicting `V(m_k) ≥ B`. ∎

**Corollary (divergence retirement).** Under the hypotheses of Lemma 1, no
*divergent* Collatz orbit eventually remains in `D` — for **any** `L₀`.

*Proof.* An unbounded orbit tends to ∞: if it had a finite liminf it would
visit some fixed value infinitely often, hence be eventually periodic, hence
bounded. So a divergent orbit eventually has all its points `≥ N₀`; a tail
inside `D` would then be a tail inside `D ∩ [N₀, ∞)`, contradicting Lemma 1. ∎

Each certified domain `D` therefore *retires a regular family of divergence
itineraries*: no orbit can diverge while eventually staying inside `D`. This
quantitatively extends the exhausted Boolean search of `dfacert` (which could
only retire `D`s that are exactly `T`-invariant).

**Lemma 2 (global soundness).** Suppose (†) holds with `D = ℕ` (i.e.
`L(A') ⊇ C`) and `N₀ ≤ 2^71`. Then every Collatz orbit reaches 1, i.e. the
Collatz conjecture holds.

*Proof.* By Lemma 1 with `D = ℕ`, no orbit has a tail in `[N₀, ∞)`, so every
orbit visits the finite set `{1, …, N₀−1}` infinitely often. By pigeonhole
some value `v < N₀` recurs, so the orbit is eventually periodic and its cycle
contains `v < N₀ ≤ 2^71`. Computational verification (Barina's project:
convergence checked for all starting values below 2^68, with the project
frontier claimed through 2^71) shows every `v` in that range reaches 1 and
the only cycle met is `(1, 2, 4)`. Hence the orbit reaches 1. ∎

Because of Lemma 2, **finding a feasible global certificate at toy sizes must
be treated as a bug**, not a result (v1 control below). The productive object
is the relativized certificate of Lemma 1.

**Why `β ≥ 0` is load-bearing.** For `D = {odd n}`, `V = β·len` with
`β = −1`, `δ = 1` satisfies (†) — an odd step increases the length by 1 or 2,
so `V` drops by ≥ 1 — yet proves nothing: `V` is unbounded below, and the
telescoping argument dies. The LP therefore carries the side constraint
`β ≥ 0` always; the selftest verifies that dropping it produces exactly this
spurious "certificate". (Boundedness of `V` below on `D` alone would suffice
for Lemma 1, but a `β < 0` domain of unbounded length is never bounded below,
and bounded-length domains are finite, hence vacuous for divergence.)

**Normalizations (WLOG).** (i) (†) is positively homogeneous in `(w, β, δ)`
jointly, so `δ = 1` WLOG. (ii) Every constraint involves only weight
*differences* `w(q) − w(p)` (plus `β·Δlen`), so `w(state 0) = 0` WLOG.

## 3. Verification algorithm (exact, no sampling)

The condition (†) quantifies over the infinite set `D ∩ [N₀,∞)` but is
decided exactly by finite product constructions, in the style of the
`dfacert` closure checks. Every complete step `n → T(n)` contributes the
linear constraint

    w(q_fin) − w(p_fin) + β·Δlen ≤ −δ,

where `p_fin = δ_A(0, enc(n))`, `q_fin = δ_A(0, enc(T(n)))`, and
`Δlen = len(T(n)) − len(n)`. The set of *realized* triples
`(p_fin, q_fin, Δlen)` over all `n ∈ D`, `len(n) ≥ L₀` is computed by BFS:

* **Even steps** (`enc(n) = 0v`, `T(n)` = drop first char, `Δlen = −1`):
  BFS over `(x, y, z, ℓ̂)` where `x` runs `A` on the full input from
  `δ_A(0,0)`, `y` runs `A` on the suffix `v` from state 0, `z` runs `A'` on
  the full input from `δ_{A'}(0,0)`, and `ℓ̂ = min(len, L₀)` is a capped
  length counter. At every `'1'`-transition (the word may end there) with the
  `A'`-target accepting and `ℓ̂ = L₀`, emit the constraint with
  `p = x`-target, `q = y`-target, `Δlen = −1`.
* **Odd steps** (`enc(n)` starts with `'1'`; the 3n+1 transducer): BFS over
  `(x, y, z, c, ℓ̂)` with `x` = `A`-state on the input, `y` = `A`-state on
  the transducer output emitted so far (one output bit per input bit), `z` =
  `A'`-state on the input, `c ∈ {0,1,2}` the carry (first bit forced `'1'`,
  initial carry 1 → after the first bit `c = 2`). At every `'1'`-transition
  with accepting `A'`-target and `ℓ̂ = L₀`, the end-of-word carry `c' ∈ {1,2}`
  is flushed into the output side (`Δlen = +1` for `c' = 1`, `+2` for
  `c' = 2`, and the flushed output ends in `'1'`, a valid encoding); emit the
  constraint with `p = x`-target, `q` = flushed `y`-state. The one-letter
  word `"1"` (n = 1) is handled at the first forced transition, exactly as in
  `dfacert`.

Every BFS configuration is realized by an actual input word (the BFS follows
real transitions from the real start), and every `n ∈ D` with `len(n) ≥ L₀`
drives the BFS through its completion check — so the emitted constraint set
is **exactly** the set of realized constraints (soundness *and* completeness
of the reduction; the selftest cross-checks it against direct enumeration of
all `n ≤ 2^16`). State spaces are ≤ `q_A²·q_{A'}·3·L₀` — tiny.

## 4. Synthesis: exact-rational LP via Fourier–Motzkin

With `δ = 1`, `w(0) = 0` fixed, the unknowns are `u = (w(1), …, w(q_A−1), β)`
and each realized triple gives a row `w(q) − w(p) + β·Δlen ≤ −1`, plus the
side row `−β ≤ 0`. Feasibility (and a witness) is decided by an exact
Fourier–Motzkin eliminator over ℚ (`long long` numerator/denominator, reduced
via `__int128` intermediates, overflow-checked — exact rationals instead of
the 1/2^20 fixed grid, strictly safer and just as simple at these sizes; ≤ 3
unknowns for `q ≤ 3`). Rows are normalized (first nonzero coefficient scaled
to ±1) and deduplicated (identical coefficient vectors keep the minimum
right-hand side) at every elimination stage. A witness is extracted by
back-substitution through the stored stages and then **re-checked exactly
against every original constraint**; any failure aborts.

Feasible certificates are further classified by re-running the LP with `β`
forced to 0:

* **escape/ranking type** (feasible with `β = 0`): a pure state-ranking
  certificate — typically `D` such that orbits provably leave `D` for
  combinatorial reasons (e.g. all-odd domains: one odd step lands even);
* **length-drift type** (needs `β > 0`): the genuinely quantitative kind —
  the certificate tracks the log₂-scale value decrease (e.g. `D` = even
  numbers: each step inside `D` halves).

Every feasible certificate is additionally validated by **simulation**: up to
10⁵ actual Collatz steps (a scan of small `n` plus long orbits started at the
smallest members of `D`), each checked exactly against
`V(T(n)) ≤ V(n) − 1` whenever `n ∈ D`, `len(n) ≥ L₀`. Any contradiction with
the LP verdict aborts the program (exit 3).

**v1 scope:** the synthesis loop instantiates `A' = A` (one canonical table
supplies both the domain, via its accepting set `F`, and the value states,
via per-state weights), over all canonical initially-connected `q`-state
tables (the `dfacert` enumerator, re-validated against a brute-force
canonicity filter) and all `2^q` accepting sets, for `q ≤ 3`. Distinct
`(table, F)` pairs may define the same language `D`; the summary counts both
raw pairs and distinct membership fingerprints (membership mask of
`n = 1..64` — a heuristic identity). Hand-built controls exercise `A ≠ A'`.

Domains are classified semantically before solving: `D` empty (vacuous —
skipped, *not* counted as certified), `D` finite vs infinite (pumping
argument on reach-set iteration), `D` = all of ℕ ("global"), and `D`
cofinite. **Global or cofinite domains that come out feasible are routed to
the bug path** (dump constraints + witness, simulate, abort): by Lemma 2 a
real one would prove Collatz, so at toy sizes it is a checker bug with
probability ≈ 1.

## 5. Controls (all enforced in `--selftest`, which runs before every search)

1. **Global domain must be INFEASIBLE.** `A = A'` = 1-state all-accepting
   (`D = ℕ`) for `L₀ = 1..8`; *every* canonical 2- and 3-state table with
   `F = all` for `L₀ ∈ {1,4}`; plus the cofinite `D = {n ≥ 2}`
   (3-state handmade). Any feasibility ⇒ selftest failure.
2. **Even-domain positive control must be FOUND.** `A` = trivial 1-state
   (`w ≡ 0`), `A'` = 3-state "first symbol is 0" DFA (`D` = even numbers).
   Constraint set is exactly `{ −β ≤ −1 }`; the LP must return feasible with
   witness `β = 1`, i.e. `V(n) = len(n)`, `V(T(n)) = V(n) − 1` — the
   "an always-even tail halves forever" certificate. Forcing `β = 0` must be
   infeasible (it is a pure length-drift certificate). Simulation must pass.
3. **Odd-domain control.** `A` = trivial 1-state, `A'` = "first symbol is 1"
   (`D` = odd numbers): constraints `{ β ≤ −1, 2β ≤ −1, −β ≤ 0 }` — must be
   INFEASIBLE. Dropping the `β ≥ 0` side row must flip it to feasible
   (`β = −1`), demonstrating that the boundedness side-condition is
   load-bearing (see §2). (With a value automaton that can *see* the first
   bit — first expressible at `q = 3` in the `A' = A` sweep — an all-odd
   domain is legitimately certified as escape-type, since an odd step lands
   even; the control pins the pure-length direction.)
4. **Constraint-generator completeness.** For the control pairs and several
   canonical 3-state tables × all `F` × `L₀ ∈ {1,3}`: every actual step
   `n → T(n)`, `n ≤ 2^16`, `n ∈ D`, `len(n) ≥ L₀` must hit a generated
   `(p, q, Δlen)` triple.
5. **Machinery ports re-validated:** transducer vs `__int128` arithmetic on
   10⁵ random odd `n < 2^60` (+ n = 1, 3, 5), even step = drop-first-char,
   encode/decode roundtrip, canonical-table counts vs brute force (q ≤ 4),
   FM unit tests (feasible/infeasible/witness on hand-solved systems),
   finite/infinite/global/cofinite language classification on known cases.

## 6. Results (this machine, sequential; `δ = 1` normalized)

Sweep of all canonical `q`-state tables × all accepting sets `F`, `A' = A`.
"pairs" = (table, F) pairs; "vacuous" = `D` nonempty but no member of length
≥ L₀; "feasible" = certified domains. The bug path never triggered: **no
global or cofinite domain was ever feasible** (433 global pairs per L₀
across q ≤ 3, plus the handmade cofinite control); every feasible witness
passed the exact re-check against all constraints and the orbit simulation.

| q | L₀ | pairs | empty D | vacuous | infeasible | (global D) | feasible | escape | drift | distinct fingerprints | finite-D feasible |
|---|----|------:|--------:|--------:|-----------:|-----------:|---------:|-------:|------:|----------------------:|------------------:|
| 1 | 1  |     2 |       1 |       0 |          1 |          1 |        0 |      0 |     0 |                     0 |                 0 |
| 2 | 1  |    48 |      18 |       0 |         27 |         18 |        3 |      1 |     2 |                     3 |                 0 |
| 3 | 1  |  1728 |     414 |       0 |       1123 |        414 |      191 |     71 |   120 |                    91 |                16 |
| 1 | 4  |     2 |       1 |       0 |          1 |          1 |        0 |      0 |     0 |                     0 |                 0 |
| 2 | 4  |    48 |      18 |       0 |         27 |         18 |        3 |      1 |     2 |                     3 |                 0 |
| 3 | 4  |  1728 |     414 |      16 |       1111 |        414 |      187 |     55 |   132 |                    92 |                 0 |

Consistency checks visible in the table: `empty D = global D` at every size
(exact, by the `F ↔ ¬F` symmetry of "every reachable `'1'`-target
non-accepting" vs "accepting"); at q = 3 the 16 finite feasible domains at
L₀ = 1 are all `D = {1}` and become exactly the 16 vacuous pairs at L₀ = 4;
the 12 domains newly feasible at L₀ = 4 (187 = 191 − 16 + 12) are domains
whose only blocking constraints came from small members (the `1 → 4 → 2 → 1`
cycle region), excised by `N₀ = 8`.

Decoded examples (raw lines in `results/q{1,2,3}_L0{1,4}.txt`):

* **`D` = even numbers** — found in-sweep at q = 3 (`tab=179, d=12.11.22,
  F={1}`, the first-symbol tracker): drift-type, `w = (0,0,0), β = 1, δ = 1`,
  i.e. `V(n) = len(n)`: an always-even tail halves forever. This replicates
  positive control 2 inside the sweep (the control itself uses `A` = 1-state,
  `A'` = 3-state, showing decoupling `A ≠ A'` buys the same certificate with
  a trivial value automaton). Retires: *no orbit tail is all-even*.
* **`D` = odd numbers** (`tab=179, F={2}`): escape-type, `w = (0,−1,0),
  β = 0` — the weight ranks "has stepped even"; one odd step lands even.
  Retires the all-odd tail trivially, and marks precisely the boundary of
  control 3: as a *pure length* certificate it is infeasible (odd steps
  lengthen), but a value automaton that sees the first bit certifies it by
  ranking.
* **`D` = the all-ones ray `{2^k − 1}`** — q = 2 already (`tab=7, d=10.11,
  F={0}`): escape-type, `w = (0,−1), β = 0`. The 2-adic all-odd ray that
  obstructs every *global* certificate (it forces unboundedly many
  consecutive odd, hence lengthening, steps) is itself retired as a *tail*
  family: `T(2^k − 1) = 3·2^k − 2` contains a `0`-bit, so no orbit stays on
  the ray for two steps. The obstruction to global certification is not an
  obstruction to relativized certification.
* **`D` = {n whose binary expansion begins with an even-length run of 1s}**
  (q = 2, `tab=0, d=01.00, F={0}`; members 3, 6, 12, 13, 15, 24, 25, 26, …):
  **drift-type**, `w = (0,−3), β = 1` — a genuinely non-obvious quantitative
  certificate: `V(n) = len(n) − 3·[state 1]` decreases by ≥ 1 at every step
  taken from a point of `D`, mixing length descent with a state correction. Retires:
  no orbit tail keeps an even-length leading-1-run forever.
* **L₀ at work**: `tab=13, d=01.12.11, F={1}` (members 8, 13, 14, 16, 25,
  26, 27, …) is infeasible at L₀ = 1 — `1 ∈ D` and `V(4) ≤ V(1) − δ` needs
  `2β ≤ −1` — but drift-certified at L₀ = 4 (`w = (0,3,0), β = 1`), i.e.
  for the tail statement restricted to `D ∩ [8, ∞)`, which is all a
  divergence-retirement claim needs.

Honest bottom line for v1: about 11% of q = 3 domains admit certificates,
almost all retiring tail families that are either one-step escapes or
halving-dominated; the drift-type class (120 of 191 at L₀ = 1) already goes
beyond what the Boolean `dfacert` search could express (those domains are
not `T`-invariant, so Boolean closure could never certify them), but none
yet touches a family adjacent to the hard region (parity-balanced
itineraries near odd-density `log 2 / log 3`). The global case is infeasible
everywhere it must be, and the machinery measures exactly where the value
direction (`β > 0`) activates — matching the SMELL.md §1 #5 prediction that
useful weights must be indexed by value-reading transducer states.

Simulation coverage note: for dense domains the 10⁵-step target is met by
the scan of all `n ≤ 2·10⁶` plus long orbits; for sparse domains (e.g. the
all-ones ray) *every* member below 2·10⁶ and every in-domain orbit point
encountered is checked — the reported `sim=` count is the number of
in-domain steps actually available, not a sampling shortfall.

## 7. Build and run

    make mac       # macOS/clang, sequential
    make linux     # Linux/gcc, OpenMP
    make test      # run --selftest (also runs automatically before searches)

    ./wfar 3       # sweep all canonical 3-state tables x accepting sets, L0=1
    ./wfar 3 4     # same with length cutoff L0=4  (N0 = 2^3 = 8)

Per-certificate lines go to stdout; summary line at the end:

    q=<q> L0=<L0>: pairs=... emptyD=... infeasible=... (globalD=...) feasible=... [escape=..., drift=...] fingerprints=... finiteD=...

Exit codes: 3 = simulation contradicted the LP (bug), 4 = feasible
global/cofinite certificate (treated as bug per Lemma 2).

## 8. Subtleties and extensions

* `T(n)` need not remain in `D` — drift is unconditional at domain points.
  This makes escape-type certificates legitimate (and abundant).
* The length cutoff `L₀` only ever *removes* constraints (short words), so
  feasibility is monotone in `L₀`; divergence retirement (Corollary) is
  valid for every `L₀` since divergent tails have `len → ∞`.
* `β ≥ 0` cannot be dropped (§2); a per-state length coefficient
  `β_s` (still ≥ 0) is the natural next template, as is decoupling `A ≠ A'`
  in the sweep (the even-domain control certifies `D` = evens with a 1-state
  value automaton, which `A' = A` cannot do below q = 3), and per-state-pair
  drift `δ` (max-plus / arctic weights proper).
* Different `(table, F)` pairs repeat languages; fingerprints (n ≤ 64
  membership masks) give the distinct-domain counts.

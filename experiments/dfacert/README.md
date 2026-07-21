# dfacert — exhaustive search for regular divergence certificates for Collatz

This program mirrors the Busy Beaver Challenge's CTL/FAR ("closed
tape language" / finite-automata reduction) deciders, applied to the
Collatz map

    T(n) = n/2      if n is even
    T(n) = 3n + 1   if n is odd.

## The certificate

A **regular divergence certificate** is a regular language `L` of binary
encodings of positive integers such that

1. `L` is nonempty,
2. the encoding of `1` is **not** in `L`,
3. `T(L) ⊆ L` (closure under one Collatz step).

If such an `L` exists, the Collatz conjecture is **false**: by induction,
the forward orbit of any member stays in `L` forever, so it never reaches 1
(it either diverges or enters a cycle avoiding 1). Conversely, if the
conjecture is true no such `L` exists at any size, so each exhausted DFA
size is a genuine negative result: *"no regular divergence certificate
recognized by a complete DFA with ≤ k states exists."*

## Encoding

`n ≥ 1` is written in binary **LSB-first**, so every valid encoding ends
in `'1'` (the MSB). Example: `6 = 110₂ → "011"`. The set of valid
encodings is `C = {w ∈ {0,1}* : w ends in '1'}`, in bijection with the
positive integers. For each candidate DFA `A` the searched language is
`L_A := L(A) ∩ C`.

Under this encoding, one Collatz step is a string operation:

* `n` even (`w` starts with `'0'`): `T(n) = n/2` = drop the first character.
* `n` odd (`w` starts with `'1'`): `T(n) = 3n+1` is a sequential
  transduction with carry `c` initialized to 1 (the `+1`): for each input
  bit `b` (LSB first), `s = 3b + c`, emit `s mod 2`, set `c = s div 2`
  (`c ∈ {0,1,2}`); after the input, flush `c` (`while c > 0: emit c&1,
  c >>= 1`). After the final input bit (a `'1'`) the carry is in `{1,2}`,
  so the flushed output always ends in `'1'` — a valid encoding.

## Exact decision procedures (no sampling)

For each DFA `A` (complete, over `{0,1}`, start state 0) and each
accepting set `F`:

* **nonempty**: some state `s` reachable from 0 has `δ(s,1) ∈ F`.
* **1 ∉ L**: `δ(0,1) ∉ F` (the string `"1"`).
* **even closure** (`w = 0v ∈ L ⇒ v ∈ L`): BFS over pairs `(x, y)` where
  `x` runs `A` from `δ(0,0)` (simulating `w = 0·prefix`) and `y` runs `A`
  from 0 (simulating `v = prefix`) on the same symbols. Violation iff a
  reachable pair has `δ(x,1) ∈ F` but `δ(y,1) ∉ F` (then `v = prefix·1`
  ends in `'1'`, `w = 0v ∈ L`, `v ∉ L`). The empty prefix gives the
  subtle base case `w = "01"` (n=2), `v = "1"` (n=1).
* **odd closure** (`w ∈ L` starting with `'1'` ⇒ `transduce(w) ∈ L`):
  BFS over triples `(x, y, c)`: `x` = `A`-state on the input read so far,
  `y` = `A`-state on the transducer output emitted so far (one output bit
  per input bit), `c` = carry. The first input bit is forced to `'1'`.
  At every `'1'`-transition whose input-side target is accepting (a
  complete odd word of `L`), the end-of-word carry flush is applied to
  the output side, which must then be accepting.

Both product state spaces are tiny (`q²` and `3q²`), so closure is decided
exactly for the *infinite* language.

## Enumeration

Canonical initially-connected complete DFAs (ICDFAs): transition tables
whose states are numbered in BFS discovery order from state 0 (symbol 0
before symbol 1), enumerated recursively via the standard rule "slot value
≤ (max state used so far) + 1, and state `s` must be discovered before its
own slots begin". This eliminates isomorphic and unreachable-state
duplicates. All `2^q` accepting subsets are tried per table. Table counts
for k=2 symbols: 1, 12, 216, 5248, 160675, ... (q = 1, 2, 3, 4, 5).

Every regular language with a complete DFA of ≤ k states appears (up to
isomorphism) among the canonical q-state ICDFAs for some q ≤ k (minimize,
drop unreachable states, renumber), so running `q = 1..k` is exhaustive
for state complexity ≤ k.

The selftest independently cross-checks the enumerator against a
brute-force canonicity filter over all `q^(2q)` tables for q ≤ 4, and a
`--plain` mode re-runs the whole search without canonicalization as an
end-to-end cross-check.

## Safety nets

* `--selftest` (also run automatically before every search):
  * transducer vs. 64-bit arithmetic `3n+1` on 100 000 fixed-seed
    (xorshift64) random odd `n < 2^60`, plus explicit cases n = 1, 3, 5;
  * even step (drop first char) vs. `n/2` on 100 000 random even `n`;
  * encode/decode roundtrip and membership runner;
  * positive/negative controls for every check: `L = C` (T-closed but
    contains 1 — only the `1 ∉ L` test may fail), `L = C minus {"1"}`
    (even closure must fail exactly at `w="01" → v="1"`), `L = {"11"}`
    (odd closure must fail: T(3)=10 ∉ L), `L = ∅` (closures vacuous,
    nonemptiness fails);
  * enumeration counts vs. brute force.
* Any candidate that passes all four conditions is **independently
  verified**: all members of `L` up to length 40 (capped at 200 000
  members / 5·10⁷ DFS nodes) are decoded to integers and `T(n) ∈ L` is
  re-checked with `unsigned __int128` arithmetic. A verification failure
  aborts the program (checker bug). Verified candidates are printed
  loudly and appended to `discoveries.txt`.

## Build and run

    make mac      # macOS/clang, sequential
    make linux    # Linux/gcc, OpenMP-parallel (outer enumeration split)
    make test     # run --selftest

    ./dfacert 4         # search all canonical 4-state DFAs
    ./dfacert --plain 3 # cross-check without canonical enumeration

Progress goes to stderr (every ~10⁷ DFAs); the machine-readable result
line goes to stdout:

    q=<q>: <count> canonical DFAs scanned, <candidates> candidates, <verified> verified certificates

## Completed results

| q | canonical tables | DFAs scanned (tables × 2^q) | candidates |
|---|-----------------:|----------------------------:|-----------:|
| 1 |                1 |                           2 |          0 |
| 2 |               12 |                          48 |          0 |
| 3 |              216 |                       1 728 |          0 |
| 4 |            5 248 |                      83 968 |          0 |
| 5 |          160 675 |                   5 141 600 |          0 |
| 6 |        5 931 540 |                 379 618 560 |          0 |
| 7 |      256 182 290 |              32 791 333 120 |          0 |
| 8 |   12 665 445 248 |           3 242 353 983 488 |          0 |

Cross-checked with `--plain` for q = 2, 3, 4 (0 candidates in both modes).
The checked q=5--8 run summaries are preserved under `logs/`; their
"canonical DFAs" count includes all `2^q` accepting subsets of each canonical
transition table.

**Conclusion: no regular divergence certificate with ≤ 8 states
exists** under this (LSB-first) encoding. This is consistent with the
Collatz conjecture; a nonzero result would have disproved it.

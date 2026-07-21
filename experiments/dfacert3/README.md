# dfacert3 — regular divergence certificates for Collatz, base-3 MSD-first

Sibling of `../dfacert` (LSB-first base 2). Same idea, mirroring the Busy
Beaver Challenge's CTL/FAR deciders, applied to the Collatz map

    T(n) = n/2      if n is even
    T(n) = 3n + 1   if n is odd

— but with integers encoded in **base 3, most significant digit first**.

## The certificate

A **regular divergence certificate** is a regular language `L` of base-3
encodings of positive integers such that

1. `L` is nonempty,
2. the encoding of `1` is **not** in `L`,
3. `T(L) ⊆ L` (closure under one Collatz step).

If such an `L` exists, the Collatz conjecture is **false**: by induction,
the forward orbit of any member stays in `L` forever, so it never reaches 1.
Conversely, if the conjecture is true no such `L` exists at any size, so
each exhausted DFA size is a genuine negative result — and one *independent*
of the base-2 result, since regularity is not preserved between base-2 and
base-3 encodings of the same set of integers.

## Encoding

`n ≥ 1` is written in base 3, MSD first, no leading zeros. Example:
`12 = 110₃ → "110"`. The set of valid encodings is
`C = {w ∈ {0,1,2}* : w nonempty, w[0] ≠ '0'}`, in bijection with the
positive integers. For each candidate DFA `A` the searched language is
`L_A := L(A) ∩ C`.

Under this encoding, one Collatz step is a string operation:

* **Parity.** `3 ≡ 1 (mod 2)`, so `n mod 2` equals the **digit sum of `w`
  mod 2**. Every product construction below carries this parity bit to know
  which words are even/odd.
* **`n` odd:** `T(n) = 3n+1` and `string(3n+1) = string(n)·"1"` — multiply
  by 3 appends a `'0'`, adding 1 turns it into `'1'`, no carry. A trivial
  one-symbol append.
* **`n` even:** `T(n) = n/2` by MSD-first long division: `r := 0`; for each
  digit `d`: emit `(3r+d) div 2`, set `r := (3r+d) mod 2`. The raw output
  has the same length as the input; its first digit is `d0 div 2`, which is
  `0` iff `d0 = 1` (`d0 ∈ {1,2}` for canonical input). Exactly that one
  possible leading zero is stripped — the next raw digit is
  `(3·1+d1) div 2 ≥ 1`, so one strip always yields a canonical string.
  Example: `12 = "110" →` raw `"020" → "20" = 6`; `4 = "11" →` raw
  `"02" → "2" = 2`.
  **Theorem** (used as an internal assertion, not an assumption): the
  running remainder `r` always equals the digit-sum parity of the consumed
  prefix — both are the prefix value mod 2 — so even inputs end with
  `r = 0`.

## Exact decision procedures (no sampling)

For each DFA `A` (complete, over `{0,1,2}`, start state 0) and each
accepting set `F`:

* **nonempty**: some accepting state is reachable from `{δ(0,1), δ(0,2)}`
  (inclusive) by arbitrary further digits.
* **1 ∉ L**: `δ(0,1) ∉ F` (the string `"1"`).
* **odd closure** (`w ∈ L` with odd digit sum ⇒ `w·"1" ∈ L`): BFS over
  pairs `(x, p)` — `x` the `A`-state reached by some canonical word, `p`
  its digit-sum parity (a digit flips `p` iff it is `'1'`). Two start
  configurations, one per first digit: `(δ(0,1), 1)` and `(δ(0,2), 0)`.
  Violation iff a reachable `(x, 1)` has `x ∈ F` but `δ(x,1) ∉ F`.
* **even closure** (`w ∈ L` with even digit sum ⇒ `div2(w) ∈ L`): BFS over
  quadruples `(x, y, r, p)` — `x` runs `A` on the input word, `y` runs `A`
  on the *canonical* divided output (one output digit `(3r+b) div 2` per
  input digit `b`), `r` the division remainder, `p` the input digit-sum
  parity. The raw output's possible leading zero is handled by the two
  start configurations: first digit `d0 = 2` emits `1` (`y` consumes it);
  `d0 = 1` emits the leading `0`, which is skipped (`y` stays at the start
  state, and the next raw digit is ≥ 1, so `y`'s input stays canonical).
  Violation iff a reachable state has `p = 0`, `x ∈ F`, `y ∉ F`. The
  invariant `r == p` is asserted at every dequeued state (a checker bug
  would abort the run, exit code 5).

Both product state spaces are tiny (`2q` and `4q²`), so closure is decided
exactly for the *infinite* language.

## Enumeration

Canonical initially-connected complete DFAs (ICDFAs) over the 3-letter
alphabet: transition tables whose states are numbered in BFS discovery
order from state 0 (symbol 0 before 1 before 2), enumerated recursively via
the standard rule "slot value ≤ (max state used so far) + 1, and state `s`
must be discovered before its own slots begin". All `2^q` accepting subsets
are tried per table. Table counts for k=3 symbols (OEIS A006690):
1, 56, 7965, 2 128 064, 914 929 500, … (q = 1, 2, 3, 4, 5) — much larger
per state than the base-2 counts (1, 12, 216, 5248, 160675).

Every regular language with a complete DFA of ≤ k states appears (up to
isomorphism) among the canonical q-state ICDFAs for some q ≤ k, so running
`q = 1..k` is exhaustive for state complexity ≤ k.

The selftest independently cross-checks the enumerator against a
brute-force canonicity filter over all `q^(3q)` tables for q ≤ 4, and a
`--plain` mode re-runs the whole search without canonicalization as an
end-to-end cross-check.

## Safety nets

* `--selftest` (also run automatically before every search):
  * string ops vs. 64-bit/`__int128` arithmetic on 100 000 fixed-seed
    (xorshift64) random `n ∈ [1, 2^60]`: `div2str` = `n/2` with remainder 0
    for even `n`; append-`"1"` = `3n+1` for odd `n`; digit-sum parity =
    `n mod 2`; encode/decode roundtrip (plus n = 1..2000 exhaustively);
  * explicit cases incl. the leading-zero divisions `12 = "110" → "20"`,
    `4 = "11" → "2"`, `2 = "2" → "1"`, `10 = "101" → "12"`, and the odd
    steps `T(1)=4`, `T(3)=10`, `T(5)=16`;
  * positive/negative controls for every check: `L = C` (T-closed but
    contains 1 — only the `1 ∉ L` test may fail), `L = all n ≥ 2` (even
    closure must fail exactly, witness `"2" → "1"`), `L = {"12"} = {5}`
    (odd closure must fail: `T(5) = 16 = "121" ∉ L`), `L = {"11"} = {4}`
    (even closure must fail *through the leading-zero branch*:
    `T(4) = 2 = "2" ∉ L`), `L = ∅` (closures vacuous, nonemptiness fails);
  * enumeration counts vs. brute force (q ≤ 4).
* Any candidate that passes all four conditions is **independently
  verified**: all members of `L` up to length 39 (capped at 200 000
  members / 5·10⁷ DFS nodes) are decoded to integers and `T(n) ∈ L` is
  re-checked with `unsigned __int128` arithmetic (39 base-3 digits keep
  `3n+1` inside 64 bits for printing). A verification failure aborts the
  program (exit code 3). Verified candidates are printed loudly and
  appended to `discoveries.txt`.
* Mutation-tested: compiling with either closure check disabled makes the
  q=2 search surface fake candidates which the independent verifier then
  rejects, aborting with exit code 3 — the zero counts below are not
  produced by a vacuous pipeline.

## Build and run

    make mac      # macOS/clang, sequential
    make linux    # Linux/gcc, OpenMP-parallel (outer enumeration split)
    make test     # run --selftest

    ./dfacert3 4         # search all canonical 4-state DFAs
    ./dfacert3 --plain 3 # cross-check without canonical enumeration

Progress goes to stderr (every ~10⁷ DFAs); the machine-readable result
line goes to stdout:

    q=<q>: <count> canonical DFAs scanned, <candidates> candidates, <verified> verified certificates

## Completed results

| q | canonical tables | DFAs scanned (tables × 2^q) | candidates |
|---|-----------------:|----------------------------:|-----------:|
| 1 |                1 |                           2 |          0 |
| 2 |               56 |                         224 |          0 |
| 3 |            7 965 |                      63 720 |          0 |
| 4 |        2 128 064 |                  34 049 024 |          0 |
| 5 |      914 929 500 |              29 277 744 000 |          0 |

Cross-checked with `--plain` for q = 2, 3, 4 (256, 157 464 and 268 435 456
DFAs scanned respectively; 0 candidates in both modes).
The checked q=5 run summary is preserved in `logs/q5.out`; its "canonical
DFAs" count includes all `2^5` accepting subsets of each canonical transition
table.

**Conclusion: no regular divergence certificate with ≤ 5 states
exists** under this (MSD-first base-3) encoding. This is consistent with
the Collatz conjecture and independent of the base-2 result in
`../dfacert`; a nonzero count would have disproved the conjecture.

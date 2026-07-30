# Cyclic descent proof miner

This experiment searches for finite recursive proofs, not for long Collatz
trajectories.

A state `(a,b)` denotes the whole affine family

```text
n(k) = a + b*k.
```

The base point `a` is replayed exactly to `1`. At a recursive step the
certificate chooses `q=2^p`, writes `k=q*t+d`, and follows an exact uniform
path in the Syracuse component graph from

```text
a + b*d + b*q*t
```

to the family belonging to another state at parameter `t`. Since `t<k` for
every `k>0`, ordinary strong induction makes a cyclic state graph sound.
`KontoroC/KontoroC/ComponentCyclicTail.lean` kernel-checks this principle.

Uniform path operations are:

```text
E   forward even branch
O   forward odd branch
I0  inverse even branch, n -> 2n
I1  inverse odd branch,  n -> (2n-1)/3
```

Every operation carries exact coefficient preconditions. Candidate discovery
is bounded, but any emitted certificate is checked independently with
unbounded Python integers and can be translated to Lean.

## Run

```bash
python3 experiments/cyclic_descent/cyclic_descent.py mine \
  --output experiments/cyclic_descent/search_audit.json \
  --z3-check
```

If `root_live` is true, add `--certificate certificate.json`, then replay it:

```bash
python3 experiments/cyclic_descent/cyclic_descent.py verify certificate.json
```

The default universe has `1<=a,b<=96`, reads at most four binary digits per
rule, and permits exact component paths of length at most fourteen inside the
displayed walk box. `bounded-unsat` excludes only this finite grammar. It is
not evidence against Collatz and must never be reported as such.

## Ranked size-change mode

The stronger mode permits a branch to reparameterize its target by
`t -> u*t+v` and asks Z3 for a state-dependent affine natural rank:

```bash
python3 experiments/cyclic_descent/cyclic_descent.py mine-ranked \
  --base-limit 12 --step-limit 12 \
  --path-depth 6 --max-split-power 1 \
  --rank-weight-limit 48 --rank-const-limit 96 \
  --max-reparam-u 12 --max-reparam-v 12 --edge-cap 5 \
  --output experiments/cyclic_descent/ranked_search_audit.json
```

`RankedTailSystem.merge_one` in Lean checks the general size-change
principle. Z3 only proposes a finite certificate; it is never part of the
trusted base. The displayed 144-state, 1,440-edge grammar is UNSAT. This is a
bounded certificate-class result, not a theorem about Collatz.

## Why this is different from a finite bar

A finite list of fixed residue cylinders cannot cover the ordinary locus;
Lean proves that any complete holonomy bar needs unbounded precision. A
cyclic-tail certificate uses finitely many **types** recursively. Each pass
deletes low digits from the ordinary parameter, so the same finite graph
generates charts at arbitrarily high precision. This is exactly the loophole
left open by the no-finite-bar theorem.

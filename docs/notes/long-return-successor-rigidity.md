# Rigidity of the successor six-cell bouncer

**Status (2026-07-30).** Kernel-checked in
`KontoroC/KontoroC/LongReturnSuccessorRigidity.lean`.  The six-phase writer
proposal is closed.  The successor construction is reduced to one canonical
eventual-zero-carry question.  No ray or Collatz counterexample is produced.

## 1. Phase is a sensor, not an actuator

The previous note observed that every split

```text
k+n+1=6
```

has the same source width and output stride.  That equality looked like a
six-letter alphabet whose intrinsic valuation `n` might write the next
residue.  It does not.

Every linked split gives

```text
ReturnBalance(6,g,F,Fnext),
3^R6(g) F = defect(6,g)+2^S6(g) Fnext.             (SR1)
```

For fixed `g,F`, the right coefficient is positive, so `Fnext` is unique.
Lean proves `returnBalance_output_unique` and the direct consequence
`sixPhase_nextSource_unique`: two different enabled phase decompositions from
the same source cannot select different next ordinary sources.

The phase can recognize a different internal exact valuation and provide a
different proof that a source lies in a finite code family.  It cannot alter
the full ordinary boundary map.  Calling it a writer confused an internal
factorization with a control input.

## 2. The homemade coordinates erase to a standard reset program

Define the fixed instruction at time `t`, with `g=g0+t`, by

```text
N_t=S_6(g),
O_t=R_6(g),
delta_t=-defect(6,g).
```

Then SR1 is literally the standard signed reset equation

```text
2^N_t F_(t+1)=3^O_t F_t+delta_t.                  (SR2)
```

`SuccessorSixBalanceRay` stores precisely the natural solutions of SR1.
Lean proves the exact coordinate equivalence

```text
Nonempty SuccessorSixBalanceRay(g0)
  iff exists m : Nat -> Int,
        Follows(successorSixReset(g0),m)
        and forall t, 0 <= m_t.                   (SR3)
```

Every richer `SuccessorSixRay` maps to this scalar object.  Thus neither the
two-rail cofactor nor the one-generation affine compiler provides extra
forward branching once ordinary boundary sources are linked.

## 3. Difference-map rigidity

Two solutions of the same program cancel the affine defect.  Over a prefix
they obey

```text
2^(sum N_t) (F_J-F'_J)
  =3^(sum O_t) (F_0-F'_0).                         (SR4)
```

The two powers are coprime.  Hence `2^(sum N_t)` divides the initial
difference.  Since every `N_t>0`, cumulative binary precision is unbounded,
and a fixed nonzero ordinary difference cannot survive.  Lean imports the
generic checked cocycle and proves

```text
SuccessorSixBalanceRay.initial_unique,
SuccessorSixBalanceRay.source_unique.
```

So this architecture has at most one ordinary ray, not a branching search
tree.

## 4. Exact ordinary-root gate

At every finite depth there is one canonical initial residue modulo the
accumulated power of two.  Write its nested representatives as

```text
r_(J+1)=r_J+2^(sum_(t<J) N_t) q_J,
0 <= q_J < 2^N_J.                                 (SR5)
```

The generic inverse-limit theorem says that one ordinary nonnegative initial
integer can realize all prefixes only if the canonical residues eventually
equal that integer literally.  Equivalently,

```text
q_J=0 for every sufficiently large J.             (SR6)
```

Lean proves `SuccessorSixBalanceRay.eventuallyZeroCarry` and transfers it to
`SuccessorSixRay`.  It also packages the adversarial direction:
`NonzeroCarriesArbitrarilyLate` implies that no successor balance ray exists.

This is why the positive local bit budget does not solve ordinary-root
coherence.  Multiplication can expand the *current quotient*, but the initial
natural has only finitely many nonzero binary digits.  A language emitting
fresh nonzero digits forever specifies a 2-adic address.

## 5. Construction target after the audit

There is now one sharp counterexample program rather than a vague grammar
search:

1. Prove the canonical carries of `successorSixReset(g0)` are eventually
   zero for some `g0>=3`.
2. Prove its canonical signed quotient chain is nonnegative at every stage;
   by SR3 this produces the unique scalar natural ray.
3. Recover the required two-rail witnesses—or prove that the full-return ray
   automatically supplies them.
4. Compile each affine return into the literal legal Collatz word and connect
   the infinite sequence to the existing counterexample consumer.

The dual termination target is equally exact: prove the canonical carries
are nonzero arbitrarily late (or the residues are unbounded), which closes the
entire successor six-cell architecture without searching individual seeds.

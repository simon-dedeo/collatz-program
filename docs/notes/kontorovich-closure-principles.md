# Closure principles for the Kontorovich challenge

This note is a design constitution for the counterexample search.  It was
written after the first exact quadratic-norm transition made the main danger
plain: an arithmetic type can survive one outward bouncer step while the
output immediately fails to decode another legal instruction.  Finding more
such points is not the same problem as finding closure.

No counterexample or infinite orbit is claimed here.  Identities called
exact below are replayed by
`experiments/kontorovich/unit_charge_norm_opcode.py`; the proposed search
rules are research strategy.

## 1. The target is a public self-map, not a sequence of witnesses

Let `T` be the accelerated odd Collatz map, or let `P` be one of the exact
partial macro maps already proved to consist of genuine `T`-steps.  A useful
closure certificate must have:

1. a finitely described state set `S` and an ordinary-positive encoding
   `E : S -> N`;
2. a decoder, or an equivalent canonicality theorem, recovering every piece
   of state which affects the next instruction from the public integer
   `E(s)`;
3. a total update `f : S -> S` and positive return time `tau(s)` with the
   exact identity

   ```text
   T^tau(s)(E(s)) = E(f(s));
   ```

4. exact valuation equality at every intermediate division, not merely the
   required divisibility;
5. one ordinary starting state `s0`, not an infinite stack of successively
   chosen CRT residues; and
6. a finite proof that its orbit never reaches `1`--for example strict growth
   at every macro return, or a nontrivial exact cycle.

This is a semiconjugacy or invariant-graph target.  In algebraic-geometric
language, the accepted-transition correspondence must contain a component on
which source-to-target is the graph of a deterministic, integer-preserving
self-map.  Isolated integral points, rational points on a quadric, and
Zariski-dense representability do not provide that graph.

## 2. Publicity: certificates may have coordinates, hardware may not

Auxiliary coordinates are useful for proofs, but the Collatz map sees only
one integer.  A quadratic representation

```text
r = x^2 + 31*u^2
```

can certify that `r` belongs to an invariant arithmetic type.  The particular
pair `(x,u)` cannot act as hidden program memory unless it is canonically and
arithmetically recoverable from `r`, and the next pair is proved to be the
canonical pair for the next integer.  Multiplying a representation by a Pell
unit or a class-group element while leaving its norm unchanged changes no
public Collatz state.

Finite type labels can still be useful when they are properties of the public
integer--for example a genus or ring-class character--rather than a choice of
representation.  The working test is simple:

> If two different auxiliary states encode the same integer but prescribe
> different next instructions, the proposed language is not a language of
> the Collatz hardware.

## 3. Self-synchronization is the immediate closure gate

For the normalized charge bouncer write

```text
R = C-D,
y_t = A^g_t R r_t,
g_(t+1) = h_t,
H_m = (C^m-D^m)/R.
```

One accepted step with defect opcode `m_t` and recharge opcode `h_t` obeys

```text
2^(23m_t+154h_t) r_(t+1)
  = 3^(17m_t+114g_t) r_t + H_(m_t).              (CP1)
```

But CP1 alone is not the decoder.  A chain additionally needs

```text
v2(A^g_t R r_t + 1) = 23m_t,                     (CP2)
v2(3^(17m_t+114g_t)r_t + H_(m_t))
  = 23m_t+154h_t,                                 (CP3)
```

and the output must satisfy CP2 for the *next* `m`.  Oddness of
`r_(t+1)` makes CP3 exact; CP2 is the separate boundary-synchronization
condition.

This distinction kills the temptation to equate type preservation with
closure.  The first exact `N_31` transition preserves the input, quotient,
and output type and grows from 184 to 193 decimal digits, but its next
collision has valuation `153`; after the 23-bit defect its recharge remainder
is `130 (mod 154)`.  It is a genuine outward typed step and a genuine closure
failure.

Hence the entry ticket for a new lane is now **automatic next-opcode
generation**.  Representation searches which leave CP2 random are diagnostic
only and should not consume a large computation budget.

## 4. Opcode chains form an exact affine semigroup

Simon suggested chaining opcodes.  The fundamental version is to compose the
symbolic transformations, rather than to hunt a longer isolated chain.  Put

```text
P_t = 23m_t+154h_t,
Q_t = 17m_t+114g_t,
M_t = [[3^Q_t, H_(m_t)],
       [0,      2^P_t   ]].
```

Then CP1 is the projective action of `M_t` on `(r_t,1)`.  For a word of
length `N`, exact multiplication gives

```text
2^(sum P_t) r_N = 3^(sum Q_t) r_0 + K_W,

K_W = sum_i H_(m_i)
      * product_(j<i) 2^P_j
      * product_(j>i) 3^Q_j.                       (CP4)
```

This turns opcode chaining into three theorem-shaped searches:

- find two legal words whose matrices satisfy an exact rewrite or conjugacy;
- find a substitution `sigma` and integer embeddings `E_n` for which
  `M_(sigma(W)) E_(n+1) = E_n M_W`;
- find an invariant family of dyadic boundary cylinders on which the matrix
  product and CP2 agree automatically.

There is a particularly clean backbone.  Remove recharge and define

```text
J_m = [[C^m, H_m],
       [0,   D^m]].
```

The geometric debris has the addition law

```text
H_(m+n) = C^n H_m + D^m H_n,
```

so, with the displayed order,

```text
J_n J_m = J_(m+n).                                 (CP5)
```

All defect-only blocks therefore collapse to one additive clock.  They also
share the signed fixed point `r=-1/R`, since the coordinate `z=Rr+1`
conjugates their affine action to multiplication by `(C/D)^m`.  This explains
both the strength and limitation of negative-cycle shadows: the defect
skeleton is integrable, not computationally rich.

The possible programming content lies in the recharge scalings inserted
between the `J_m`.  They are the only source of noncommutativity and of the
correction debris which must be banked.  Future opcode-chain search should
therefore look for exact relations in this *decorated* semigroup, or prove it
free/contracting in a relevant class.  Enumerating words without exploiting
CP4--CP5 is too blind.

## 5. A finite program must pay its address bill

An accepted block consumes an exact dyadic cylinder of width
`23m+154h`.  Fresh CRT selection at each generation pays that address bill
with an infinite preloaded 2-adic tape.  A positive ordinary program instead
needs a finite mechanism which consumes a low-order instruction and creates
enough new, publicly decodable structure to pay the next bill.

This is an information/codimension balance, not currently a theorem.  It is a
useful kill test:

- every large exact valuation is a constraint whose source must be named;
- an unbounded opcode must be computed from existing public payload, not
  supplied as a new parameter;
- a parameter that loses one independent residue class per step is a 2-adic
  compiler unless another part of the state regenerates that freedom; and

- positive outward drift is not repayment.  The bouncer already grows; its
  one-step witness shows that scale can grow while synchronization dies.

This is the arithmetic version of a self-delimiting tag program.  The natural
machine is mixed-radix: it reads a low binary prefix through `v2` and writes a
ternary prefix through the large factor `3^(114h)`.  A plausible closure
mechanism is therefore a two-stack or round-trip transducer which converts
the emitted ternary register into the next binary delimiter.  A complete
write alphabet without this feedback is not enough.

## 6. Closure should be an identity before it is a search hit

The preferred order of work is now:

1. **Choose an observable state and decoder.**  State exactly which integer
   valuation or canonical residue determines each opcode and finite type.
2. **Derive the symbolic return.**  Compose opcode matrices and expose the
   debris term, using CP4 and the Lucas law CP5 before specializing numbers.
3. **Propose a self-map.**  The output parameters must be explicit functions
   of the input parameters; no fresh representation, CRT lift, or prime is
   allowed.
4. **Prove exact synchronization.**  Establish both valuation divisibility
   and the odd cofactor which makes it equality.
5. **Pass the ordinary-integer gate.**  The initial encoding is one finite
   positive integer and every future state is generated forward.
6. **Only then search.**  Computation should solve the finite coefficients of
   the proposed identity, find a short decorated-semigroup relation, or
   falsify a whole ansatz class.

A useful practical rule is: do not launch a large job unless a success would
produce either (a) an exact self-map, (b) a finite rewrite system with a proved
nonhalting invariant, or (c) a theorem-level obstruction which closes the
entire ansatz.

## 7. Current consequences and next attacks

The quadratic `d=31` lane remains useful, but its role has changed.  The
identity `R=7706^2+31*1407^2` removes a local opcode tax and CP1 exposes a
small payload.  Further isolated norm points or even a two-step typed point
do not address the bottleneck.  The incomplete two-step parameterization is
retained as a diagnostic, not promoted to the main search.

The next fundamental attacks are:

- **Decorated-semigroup relations.**  Classify short relations or
  conjugacies among the `M(m,g,h)`, after quotienting the exact CP5 defect
  backbone.  A survivor must include the CP2 boundary cylinders, not merely
  matrix equality.
- **Debris endogenization.**  Use
  `H_(m+n)=C^nH_m+D^mH_n` to make collision debris part of the next opcode
  state rather than an error corrected by a fresh CRT word.
- **Mixed-radix feedback.**  Treat the reversible bouncer as a binary reader
  and ternary writer.  Seek an exact round trip implementing the two remote
  stack operations needed by a tag/counter program.
- **Public formal-group coordinates.**  A 2-adic or algebraic group law is
  useful only if its parameter is a canonical function of the integer and its
  endomorphism makes CP2 automatic.  Motions among invisible norm
  representations are rejected.
- **Adversarial no-go transfer.**  Ask the companion Lean worker to turn each
  proposed identity into its cheapest universal theorem or obstruction before
  scaling a search.

The intended change is methodological: search for a graph before searching
for its points, and search for an opcode algebra before searching for its
programs.

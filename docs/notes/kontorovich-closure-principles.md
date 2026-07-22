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

## 0. Five conservation laws for closure

These are the fundamental filters to apply before any large search.

1. **Semantic conservation.**  Every abstraction layer must sit in a
   commuting diagram with the literal accelerated Collatz map.  An affine
   state called “ordinary” is not enough: its encoder, valuation word, and
   literal endpoint must be explicit.
2. **State conservation.**  The future may depend only on information
   canonically recoverable from the current integer.  A fresh norm
   representation, CRT lift, or external clock is an illicit second tape.
3. **Synchronization conservation.**  Consuming an exact `2`-adic delimiter
   spends address information.  A closed program must regenerate the next
   delimiter, including its phase, from its surviving public payload.
4. **Endomorphism before orbit.**  Reproduction is an exact self-map or
   semiconjugacy on a public type.  More isolated represented points—even
   consecutive ones—do not approach that objective unless they expose the
   depth-independent update.
5. **Control, not merely scale.**  Outward drift and a favorable bit budget
   show capacity, not programmability.  The surplus must write the *specific*
   next opcode.  This is the distinction between a growing amplifier and a
   reproducing glider.

Opcode chaining is judged by the same laws.  A matrix relation is useful only
when its source cylinder, public decoder, and literal Collatz word also
compose.  The search target is therefore a semantic monoid action, not just a
semigroup collision.

There is already one rigorous lower bound on the architecture.  Lean commit
`e8585c4` excludes every eventually periodic arithmetic bouncer schedule.
Consequently a controller whose future opcode depends only on an autonomous
finite control state cannot work: after a transient its state, hence its
opcode stream, would cycle.  Any surviving program must expose at least one
**unbounded public register** which continues to affect control.  This is the
right lesson to import from tiny counter and tape languages.  Universality is
not required to refute Collatz, but finite control alone is provably too weak
for this bouncer.

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

### 3.1 The canonical public-cofactor machine

There is a more fundamental state than the normalized norm payload.  Every
accepted boundary has a unique expression

```text
y=D^m w-1,          m>0, w>0 odd,                  (PC1)
```

because `23m=v2(y+1)`.  With `M=3^33(C-D)`, the fixed public register is
exactly the pair of endpoint conditions

```text
M | D^m w-1,        F | D^m w.                    (PC2)
```

Write the next state as `y'=D^m' w'-1`.  Eliminating the odd collision
quotient gives

```text
A^h(C^m w-1)=B^h(D^m' w'-1),                      (PC3)
```

or

```text
B^h D^m' w'=A^h C^m w-(A^h-B^h).                 (PC4)
```

Inside the normalized charge arithmetic, this is not merely another
necessary Diophantine equation.  For positive
`m,h,m'`, odd positive `w,w'`, and PC2 at both endpoints, coprimality of
`A` and `B` makes

```text
q=(C^m w-1)/B^h=(D^m' w'-1)/A^h
```

an odd integer.  The normalized charge collision is then

```text
D^m(C^m w-1)=D^m B^h q,
```

so its valuation is exactly `23m+154h`, and its normalized output is
`A^h q=D^m'w'-1`.  Lean commit `5a9324b` proves that PC1--PC3 are an exact
public-coordinate presentation of the arithmetic `ChargeBouncerStep`
surrogate.  It proves coordinate uniqueness, builds the positive odd quotient
by coprime divisibility, reconstructs that arithmetic structure, and proves
the forward balance for every such step presented in these coordinates.  It
does **not** by itself produce a `WordLegal` Collatz execution.

This should now be the primary compiler language.  A closure ansatz is one
finite formula for positive odd `W(s)` and opcode updates
`(m,h,s)->(m',f(s))` satisfying PC2--PC3 identically.  Norms and class forms
may certify candidate values of `w`; their noncanonical coordinates no longer
pretend to be state.  An infinite forward solution of this recurrence starts
from one normalized integer `D^m w-1`, so the ordinary-versus-2-adic gate is
visible rather than deferred; a separate finite-level encoder must still turn
that normalized state into the literal odd Collatz state.

### 3.1.1 The semantic descent is one more programming layer

The normalized value `y` is not the Collatz integer, and neither is the
quantity historically named `ordinary_start` in the glider worker.  The
complete research-side coordinate chain is

```text
public y -> charge packet -> unit packet -> level-two packet
 -> level-one glider packet -> breakoff k -> literal odd Collatz x.
```

The level-two packet `K` maps affinely to the intermediate breakoff state

```text
k = 5841333965851681082096808370372608*K
    -76096151213931339145826796194905.             (PC5)
```

The final router conversion is not affine.  With

```text
r=v3(8k-1)-2,
x=-1+2^(r+1)*(8k-1)/3^(r+1),                      (PC6)
```

the rail length `r` varies.  Consequently monotonicity of `y` or `k` is not a
global monotonicity theorem for arbitrary encoded Collatz states; literal
growth must be proved edge by edge or on the eventual incoming-link type.

The exact symbolic word grammar is nevertheless finite:

```text
charge cell N      -> unit cells [N,1]
level-two cell N   -> level-one gliders [1,2,1^N]
level-one glider N -> breakoff gates [E,H,E^N]
```

The final gates emit their literal valuation words through the already exact
router.  The bounded
[`unit_charge_semantic_compiler.py`](../../experiments/kontorovich/unit_charge_semantic_compiler.py)
artifact reconstructs all 54 members with `m,h,m'<=3`, emits 14,057
accelerated instructions, and independently replays every word by direct
`3x+1` arithmetic.  This repairs the regression seam but remains bounded;
the universal composition theorem is now the formal target.

### 3.2 Two canonical charts form an `S`-unit ladder

After the first accepted return, the same public integer also has a canonical
ternary chart.  Put

```text
g=v3(y)/114,       y=A^g R r,       R=C-D.
```

Here `g` and the scalar `r` are functions of `y`; only a later *representation*
of `r` as a quadratic form would be noncanonical.  Combining this chart with
PC1 turns one transition into two adjacent unit equations:

```text
D^m w = 1 + A^g R r,                              (SL1)
C^m w = 1 + B^h R r'.                             (SL2)
```

The next state supplies the next copy of SL1,

```text
D^m' w' = 1 + A^h R r'.                           (SL3)
```

Thus an orbit is an alternating positive `S`-unit ladder

```text
(g,r) --SL1-- (m,w) --SL2-- (h,r') --SL3-- (m',w') ...
```

PC3 is obtained by eliminating `r'`; CP1 is obtained by eliminating `w`.
They are complementary projections of the same square.  This is a better
spatial realization of Simon's splash picture than either projection alone:
`w` is the sacrificial binary-address rail, `r'` is the surviving ternary
rail, and closure means that the next square is produced by the previous one.

The constructive algebraic target can now be stated as a Vieta-, cluster-, or
renormalization-style move on whole positive integer squares SL1--SL3.  Such a
move must preserve the canonical public charts; moving among multiple norm
representations of a fixed `r` still does nothing.  The determinant-four
resonances `A^23=3^4 C^154` and `B^23=D^154` are the obvious scale at which to
look for a nontrivial square-to-square renormalization.

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

The independent Lean audit has already removed the smallest collision
targets.  A single decorated matrix uniquely recovers its three opcodes.  For
two legal letters with fixed initial/final recharge phases, the diagonal
entries recover total defect length and the intermediate recharge.  At those
fixed values, moving one defect cell from the second letter to the first
changes the off-diagonal entry by

```text
(A^h-B^h) C^e D^i > 0.
```

Thus fixed-boundary one- and two-letter products collide only trivially.
Longer equality searches remain logically open but are no longer the leading
constructive bet.  A conjugacy or renormalization can map *different* matrix
products through different public encodings; that is the more appropriate
self-reproduction target.

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

### 4.1 Seven gates for a useful opcode chain

“The matrices multiply” is only the first of seven increasingly strong
claims.  Every proposed chain should be classified at the first gate it
fails:

1. **Affine composition:** CP4 holds for the word.
2. **Type composition:** every target phase is the next source phase.
3. **Cylinder composition:** the output family lies in the next exact dyadic
   source cylinder; divisibility is not reselected by CRT.
4. **Causal decoding:** the next word or opcode is a function of public state,
   not an externally supplied clock.
5. **Ordinary realization:** the nested cylinders contain one nonnegative
   ordinary integer, equivalently their canonical residues eventually
   stabilize rather than merely converging 2-adically.
6. **Semantic composition:** the full hierarchy expands to one legal literal
   accelerated-Collatz word with the advertised endpoint.
7. **Nonhalting closure:** a finite invariant proves that the process can
   continue forever and never reach `1`.

This ladder separates two different uses of chaining.  Equal products or
conjugacies are algebraic rewrite rules at gates 1--2.  A counterexample is a
self-interpreter passing all seven.  Computation is most valuable when it
tests one named gate for an entire parametric family.

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

The canonical cofactor language makes the bill quantitative.  At fixed
public control `m`, a branch `(h,m')` reads

```text
P=154h+23m'
```

low binary bits of its canonical tail.  Exact valuation decoding makes
distinct branch cylinders prefix-disjoint, and their Kraft mass is

```text
sum_(h,m'>=1) 2^-(154h+23m')
  = 1/((2^154-1)(2^23-1)).
```

The shortest instruction therefore costs 177 bits.  This explains why
ordinary sampling almost never sees the language, but it is not itself a
no-go.  On a branch with `m'=m`, the surviving-tail coefficient obeys the
exact favorable inequality

```text
3^(114h+17m) > 2^(154h+23m),
```

because `3^114>2^154` and `3^17>2^23`.  The hardware has scale capacity to
replace the address it consumes.  The missing result is *semantic capacity*:
turning that extra scale into the particular next low-bit delimiter rather
than uncontrolled carry noise.

This is the arithmetic version of a self-delimiting tag program.  The natural
machine is mixed-radix: it reads a low binary prefix through `v2` and writes a
ternary prefix through the large factor `3^(114h)`.  A plausible closure
mechanism is therefore a two-stack or round-trip transducer which converts
the emitted ternary register into the next binary delimiter.  A complete
write alphabet without this feedback is not enough.

### 5.1 The ordinary-address gate is a coboundary problem

There is a more constructive alternative to watching longer dyadic prefixes.
In the canonical cofactor coordinate, any opcode chain has

```text
2^P_i w_(i+1)=3^Q_i w_i+s_i,
s_i=2^(154h_i)-3^(114h_i).                        (CP6)
```

Backward unrolling gives one forced 2-adic candidate

```text
w_0 = -sum_(i>=0)
  s_i * 2^(sum_(j<i) P_j) / 3^(sum_(j<=i) Q_j).   (CP7)
```

The series converges 2-adically because every `P_i>0`.  An ordinary program
requires this value not merely to exist in `Q_2`, but to be the embedded
positive integer satisfying the public register conditions.  This reframes
the search as **rationality engineering**:

The hardware already exposes a near-coboundary.  With
`a_i=2^P_i/3^Q_i`, direct cancellation gives

```text
-s_i/3^Q_i = 3^(-17m_i)-a_i*2^(-23m_(i+1)).       (CP8)
```

The obstruction is therefore not arbitrary debris: the two ends use
different canonical charts, ternary on entry and binary on exit.  A genuine
resonant glider must align those two potentials across successive cells.

- a p-adic irrationality theorem closes a whole scheduled family at once;
- a construction should try to make the summand a public coboundary
  `Phi_i-a_i*Phi_(i+1)`, so CP7 telescopes to a
  rational—and ultimately integral—initial state; and
- finite prefix agreement is useful only as evidence for such a telescoping
  identity or for a nonzero-lift obstruction.

This is the algebraic form of “splash, scrub, reseed.”  The collision debris
must be banked as the difference of two successive public potentials, not
cancelled by a newly chosen future residue.  Fixed-rate counter policies tend
to produce partial-theta series; payload-dependent variable jumps are useful
only if they change CP7 into an exact coboundary or another provably rational
series.

The determinant-four phase-up family demonstrates this exactly.  For every
fixed `k>=1`, `m_i=m_0+4ki` and `h=391k+1` turn CP7 into a nonzero rational
multiple of

```text
f_(3^(68k)/2^(92k))
  (2^(23m_0+154h)/3^(17m_0+114h)).                (CP9)
```

Lean commit `466e381` checks the public-step bridge, completed `Q_2` series,
and coefficientwise CP9 identification.  The inspected main theorem of
Väänänen--Wallisser (1989), pp. 200--201, makes CP9 irrational under an exact
audited size inequality.  Thus the fixed-jump counter is closed with that
external theorem as the explicit seam.  A surviving resonant controller must
change its jump or direction from public payload infinitely often.

There is a second, more elementary constraint on opcode chaining.  Write

```text
tau_m   = C^(-m),            beta_m = D^(-m),
a_i     = B^(h_i) D^(m_(i+1)) / (A^(h_i) C^(m_i)),
Delta_m = tau_m-beta_m < 0.                          (CP10)
```

Dividing PC4 gives the exact **typed interface law**

```text
w_i-tau_(m_i) = a_i (w_(i+1)-beta_(m_(i+1))).       (CP11)
```

Thus every ordinary forward cell has the same type: ternary entry potential
to binary exit potential.  It is not a binary-to-ternary adapter.  If
`A_j=product_(i<j) a_i`, a word of `N` cells satisfies

```text
w_0-tau_(m_0)
  = sum_(1<=j<N) A_j Delta_(m_j)
      + A_N (w_N-beta_(m_N)).                       (CP12)
```

Every internal interface tax in CP12 is strictly negative in the ordinary
real ordering, since `3^17>2^23`.  Consequently no choice of recharges,
jumps, or directions can make a multi-cell word into a *clean* bare chart adapter
by termwise cancellation: chaining more copies of the same opcode type only
accumulates the ternary/binary mismatch.  This does not rule out a nonlocal
2-adic cancellation or an ordinary orbit.  It does rule out a tempting but
weaker closure plan in which a clever four-letter word is expected to
telescope solely because its phase returns.

This tax is not a new mysterious constant.  It is exactly the normalized
defect polynomial already found in the opcode semigroup:

```text
Delta_m = -(C-D) H_m/(C^m D^m),
H_m=(C^m-D^m)/(C-D).                              (CP12a)
```

The Lucas law `H_(m+n)=C^n H_m+D^m H_n` explains both facts at once:
recharge-free opcode chaining merely banks more positive defect and remembers
only total length.  Cancellation requires an operation outside that positive
semigroup.  The signed intercept in a parallel-branch conjugacy is a concrete
place where such an opposite correction can enter.

The constructive object must therefore carry an adapter in its payload.  If
`Phi_i=tau_(m_i)+e_i` is a proposed public potential, its correction rail must
obey

```text
e_i = a_i (e_(i+1)+Delta_(m_(i+1))).                (CP13)
```

and make `Phi_i` an ordinary positive cofactor at every state.  An affine
resonant embedding, paired rail, or turnaround is useful precisely when its
intercept supplies the missing positive correction in CP13.  This is a more
discriminating opcode type system than matching source and target phases:
period four is merely the first schedule not excluded by the present
multi-theta estimate, whereas a genuine program needs a public CP13 adapter.

The determinant-four conjugacies carry a second conserved-resource test.
Their two charts begin `2622k` phase units apart but end only `2618k` apart.
Composing such parallel cells therefore requires

```text
1311 k_(i+1)=1309 k_i.                            (CP14)
```

Since the two coefficients are coprime, `N` cells force `1311^N` to divide
the first positive jump.  An infinite ladder of these cells is impossible
before any tail arithmetic is considered.  In the spatial metaphor, the
current resonant opcode moves a boundary but consumes chart separation.  A
reproducing instruction set needs a phase booster with the inverse expansion,
not just a richer word over phase-up and phase-down cells.

At word level, that booster has a necessary signed-area law.  If two
length-`N` words have equal total binary and ternary exponents and their
boundary phase differences are `d_0,...,d_N`, elimination of the recharge
differences gives

```text
1311 d_N-1309 d_0=-2 sum_(0<i<N) d_i.             (CP15)
```

Positive endpoint separation can therefore be regenerated only by crossing
the charts somewhere inside the word.  The two-opcode family
`W_r=[(r,h0,L-r),(L-r,h1,r+d)]` realizes the minimal sign pattern
`(d,-d,d)` and has total gains independent of `r`.  The bounded exact
phase-swap artifact verifies two adjacent *parallel* affine conjugacy squares
at `L=4,d=h0=h1=1`.  It also proves that their embedded next-source tail
strictly outruns the current output in both constant and slope, so the squares
do not hand off along the advertised conjugacy.  The sign crossing solves the
exponent budget, not the typed/cylinder handoff.  A live construction must
first make the node-gauge correction compose, and then convert the exhausted
middle phase into a larger public `L'` rather than load a fresh delay
externally.

### 5.2 Chaining is a renormalization, not yet a program

The failed conjugacy reveals a distinction which every opcode search should
make first.  A compiled word has one source cylinder and one output ray,

```text
x=rho+2^P u  ->  y=sigma+3^Q u.                  (CP16)
```

To execute a second word with source `rho'+2^P' v`, the actual dynamic
handoff is

```text
sigma+3^Q u = rho'+2^P' v.                       (CP17)
```

This is not the conjugacy equation between two parallel maps.  Since the two
coefficients are coprime, CP17 always has an integer solution lattice.  Once
one nonnegative base pair `(u_0,v_0)` is chosen, all its forward solutions are

```text
u=u_0+2^P' t,       v=v_0+3^Q t.                 (CP18)
```

The updated phase-swap artifact constructs and replays CP18 for both adjacent
word pairs.  Thus the Lean no-link theorem has a precise scope: the
*conjugacy-selected* next source never meets the current output.  Other finite
links exist, but they pay for themselves by selecting a fresh dyadic cylinder.

This is the fundamental renormalization law for opcode chaining.  The map on
surviving parameters in CP18 has exactly the same form as the original
hardware: read a binary address, then write an odd ternary-scaled tail.  Any
finite list of compatible opcodes can therefore be compiled into a larger
macro-opcode.  That fact is almost free and is not evidence of reproduction.
An infinite prescribed chain again selects one 2-adic address; closure begins
only when the parameter transducer generates its own future address from one
ordinary public state.

There is also a sharp obstruction to the simplest proposed repair.  Suppose
the parameter of node `i` were encoded for *every* natural register value by

```text
u_i=c_i+s_i z,
```

and one dynamic handoff used a total affine update
`z'=a_i z+b_i`, with positive integral slopes.  Comparing coefficients in
CP17 forces

```text
3^Q_i s_i = 2^P_(i+1) s_(i+1) a_i.              (CP19)
```

Because `P_(i+1)>0`, CP19 strictly spends the 2-adic valuation of `s_i` at
every step.  Multiplying through `N` steps shows that
`2^(sum P_i)` divides the initial slope `s_0` after cancellation of odd
powers of three.  No fixed positive `s_0` can support arbitrarily many
steps.  This elementary derivation has been sent to the Lean adversary for a
kernel-checked finite-divisibility theorem.

So a one-register, everywhere-defined affine node gauge cannot be the
reproducer, even with infinitely many phase labels.  A survivor must do at
least one genuinely programming-like thing:

- restrict to a decoded source cylinder and thereby pop binary digits;
- use a nonlinear public update which writes replacement address bits; or
- move the address budget between two or more public rails, then swap their
  roles at a regenerative collision.

This is the exact reason the Brainfuck/tag-system analogy is more than
decoration.  The missing operation is not another affine opcode; it is a
public stack rotation or base-conversion round trip.  Searches should now ask
for that operation coefficientwise before enumerating instruction words.

### 5.3 Two Kraft measures forbid a complete all-outward ISA

There is an important limit on the multi-branch escape.  One might try to
partition every tail into a complete prefix code of macro words and demand
that every branch be outward.  Kontorovich--Sinai negative drift has a short
coding-theoretic form which makes this impossible.

For an accelerated valuation word `w=(k_1,...,k_n)`, put
`S(w)=sum k_i`.  Its ordinary dyadic cylinder weight is

```text
p(w)=2^(-S(w)),
```

because `sum_(k>=1) 2^(-k)=1`.  There is a second exact Kraft weight

```text
q(w)=3^n/4^S(w),
```

because the one-letter weights also sum to one:

```text
sum_(k>=1) 3/4^k = 1.                            (CP20)
```

Consequently every prefix-free family has `sum q(w)<=1`, just as it has
`sum p(w)<=1`.  But a word has outward affine slope exactly when

```text
3^n > 2^S(w),
```

and on such a word

```text
q(w)/p(w)=3^n/2^S(w)>1.                          (CP21)
```

If a prefix code were complete in ordinary dyadic measure, then
`sum p(w)=1`.  If all its leaves were outward, CP21 would give
`sum q(w)>1`, contradicting the tilted Kraft inequality.  This argument does
not require a bounded stopping time; it is the exact nonnegative-martingale
change of measure behind the drift `log(3/4)<0`.  A kernel formalization has
been requested before promoting it to the headline result map.

This corrects an overly ambitious constructive idea.  The parity-complete
splash decoder can be total, or a branch language can be uniformly outward,
but it cannot be both on every prefix leaf.  The route to a counterexample is
therefore a **thin trapping language**:

1. an explicit ordinary public state lies in a proper prefix sublanguage;
2. its payload-decoded branch is outward;
3. the output returns to the same sublanguage by a finite symbolic rule; and
4. the omitted shrinking/halting branches are provably inaccessible from
   that invariant.

Such a set may have zero ordinary density—that is exactly the sparse-program
possibility in Kontorovich's challenge.  The advantage over prescribing one
itinerary backwards is that membership and forward invariance start from one
ordinary integer, so no infinite 2-adic tape is preloaded.  Computation should
now search for algebraic trapping predicates on the complete splash payload
map, not for an all-outward completion and not for longer individual traces.

The right finite proof object is therefore not a long orbit but a **thin-trap
certificate**.  In the already formalized canonical splash state space it
consists of a public predicate `L`, one explicit ordinary state `x_0` in `L`,
and a public successor rule `f` such that, for every `x` in `L`,

```text
x.next = some (f x),      L(f x),      start(x)<start(f x).   (CP22)
```

Iteration of `f` then constructs the required infinite outward orbit without
choosing an itinerary or an infinite address in advance.  The mathematical
content is all in making `L` small enough to evade the two-Kraft obstruction
but rigid enough that CP22 is a finite symbolic identity.  This is the closure
analogue of a loop invariant in program verification.  It also clarifies the
role of opcode chaining: an opcode is useful only when it preserves `L` after
writing its next address; merely having a solvable input congruence is not an
instruction.

There is a quantitative version worth keeping as a search heuristic.  On any
prefix-free leaf family,

```text
sum_w p(w) * (3^length(w)/2^sum(w)) = sum_w q(w) <= 1.       (CP23)
```

Thus if every accepted macro has slope at least `lambda>1`, its ordinary
cylinder mass is at most `1/lambda`.  After `N` closed macro generations a
uniform-`lambda` trap occupies at most `lambda^(-N)` of the ambient dyadic
address space.  A genuine glider is therefore forced to be progressively
thin; failure to find it by density sampling is expected, while a proposed
finite-width invariant should be viewed suspiciously.  CP23 does not forbid
one explicit ordinary seed in the intersection.  It says that the seed must
be produced by a self-writing invariant, not found by typicality.

### 5.4 Mixed-base reproduction certificates and a uniform-block no-go

Yolcu--Aaronson--Heule's 11-rule mixed binary/ternary string system gives a
second exact closure interface.  A literal **context loop**

    u ->+ left ++ u ++ right                             (CP24)

is already a finite nontermination certificate: the same derivation can be
replayed inside its reproduced occurrence of u forever.  Their Theorem 3.17
then converts nontermination of this particular rewriting system into failure
of Collatz; that published equivalence is an explicit external seam.

For the natural one-`/`, one-later-`.` configuration language, however, a
*proper outer* context is the wrong spatial target.  The rules preserve the
number of boundary markers and act only on the interior side of each marker;
their two outer flank lengths therefore do not change.  Lean commit
`ef1b888` proves the generic consequence: if
`endpoint=left++start++right` preserves the marker counts and both flank
lengths, then `left=right=[]`.  The Python artifact checks those four
diagnostics on all 825,708 raw rule applications in its complete bounded
graph and finds no violation.  The universal per-rule YAH bridge is still a
formalization seam.  Constructively, CP24 should now be read as a certificate
interface and cycle detector, not the primary glider ansatz.  The spatially
live object is an *internal* active template moving or reproducing inside a
fixed boundary frame.

The genuinely scale-changing version uses a nonerasing word morphism sigma.
If every one of the 11 rules has a nonempty checked simulation

    sigma(lhs) ->+ sigma(rhs),                          (CP25)

and one seed derivation satisfies

    u ->+ left ++ sigma(u) ++ right,                    (CP26)

then applying sigma to CP26 and replacing each image rule by CP25 produces
the next nonempty derivation at every scale.  CP25--CP26 are a finite morphic
glider certificate: they formalize reproduction rather than an orbit prefix.
Commit `1b3459d` kernel-checks this generic relation-theoretic construction,
including accumulated contexts and a nonempty rewrite chunk at every scale.
The concrete 11-rule certificate and the published YAH-to-Collatz implication
remain separate.  Commit `b733caa` pins that concrete seven-symbol, 11-rule
carrier in Lean, proves context closure and marker-count preservation, and
specializes both certificate consumers to it; certificate replay and the
external equivalence remain separate.
Commit `442826d` connects any actual trace on that carrier to the boundary
filter, deriving both marker-count equalities and taking only the two flank
equalities as certificate inputs.

The exact [yah_context_loop.py](../../experiments/kontorovich/yah_context_loop.py)
worker now checks both certificate forms one literal rule application at a
time.  It pins the authors' ASCII rule table, replays their 12-to-1 example
with auxiliary-value preservation and all eight dynamic values, and performs
three scoped classifications:

- all 5^5=3,125 delimiter-fixing letter morphisms are checked; the identity
  is the only rule-simulating morphism;
- all 25^5=9,765,625 delimiter-fixing uniform two-symbol block morphisms are
  exhausted by exact constraint propagation; none simulates all 11 rules;
- the entire induced rewrite graph on 513,916 words of length at most eight
  with one ordered delimiter pair is acyclic (694,458 exact edges), and no
  literal context loop occurs from the 10,791 cores of length at most six in
  at most 20 steps with intermediate length at most 14.

These are instruction-class exclusions, not seed verification.  The acyclic
graph still contains a 299-rewrite spatial delay from the canonical word for
834 to one for 1079, including 52 genuine dynamic steps.  Long motion is
therefore easy even in this tiny language; the missing event is reproduction.

There is also a general obstruction to every *uniform* digit-block morphism,
not just width two.  Suppose sigma fixes the two delimiters, maps every
ordinary symbol to a word of common length w, and simulates all rules.  From
the image of the binary-zero dynamic rule, track the multiplicative slope of
the digit functions.  An auxiliary swap preserves the slope, deleting a
binary zero divides it by two, and consuming a binary one multiplies it by
3/2.  A path from sigma(binary-zero) followed by the end delimiter to the end
delimiter can finish only if sigma(binary-zero) is the all-zero binary word
of length w: it has no ternary symbol, no binary-one dynamic step, and every
binary digit is deletable.

Now apply the image of the left-boundary digit-one rule.  Its two sides contain
no end delimiter, so every step preserves the represented integer.  The right
side has value 2^(2w), whereas any length-w digit block starting from the left
delimiter has value at most

    2*3^w-1.

For every w>=3, 4^w>2*3^w, a contradiction.  Width two is the finite exact
classification above; width one has only the identity.  Commit `2d50381`
kernel-checks this entire uniform rewriting seam, not only the arithmetic
endpoint.  Commit `bfe12f0` is stronger: without any common-width premise,
every nonerasing marker-fixed digit-word morphism which nontrivially simulates
the eleven rules is the identity.  Thus the first plausible scale compiler
must be **delimiter-changing or context-dependent/multi-block**.  Assigning
independent variable-length codewords to the five digits cannot be the glider.
The bounded classifications and diagnostics remain independently replayed in
the Python artifact.

### 5.5 The carry defect is the first internal opcode

The auxiliary six-rule base-conversion subsystem has an exact involution:

    bin0 <-> bin1,       tri0 <-> tri2,       tri1 <-> tri1.    (CP27)

It permutes the A-rules in three pairs.  The dynamic boundaries break this
symmetry, but in a particularly informative way.  If a marker-free digit word
`V` acts by `x |-> s*x+t`, the complemented image of
`bin0 dot -> dot` would need `bin1 V` to behave like `V bin0`.  Their slopes
are equal and their intercept defect is

    delta(V)=s-t.                                             (CP28)

Every finite mixed-base digit word has `0<=t<s`; moreover `delta=1` exactly
when every digit is maximal in its own base.  Thus no passive right buffer can
repair the complement symmetry.  The obstruction is not an unstructured
carry cloud, however: saturation compresses it to one unit.

That unit is an executable unary-counter increment.  Direct rule induction
gives

    bin1 tri2^n dot  ->+  tri2^(n+1) dot,                    (CP29)
    bin0 tri0^n dot  ->+  tri0^n dot.                        (CP30)

The left boundary supplies a two-block transfer instruction:

    slash tri0^k tri2^n dot
      ->+ slash tri1^(k-1) tri2^(n+1) dot,    k>=1.          (CP31)

It consists of `B_0`, `k-1` copies of `A_t0`, `n` copies of `A_t2`, and one
`DT_t`.  In represented integers,

    N_0(k,n)=3^(k+n)+3^n-1,
    N_1(k-1,n+1)=(3^(n+1)(3^k+1))/2-1,

and `2*N_1=3*N_0+1`; CP31 is one exact odd shortcut step and is strictly
outward.  It increments the right counter by spending one left token and
phase-changing the remaining left block.

The exact [yah_carry_opcode.py](../../experiments/kontorovich/yah_carry_opcode.py)
artifact checks the CP27 permutation, exhausts all 488,281 digit buffers of
length at most eight for CP28 and the saturation equality case, and literally
replays 1,443 bounded instances of CP29--CP31 and a related two-dynamic
alternating-block identity.  Commit `0365c72` independently kernel-checks
CP28--CP31 for arbitrary digit words/run lengths over the pinned rule system.

This changes the programming model.  A global independent-letter morphism
must simulate each boundary rule in isolation, so it cannot transport CP28's
carry between the two ends.  A viable glider should instead be a **typed
contextual macro**: a left token/correction block and a right max-trit counter
evolve together across the whole canonical word.  Its missing opcode is now
precise:

    recharge tri1^(k-1) ... tri2^(n+1)
      back to tri0^k' ... tri2^n',                           (CP32)

with `k'` not exhausted and with the generated instruction determined by the
public blocks.  CP32 is allowed to be nonlocal; indeed the positive defect
shows that a passive local adapter cannot work.  This is Simon's “splash the
gap” in the mixed-base language: the bad carry is a one-unit instruction
which must be caught by a second block and rewritten into the next token.

### 5.6 Macro-space conservation exposes the nonlocal instruction bit

The eleven YAH rules admit an exact compiler-level quotient.  Let `Q_c` be
long division by two on a ternary word with incoming carry `c in {0,1}`.  Its
two-state Mealy table is

```text
       input 0    input 1    input 2
c=0     (0,0)      (0,1)      (1,0)
c=1     (1,1)      (2,0)      (2,1),
```

where each pair is `(output trit,next carry)`.  At the right boundary, carry
zero emits nothing and carry one emits a final `2`.  The latter is exactly an
odd shortcut step.  If `M` consumes one ternary head opcode after the slash
and returns to a pure ternary word, the three opcodes factor as

```text
M(0v)=Q_1(v),
M(1v)=Q_0(Q_0(v)),
M(2v)=Q_0(Q_1(v)).                                  (CP33)
```

Commit `1a88c3e` constructs these traces over the pinned 11-rule carrier for
arbitrary suffixes and proves the length law below; the quotient abstraction
is not inferred from bounded replay.

This is the hardware/software model in its smallest exact form.  The head
chooses one or two quotient sweeps; the entire remaining program is rewritten
by a two-state carry; and an odd sweep deposits a new maximal trit at the
remote end.  It resembles an iterated sequential transducer or queue machine,
but no universality is inferred from those model classes.

Every sweep is letter-for-letter away from the final deposit.  Consequently

```text
|M(hv)|-|hv| = (# odd sweeps in the macro)-1.         (CP34)
```

One head cell is spent, and remote odd carries are the only source of new
space.  CP34 is the closure budget which the earlier metaphor lacked.  Head
zero executes one sweep and can only shrink or preserve length.  Heads one and
two execute two sweeps; they reproduce one cell precisely when both are odd.
For canonical value `N`, the complete type table is

```text
head 0:   delta=0 for N odd, delta=-1 for N even;
head 1/2: delta=-1,0,0,+1 for N mod 4 = 0,1,2,3.      (CP35)
```

The reproducing instruction is therefore *not local*.  If the explicit trits
are `d_0...d_(m-1)`, then

```text
N mod 4 = (-1)^m + sum_i d_i*(-1)^(m-1-i) mod 4.     (CP36)
```

Its opcode is “head is one/two **and** the alternating checksum of the entire
digit span is three.”  This is the precise mathematical realization of
Simon's suggestion that a Collatz instruction may be distributed across the
whole program rather than stored in neighboring digits.  Commit `b1dd87a`
kernel-checks the Euclidean-division semantics, CP35, and CP36 in `ZMod 4`.

The one-step program census is closed form.  Among all `3^m` words of fixed
trit length `m>=1`,

```text
shrink  = 3^(m-1),
neutral = (3^m+1)/2,
grow    = (3^(m-1)-1)/2.                            (CP37)
```

The uniform mean space change is therefore
`-1/6-1/(2*3^m)`, and only asymptotic density `1/6` executes a reproducing
macro.  This is a literal program-space counterpart of the negative-drift
heuristic: typical software loses queue cells, while a counterexample must
remain in a repeatedly selected thin checksum language.  CP37 does not say
that the successive types are independent.

The carry transfer also performs a genuine spatial splash.  A second macro
turns a run of phase-one tokens into a distributed comb:

```text
M(1^(2q) 2^n)   = (01)^(q-1) 0 1^(n+1),
M(1^(2q+1) 2^n) = (01)^q (02)^ceil(n/2).             (CP38)
```

The following head-zero macro maps those combs to period-four packets; the
explicit formulas are recorded in the exact worker.  On the resulting family
`2 (0012)^s (01)^q`, the next head-two macro is itself a finite block compiler.
Both input block types advance one public phase modulo four.  At entry phases
`0,1,2,3`, respectively,

```text
0012 -> 0210, 1112, 2022, 0001,
  01 ->   02,   11,   21,   00,
tail ->    1,    2,   22, empty.                       (CP39)
```

It therefore grows by one exactly when `s+q=2 mod 4`, shrinks when the sum is
three, and is neutral otherwise.  This is the first chained distributed
opcode whose branch is a public block-count checksum.  It is not closure:
its output block alphabet differs from its input alphabet.  Commit `b794b2f`
proves the strongest immediate version of that warning: no source packet
`2(0012)^s(01)^q` maps to any target packet of the same family, because the
endpoint head is always zero or one rather than two.  At least one additional
packet type is mandatory.

The simplest possible closure is now formally dead.  Commit `64bccb8` proves
that an ordinary natural orbit cannot execute a `+1` macro forever.  Every
such macro satisfies

```text
4*(N_next+1)=9*(N+1),                                (CP40)
```

so infinitely many consecutive reproductions would force arbitrarily high
powers of four to divide one fixed positive `N+1`.  A real survivor must
interleave non-growing collisions.  Commit `db13d82` proves the exact finite
version: a burst of `r` growing macros has
`4^r*(N_r+1)=9^r*(N_0+1)` and forces `4^r | N_0+1`.

CP40 exposes the conserved resource those collisions must restore.  Define

```text
Battery(w)=2*|w|+v2(N(w)+1).                         (CP41)
```

A growing macro adds one cell and removes exactly two units of
`v2(N+1)`, so CP41 is unchanged.  Put `D=N+1`.  Direct evaluation gives the
complete recharge ledger:

```text
head 0, N even:       Delta Battery = v2(D+1)-3,
head 0, N odd:        Delta Battery = -1,
head 1/2, N=0 mod 4:  Delta Battery = v2(D+3)-4,
head 1/2, N=1 mod 4:  Delta Battery = v2(3D+2)-3,
head 1/2, N=2 mod 4:  Delta Battery = v2(D+1)-2,
head 1/2, N=3 mod 4:  Delta Battery = 0.             (CP42)
```

The first worker implementation checks CP41--CP42 exactly at every word in
its exhaustive scope; their universal algebra has been sent for Lean replay.
This is a sharper version of “splash the gap.”  A shrink/neutral collision is
useful only if one of the displayed numerators has excess dyadic valuation;
that gain must then fund more future cells than the collision destroyed.  The
constructive target is a comb/packet grammar which maps one of these recharge
cylinders into the phase-two reproducing packet and back again.

For the first packet family the recharge cylinders have a particularly clean
research-side parametrization.  Put

```text
P(s,q)=2 (0012)^s (01)^q,
C_s=(81^(s+1)+1)/2.
```

Then `C_s` is odd, `C_s=1 mod 8`, and direct block evaluation gives

```text
N(P(s,q))=(9^q*C_s-1)/8.                             (CP43)
```

Writing `r=s+q mod 4`, CP42 becomes

```text
r=0: Delta Battery = v2(3*9^q*C_s+37)-6,
r=1: Delta Battery = v2(  9^q*C_s+15)-5,
r=2: Delta Battery = 0,
r=3: Delta Battery = v2(  9^q*C_s+31)-7.            (CP44)
```

Consequently a requested battery gain `g>=1` is a single public address:

```text
r=0: 9^q = -37/(3*C_s) mod 2^(g+6),
r=1: 9^q = -15/C_s     mod 2^(g+5),
r=3: 9^q = -31/C_s     mod 2^(g+7).                 (CP45)
```

Each right side is `1 mod 8`.  Since powers of nine form the cyclic group
`1+8 Z / 2^K Z`, CP45 has one `q` class modulo `2^(K-3)` and its low bits
select the advertised phase.  Thus arbitrarily deep one-shot battery recharge
is syntactically available inside this packet family; it is not evidence of
closure.  Commit `b794b2f` says the output is a different packet type, and the
real compiler obligation is for that output type to write the *next* CP45
address rather than choosing a fresh congruence externally.  CP43--CP45 have
been sent for independent kernel audit.

Thus the original contiguous reservoir is not merely consumed—it is spatially redistributed.
The revised closure target is a finite **type cycle** of such comb/packet
grammars whose total CP34 charge is positive and whose CP36 checksum enables
the next reproducing opcode.

There is one more clock constraint.  A fixed shortcut word with `L>0` dynamic
steps and `O` odd steps acts affinely as

```text
2^L N' = 3^O N + C.
```

If a finite phase cycle sent a ternary exponential family
`N_n=A*3^n+B` back to the same phase with a fixed positive exponent shift
`n -> n+d`, coefficient comparison would require
`2^L*3^d=3^O`, impossible for `L,d>0`.  Hence a true scale-reproducer cannot
have a fixed-time phase period on a simple ternary-run family.  Its clock must
grow with its public counter, or its state family must use a genuinely mixed
dyadic--triadic/nonlinear scale.  This rules out another class of Life-like
glider analogies while preserving Kontorovich's deeper program analogy.
Commit `99d3405` kernel-checks the prime-power obstruction and its fixed-phase
coefficient wrapper.

The packet recharge can nevertheless be turned into an arbitrarily large
finite space amplifier.  Specialize CP43 to

```text
P(q)=P(0,q)=2(01)^q,       C_0=41.
```

Given a target `G>=1`, put `K=4G+1`.  Powers of nine generate
`1+8 Z/2^(K+5) Z`, so there is a unique class

```text
q=q_0 mod 2^(K+2),
41*9^q+15=0 mod 2^(K+5).                           (CP46)
```

Reduction modulo 32 also gives `q_0=1 mod 4`.  The packet is therefore in
phase one, its first macro is length-neutral, and direct shortcut evaluation
gives

```text
D(M(P(q)))=3*(41*9^q+15)/32.                       (CP47)
```

Thus CP46 writes at least `K` units of `v2(D)` into the endpoint.  Starting
there, take the maximal prefix of *whole queue macros* all of whose shortcut
steps are odd.  If `J` is its number of odd shortcut steps, then `J>=K-1`:
a zero-head macro consumes one unit and a nonzero-head macro consumes two, so
the first macro which would cross the valuation boundary can strand at most
one unit.  At every safe macro boundary,

```text
D_J=3^J*D_0/2^J.                                   (CP48)
```

Both endpoints are canonical pure-ternary words.  If their length difference
is `delta`, their canonical scale intervals and CP48 imply

```text
2^(J+1)*3^delta > 3^J.
```

Were `delta<=G-1`, using `J>=4G` would contradict

```text
2^(4G+1)*3^(G-1) <= 3^(4G),
```

which is just `2*16^G<=3*27^G`.  Therefore `delta>=G`.  This proves a
research-side all-`G` finite amplification schema: closure does not fail for
lack of workspace, but only because the next recharge call has not yet been
generated internally.

Crucially, the address survives that call.  Put `L=2^(K+2)` and normalize the
forced charge:

```text
A_K(t)=3*(41*9^(q_0+L*t)+15)/2^(K+5).              (CP49)
```

For `t!=u`, LTE gives

```text
v2(A_K(t)-A_K(u))
 = v2(9^(L*(t-u))-1)-(K+5)
 = v2(t-u).                                        (CP50)
```

Thus the free lift `t` is transmitted isometrically through recharge; modulo
every `2^h`, CP49 is a permutation.  This is the first exact combination of
an unbounded finite space amplifier and a lossless unbounded address channel
inside the queue language.  It is not closure: a forward finite type rule
must still decode `A_K(t)` into the next CP46 address without an external
choice of `t`.

The safe endpoint has an equally useful spatial type.  For `q>=1`,

```text
v3(41*9^q+15)=1,
```

because division by three leaves `41*3^(2q-1)+5`, which is nonzero modulo
three.  Hence `v3(A_K(t))=2`.  After `J` safe odd steps, CP48 gives

```text
v3(D_J)=J+2.                                        (CP51)
```

The endpoint integer `N_J=D_J-1` therefore has exactly `J+2` trailing maximal
ternary digits.  Recharge emits a clean right-hand reservoir as well as the
arbitrary prefix register.  A plausible next type edge is no longer
completely abstract: route that prefix/reservoir word through CP38's carry and
comb compilers and test whether it regenerates the alternating packet whose
block count satisfies CP46.

At the first useful charge this routing problem already exposes a literal
programming instruction.  Take `K=5`; the least CP46 address is `q_0=17` and
all lifts are

```text
q=17+128t.
```

After the neutral packet macro and five safe odd steps, define the stripped
register

```text
R(t)=(41*9^(17+128t)+15)/(3*2^10).                 (CP52)
```

The resulting state has the exact form

```text
N(M^4(2(01)^(17+128t))) = 3^7*R(t)-1              (CP53)
```

at the integer level.  At the word level it is a lasso `U V^t Z` with
generated lengths `31,256,6`; the last digit of `U` and the six-digit `Z`
together form the seven-trit reservoir.  The stride `|V|=256` is
`ord_(2^10)(3)`, the base-three repetend of the normalized dyadic register.
The exact worker obtains this identity by four finite-state lasso
compositions, each of whose block maps fixes the entering carry.

The lift isometry specializes to a bit identity.  The difference
`R(t+1)-R(t)` is odd, while `R(0)` is even, so

```text
R(t)=t mod 2.                                       (CP54)
```

The word in CP53 always has head zero.  Its next macro therefore reads this
least significant bit exactly:

```text
R=2r:    3^7*R-1 -> 3^8*r-1,
R=2r+1:  3^7*R-1 -> (3^7*(2r+1)-1)/2.              (CP55)
```

The zero branch is one odd shortcut step: it emits a terminal carry, shifts
the register, and extends the trailing-two reservoir from seven to eight.
The one branch is one even step: it emits no carry, loses one cell, destroys
the clean reservoir, and enters a new chart.  The 256-trit repeated block
flips the sweep carry, giving an exact lasso-level parity split

```text
t=2s:    U_0 V_0^s Z_0,   (|U_0|,|V_0|,|Z_0|)=(30,512,7),
t=2s+1:  U_1 V_1^s Z_1,   (|U_1|,|V_1|,|Z_1|)=(286,512,6). (CP56)
```

This is the first genuine LSB-first queue opcode: a nonlocal register bit
selects between extending a spatial delay line and colliding with it.  The
missing closure instruction is now the bit-one branch's return from its new
chart to a CP46 packet with a newly written unbounded register.

That return can be built on a thinner cylinder.  Restrict the bit-one chart to

```text
t=91+256u,  s=45+128u,  q=11665+32768u.             (CP57)
```

The q-stride is 32,768 and `v2(9^32768-1)=18`.  The incoming CP52 register
obeys `R=151 (mod 256)`, so

```text
2^8 | 3^6R+1,  R'=(3^6R+1)/2^8.                    (CP58)
```

After CP55's bit-one collision, the next head-one queue macro is a neutral
recharge.  Its defect and the eventual return defect are

```text
D_recharge=9*2^5R',
D_return=3^7R'.                                     (CP59)
```

The intervening head schedule `0,2,1` spends five odd shortcut steps.  In
total the five macro carries are

```text
[0], [0,1], [1], [1,1], [1,1],
```

and the word returns to head zero with exactly seven trailing twos.  From the
incoming CP53 decoder word to this returned word, the length increases by
exactly one.  This is therefore a parameterized

```text
read -> collide -> recharge -> reproduce             (CP60)
```

instruction, not merely a long transient.

The complete word identity is finite-state.  Restricting the CP56 lassos and
composing their fixed-carry block maps gives prefix/block/suffix lengths

```text
incoming     (23327,65536,6)   recharge  (23325,65536,7)
bit-one      (23326,65536,6)   safe-1    (23324,65536,8)
safe-3       (23323,65536,10)  returned  (23322,65536,12). (CP61)
```

The final suffix length is a lasso-decomposition artifact; the literal word
has exactly seven trailing twos.  The returned block has the same length as
the incoming block but different contents.  Moreover `R'` remains a 2-adic
isometry in `u` and satisfies `R'(u)=u+1 (mod 2)`.                 (CP62)

This is the first actual reproduction edge, but the type graph is still open.
Companion commit `f96e621` proves the stronger separation

```text
R(t) < (3^6R(t)+1)/2^8 < R(t+1),                   (CP63)
```

so no returned register equals any member of the original decoder family.
Repeatedly selecting deeper restorative cylinders may therefore create an
infinite tower of one-use charts rather than a finite program.  The next win
condition is a finite set of chart languages closed under these generated
edges, containing one forward ordinary state and at least one recurrent
space-positive component.

The exact
[yah_queue_macro.py](../../experiments/kontorovich/yah_queue_macro.py)
artifact independently implements CP33 and literal rule replay.  It compares
them on every one of the 88,572 nonempty ternary words of length at most ten,
checks CP34--CP37, and replays 16,769 bounded CP38/comb/packet identities through
coordinate 64.  The bounded audit is not the proof of the all-length laws;
their induction statements have been sent to the companion formalizer.
The companion
[`yah_recharge_amplifier.py`](../../experiments/kontorovich/yah_recharge_amplifier.py)
artifact checks 32 CP46 addresses, exhaustive ten-bit CP50 permutations for
four targets, and exact queue traces through a 369,187-trit packet, including
the CP51 reservoir length.  CP46--CP51 are all-length research-side proof
schemas.  Commit `67eabe3` kernel-checks the generic CP48 scale consequence:
canonical endpoints with `J>=4G` and the exact all-odd defect balance gain at
least `G` cells.  The packet/maximal-prefix wrapper, CP50, and CP51 remain
pending kernel replay.
The exact
[`yah_lift_decoder.py`](../../experiments/kontorovich/yah_lift_decoder.py)
artifact constructs the CP53/CP56 finite-state blocks and independently
replays CP52--CP56 for all 65 parameters through `t=64`.  The all-parameter
lasso induction and bit opcode have been sent for kernel replay.
The exact
[`yah_restorative_decoder.py`](../../experiments/kontorovich/yah_restorative_decoder.py)
artifact constructs CP57--CP62 and independently replays `u=0,...,4` through
all five macros.  Commit `24b2dd5` kernel-checks the generic decoder arithmetic
and fixed/flipping-lasso engine; commit `f96e621` kernel-checks CP63.  The
all-stage word instantiation and any finite recurrent chart graph remain open.

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

- **Canonical cofactor invariant languages.**  Work in the public `(m,t)`
  transducer from PC1--PC4.  Seek finitely described sets `L_m` with every
  `t in L_m` decoding a legal branch and landing in `L_m'`.  The first target
  is a two-stack/mixed-radix encoding in which the `2^P` source cylinder pops
  a binary instruction and the `3^Q` output coefficient supplies the remote
  write.  This is now prior to any norm-representation condition.
- **Decorated-semigroup relations.**  Classify short relations or
  conjugacies among the `M(m,g,h)`, after quotienting the exact CP5 defect
  backbone.  A survivor must include the CP2 boundary cylinders, not merely
  matrix equality.  Lean commit `e8585c4` closes every fixed nonempty finite
  opcode period, even after a transient, by compressing the period to one
  expanding coprime affine gain law.  The constructive lane must therefore
  use payload-driven genuinely aperiodic substitutions or conjugacies.
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

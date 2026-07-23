# KL-calibrated escape: branching entropy, cycle tax, and the finite `-1` counter

2026-07-23. Status: **the path/cycle tax, strict selected-cycle drift,
mixed-word budget, and pure minus-one rail obstruction are kernel-checked in
companion commits `9f307a9`, `ddff8d7`, and `7aa7c0d`; `cc9f441`
kernel-checks the exact ordinary size cost of tracking the minus-one spine;
`408cb2c`/`814fb00` prove the three-branch recharge ledger and that its
dyadic depth is exactly the next forced odd-burst length; `35200ca`,
`616ace8`, `2fcddea`, `2700d1e`, and `aab22e7` prove the primitive-core,
finite/infinite shadow, connector-cost, and exact reset-recurrence package;
`e15c6f0` proves the uniform cycle-product defect bound; `8c20163`,
`54eb749`, and `961c692` prove that a fixed controller word has one exact
ternary input cylinder and that, once the word contains a divided letter,
this cylinder is equivalent to all of its local legality tests; `2acceaa`
accumulates arbitrary reset blocks into one dyadic cylinder and proves
ordinary initial-payload uniqueness at unbounded cumulative precision;
`d8d8337` proves that the terminal cylinder reconstructs all intermediate
integer quotients and that every finite reset word has a strictly positive
payload chain; `2963a8d`/`ca8dc5c`/`18b8c93` prove canonical-residue
stabilization for ordinary chains, expose the exact bounded reset carry, and
characterize ordinary integer chains by an eventual zero-carry tail;
`73601f7` makes bounded canonical residue height equivalent to that gate;
and `1aa3e52` excludes every periodic or ultimately periodic path through the
first four-word proper outward language**.
The full
cross-precision rigidity problem remains research.  There is no
counterexample.
This note rereads Krasikov--Lagarias from the deliberately opposite direction:
not to prove that many integers terminate, but to identify what a single
escaping orbit would have to do that their extremal predecessor system refuses
to do.

Primary source: I. Krasikov and J. C. Lagarias, *Bounds for the 3x+1 Problem
using Difference Inequalities*, arXiv:math/0205002 (2002), especially
Theorem 2.2, Sections 3--5, and the equality discussion at the end of Section
6.  The source was checked against the local PDF
`papers/krasikov-lagarias-2002-bounds-3x1-difference-inequalities.pdf`.
Its printed deletion proof and equation (2.1) are not reused: their exact
defects and the replacement theorems are recorded in
`experiments/kl/TERMINATION_AUDIT.md`.

## 1. The equality object in the original paper

KL's Section 6 makes the right converse observation.  At a critical parameter
`lambda`, if the principal LP inequalities are equalities, the pure
exponentials

```text
phi_m(y)=c_m*lambda^y
```

solve the difference system with equality.  The repaired project strengthens
this point: the finite critical min-of-linear operator has a positive
eigenvector, and a minimizing lift can be selected on every chord row.  The
selected graph has the following edge shifts:

```text
transport m -> 4m:                 w=-2,
class-2 chord m -> (4m-2)/3:       w=log_2(3)-2,
class-8 chord m -> (2m-1)/3:       w=log_2(3)-1.
```

Only the class-8 chord has positive shift.  Reversing a predecessor edge turns
its shift into the leading logarithmic size change of the corresponding
forward block.  Thus positive total shift is exactly the symbolic resource an
escaping forward program needs.

## 2. Selected-policy cycles are strictly retarded

Let `c>0` be an exact critical eigenvector and retain the fiber-minimizing
chord on each chord row.  Every selected summand is bounded by the full row:

```text
lambda^w * c(target) <= c(source).                    (2.1)
```

Multiply (2.1) around a directed cycle.  The potential values telescope, so

```text
lambda^(sum w) <= 1, hence sum w <= 0.                (2.2)
```

The inequality is strict in the KL graph.  A cycle sum has the form
`A*log_2(3)-B` with integers `A>=0,B>0`.  Equality with `A>0` would give
`3^A=2^B`; with `A=0`, every used shift is already negative.

This changes how the critical KL eigenvector should be used in a construction
program.  Its active policy is not a hidden counterexample schedule.  Every
one of its cycles contracts in the forward-reversed size cocycle.  The
spectral radius reaches one because rows *add predecessor branches*--that is,
through branching entropy--not because one selected ray grows.  The old KL
method therefore cannot be tropicalized to a single escape path without
losing its entire source of gain.

At each fixed precision the graph is finite, so cycle erasure strengthens
this from cycles to arbitrarily long selected walks: after a bounded simple
remainder, every walk is a concatenation of negative-shift cycles.  Hence its
asymptotic shift is bounded above by the largest (strictly negative) simple
cycle mean.  There is no reason for that negative margin to be uniform in the
precision--the elementary lower bound from `|2^B-3^A|>=1` can be exponentially
small in the cycle length.  A hypothetical escape can therefore evade this
finite-level obstruction only through a genuinely precision-changing,
noncoherent limit policy.  This is the same quantifier seam that turns fresh
CRT digits into a 3-adic stack rather than one natural.

The path/cycle telescoping and strict KL cycle claims are kernel-checked as
QM127 in companion commit `9f307a9`.  The fixed-graph cycle-erasure corollary
in the preceding paragraph is not separately packaged in Lean.

## 3. Leaving the policy has an exact deviation tax

The full refinement fiber contains three possible chord targets.  Write
`c_min` for the selected value and `c_alt` for a different lift, and put

```text
d(e)=c_alt/c_min >= 1.
```

On transport and selected edges set `d(e)=1`.  Equation (2.1) becomes, for
every full-lift edge,

```text
lambda^w*c(target) <= d(e)*c(source).
```

Telescoping around any full-lift cycle gives the calibrated escape tax

```text
lambda^(sum w) <= product d(e).                       (3.1)
```

An outward cycle must therefore make non-minimal refinement choices, and the
product of their potential ratios must pay for at least all of its outward
shift.  This is a useful search ordering: enumerate recharge cycles in
increasing exact tax surplus, not seeds in increasing numerical size.  It is
also only a necessary condition.  The selected digit may change with the
precision, and a coherent inverse-limit digit table can describe a 3-adic
address without describing one ordinary natural.

The cycle formulation is not the real limit of the argument.  For an
arbitrary finite path `x_0 -> ... -> x_N`, multiplication gives

```text
lambda^(sum_(i<N) w_i) * c(x_N)
  <= product_(i<N) d_i * c(x_0).                    (3.2)
```

At one fixed KL precision the positive potential has finite condition number
`kappa=max(c)/min(c)`, hence

```text
lambda^(sum_(i<N) w_i)
  <= kappa * product_(i<N) d_i.                     (3.3)
```

Thus eventual periodicity is irrelevant: every aperiodic path with sustained
positive shift must pay non-minimizing-lift tax at a sustained asymptotic
rate.  The endpoint factor is only `kappa`, independent of path length.  This
is still a fixed-level theorem; `kappa` may grow with the precision, so a
precision-uniform escape-rate conclusion would require a new bound.  The
path-product statement is kernel-checked as QM130 in companion commit
`ddff8d7`.

For selected paths all `d_i=1`, so the fixed-level consequence is stronger
than a nonpositive asymptotic mean.  If `kappa<=lambda^B`, then every selected
path, of every length, satisfies

```text
sum_(i<N) w_i <= B.                                  (3.4)
```

The selected policy cannot accumulate unbounded outward shift at one
precision at all.  This corollary is kernel-checked in companion commit
`7aa7c0d`; a live path must either pay nonselected deviation tax or increase
precision so that the endpoint budget itself changes.

The certified feasible subeigenvectors show that this qualification is active
rather than cosmetic.  Over `k=12,...,19`, their exact condition numbers
increase strictly from `146.967160601293` to `2782.61599307298`.  These are
finite certificate facts, not critical-eigenvector identities or a limiting
growth law.  They identify the next rigidity question: either renormalize the
growing exceptional potential spike uniformly across the tower, or prove that
an ordinary path cannot track the spike cofinally.  A fixed-level argument
alone cannot decide that seam.

There is now one exact cross-precision constraint.  Companion commit
`cc9f441` proves for naturals

```text
n mod 3^k = 3^k-1  ->  3^k <= n+1.                 (3.5)
```

Consequently every fixed natural eventually avoids the exact all-`2` spine
and no natural represents `-1` at every ternary precision.  This does not
exclude a diagonal sequence `n_k` whose size grows with `k`; it proves that
such tracking costs at least exponential ordinary size.  A useful global
theorem must compare that cost with the height gain and counter recharge of
the same coherent orbit.

There is a second exact pruning budget which does not use `c`.  If a mixed
word contains `n8` class-8 chords, `n2` class-2 chords, and `ns` transports,
positive leading shift means

```text
(n8+n2)*log_2(3) > n8+2*n2+2*ns.
```

The already kernel-checked separator `3^41<2^65` gives
`log_2(3)<65/41`, hence the necessary integer inequality

```text
24*n8 > 17*n2+82*ns.                                 (3.6)
```

In particular each transport used by a recharge phase costs more than
`82/24` positive class-8 discharges before the leading multiplier can exceed
one.  This is a strong branch-and-bound rule for the mixed search, not a
sufficient condition for an actual trajectory.

## 4. The cheapest visible finite calibration is the nonordinary point `-1`

On a class-8 chord, use the affine coordinate `z=m+1`.  The predecessor map is

```text
m -> (2m-1)/3,       z -> (2/3)z.                    (4.1)
```

Its forward reversal is `z -> (3/2)z`, the only positive-shift KL block.  The
point `m=-1` is a fixed point of (4.1).  It is also the unique rational
periodic point of a pure class-8 word: iterating gives

```text
R8^L(m)+1=(2/3)^L*(m+1),
```

so a positive period `L` forces `(3^L-2^L)(m+1)=0` and hence `m=-1`.

The certified feasible subeigenvector profiles near `-1` make the calibration
visible.  The self-lift is not the minimizing lift, and over the eight stored
levels the exact ratio `c(-1)/min_fiber(c)`, divided by the certified
class-8 lower weight, decreases from `1.00491098975441` to
`1.00029914602351`.  This is finite evidence consistent with saturation, not
a critical-eigenvector limit theorem.  The exact limiting local law, if its
critical-tower hypotheses hold, would give
`lambda^(log_2(3)-1)`, precisely the tax for the positive self-loop.  In every
case the exact affine fixed object is the negative 3-adic point, not the
required positive ordinary seed; the feasible-vector data does not promote
it to a critical equality object.

## 5. Ordinary finite rails consume a finite counter

The positive natural approximation to the `-1` loop is elementary and exact.
For `L,t>0`, define

```text
x_j=3^j*2^(L-j)*t-1,        0<=j<=L.
```

Every `x_j` with `j<L` is odd, and one shortcut step gives

```text
(3*x_j+1)/2=x_(j+1).
```

Hence

```text
T^L(2^L*t-1)=3^L*t-1,                                (5.1)
```

and the block grows strictly.  Its fuel is the finite counter `v_2(x_0+1)`.
If two such pure rails splice, then

```text
3^(L_i)*t_i=2^(L_(i+1))*t_(i+1),
```

and therefore

```text
v_2(t_(i+1))=v_2(t_i)-L_(i+1).                       (5.2)
```

No fixed positive payload supports infinitely many positive rail lengths:
the nonnegative counter in (5.2) cannot decrease forever.  This is the exact
version of the earlier intuition that an infinite escape needs a counter
which is repeatedly regenerated, not merely one which starts large.  Companion
commit `9f307a9` connects (5.1)--(5.2) to the literal Syracuse semantics and
proves the infinite-splice contradiction.

## 6. Recharge is an immediate forced burst, not stored fuel

The three literal KL predecessors of a positive target `a=2 (mod 3)` are

```text
advancedChild=(2a-1)/3,
retardedChild=2*advancedChild,
transportChild=4a.
```

Companion commit `408cb2c` connects them to one, two, and two shortcut
Syracuse steps respectively and proves the exact centered balances

```text
3*(advancedChild+1)=2*(a+1),
3*(retardedChild+2)=4*(a+1),
transportChild+4=4*(a+1).                           (6.1)
```

The corresponding dyadic depths are therefore `1+v_2(a+1)`,
`2+v_2(a+1)`, and `2+v_2(a+1)`.  Class-2 and transport do not reset an
independent battery for free; they move the exceptional center from `-1` to
`-2` or `-4` and pay the exact ordinary-size inequalities recorded in
`KLRechargeLedger.lean`.

Commit `814fb00` makes the operational meaning sharper.  For every natural
`n`, put

```text
r=v_2(n+1),       t=(n+1)/2^r.
```

Lean proves `t>0`, `t` odd, `n=2^r*t-1`, and

```text
T^j(n)=3^j*2^(r-j)*t-1,       0<=j<=r.              (6.2)
```

Every source before `j=r` is odd and the endpoint at `r` is even.  Thus
`v_2(n+1)` is exactly the maximal length of the next consecutive odd burst.
A deep recharge cannot be stored or assigned to a later program branch: it
forces its entire discharge immediately.

## 7. The hidden invariant is one two-place content ledger

The specific identities (6.1) have a moving-center form.  If `h=1 (mod 3)`
is the positive center of a negative controller, define

```text
h8=(2h+1)/3,       h2=(4h+2)/3,       hs=4h.
```

Direct substitution gives

```text
3*(advancedChild(a)+h8)=2*(a+h),
3*(retardedChild(a)+h2)=4*(a+h),
transportChild(a)+hs=4*(a+h).                       (7.1)
```

Consequently the `2,3`-primitive cofactor of the positive centered distance
`a+h` is unchanged by every coherent KL branch.  Moreover, for any positive
integer `z`,

```text
2^v_2(z) * 3^v_3(z) <= z.                           (7.2)
```

So ordinary height, ternary shadow precision, and dyadic burst depth are not
three resources which can be optimized independently.  They are the two
prime contents of one integer.  If `a=-h (mod 3^k)` and
`b=v_2(a+h)`, then (7.2) gives the combined address cost

```text
2^b*3^k <= a+h.                                     (7.3)
```

The special branch balances are kernel-checked in `408cb2c`.  Companion
commit `35200ca` proves QM131 in full: the complementary ternary balances,
two-place content divisor and height bound, the three abstract core-transfer
lemmas, and every moving-center invariant in (7.1).  Thus the collapse from
three apparent resources to one centered integer is a kernel-checked result.

## 8. Negative cycles are finite calibration templates

The fixed point `-1` is not the only signed controller worth calibrating.  The
new exact worker checks the three explicitly supplied signed shortcut cycles through
`-1`, `-5`, and `-17`, whose KL positive-center presentations are

```text
1 -> 1,
7 -> 10 -> 7,
25 -> 34 -> 136 -> 91 -> 61 -> 82 -> 55 -> 37 -> 25.
```

Their branch counts give the strict outward separators `3>2`, `3^2>2^3`,
and `3^7>2^11`.  For each certified feasible subeigenvector at
`k=12,...,19`, the worker extracts the prescribed lift on every chord and
computes the exact rational product

```text
product(c_prescribed/minFiber) /
product(certified edge-weight lower bounds).         (8.1)
```

All 24 values exceed one.  Each finite sequence decreases strictly, and the
`-1` template is exactly cheapest in every row:

```text
template                 k=12              k=19
-1 fixed point        1.00491098975441   1.00029914602351
-5 cycle             1.14003194854355   1.06409075514007
-17 cycle            1.86455471354517   1.48129516352954
```

These finite values motivate comparing signed cycles as controller templates;
they do not identify an Aubry/equality set.  The vectors are independent
certified feasible subeigenvectors at different dimensions and parameters,
not a coherent critical tower.  In particular, the `-17` surplus `1.4813` is
not close enough to justify an equality label, and even the observed ranking
has no cross-level theorem.  Neither convergence nor completeness of the
three templates is claimed.  The exact artifact SHA-256 is
`f52afeca61dc4bd0683a2ab72e285377355e86edd5e52fec85e89a84ab534249` and
contains `counterexample:null`.

There is nevertheless one safe fixed-level structural conclusion.  If an
outward `q`-chord cycle has calibrated lower weight `W` and every chord
deviation is at most `M`, then

```text
W <= product d_i <= M^q.                             (8.2)
```

Companion commit `e15c6f0` kernel-checks (8.2).  Thus an outward cycle forces
some nontrivial projective fiber defect.  It does not identify one persistent
edge: in the exact `-5` record, the chord carrying the larger deviation
alternates across levels.  Any future renormalization theorem must control
the cycle product rather than a named lift.

## 9. Coherent negative shadowing has universally finite depth

There is an elementary obstruction broader than periodic negative cycles.
Suppose two signed shortcut-Syracuse orbits have the same parity choices for
`N` steps, with `O_N` odd sources.  Subtracting their one-step affine laws and
iterating gives

```text
2^N*(T^N(x)-T^N(y))=3^O_N*(x-y).                    (9.1)
```

Because `3^O_N` is odd and the endpoint difference is integral,

```text
2^N divides x-y.                                    (9.2)
```

Thus two distinct ordinary integers cannot share an infinite parity
itinerary.  In particular, a positive orbit cannot coherently shadow any one
fixed signed negative orbit forever, even if that controller is aperiodic.
It may still reset to a different controller, but a post-reset shadow of
length `N` needs a fresh address modulo `2^N`.

Controller switching has a parallel ternary cost.  If a legal positive-center
connector has counts `(nS,n2,n8)`, then `S(h)=4h`, `R2(h)<=2h`, and
`R8(h)<=h`, so

```text
h' <= 4^nS*2^n2*h.
3^k <= |h'-g| <= h'+g <= 4^nS*2^n2*h+g             (9.3)
```

for a distinct target match `h'=g (mod 3^k)`.  Thus no fixed-length connector
between fixed or bounded centers works at cofinal precision.  This must not be
read as a finite-alphabet no-go: transport alone has
`S^(1+3^(k-1))(1)=4 (mod 3^k)` with an endpoint different from `4`, so
unbounded word length reaches every precision.

Companion commit `616ace8` proves QM132 in both abstract and literal signed
form: the exact identity (9.1), both divisibility forms, the sharp distance
bound, and uniqueness of the initial integer under an infinite common parity
itinerary.  Commit `2fcddea` proves the converse residue-coding direction and
constructs an explicit negative representative for every finite parity
cylinder.  Thus finite positive/negative shadowing at arbitrarily large,
separately chosen depths is automatic and is not evidence for an exceptional
orbit.  Commit `2700d1e` proves the coarser `4^L*h` connector estimate, and
`aab22e7` proves the count-sensitive strengthening (9.3).  None of these
theorems excludes compatible resets across depths.

## 10. Dual affine cylinders isolate the real construction interface

The dyadic and ternary conditions by themselves are coprime CRT constraints,
so they are always locally compatible.  The nontrivial coupling appears only
when the outgoing payload of one shadow block must write the next address.
Write a reset state as

```text
x_j=c_j+2^N_j*m_j,
```

where `c_j` is its signed controller.  If the two orbits share `N_j` shortcut
branches, with `O_j` odd sources, then (9.1) and the next reset representation
give the exact quotient recurrence

```text
2^N_(j+1)*m_(j+1)=3^O_j*m_j+delta_j,
delta_j=T^N_j(c_j)-c_(j+1).                         (10.1)
```

Backward iteration of (10.1) selects one canonical 2-adic initial payload.
An ordinary escape requires that value to be a positive natural and every
forward quotient to be positive, integral, and branch-legal.  If the reset
coefficients are eventually periodic, composing one period reduces (10.1)
to a single rational affine fixed-point audit, already covered by the
project's periodic/finite-state no-go machinery.  A surviving controller must
therefore have a genuinely aperiodic, payload-written reset schedule.

For the ternary side, a center word has exact radix accumulators `(A,B,r)`:

```text
S:  (A,B,r)->(4A,4B,r),
R2: (A,B,r)->(4A,4B+2*3^r,r+1),
R8: (A,B,r)->(2A,2B+3^r,r+1),
3^r*h'=A*h+B.                                       (10.2)
```

Thus a precision-`k` target test is one exact congruence
`A*h+B=3^r*g (mod 3^(k+r))`, not an undirected seed search.  Equations
(10.1)--(10.2) are kernel-checked in companion commit `aab22e7`, with
positivity, integrality, and branch legality deliberately left as explicit
construction obligations.

The coefficient `A` is exactly a power of two and is therefore a unit modulo
every power of three.  Commits `8c20163` and `54eb749` prove that the numerator
congruence has exactly one input class and that it is simultaneously compatible
with any prescribed dyadic class by CRT.  Commit `961c692` removes the last
local filter.  If `r>0`, then

```text
LegalWord(w,h)
  <-> A*h+B = 3^r (mod 3^(r+1)).                    (10.3)
```

Moreover, for every `g=1 (mod 3)` and `k>=1`, there is a positive legal input
class, unique modulo `3^(k+r)`, whose endpoint is `g mod 3^k`.  Thus a fixed
word is a ternary cylinder bijection: each divided letter consumes one new
ternary digit, but no finite word or finite target can fail for lack of
legality.  This is the exact ternary analogue of the binary parity-cylinder
theorem.  Finite binary shadowing, finite ternary controller targeting, and
their mixed CRT problem are all automatic.

The live distinction is therefore an inverse-limit and height condition.
Successive applications of (10.1) must select the same ordinary initial
payload, not merely a fresh 2-adic residue at each depth.  Successive
applications of (10.3) must likewise come from one ordinary controller, not
merely a fresh 3-adic representative.  The real KL cocycle must remain
outward at the same time.  These three places--dyadic address, ternary
address, and real height--are the smallest formulation in which a finite hit
can carry information about a counterexample.

Commits `2acceaa` and `d8d8337` make the dyadic half exact.  A reset instruction
`(N,O,delta)` updates accumulated data `(S,P,D)` by

```text
(S,P,D)->(S+N,P+O,3^O*D+2^S*delta),
2^S*m_end=3^P*m_start+D.                            (10.4)
```

The terminal congruence

```text
2^S divides 3^P*m_start+D
```

is equivalent to existence of all intermediate integer quotients in the
finite reset chain.  Moreover, shifting a solution by a sufficiently large
multiple of `2^S` makes the start, endpoint, and every intermediate payload
strictly positive.  Hence every finite reset instruction word is positively
realizable: finite integrality and positivity are not promotion criteria.
For an infinite reset program, if cumulative
`S` is unbounded, any two ordinary integer payload chains following it have
the same initial payload.  This is the precise answer to the resource
question: no individual block counter has to increase monotonically, but the
cumulative written precision must increase, and its nested classes must
converge to one positive ordinary integer.  Commits `2963a8d`/`ca8dc5c`
prove that the canonical representatives form a nested nondecreasing
sequence and that a nonnegative ordinary chain with unbounded precision makes
it eventually constant.  More precisely, if `z_J` is the exact endpoint of
the canonical depth-`J` chain, then

```text
r_(J+1)=r_J+2^S_J*q_J,  0<=q_J<2^N_J,
q_J=0 <-> 2^N_J divides 3^O_J*z_J+delta_J.          (10.5)
```

Nonzero carries arbitrarily late are therefore a kernel-checked no-chain
certificate.  Commit `18b8c93` proves the converse too:

```text
EventuallyZeroCarry(e)
  <-> exists m, Follows(e,m) and 0<=m(0).            (10.6)
```

This has no hidden unboundedness hypothesis; bounded cumulative precision
forces eventual zero-width instructions and hence zero carry.  The
equivalence does not establish strict positivity of the later quotients or
outward growth.

Commit `302ce3b` provides a separate abstract finite-table consumer.  A
`CoveringDispatcher` must already certify, on every selected residue
cylinder, the exact quotient, an invariant payload threshold, current-state
positivity, and strict reset-state growth; Lean then constructs its infinite
growing affine orbit.  The file deliberately supplies no signed-Syracuse
meaning.  For actual controllers, a total outward cover is expected to reduce
by odd-affine preimage to the existing Two-Kraft complete-code no-go.  That
last bridge is not yet kernel-packaged, so the current constructive target is
the already identified proper invariant thin language, not a total table.

## 11. The revised theorem-driven construction target

The KL reading now narrows a viable counterexample architecture much more
than “make the counters grow.”

1. **Coherent segment.**  Follow a signed calibration controller.  The
   centered primitive cofactor stays fixed, and dyadic recharge immediately
   becomes a forced odd burst.
2. **Controller switch.**  Write a genuinely new negative center.  The finite
   ternary target and every local legality check have one automatic input
   cylinder by (10.3); the construction must make those cylinders coherent
   across unbounded precision rather than solve them separately.
3. **KL payment.**  The complete word must obey
   `24*n8>17*n2+82*ns` and its non-minimal lift deviations must pay the
   calibrated path tax.  The three signed cycles supply the baseline prices.
4. **Autonomy.**  One positive payload must satisfy (10.1), generate the next
   longer, finer controller switch, and pass the ordinary-height gate.
   Supplying fresh CRT digits externally merely constructs a pair of 2- and
   3-adic stacks, not an ordinary counterexample.

This is not a counterexample.  It identifies the only remaining constructive
freedom: an aperiodic self-writing sequence of controller resets.  A big
positive result would be an exact recurrence that generates those resets and
beats both KL costs.  A big negative result would show that every such reset
changes or drains the primitive cofactor faster than the next coherent
segment can recover.  Pure seed widening and fixed-controller searches no
longer address the live seam.

## 12. A proper outward parity language and its exact ordinary gate

The first bounded signed-controller audit does not attempt a total dispatcher.
For controllers `-96<=c<0` and shadow depths at most eight, the 246 outward
modes reduce to the prefix-free shortcut code

```text
1, 011, 001111, 010111.                             (12.1)
```

Its ordinary Kraft mass is `21/32`, so it omits 88 of the 256 resolved
residues.  Its tilted mass is `1905/2048`.  Odd-affine pullback preserves the
168 admitted residues for every current mode, and the exact worker checks
41,328 positive, strictly state-growing reset transitions.  This is a proper
thin language and therefore does not reopen the Two-Kraft complete-code lane.

The infinite promotion gate is much sharper than the finite counts.  Commit
`73601f7` proves

```text
canonical residues bounded
  <-> canonical residues eventually constant
  <-> reset carries eventually zero
  <-> a nonnegative ordinary reset chain exists.    (12.2)
```

The bounded tree contains many finite zero-lift suffixes.  Its strongest
depth-nine prefix, beginning at `M=138770`, has eight zero-lift blocks after
deterministic lookahead and then no zero-lift extension in (12.1).  This is
finite exclusion of one prefix, not evidence for a universal no-go.
Companion commit `1aa3e52` supplies the first infinite theorem: every periodic
or ultimately periodic concatenation of (12.1) is impossible on positive
ordinary states.  It accumulates a repeated word to

```text
2^S*x_(t+1)=3^O*x_t+A,  A>=0,
```

and applies the expanding coprime affine-gain obstruction when `2^S<3^O`.
Thus only a genuinely aperiodic path whose address nevertheless satisfies
(12.2) remains live.

## 13. The EC17 core odometer is not a KL path

The period-three core has a genuine and useful fixed-depth clock.  With
`m_t=2*core(t)`, consecutive EC17 coefficient congruences give

```text
m_(t+1)=4^(-4*Delta_t)*m_t (mod 3^d).               (13.1)
```

For cycle gain `K`, the three-step multiplier has orbit length
`3^(d-1-min(v_3(K),d-1))`; when `3` does not divide `K`, it permutes all of
`Y_d`.  This fact does not identify the boundary transition with a KL edge.
For `y=u*m`, the KL chord equations each have exactly one source over a full
odometer orbit, while transport requires the exceptional congruence `u=4`.
The exact `(-1,1,1)` regression therefore finds, phase by phase,

```text
d=3: transport=0, R2=1, R8=1, nonedge=7;
d=4: transport=0, R2=1, R8=1, nonedge=25.           (13.2)
```

There is also an affine semantic obstruction.  A KL predecessor word with
`r` divided letters has defect

```text
D >= 3^r-2^r.                                       (13.3)
```

A normalized EC17 core step has `r=6n+11>=17` but defect only 34, whereas
`3^17-2^17=129009091`.  It therefore cannot be a KL word, even after grouping
multiple KL edges with the same chord count.  Consequently the proposed
Haar-average KL tax on the core odometer is invalid.

This is a scoped bridge failure, not a closure of KL for the ether program.
The actual packet compiler has different ordinary Collatz endpoints.  A valid
KL tax must expand that literal packet path, sample its successive
`2 mod 3` visits, reverse the resulting genuine full-lift edges, and only then
read deviations from the KL potential.  The boundary-core clock cannot be
used as a substitute.

The finite corrected bridge now carries out exactly that procedure.  For each
returning glider macro it reconstructs the complete breakoff-state chain,
checks the linked ordinary Collatz endpoints, expands the accelerated
valuation words to every one-halving state, and samples the successive
`2 mod 3` visits.  Only after every reversed pair passes one exact transport,
class-2, or class-8 equality does it consult the stored KL vector.

At ether lengths `1..6` and packet tail zero, the genuine edge counts are

```text
n       1       2        3        4        5        6
R2      6       8       10       12       14       16
R8      9      13       18       22       25       29
S       0       0        0        0        0        0.       (13.4)
```

Thus these literal packet paths are class-8-heavy outward chord paths, not
the sparse nonedge boundary clock.  The worker re-verifies the complete
level-12 KL certificate and checks, edge by edge, the exact rational
inequality

```text
weight(edge)*c(prescribed target)
  <= deviation(edge)*c(source),                     (13.5)
```

then verifies the telescoped product.  No critical-eigenvector equality is
assumed: the stored vector is a feasible subeigenvector with certified lower
weights, and a failed inequality suppresses the tax row.  All six rows pass
and all contain nonselected lifts.

Companion commit `82c01dd` makes the edge semantics independent of this
finite worker.  For every positive state `n=2 mod 3`, Lean identifies the
next visit to the same residue class and proves that the reversed pair is
exactly one KL principal edge: odd `n` gives the advanced chord, `n=0 mod 4`
gives transport, and `n=2 mod 4` gives the retarded chord.  It also proves
that the intermediate even-case state is not another `2 mod 3` visit.  Thus
literal Syracuse replay is sufficient to obtain a genuine KL path.

Equation (13.5) is finite calibration, not an obstruction to an infinite
ether ray.  The live theorem is now correctly posed: express the prescribed
KL lift sequence as a function of the actual macro tail, then determine
whether the period-three arithmetic forces typical/averaged tax or permits
one ordinary tail to track the exceptional low-tax fibers indefinitely.  The
variable ternary valuation inside the true endpoint chart is precisely why
the core odometer does not answer this automatically.

## 14. EC17 synchronization selects the rational ether cycle

The endpoint valuation is variable only before macro linkage is imposed.  For
a free length-`n` packet write

```text
K=R_n+2^(8n+15)q,
Z(K)=2^35*K-358513857,
r=v_3(Z),
C(K)+1=3*2^(r+1)*(Z/3^r).                         (14.1)
```

Because the coefficient of `q` in `Z` is `2^(8n+50)`, a 3-adic unit, the
complete system `q mod 3^d` has exact capped histogram

```text
# {q: v_3(Z)=j}=2*3^(d-j-1),  0<=j<d,
# {q: v_3(Z)>=d}=1.                                   (14.2)
```

Conditional on a finite rail, (14.1) is affine and uniform on
`{C:v_3(C+1)=1}={2,5 mod 9}`.  This is a free-tail chart theorem, not an
orbit distribution.

The EC17 core is related to `q` only after ten fixed ternary digits:

```text
u=u_base(n)+473*2^20*3^10*q.                       (14.3)
```

Thus the core condition `u=1 mod 3` is automatic and does not mean
`q=1 mod 3`.  Using `83790531=473*3^11`, direct cancellation gives

```text
473*3^10*Z=2^(8n+30)u-9591553,
9591553=17*(2^15+3^12).                            (14.4)
```

Now impose one genuine linked step

```text
2^(8m+15)u'=3^(6n+11)u+17.                         (14.5)
```

Equations (14.4)--(14.5) yield

```text
2^(8m+30)u'-9591553
 =3^12*(2^15*3^(6n-1)u-17).                        (14.6)
```

For `n>=1`, the bracket is `-17 mod 3`, hence a unit.  Therefore every
linked successor has

```text
v_3(Z')=2.                                         (14.7)
```

This is the decisive distinction between free tails and a coherent ray.  The
literal boundary formula simplifies further to

```text
473*C'+881=2^18*3^(6n)u,
v_3(473*C'+881)=6n.                                (14.8)
```

Consequently any linked chain with `n -> infinity` approaches the rational
3-adic center `-881/473`.  Also, if `d<=6n+1`, reducing (14.5) modulo
`3^(d+10)` annihilates the source term; after dividing the fixed `3^10` in
(14.3), `q' mod 3^d` is determined only by the target branch `m`.  There is
no exceptional tail choice at fixed precision once the preceding branch is
wide enough.

The literal router skeleton becomes

```text
[2,0,2,0,1,0]+[2,0]^(n-1),                         (14.9)
```

and hence

```text
N_2=2n+4,  N_8=4n+7,  N_S=0,
N_odd=6n+11,  N_half=8n+15.                        (14.10)
```

The repeated pair `[2,0]` is a six-edge KL cycle (in reverse KL direction a
cyclic word with two `R2` and four `R8` edges) whose ordinary affine map is

```text
F_E(x)=(729*x+881)/256,
F_E(-881/473)=-881/473.                             (14.11)
```

At level 12 the exact feasible certificate gives, for synchronized macros
`n=2..6`,

```text
Dev(n)=Dev_base*Dev_E^n,                            (14.12)
Dev_E=2.973148268...,
Dev_E/W_E=1.217522341....
```

The ether cycle has one selected and five nonselected lifts at this level.
All decimals in (14.12) are renderings of exact rational products stored in
the artifact.  This does not prove a critical-vector limit and does not
construct a ray.  It does show that KL is no longer an undirected diagnostic:
the period-three compiler is forced onto one explicit rational 3-adic KL
spine.  The remaining obstruction is entirely the existence and ordinary
dyadic coherence of one positive infinite EC17 chain.

The independent exact cycle worker extends (14.12) across all stored
certificate levels `12..19`.  It derives the rational centers

```text
881,1490,1151,1850,1391,1085,881  (all divided by 473)
```

and reconstructs every three-lift fiber from the SHA-pinned potential vectors.
The exact ratios `Dev_E/W_E` remain greater than one and decrease strictly:

```text
k       12       13       14       15
ratio   1.21752  1.16417  1.14829  1.11350

k       16       17       18       19
ratio   1.09709  1.07637  1.06627  1.05157.         (14.13)
```

Every adjacent inequality in (14.13) is stored as a positive exact integer
cross-product difference.  The cycle has one selected lift through `k=15`
and two from `k=16` onward.  The downward trend is evidence that the ether
cycle is a near-critical KL direction, not proof that the ratio tends to one
or that a compatible infinite ordinary path exists.

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

## 15. The KL center is a self-writing two-rail coordinate

The denominator `473` does more than identify the synchronized center.  For a
genuine branch-`n` packet, set

```text
z=3^(6n)u,                 R=(z-4)/473.
```

Packet validity implies `z=4 mod 473`.  Define two fixed affine maps

```text
D(R)=(3^11 R+1221)/2^15,
E(R)=(729 R+4)/256.                                  (15.1)
```

Their defining identities are

```text
3^11(473R+4)+17=2^15(473D(R)+4),
256(473E(R)+4)=729(473R+4).                          (15.2)
```

Consequently an EC17 transition to branch `m` is exactly

```text
R'=E^m(D(R)),
v_2(473D(R)+4)=8m.                                  (15.3)
```

The binary delay in (15.3) is written by `E^m` into the factor `3^(6m)` of
the next packet.  Under

```text
C=2^18 R+2215,
```

the map `E` is conjugate to `(729C+881)/256`, and the fixed point
`R=-4/473` is exactly `C=-881/473`.  The rational KL center has therefore
exposed the actual recharge--ether normal form of the packet map.

There is an integer-only compression.  Every packet has

```text
R=1044929+2^20 q,
Z(q)=494251421+495976448q,
W(q)= 83499104+ 83790531q,                           (15.4)
```

and coefficientwise

```text
3^11 Z(q)+17=2^20 W(q).                              (15.5)
```

For a valid current state `v_3(Z)=6n`.  If

```text
v_2(W)=8m-5,       h=W/2^(8m-5),
```

then continuation is precisely

```text
q'=(729^m h-494251421)/(473*2^20) in Nat.            (15.6)
```

On acceptance, `Z(q')=729^m h`; because `h=1 mod 3`, this has exact ternary
valuation `6m`.  Thus (15.6) is a deterministic self-writing mixed-radix
controller on one public nonnegative integer.

For a fixed target `m`, the two local conditions on `h` are

```text
h = 83499104*2^(-(8m-5))       (mod 473*3^11),
h = 494251421*729^(-m)         (mod 2^20).            (15.7)
```

CRT gives one class, and hence the complete branch

```text
q=a_m+2^(8m+15)t,
q'=b_m+3^(6m+11)t.                                  (15.8)
```

The source branch condition is a further coprime ternary class of `t`, so
every finite `n -> m` link exists.  This rules out using the synchronized
`r=2` rail or the factor `473` as a local obstruction.  Their real value is
the global recurrence (15.6).

The same calculation exposes the packet premise missing from a bare EC17
ray.  With `s=2^(8n-5)u`, put

```text
chi=s+291427 (mod 473).
```

Every EC17 step satisfies `chi'=316chi`; actual packets have `chi=0`.
Nonzero colors never enter the packet lattice, even if the bare EC17
recurrence is coherent.  One color-zero seed repairs the semantic bridge and
then propagates automatically.

Finally, every accepted transition has `q'>q`.  In `Z` coordinates its
leading multiplier is `3^(6m+11)/2^(8m+15)>1` for `m>=1`, and the additive
term is positive.  Hence the branch counter need not increase monotonically,
but this canonical payload counter must.  An infinite accepted orbit of
(15.6) would be an exact construction certificate.  None is known; the
artifact records `counterexample:null`.

Companion commit `7ca6d4f` kernel-checks (15.5) and packages a hypothetical
self-writing orbit by the two exact `Z`/`W` factorizations.  From that
hypothesis Lean derives the EC17 balance, strict payload monotonicity, and the
impossibility of an eventually periodic branch sequence.  The formal
definition deliberately does not infer an orbit from finite CRT rows.

## 16. Branch pressure and the invariant EC1 component

The useful lesson from the KL paper is thermodynamic rather than a direct
core-edge identification.  For target branch `m`, put

```text
P_m=8m+15,        Q_m=6m+11.
```

Eliminating the affine tail from (15.8) gives

```text
2^P_m q' = 3^Q_m q + delta_m,
delta_m=(3^(6m)W0-2^(8m-5)Z0)/473 > 0.             (16.1)
```

The target cylinders are pairwise disjoint because they prescribe different
exact values `v_2(W)=8m-5`.  A prescribed target schedule is therefore an
LSB-first variable-length code with lengths `23,31,39,...`.  Its exact Kraft
mass and schedule generating function are

```text
sum_(m>=1) 2^(-P_m) = 1/(255*2^15),
A(x)=1/(1-sum_(m>=1)x^P_m)=(1-x^8)/(1-x^8-x^23).   (16.2)
```

Consequently the usual prefix-code pressure dimension is the unique `d>0`
such that

```text
sum_(m>=1)2^(-d P_m)=1,
x^8+x^23=1,  x=2^(-d),
d=0.07065929109419928758... .                       (16.3)
```

The exact worker verifies the code-cylinder recurrence and a rational bracket
for the root of (16.3).  The Hausdorff-dimension interpretation is the standard
Bowen/prefix-code consequence, not yet a Lean theorem in this repository.
It explains why a flat branch box is wasteful and why typical infinite
schedules are only 2-adic: an ordinary seed is an exceptional eventually-zero
address inside a set of very small dimension.  Dimension alone cannot decide
whether one such exceptional natural exists.

There is a more arithmetic invariant component.  Both offsets in (15.4) are
divisible by `17`.  Since the two strides are units modulo `17`,

```text
17|q  <->  17|Z(q)  <->  17|W(q),
```

and this condition is preserved and reflected by every accepted step.
Writing `q=17r` gives

```text
Zbar(r)=29073613+495976448r,
Wbar(r)= 4911712+ 83790531r,
3^11 Zbar(r)+1=2^20 Wbar(r).                        (16.4)
```

Thus if consecutive normalized cores are `u=17v`, `u'=17v'`, an accepted
`n -> m` step reduces exactly to

```text
2^(8m+15)v'=3^(6n+11)v+1,       v,v'=2 (mod 3).    (16.5)
```

This is the irreducible EC1 unit component.  It is not the KL predecessor
graph: attaching the KL core-edge tax directly is still invalid for the
defect reason in the failure ledger.

The unit component nevertheless has a schedule-independent all-depth
obstruction.  Modulo `17`,

```text
Zbar(r)=9+3r,       Wbar(r)=4+13r,
r'-14=6*(-2)^(m-1)*(r-1).                           (16.6)
```

The current core contains `17^2` exactly when `r=14`; the successor core
contains `17^2` exactly when `r=1` (equivalently `r'=14`).  These source
classes are disjoint.  Hence every accepted unit-component step satisfies

```text
min(v_17(u),v_17(u'))=1.                            (16.7)
```

Deep `17`-adic core events can never be adjacent and have upper density at
most one half along any hypothetical orbit.  Restricting to `17|q` does not
change the dyadic or ternary local code geometry—multiplication by `17` is a
unit in both residue towers—and every finite `n -> m` link remains CRT
solvable.  So (16.7) is a real filter for invariant ansatzes, not a no-orbit
theorem.

The worker
`experiments/kontorovich/breakoff_ether_branch_pressure.py` checks (16.1)--
(16.7), constructs 1,278 distinct schedule cylinders through 160 source bits,
and lifts the higher `17`-adic branch checksum through precision 12.  Its
artifact has `counterexample:null`.

## 17. Shallow rails are writable, and color zero closes the packet rail

The finite mod-17 system does not merely alternate shallow and deep cores.
Removing the two residues `1,14` gives one strongly connected 15-state graph,
and each branch class modulo eight has a fixed shallow residue:

```text
j                 1  2  3  4  5  6  7  8
r_j              12  2 13  3 15  6  9  0.         (17.1)
```

Thus the conditional language

```text
m_t=j (mod 8),       q_t/17=r_j (mod 17)            (17.2)
```

keeps every normalized core at exact 17-adic depth one.  Its branch alphabet
has lengths `P_(j+8k)=8j+15+64k`, hence

```text
K_j=2^(-(8j+15))/(1-2^-64),
A_j(x)=(1-x^64)/(1-x^64-x^(8j+15)),
x^64+x^(8j+15)=1.                                  (17.3)
```

The largest pressure dimension is `0.0250459467556681664...`, for `j=1`.
This is a rigorous search compression, not an exclusion: a countable set of
ordinary integers can meet a set of arbitrarily small Hausdorff dimension.

The first higher digit makes the constructive meaning explicit.  On the
`j=1` rail, write

```text
r=12+17s,       m=1+8ell.
```

Then

```text
s'=6s+10ell+13 (mod 17).                           (17.4)
```

The branch coefficient `10` is invertible.  The other seven rails have the
same property, with coefficient triples

```text
(6,10,13), (5,9,3), (7,5,8), (3,4,0),
(11,12,16), (12,6,12), (10,8,10), (14,2,0).        (17.5)
```

In `x=Zbar(r)` coordinates the complete higher clock is

```text
x'=(729/256)^m (3^11*x+1)/2^15.                   (17.6)
```

Because `v_17(3^48-2^64)=1`, LTE says that changing `m` by `8d`
changes a shallow output at exact valuation `1+v_17(d)`.  Consequently
source and target residues modulo `17^k` decode `m modulo 8*17^(k-1)`.
Higher payload digits are a writable branch counter.  A stationary all-depth
lift forces stationary branch data and is impossible for a positive orbit;
an evolving aperiodic counter is not.

The packet-promotion conditions also collapse.  For any positive bare EC17
step

```text
2^(8m+15)u'=3^(6n+11)u+17,
E=3^(6n)u-494251421,
```

subtracting (15.5) gives

```text
3^11 E=2^20(2^(8m-5)u'-83499104).                 (17.7)
```

Thus the factor `2^20` in `OnZRail` is automatic.  Moreover

```text
473|E  <->  2^(8n-5)u+291427=0 (mod 473),          (17.8)
```

which is exactly packet color zero.  Since
`0<494251421<473*2^20` and the constant is not divisible by three, a positive
branch cannot give `E=0`, and a stride-divisible `E` cannot be negative.
Therefore a positive bare EC17 ray plus color zero at one state already lies
on the full nonnegative packet rail.  The live ordinary construction gate is

```text
eventual zero canonical dyadic carry + one color-zero seed. (17.9)
```

Companion commit `ded9c30` kernel-checks the stronger iff: for any supplied
positive bare ray, color zero at a chosen state is equivalent to promotion of
its one-step tail.

There is an even cleaner equivalent construction coordinate.  The public
payload itself obeys the branch-only reset program

```text
2^(8m+15)q'=3^(6m+11)q+delta_m.                   (17.10)
```

Companion commit `d4a8edf` proves that eventual-zero canonical carry for
(17.10) constructs a self-writing orbit after the necessary one-state shift,
and that every supplied self-writing orbit has eventual-zero public carry.
Thus (17.10), rather than the bare defect-one core program, is the primary
search and falsification interface; it folds color and full packet semantics
into one ordinary-address condition.

The shallow odd checksums do not help at finite depth.  By CRT, every finite
dyadic reset cylinder can be intersected with a prescribed color and shallow
residue class, then shifted high enough to make all finite quotients positive.
Only literal stabilization of the least dyadic representatives can decide an
ordinary infinite seed.  The theorem-driven role of (17.4)--(17.6) is to
select schedules for that carry problem, not to replace it with a residue
scan.

Companion commit `3ebde99` upgrades this last finite warning to a universal
Lean theorem for all eight rails: every finite branch word in the chosen
class has a strictly positive exact public chain in the fixed payload class
modulo `17^2`.

## 18. The public address is one variable-exponent KL theta value

The branch defect in (16.1) has a telescoping form that is hidden in the raw
integer constants.  Define

```text
alpha_m=2^(8m+15)/3^(6m+11),
A=83499104/(473*3^11),
B=494251421/(473*2^20).
```

The determinant identity gives

```text
epsilon=A-B=17/(473*2^20*3^11),
delta_m/3^(6m+11)=A-B*alpha_m.                    (18.1)
```

For targets `m_0,...,m_(N-1)`, put

```text
R_0=1,       R_j=product_(i<j)alpha_(m_i).
```

Backward unrolling of the exact public recurrence (17.10) and substitution
of (18.1) telescope to

```text
q_0+A+epsilon*sum_(1<=j<N)R_j=R_N*(q_N+B).        (18.2)
```

The v3 branch-pressure artifact checks (18.2) independently on every one of
the 1,278 stored schedule cylinders through 160 source bits.  It is a
universal rational identity; the finite audit guards indexing and constants.

For an ordinary infinite public chain, every `q_N` is a natural and
`v_2(R_N)>=23N`, so the right side tends to zero in `Q_2`.  Therefore

```text
q_0=-A-epsilon*Theta,
Theta=sum_(j>=1)R_j=-2^20*W(q_0)/17.              (18.3)
```

The schedule enters only through cumulative branch positions:

```text
R_j=(2^15/3^11)^j*(2^8/3^6)^M_j,
M_j=sum_(i<j)m_i.                                  (18.4)
```

Thus the complete ordinary-address problem is one variable-exponent
Tschakaloff/KL series.  Its tails obey

```text
Theta_t=alpha_(m_t)*(1+Theta_(t+1)),
v_2(Theta_t)=8m_t+15.                              (18.5)
```

Equation (18.5) shows that the series and the deterministic public program
contain exactly the same branch information.  For arithmetic `M_j`, (18.4)
is the partial-theta specialization already excluded by the inspected 1989
theorem.  Periodic increment words split into the previously studied finite
multi-theta systems.  Neither result applies to arbitrary nonlinear,
payload-written `M_j`.

On the invariant unit slice `q_0=17r`, (18.3) becomes

```text
Theta=-2^20*Wbar(r),                               (18.6)
```

a negative ordinary integer.  Hence the shallow 17-adic rails are naturally
coupled to the theta problem: they select branch digits inside a one-series
integer-value problem.

The constructive problem is now precise: choose a genuinely nonlinear
increasing exponent sequence satisfying the public branch semantics for which
the `Q_2` value in (18.3) is the exact rational attached to some `q_0>=0`.
The small pressure quantifies how exceptional such a digit expansion is;
the shallow 17-adic clock supplies a writable selector for its exponent
positions.  No theorem here says that the rational lattice is hit, and no
counterexample is known.

## 19. One lattice hit is sufficient, and fresh counter depth has a price

The tail equation (18.5) removes a possible hidden gate.  Suppose only that
the initial series value is an ordinary negative integer,

```text
Theta_0=-X_0.
```

The first term has uniquely least dyadic valuation, so
`v_2(Theta_t)=8m_t+15`.  Consequently every suffix is forced to be an ordinary
negative integer and

```text
X_t=2^(8m_t+15)h_t,
X_(t+1)=3^(6m_t+11)h_t+1.                          (19.1)
```

If `X_0=2^20*Wbar(r_0)`, the affine packet lattice propagates as well.  The
proof uses only the reduced determinant identity and

```text
3^6=2^8 (mod 473),       32Wbar(0)=Zbar(0) (mod 473).
```

Indeed, with `z'=3^(6m_t)h_t`, equation (19.1) reads
`X_(t+1)=3^11z'+1`.  Its suffix valuation gives divisibility by `2^20`;
the two displayed congruences give `z'=Zbar(0)` modulo `473`, while the
determinant identity gives the remaining `3^11` factor.  Thus there is a
nonnegative `r_(t+1)` with

```text
z'=Zbar(r_(t+1)),       X_(t+1)=2^20Wbar(r_(t+1)). (19.2)
```

Also `h_t=2 (mod 3)`, so the ternary factor in (19.2) is exact.  Therefore a
single equality `Theta=-2^20Wbar(r)` is already a construction certificate
for the whole accepted public orbit after the standard one-step shift.  There
is no additional suffix-integrality or lattice condition to search.

Companion commit `3f7cc7c` kernel-checks the tail functional equation, its
exact norm, and propagation of ordinary suffix integrality.  The
`Wbar`-lattice propagation in (19.2) and final orbit assembly remain the
unformalized part of this converse; QM151b now records their exact indices.

The same one-series form recovers the universal counter-growth sieve already
proved in the normalized EC17 core coordinate.  Its public-theta form is
useful because it applies directly to the exact lattice target.  Put

```text
M_N=sum_(i<N)m_i,
D_N=11N+6M_N,
V_N=15N+8M_N,
S_N=sum_(1<=j<=N)R_j=A_N/3^D_N.
```

If `Theta=-K` for a positive integer `K`, the first omitted term has exact
valuation `V_(N+1)`.  Since `alpha_m<=alpha_1<1/2`, the real partial sum lies
strictly between zero and one.  Hence

```text
2^V_(N+1) <= K*3^D_N+A_N < (K+1)*3^D_N.           (19.3)
```

Using the exact separator `3^41<2^65`, (19.3) bounds the fresh-branch excess

```text
41V_(N+1)-65D_N
  =328m_N-62M_N-100N+615.                          (19.4)
```

In particular an unbounded positive excess is impossible.  A convenient
corollary is that schedules with `m_N>=M_N` at arbitrarily late indices are
excluded, because then

```text
2^V_(N+1)/3^D_N
  >=2^15*(2^31/3^17)^N -> infinity.                (19.5)
```

This restates, rather than supersedes, the existing kernel-checked EC17 scale
budget and online branch ceiling.  It answers the counter-growth question
precisely.  Branch values need not
be bounded and are not known to be forced to infinity, but a new branch may
not outrun the cumulative depth that financed it.  Naive exponentially deep
digit clocks and superincreasing schedules are closed.  Slow nonlinear
counters remain live.  The v4 exact artifact checks all constants and the
exponent elimination in (19.4); QM151 requests the universal Lean package.

There is also a constructive no-go hidden in the telescope.  If an ansatz
writes `R_j=T_j-T_(j+1)` with one rational boundary `T_N` tending to zero both
really and 2-adically, then `Theta=T_1` is the same positive rational in both
completions and can never be (18.6).  The boundary of a genuine orbit is
necessarily asymmetric: it tends to zero in `Q_2` but to
`K+sum_(j>=1)R_j>0` in the real metric.  A successful closed-form controller
must manufacture this adelic separator explicitly; a local decaying
coboundary cannot work.

## 20. Wang's theorem closes the slow 17-ruler

For the valuation ruler

```text
m_n=j+8*v_17(n+1),          1<=j<=8,
```

Legendre's formula turns the theta series into one exact Mahler function.
Let

```text
a=2^15/3^11, b=2^8/3^6, z_j=a*b^j, c=b^8,
F_c(z)=sum_(n>=0)c^v_17(n!)*z^n.
```

Then `1+Theta=F_c(z_j)`, and

```text
F_c(z)=(1+z+...+z^16)F_c(c*z^17).                 (20.1)
```

Because `c^(1/16)=16/27`, a rational rescaling converts (20.1) to a standard
17-Mahler equation.  Put `kappa=16/27`.  Legendre's digit-sum formula gives

```text
16v_17(n!)=n-s_17(n),
G(x)=sum_(n>=0)kappa^(-s_17(n))*x^n
    =product_(k>=0)P_17(x^(17^k)/kappa),            (20.2)
G(x)=P_17(x/kappa)G(x^17).
```

Its required value is exactly

```text
G(2^(19+8j)/3^(14+6j))=1-2^20Wbar(r).             (20.3)
```

The complex product is holomorphic in the unit disk.  Its zeros satisfy

```text
x^(17^k)=kappa*zeta,       zeta^17=1, zeta!=1.
```

They approach every point of the unit circle from inside, so the identity
theorem rules out analytic continuation through any boundary point.  Thus
`G` has the unit circle as a natural boundary and is transcendental over
`C(x)`.  Since its coefficients are rational, a finite-linear-system scalar
descent transfers this to transcendence over `C_2(x)`.

Wang's 2006 p-adic Mahler-value theorem now applies with

```text
p=2, rho=17, N=1,
Q_0(z,u)=P_17(z/kappa), Q_1(z,u)=-u,
M_0=17,       M_0N^2=17<17^2.
```

For `x_j=2^(19+8j)/3^(14+6j)`, one has
`|x_j|_2=2^(-(19+8j))<1`, and the required elimination polynomial never
vanishes because `P_17(x_j^(17^k)/kappa)>0` in the real embedding.  Wang's
theorem therefore makes every `G(x_j)` transcendental in `Q_2`, contradicting
the ordinary integer in (20.3).  All eight slow schedules are excluded.

This conclusion uses the source-audited published theorem, not merely the
function's nonrationality.  Version 5 of the exact artifact checks the
digit-sum conversion, all specializations, and the elementary theorem
hypotheses.  The companion request QM153 asks Lean to connect the functional
equation to the already checked theta endpoint.  Amplified rulers remain
independently excluded by (19.3), and no counterexample is constructed.

## 21. The place-value ruler reaches a genuinely bivariate boundary

Replace the valuation itself by its 17-adic place value:

```text
m_n=j+8*17^v_17(n+1),          1<=j<=8.
```

Set

```text
A_n=sum_(1<=t<=n)17^v_17(t).
```

Splitting at `17n+r` gives the exact recursion

```text
A_(17n+r)=17A_n+16n+r,          0<=r<17.           (21.1)
```

In digit form, if `n=sum_i d_i17^i`, this is

```text
A_n=d_0+sum_(i>=1)d_i17^(i-1)(17+16i).             (21.2)
```

With `c=(2^8/3^6)^8`, `z_j=(2^15/3^11)(2^8/3^6)^j`, define

```text
H(C,Z)=sum_(n>=0)C^A_n Z^n.
```

Then

```text
1+Theta=H(c,z_j),
H(C,Z)=P_17(CZ)H(C^17,C^16Z^17).                  (21.3)
```

The associated monomial transformation

```text
T(C,Z)=(C^17,C^16Z^17)
```

has the exact iterate and product

```text
T^k(C,Z)=(C^(17^k),C^(16k17^(k-1))Z^(17^k)),
H(C,Z)=product_(k>=0)
  P_17(C^(17^k+16k17^(k-1))Z^(17^k)).             (21.4)
```

There is no scalar rational base hidden in the eight specializations.  In
the prime-exponent plane,

```text
c   -> (64,-48),
z_j -> (15+8j,-11-6j),
det -> 16.                                         (21.5)
```

The stronger research-side statement is Zariski density of the forward
orbit.  Indeed, a monomial `C^pZ^q` at `T^k(c,z)` has real logarithmic size

```text
17^k[p log(c)+q log(z)+(16/17)qk log(c)].          (21.6)
```

Because `0<c,z<1`, the lexicographically least `(q,p)` in a nonzero Laurent
polynomial uniquely dominates for large `k`, precluding vanishing on the
whole orbit.  Companion commit `0e3fcf8` kernel-checks the exact block law,
functional equation, Jordan iterates, and determinant.  Version 7 of the
executable artifact additionally gives the exact `2`-adic valuation of every
monomial and constructs a depth after which one monomial in any supplied
finite polynomial has uniquely least valuation.  This is a zero-estimate
ingredient, not a special-value theorem.

The public height obstruction is silent here for a structural reason.  At
the spike indices,

```text
A_(17^k-1)=16k17^(k-1),                            (21.7)
```

so the cumulative depth is of order `k17^k`, larger than the fresh
`17^k` spike.  Thus neither (19.3) nor Wang's univariate theorem closes this
schedule.  The natural complex multivariate theorem inspected in the
literature is not a ready substitute: the exponent matrix
`[[17,0],[16,17]]` is a defective Jordan block outside its audited
admissibility hypothesis, and that theorem is not 2-adic in any event.

Wang's 2009 paper
[“Transcendence Measure for the Value of Mahler Type Functions with Several
Variables”](https://actamath.cjoe.ac.cn/Jwk_sxxb_cn/EN/10.12386/A2009sxxb0026)
was also audited as a possible replacement.  The primary metadata and
abstract describe multivariable nonlinear Mahler values but contain no
`p`-adic setting; the journal's PDF object is empty and the available mirror
copies require login, so its exact monomial-map hypotheses cannot responsibly
be certified here.  Even if the defective Jordan matrix were admissible, its
advertised complex special value is not the completion-specific `Q_2` sum in
(21.8).  This paper therefore does not close the seam; matrix admissibility is
recorded as unknown, not as a theorem failure.

The closely related 2010 Liu--Hao paper
[“Algebraic Independence of the Values of Mahler Functions”](https://sxjk.magtechjournal.com/CN/Y2010/V25/I2/191)
is openly available and makes the structural exclusion explicit.  For a
monomial transformation with spectral radius `d`, it requires every entry of
the `k`th matrix power to be `O(d^k)`.  Our Jordan power has off-diagonal entry
`16k17^(k-1)`, so it fails this hypothesis exactly.  Its theorem and proof are
also formulated over complex holomorphic germs and ordinary absolute values,
despite an introductory comparison with a `p`-adic analogue.  This nearby
theorem therefore confirms both obstructions without licensing an inference
about the unavailable 2009 theorem text.

The resulting target is exact but open:

```text
H(c,z_j)=1-2^20Wbar(r).                            (21.8)
```

A useful next theorem would be a multivariate `Q_2` Mahler-value result for
this Jordan map, or a direct auxiliary-function proof specialized to (21.3).
Version 7 of the artifact checks (21.1)--(21.7), including eventual monomial
separation, in the stated exact and finite regression ranges.  It makes no
value or orbit claim.

## 22. The minimal raw outward system is critical, and an orbit is an atom

The YAH/tag compiler is sufficient hardware for a counterexample, but it is
not a sensible default search space.  Its cheapest public instruction consumes
23 address bits and its schedule dimension is only `0.070659...`.  Strip the
construction back to the raw shortcut map.

For a parity word `w`, write

```text
S(w)=length(w),  O(w)=number of odd sources,
R(w)=3^O(w)/2^S(w).
```

Let `F` be the strict ascending first-passage code:

```text
R(w)>1, and R(u)<=1 for every proper prefix u of w. (22.1)
```

It is prefix-free.  More strongly, every outward word has a unique prefix in
`F`, so replacing each word of any outward prefix-free code by its
first-passage prefix proves that `F` is maximal in both ordinary and tilted
Kraft mass.  The first crossing layers are

```text
(S,count)=(1,1),(3,1),(6,2),(9,7),(11,30),...
F_(<=6)=F_(<=8)={1,011,001111,010111}.             (22.2)
```

This retrospectively identifies the signed thin language of Section 12 as the
canonical finite truncation, rather than an arbitrary controller sample.

Put

```text
p(w)=2^-S(w),       q(w)=p(w)R(w)=3^O(w)/4^S(w).  (22.3)
```

The `p` law is fair parity and has negative logarithmic slope drift.  The `q`
law is Bernoulli parity with odd probability `3/4`; its log drift is positive
because `3^3>2^4`.  Consequently `q` reaches (22.1) almost surely, and the
stopped martingale gives

```text
P=sum_(w in F)p(w)<1,       sum_(w in F)q(w)=1.    (22.4)
```

For every first passage, `1<R(w)<=3/2`.  If `P_L,Q_L` are the exact masses
through length `L`, the unobserved `q` tail therefore gives

```text
P_L+(2/3)(1-Q_L) <= P <= P_L+(1-Q_L).             (22.5)
```

The exact dynamic program uses the subcritical state count

```text
b_(n,k)=1_(3^k<=2^n)*(b_(n-1,k)+b_(n-1,k-1)).    (22.6)
```

At `L=256`, (22.5) is the rational interval whose decimal rendering is

```text
0.713684569145118094... < P < 0.713684640996637644...,
1-Q_L=0.000000215554558648... .                   (22.7)
```

The exact values, all crossing counts, source hash, and `counterexample:null`
are in `outward_first_passage_audit.json`.

Schema v2 evaluates the minimum-address invariant itself by exhaustive exact
ordinary replay.  For every positive source through `300000`, the shortcut
orbit is followed to the `1--2` cycle, yielding the certified record changes

```text
(n,h_n)=(1,1),(2,3),(3,7),(4,15),(5,27),(16,703),
        (17,4255),(20,4591),(22,31911),(25,77671),
        (26,113383),(28,159487),(30,270271).       (22.7a)
```

The value remains constant between change points through `h_36`, and
`h_37>300000`.  The last record source still reaches the terminal cycle.
This is a bounded theorem-variable audit, not a trend extrapolation or an
infinite-orbit claim.

Critical ensemble mass is not a single orbit.  For a concatenation `u`, the
shortcut identity is

```text
2^S(u) T^S(u)(x)=3^O(u)x+A(u),  A(u)>=0.
```

Let `r(u)` be the least nonnegative solution of its parity cylinder, and set

```text
h_n=min_(u in F^n)r(u).                            (22.8)
```

Extension has the exact form

```text
r(uv)=r(u)+2^S(u)*ell(u,v),  ell(u,v)>=0.          (22.9)
```

Hence `h_n` is nondecreasing.  Boundedness of `h_n` forces one natural in a
fixed finite window to realize arbitrarily many depths.  Prefix-free parsing
is deterministic, so that same natural realizes every depth.  Conversely an
infinite ordinary survivor bounds `h_n`.  Thus

```text
ordinary positive infinite F-orbit
  <-> h_n bounded
  <-> h_n eventually constant
  <-> one path has eventually zero extension carry. (22.10)
```

Companion commit `8959436` kernel-checks the literal shortcut-execution core
of (22.10): an all-depth execution exists iff the canonical minimum-start
sequence has bounded range iff it is eventually constant.  The proof builds
positive parity-cylinder witnesses, proves nestedness in depth, and applies
finite-window infinite pigeonhole; it assumes no mass or probabilistic
selection principle.

Each block is outward, so such an orbit would be strictly increasing and
would disprove Collatz.

The measure form identifies exactly why KL-style branching does not yet do
this.  A projectively consistent flow suffices if its canonical residues are
uniformly tight; a uniform first-moment bound is stronger and sufficient.
But the natural critical product flow is diffuse.  Since every block has
`q(w)<=q(1)=3/4`, and at most `B` distinct deterministic paths can have
canonical residue at most `B`,

```text
mu_q{r_n<=B} <= B*(3/4)^n.                         (22.11)
```

It escapes every fixed ordinary-height window.  Therefore the next
construction theorem is not positive pressure, another KL eigenmeasure, or a
larger tag program.  It is an arithmetic, necessarily atomic, aperiodic
selector proving `sup_n h_n<infinity`.  Any proposed Doob transform must be
audited against (22.11): if it remains uniformly diffuse, it cannot solve the
ordinary-seed problem.

## 23. Odd-charge compression and triadic min-plus renewal

Section 22 identifies the atom gate.  It can be sharpened in both the forward
and inverse directions without returning to YAH hardware.

### 23.1 A sub-`2^n` carry bound is enough

Along a coherent concatenation, let `L_n` be the total shortcut length after
`n` nonempty first-passage words and let `rho_n` be the canonical least
source residue.  Cylinder extension is

```text
rho_(n+1)=rho_n+2^L_n ell_n,   ell_n>=0,
L_n>=n.                                                   (23.1)
```

Thus every nonzero carry obeys

```text
ell_n>0  =>  rho_(n+1)>=2^n.                              (23.2)
```

This yields a substantially weaker sufficient condition than uniform
tightness:

```text
rho_n=o(2^n), or limsup rho_n^(1/n)<2,
  => ell_n=0 eventually
  => one ordinary infinite first-passage execution.       (23.3)
```

For a projectively consistent selector measure, Markov's inequality gives

```text
Pr(ell_n>0)<=E[rho_(n+1)]/2^n.                            (23.4)
```

Hence summability of the right side forces eventual zero carry almost surely
by Borel--Cantelli.  This is not a constructed selector.  Companion commit
`e48bd60` kernel-checks the elementary deterministic core (23.1)--(23.3) and
its frequent-carry contrapositive; the measure corollary remains
research-side.

The ordinary renewal law also calibrates proposed selectors.  Put
`P=sum_F p(w)`.  Prefix-freeness gives the exact defective geometric law

```text
p(complete at least n blocks)=P^n,
p(complete exactly n blocks)=(1-P)P^n.                    (23.5)
```

Conditioning fair parity on `n` completed blocks factorizes as the product
law

```text
p_hat(w)=p(w)/P.                                          (23.6)
```

Its projective survival limit is still diffuse.  Its largest block atom is
the word `1`, with probability

```text
max_w p_hat(w)=1/(2P)=0.7005895... .                       (23.7)
```

At most `B` deterministic word paths can have positive canonical residue at
most `B`, so

```text
nu_hat{rho_n<=B}<=B*(1/(2P))^n.                           (23.8)
```

The classical ladder-epoch Doob process therefore does not produce an
ordinary atom.  A viable arithmetic kernel must place positive mass on one
path, which for transition probabilities `k_n` requires
`product k_n>0`, equivalently `sum(1-k_n)<infinity` after excluding zero
terms.  In operational language, it must become summably deterministic along
one genuinely aperiodic arithmetic trajectory.  Equations (23.5)--(23.8) are
an exact research-side derivation; the artifact checks the rational `P`
bracket and its numerical consequences, while QM157 records the formal seam.

At depth 36 the exact bracket gives

```text
1.438886352945... < 270271*P^36 < 1.438891568006....       (23.9)
```

This explains why the record scale is not astronomically anomalous under a
renewal heuristic, but it is not a uniform density theorem.  Exact replay in
`[1,300000]` finds survivor counts

```text
depth 1: 214170,   depth 15: 1559,
depth 30: 2,       depth 36: 1,       depth 37: 0.         (23.10)
```

The fixed-depth natural density is `P^n`; using it uniformly at
`n` comparable to `log B` would require a new short-interval discrepancy
theorem for parity cylinders.

### 23.2 The canonical odd-charge map

Every first-passage word ends in an odd shortcut step, so its endpoint is
`2 mod 3`.  Write every completed boundary uniquely as

```text
x=3H-1,    H=(x+1)/3>0.                                  (23.11)
```

If `H` is even, then `x` is odd.  The next word is forced to be `1`, and its
charge action is

```text
H |-> 3H/2.                                               (23.12)
```

Consequently the run of one-letter blocks has length exactly `v_2(H)`.
Every infinite execution must contain infinitely many nontrivial recharge
words.

Let a nontrivial word `w` have affine data

```text
2^S T^S(x)=3^O x+A_w
```

and define

```text
e_w=(A_w+2^S-3^O)/3.                                    (23.13)
```

Such a word starts in `0`: otherwise its first bit would already be the word
`1`.  It ends in `11`: if the penultimate bit were zero, the last two slope
factors could raise a nonoutward prefix only to `3/4`.  For
`E_w=A_w+2^S-3^O`, appending a bit gives

```text
E_(w0)=E_w+2^S,       E_(w1)=3E_w.                       (23.14)
```

The initial zero makes the defect positive and the terminal two ones make
`3|e_w`.  If `w` maps `3H-1` to `3K-1`, substitution into its affine identity
gives

```text
2^S K=3^O H+e_w.                                        (23.15)
```

In particular `3|K`.  On an odd input charge, take the unique literal
nontrivial first-passage word, put

```text
K=(3^O H+e_w)/2^S,   a=v_2(K),
R(H)=3^a K/2^a.                                         (23.16)
```

This compresses the recharge and its `a` forced one-letter drains.  It maps
positive odd charges to positive odd charges, consumes `1+a` first-passage
blocks, and satisfies

```text
R(H)>H,
v_3(R(H))=a+v_3(K)>=a+1,
3R(H)-1 == -1 (mod 3^(a+2)).                            (23.17)
```

Thus dyadic recharge becomes exact ternary proximity to the signed fixed
point `-1`.  Discarding the first completed boundary and its finite initial
drain proves, research-side,

```text
ordinary infinite first-passage execution
  <-> infinite orbit of the partial map R on positive odd H.              (23.18)
```

QM157 asks for the kernel-checked package.  Schema v3 independently replays
every displayed finite identity.

For the shallow word `011`, `S=3`, `O=2`, and `e=3`.  Legality is
`H=5 mod 8`, and

```text
K=3(3H+1)/8,
a=v_2(3H+1)-3.                                          (23.19)
```

Writing `H=3^c u` and `R(H)=3^c' u'`, with primitive odd cofactors, gives

```text
2^(c'+2)u'=3^(c+1)u+1,
v_2(3^(c+1)u+1)=c'+2.                                  (23.20)
```

An infinite solution would already be a counterexample in the `{1,011}`
subsystem.  The finite source `159487` realizes

```text
(c,u): (7,623) -> (2,255469) -> (12,421) -> (7,1310957), (23.21)
```

after which the next repetition is illegal.  This is not a cycle.

### 23.3 Exact inverse renewal on triadic fibers

For any parity word `w`, let `r_w in [0,2^S)` be its canonical source
residue and let `b_w=T^S(r_w)`.  Induction on bits gives

```text
0<=b_w<3^O,
2^S b_w=3^O r_w+A_w,
(source,target)=(r_w+2^S t,b_w+3^O t), t>=0.             (23.22)
```

Let `E_n` be the set of positive seeds completing `n` blocks.  If

```text
m_n(k,a)=min(E_n intersect {x:x=a mod 3^k}),
tau_n(w)=min {t>=0:b_w+3^O t in E_n},                    (23.23)
```

with infinity for an empty fiber, then the first-block decomposition is the
exact min-plus recurrence

```text
h_(n+1)=min_(w in F) [r_w+2^S tau_n(w)]
       =min_(w in F)
          [r_w+2^S(m_n(O,b_w)-b_w)/3^O].                 (23.24)
```

This exposes why scalar record minima are not a coherent selector: they throw
away the target's triadic phase.  Successive record seeds share only
`2,2,5,4,3,4,5,3,6` first-passage blocks after the initial records, while
the last seed's exceptional tail comes from literal post-address renewal.

There is a sharper scalar slice.  The first-passage boundaries are successive
strict record highs of the cumulative log slope.  Deleting an initial even
step preserves every later strict record, and may add records.  Therefore the
odd part of a source completes at least as many blocks, so every `h_n` is odd.
Its first word is `1`.  With

```text
m_n=min {y in E_n:y=2 mod 3},
```

the bijection `y=(3h+1)/2` gives

```text
h_(n+1)=(2m_n-1)/3.                                     (23.25)
```

Schema v3 checks (23.25) on every certified minimum through `h_36`.  QM158
requests the general Lean theorem.  The resulting search program is
principled: propagate finite approximations to the min-plus 3-adic profile,
look for a coherent branch satisfying (23.3), and use `R` as the smallest
forward state.  A proof in the opposite direction would seek a coercive
Archimedean--2-adic--3-adic barrier for (23.16) or (23.24).  Merely widening
the seed scan does neither.

### 23.4 What the record orbit proves

For `270271`, the first block reaches `H=135136`; five forced `1` drains give
the first odd charge `H_0=1026189`.  The artifact then checks 13 nontrivial
recharges, whose output charges end at

```text
1154463, 2773845, 35545311, 85405077, 324272403,
346281129, 493044813, 554675415, 562243005, 632523381,
1601074809, 1622918709, 4108012983.                       (23.26)
```

The source address is fully consumed at block eight and state `3698459`.
There are then 28 complete zero-carry extensions.  The last odd visualizer
boundary after stabilization is

```text
3698459 -> 8216025965
```

in 72 accelerated steps and 27 completed extensions.  The next recharge is
undefined and the orbit reaches the terminal cycle.  These are exact finite
renewal data and a useful target for the bit visualizer; they do not imply an
infinite escape.  The artifact continues to record `counterexample:null`.

## 24. Growing phase precision and directed carry repair

The dual-residue family (23.22) gives the complete phase-aware operator, not
only the scalar minimum.  For a desired source phase `a mod 3^k`, define

```text
c=(a-r_w)*2^(-S) mod 3^k,
d=b_w+3^O*c,       0<=d<3^(O+k).                   (24.1)
```

Then `x=a mod 3^k` iff its family parameter is `t=c mod 3^k`, iff the target
is `y=d mod 3^(O+k)`.  Therefore

```text
m_(n+1)(k,a)=min_(w in F)
 [r_w+2^S(m_n(O+k,d)-b_w)/3^O].                   (24.2)
```

This is exact, but it explains why a fixed finite-state profile is not enough:
even word `1` raises the queried input precision from `k` to `k+1`.  At finite
source height `B`, define

```text
W_B={w in F:r_w<=B},
T_w(B)=floor((B-r_w)/2^S),
C(B)=max_(w in W_B)[b_w+3^O*T_w(B)].               (24.3)
```

The canonical source residue determines a first-passage word injectively, so
`|W_B|<=B`.  Every source at most `B` uses a word in `W_B`, and its target is
at most `C(B)`.  Hence `E_(n+1) intersect [1,B]` is determined by the finite
word table and `E_n intersect [1,C(B)]`.  A precision `3^K>C(B)` is then an
exact membership bitmap and answers every higher-modulus query.  Nonzero
family parameters satisfy the sharper target bound `y<=3B-1`; only a
zero-carry canonical word can make `C(B)` larger.

The exact `outward_minplus_profile` artifact checks (24.2) for `B=50`,
`C(B)=74`, depths through six, and every phase `k<=3`.  The complete table is

```text
(S,O,r,b): (1,1,1,2), (3,2,6,8), (6,4,18,26),     (24.4)
words:     1,          011,         010111.
```

All 240 operator comparisons with literal execution pass.  This certifies the
finite operator; it does not stop the required phase depth from growing in the
inverse limit.  Companion commit `a0e460d` kernel-checks the general
dual-residue family (23.22), and `8d79424` proves the finite active-code
min-plus minimum theorem.  Commit `4c39f8d` proves the full growing-phase
equivalences and phase-refined finite active-code minimum.  Commit `1aec3fc`
proves the literal residue-two predecessor equivalence, and `5448445` proves
odd-part monotonicity and the unconditional formula (23.25).

The carry threshold also turns a failed prefix into a directed candidate
family.  The 36-block prefix of `270271` has cumulative length 124.  Since its
zero-carry continuation dies, every repair preserving those blocks is

```text
x_ell=270271+2^124*ell, ell>=1.                    (24.5)
```

The exact carry-lift worker exhausts the first million positive `ell`.  The
first maximum is

```text
ell=636503,
x=13536921712017380925614270484633922618793919,
73 completed blocks.                               (24.6)
```

It stabilizes its own address at block 50, completes 23 later blocks, and
reaches `1`.  Carry `719011` ties 73 and also dies.  This probes the smallest
theorem-mandated repairs of one prefix; it is not a general computational
verification bound.

Finally, scalar cross-prime height corrections do not control the charge map.
For

```text
Phi_alpha(H)=log H-alpha*v_3(H),
```

no nonzero `alpha` is branch-monotone.  The useful exact obstruction is the
resonant word

```text
w=00000011111111111,
(S,O,e)=(17,11,7*3^12),
H_L=3(2^17*3^L-7) -> 3^(12+L).                    (24.7)
```

It produces arbitrarily large ternary-charge spikes.  It does not renew: a
fixed finite composition has form `(3^A H+B)/2^D`, and a return from `3^C` to
an unbounded member of (24.7) would imply

```text
min(L'+1,A+C)<=v_3(B+21*2^D),                     (24.8)
```

whose right side is fixed.  Thus any resonant return must have
parameter-dependent word length or recharge counts.  The live construction
target has become precise: growing arithmetic phase, not a fixed-state Doob
kernel or fixed macro return.

## 25. Exponent cylinders and bounded coherent CEGIS

The resonant edge lands on `H=3^C`.  Its first `010111` recharge is not a
condition on the size of `C`, but one exact exponent cylinder.  The word has

```text
(S,O,r,b,e)=(6,4,18,26,63),
```

and legality is

```text
3^(C+1)-1 = 18 (mod 64),
C = 12 (mod 16).                                      (25.1)
```

For such `C`, exact substitution gives

```text
K=9*(3^(C+2)+7)/64,
a=v_2(3^(C+2)+7)-6,
R=3^(a+2)*(3^(C+2)+7)/2^(a+6).                        (25.2)
```

Write `C=12+16n` and `f(n)=3^(14+16n)+7`.  Since

```text
v_2((3^16)^(2^k)-1)=6+k,                              (25.3)
```

there is a unique `r_k mod2^k` with `2^(6+k)|f(r_k)`.  Exactly one of the two
lifts `r_k` and `r_k+2^k` becomes `r_(k+1)`.  Thus

```text
a(C)>=k  iff  C=12+16*r_k (mod 2^(k+4)).               (25.4)
```

The exact worker constructs (25.4) through `k=64` by modular exponentiation.
This proves that arbitrarily deep *finite* recharge classes exist; the nested
classes converge to a 2-adic exponent, not automatically to one natural `C`.
Commit `7826516` proves they cannot eventually stabilize to a natural `C`, so
the shallow tower alone cannot be the requested ordinary infinite ray.
Moreover (25.2) has `v_3(R)=a+2>=2`, whereas the resonant input family has
valuation one, so this branch cannot return directly in one recharge.

As a finite calibration, the same worker follows every compressed orbit from
`3^C`, `12<=C<=10000`, on Akdeniz.  All 9,989 exponents terminate before the
declared limits, none returns to a pure power or the resonant family, and the
unique maximum is 11 recharges at `C=700`.  The interval scan is subordinate
to the exponent-cylinder theorem; it is not extrapolated.

The next bounded search maintains a beam of coherent nested seed cylinders
`(rho,L,Q,y)` with the exact affine meaning

```text
rho+2^L*ell  |->  y+3^Q*ell.                           (25.5)
```

For a candidate next word `(S,O,r,b)`, the unique lift digit is

```text
ell_0=(r-y)*3^(-Q) mod2^S,                             (25.6)
```

and the child has `rho'=rho+2^L ell_0`.  Every edge is checked by literal
Collatz replay.  Growing-precision triadic min-plus minima are retained as
bounded ranking witnesses, never used as an unsound forward dominance rule.
A small lookup selector on `(v_3(H), primitive(H) mod3^k)` is then fitted to
elite coherent traces.  Its first exact mismatch or halt is a CEGIS witness
that refines the selector or precision.  Such a witness is not a Collatz
counterexample.  The only promotion target is a compact parametric invariant
whose exact replay closes for all counter values.

## 26. Selector architecture and invariant CEGIS

The predictor and invariant questions are different.  A selector tries to
guess the next first-passage word on a chosen finite population.  An invariant
is a predicate on the actual odd charge and must make the partial map total on
its whole domain.  The latter is the theorem-bearing target.

### 26.1 Coherent selector architecture pilot

The bounded coherent worker keeps the exact cylinder

```text
rho+2^L*z  |->  y+3^Q*z
```

at every beam node.  It does not combine minima from unrelated parents.  Its
outer loop begins with the ternary feature

```text
(min(v_3(H),c_max), primitive(H) mod 3^k)
```

and opens one-step word memory, a coarse remaining-address carry, or an
additional dyadic charge residue when the first exact replay failure collides
with an already labeled feature.  Models are a default action plus a bounded
exception table, so merely observing a new feature does not force an entry.

The Akdeniz run used all 32 cores with the following exact bounds:

```text
depth=32, beam=512, maximum word length=14,
154 complete first-passage words, phase precision=4,
selector ternary precision<=5, v_3 cap<=8,
dyadic bits<=6, exception entries<=128,
32 exact rollout blocks, 250000 shortcut steps.
```

The first charge-only collision occurs at depth three.  Further collisions
open architecture levels two and three; one-step memory plus dyadic residue
occasionally wins an intermediate fit, but no refinement becomes exact.  The
final model uses five dyadic bits and has

```text
70 weighted errors / 16722 weighted examples,
31 ambiguous features,
127 stored exceptions.
```

Its champion is the ordinary seed `34834345`.  It has 15 zero-carry suffix
blocks after its address has stabilized, but its exact continuation reaches
state `2`.  This is useful negative architecture evidence: a small
next-word table does not expose a compact renewal law.  It neither excludes a
larger selector nor proves anything from the champion's finite survival.

### 26.2 Exact recharge step cells

For a nontrivial first-passage word with data `(S,O,A,r)` put

```text
e=(A+2^S-3^O)/3.
```

If `a` is the number of forced one-letter drains after this recharge, the
branch-homogeneous source cell is

```text
Cell(w,a):
  3H-1 = r (mod 2^S),
  v_2(3^O H+e)=S+a.                                  (26.1)
```

The exact map on the whole cell is

```text
R(H)=3^a(3^O H+e)/2^(S+a).                           (26.2)
```

Equivalently, (26.1) is one odd residue modulo `2^(S+a+1)`.  This is the
right unit for invariant synthesis: legality and the affine update are
proved simultaneously, rather than inferred from training labels.

The invariant grammar forms finite DNFs of such cells with atoms drawn from
exact/lower/congruential conditions on `v_3(H)`, dyadic charge or primitive
residues, and ternary primitive residues.  It also admits normalized recursive
families

```text
T_0(t,z)=z,
T_(i+1)(t,z)=
  (alpha_i*3^(m_i*t+r_i)*T_i(t,z)+beta_i)/2^d_i.     (26.3)
```

The first implemented instances are `3^t` and the exact resonant family
`3*(2^17*3^t-7)`.  Candidates are ordered lexicographically by recursive
depth, parameter dimension, family count, DNF count, atom count, modulus
budget, coefficient bit length, and threshold bit length.  Congruences and
valuations are canonicalized before hashing.

For a closure witness `H -> H'`, CEGIS compares two legitimate refinements:
exclude the spurious source, or adjoin the target as a new positive example.
It selects the lower-complexity feasible predicate.  If the witness is already
a required reachable positive, the target must be adjoined; an undefined map
at such a positive rejects the architecture.

### 26.3 Exact bounded verdict

The theorem-driven anchor is the resonant member with `L=688`, which maps to
the previously calibrated record charge `3^700`.  It is an explicit 1110-bit
natural charge, so the corresponding ordinary seed `3H_0-1` is fixed from the
start; no projective 2-adic compatibility is being smuggled in.

The default invariant artifact exhausts all positive odd `H<=200001`, family
parameters through 800, up to four primitive ternary digits and eight dyadic
bits, at most 64 CEGIS rounds, and symbolic progression periods through one
million.  All eight implemented architectures are rejected.  In grammar
order, their least stored exact failures are

```text
valuation                              H=3      (R undefined),
valuation+primitive3                   H=15     (R undefined),
valuation+dyadic                       H=3      (R undefined),
valuation+primitive3+dyadic            H=15     (R undefined),
step+valuation                         H=189    (R(H)=213 outside),
step+valuation+primitive3              H=82701  (R(H)=93039 outside),
step+valuation+primitive3+dyadic       H=23541  (R(H)=59589 outside),
recursive-family+step-DNF              H=333    (R(H)=375 outside).
```

These minima refer to the rejected candidates encountered within each
architecture, and the artifact retains the exact candidate hash, word,
`(S,O,A,e,a)`, affine identity, and target-clause truth vector.  The family
lane does learn that adding a pure-power target is preferable after the
resonant modulus reaches its precision cap; later exact step-cell witnesses
still destroy closure.  No all-parameter recursive transition rule survives.

### 26.4 Promotion theorem and remaining mathematics

Lean commits `483d2a8`/`4cd716b`/`096558e` supply the exact endpoint.  The
last defines a cutoff-free `canonicalRechargeMap`, identifies its graph with
a literal nontrivial recharge followed by complete drain, and proves every
target is an odd multiple of three.  A positive member `H_0`
and a proof that every invariant member has a sound nonempty recharge macro
to another member yield an ordinary infinite first-passage execution from
`3H_0-1`, hence a Collatz counterexample.  It also proves every such invariant
set is unbounded.  Therefore finite state tables and bounded-height cylinder
unions cannot be successful invariants even in principle.

For finite periodic step DNFs, the worker has a universal checker: decompose
each source clause into arithmetic progressions, apply the affine formula
(26.2), and enumerate the complete target-membership period.  It reports
universal closure only if every progression is completed within the explicit
symbolic period budget.  Recursive families require a separate coefficient
identity, integrality proof, and Presburger/residue-domain inclusion; bounded
family samples never set `universal_closed=true`.

If a future candidate is specified only as nested inverse cylinders rather
than by an explicit natural `H_0`, it still owes the old coherence gate: one
dyadic residue path whose canonical addresses stabilize, or whose carries
are eventually zero (the sufficient bound `rho_n=o(2^n)` remains useful).
Finite nonempty cylinders at every depth describe at most a 2-adic object.

The lane is time-boxed to 24 hours.  A continuation is justified only by a
new symbolic family-transition theorem or a qualitatively smaller invariant
architecture.  Larger undirected seed or finite-survival scans are outside
the lane.  Both artifacts record `counterexample:null`.

## 27. Primitive-coordinate invariant types and the growing-rank obstruction

The anchored invariant grammar exposed the wrong abstraction boundary.  Write
every positive odd charge uniquely as

```text
H=3^c*u,  gcd(u,6)=1.
```

For a legal recharge word `(S,O,e)`, factor `e=3^t*d`, `3∤d`, and set

```text
N=3^(O+c)*u+e,
a=v_2(N)-S.
```

Unequal 3-adic orders and the one cancellation case give the exact transition
grammar

```text
t<O+c:  2^(S+a)u'=3^(O+c-t)u+d,  c'=t+a;
t>O+c:  2^(S+a)u'=u+3^(t-O-c)d,  c'=O+c+a;
t=O+c: v=v_3(u+d),
         2^(S+a)3^v*u'=u+d,       c'=t+a+v.        (27.1)
```

Thus the smallest honest predicate language has finite *types* but unbounded
arithmetic binders `a` and, only at resonance, `v`.  Capping those valuations
turns the construction back into a finite next-word table.  A universal
candidate must prove word legality, existence and uniqueness of the valuation
binders, the exact target substitution, total guard coverage, and inclusion
of an explicit ordinary root progression.

There is a complementary rank law.  For a fixed canonical chart

```text
F(t)=(alpha*3^(m*t+r)+beta)/2^d
```

put `chi=Int(v_2(alpha))-Int(d)`.  A fixed recharge word and fixed drain send

```text
chi' = chi-(S+a).                                  (27.2)
```

Consequently no finite reachable graph of fixed coefficient-matched chart
instances can have total outgoing coverage: a repeated node would contradict
strict rank descent.  This statement requires integer-valued rank and formal
coefficient matching; it is false for arbitrary re-presentations on a finite
parameter domain.  QM162 asks the companion Lean worker to check precisely
this scoped theorem.  The surviving architecture is a finite graph of chart
*types* whose runtime denominator/rank is unbounded below.

`outward_primitive_invariant_cegis.py` audits this architecture separately.
It traces only the theorem-mandated pure-power roots `C=12 mod16`, checks
(27.1) at every defined edge, tests successive guard architectures, and keeps
one coherent nested exponent cylinder.  The reconstructible default artifact
tests 62 ordinary roots through `C=988` and 178 exact states.  All 116 defined
recharges are LOW cases.  Charge/ternary features leave 74 minority transition
errors.  Adding ten dyadic and ten exponent-residue bits separates the finite
sample, but supplies neither unbounded word coverage nor invariant closure.

The coherent root address moves

```text
12 -> 28 -> 60 -> 60 -> 188 -> 188 -> 700
```

as precision grows from four to ten bits.  Its final singleton is the known
`C=700` record.  The resource ledger is more informative than its height:
over eleven recharges the charge stays between 1110 and 1112 bits while the
chart depth rises from zero to 105.  This is exactly the visualizer's finite
tape signature, not a return-and-write gadget.

The same worker exhaustively checks the proposed mod-nine word lemma on every
first-passage word through length 24: 14,764 complete words, including 533
with `v_3(e)=1`, give no failure.  Research-side, that lemma implies that no
later itinerary after the root `010111` edge can return to the original
resonant family `3*(2^17*3^L-7)`; QM163 requests its Lean proof.  Until that
unbounded proof lands, the statement remains a research derivation backed by
the displayed finite regression.

The primitive split also explains the resonant word as a general decoder.
For `w=0^z1^o` at first passage,

```text
e_w=(2^z-1)3^(o-1).
```

If `v_3(2^z-1)=c+1` and `d=(2^z-1)/3^(c+1)`, then legality from
`H=3^c*u` is exactly

```text
u+d=2^(z+o)q,
```

and the pre-drain target is `3^(c+o)q`.  The canonical recharge exposes the
primitive part `u'` of `q` and increments `c` by `o+v_2(q)+v_3(q)`.  But
`u'<=q<u`, so an ordinary orbit cannot use only such resonant decoders
forever.  The old `(z,o,c,d)=(6,11,1,7)` family is the specialization
`q=3^L`.  QM164 asks Lean to check the general decoder and strict-payload
descent theorem.  Mixed architectures remain open, but they now have a sharp
resource obligation: a nondecoder edge must replenish the primitive payload.

The artifact has `universal_invariant:null` and `counterexample:null`.  It is
a grammar reduction and a resource diagnosis, not a nontermination claim.

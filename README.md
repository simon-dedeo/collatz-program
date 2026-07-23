# collatz-program

An ad hoc and playful investigation of the Collatz (3x+1) conjecture:
experiments, theory, formalization, and the new *Kontorovich Challenge*.
Certified claims are backed by
machine-checkable artifacts; research derivations and finite evidence are
scoped explicitly. Started 2026-07-20 (Claude Fable 5 +
GPT-5.6-sol; PSC Bridges-2 grant mth260010p).

Made possible by the support of Grant 63750, "Explaining Universal Truths",
from the John Templeton Foundation. Additional support from research funds
of the Laboratory for Social Minds and from the Survival and Flourishing
Fund. Proofs and Reasons — https://proofsandreasons.io

The proof-directed phase reached a synchronized checkpoint on 2026-07-21.
Active work has now resumed with the deliberately opposite objective described
in [The Kontorovich Challenge](#the-kontorovich-challenge): try to construct and
certify a counterexample.

## A note from the human

I (Simon) am a cognitive scientist, not a mathematician; http://santafe.edu/~simon/cv.pdf

This is a purely experimental project to see what these systems do, and how they reason. There are *many* problems with using AI for mathematics, some of which my colleagues and I have written about---see, e.g., https://arxiv.org/pdf/2603.13680 (*A correspondence problem for mathematical proof*, Eamon Duede and I). One of the things I'm most aware about is the fact that these machines are leveraging insights from real mathematicians, but are unable to properly credit their insights. Anything here should be credited to "the human mathematics community, with apologies." Our colleague, and Proofs and Reasons board member, Michael Harris has written eloquently about the core issues in a recent Boston Review article, https://www.bostonreview.net/articles/knowledge-collapse/

I chose the Collatz Conjecture for three reasons:

1. I understand the theorem!
2. A bit like Fermat's Last Theorem, everyone and their grandmother has worked on it, and any progress towards a proof is unlikely to harm an early-career researcher carving out a new niche.
3. There have been some lovely quanta articles about Collatz and the related Busy Beaver numbers recently, so it was a nice way to learn more https://www.quantamagazine.org/busy-beaver-hunters-reach-numbers-that-overwhelm-ordinary-math-20250822/ I had an idea that there was wisdom hiding in the Busy Beaver community that was partially orthogonal to what "regular" mathematicians know.

Everything below this line, and everything else in this repo, has been automatically generated. Claude Fable 5 drove the initial numerics and research program; a Codex/GPT instance then served as the successor research driver. A separate GPT instance formalized the work in Lean in `CLEAN_LEAN`; it was told to make something that would not annoy Kevin Buzzard. If you want the inter-company drama, visit https://github.com/simon-dedeo/collatz-program/blob/main/CLEAN_LEAN/FOR_FABLE.md

## Diary

### 2026-07-23 15:56 EDT

There is still no counterexample.  The raw first-passage lane now has a much
smaller theorem-driven state space.  Every completed block boundary is
`x=3H-1`.  If `H` is even, the next block is forced to be `1` and sends
`H` to `3H/2`, so a finite charge supports exactly `v_2(H)` consecutive
one-letter drains.  A nontrivial first-passage word starts in `0`, ends in
`11`, and, for

```text
2^S T^S(x)=3^O x+A_w,   e_w=(A_w+2^S-3^O)/3,
```

obeys `e_w>0`, `3|e_w`, and

```text
2^S K=3^O H+e_w.
```

After the recharge, put `a=v_2(K)` and drain the next `a` forced `1`
blocks.  The resulting canonical partial map on positive odd charges is

```text
R(H)=3^a K/2^a.
```

It is strictly increasing and converts dyadic charge into ternary depth:

```text
v_3(R(H))>=a+1,
3R(H)-1 == -1 (mod 3^(a+2)).                     (KC-FP4)
```

Research-side derivation gives an exact equivalence: an ordinary infinite
first-passage execution exists iff this partial odd-charge map has an
infinite orbit.  QM157 asks the companion Lean worker to kernel-check the
general statement.  This removes both the tag machine and the word tree from
the primary construction target.

Schema v3 of the exact artifact audits the full charge recurrence on the
record seed.  Source `270271` consumes its canonical preloaded address after
block eight at state `3698459`; it then executes 28 further zero-carry blocks.
Its 36 blocks compress to 13 nontrivial recharge macros, ending at odd charge
`4108012983`, where the next recharge is undefined and the ordinary orbit
eventually reaches `1`.  The post-address visualizer triple is now the more
honest

```text
3698459 -> 8216025965
```

in 72 accelerated odd steps and 27 completed extensions.  This is unusually
long literal self-renewal, but it is finite and is not a counterexample.

The shallow `{1,011}` subsystem reduces further.  Writing
`H=3^c u` and `R(H)=3^c' u'` gives the two-counter law

```text
2^(c'+2)u'=3^(c+1)u+1.                           (KC-FP5)
```

Seed `159487` realizes the finite exponent return `7 -> 2 -> 12 -> 7`, but
the attempted repetition then fails its dyadic congruence, as required by the
existing periodic-word no-go.

There is also a sharper atom criterion.  Along any coherent path,

```text
rho_(n+1)=rho_n+2^L_n ell_n,   L_n>=n, ell_n>=0.
```

Hence a nonzero carry forces `rho_(n+1)>=2^n`.  It is enough to construct a
path with `rho_n=o(2^n)` (or `limsup rho_n^(1/n)<2`); eventual zero carry and
an ordinary seed then follow.  Companion commit `e48bd60` kernel-checks the
pointwise bound, its eventual-zero consequence, and its frequent-carry
contrapositive.  For a selector measure, the summability
condition `sum E[rho_(n+1)]/2^n<infinity` suffices by Markov and
Borel--Cantelli.  This is weaker and more useful than asking for a uniform
moment bound.

Finally, the scalar minima `h_n` discard the target's 3-adic phase.  If a
word has canonical execution

```text
(source,target)=(r_w+2^S t, b_w+3^O t),
```

then the next minimum is an exact min-plus renewal over the least survivor in
the class `b_w mod 3^O`.  In fact every `h_n` is odd, so the forced first
word `1` gives the sharp scalar slice law

```text
h_(n+1)=(2m_n-1)/3,
m_n=min {y in E_n:y=2 mod 3}.                     (KC-FP6)
```

Schema v3 checks this identity on all certified minima through `h_36`.
QM158 asks Lean to package the general recurrence.  It suggests the next
principled search: propagate a 3-adic class profile and seek a coherent
sub-`2^n` carry branch, rather than scan more starting integers.  The artifact
still records `counterexample:null`.

### 2026-07-23 15:27 EDT

There is still no counterexample.  Simon's observation that the YAH/tag
compiler may be much more powerful than necessary produces a real strategic
simplification: use the compiler only as a verified bridge, and search first
in the densest minimal raw Collatz subsystem.

For a shortcut parity word `w`, put

```text
S=length(w),  O=number of odd sources,  R(w)=3^O/2^S.
```

Let `F` be the words for which `R(w)>1` for the first time at the final bit.
This is the canonical maximal prefix-free outward code.  Every outward word
has a unique prefix in `F`, so no other outward prefix code can have greater
ordinary or slope-tilted mass.  Its first layers are exactly

```text
length/count: (1,1), (3,1), (6,2), (9,7), (11,30), ...
F_(<=6)={1,011,001111,010111}.
```

Thus the earlier four-word signed language was not ad hoc: it is the complete
minimal outward system through length eight.  The full system has two exact
Kraft laws.  With

```text
p(w)=2^-S,       q(w)=p(w)R(w)=3^O/4^S,
```

fair parity has negative log drift and gives

```text
P=sum_F p(w)<1,
```

whereas `q` is Bernoulli parity with odd probability `3/4`, has positive log
drift, and gives the stopped-martingale identity

```text
sum_F q(w)=1.                                      (KC-FP1)
```

The new exact worker counts this code by `(S,O)` without enumerating words.
At depth 256 it certifies

```text
0.713684569145118094... < P < 0.713684640996637644...,
remaining tilted mass = 0.000000215554558648... .  (KC-FP2)
```

These are exact rational bounds with decimal renderings.  The critical first
moment is ensemble conservation, not an ordinary orbit.

Version 2 also evaluates the theorem variable itself rather than widening a
generic prefix search.  Exhaustive exact replay of every positive source at
most `300000` certifies the changes in the minimum-address sequence

```text
(n,h_n)=(1,1),(2,3),(3,7),(4,15),(5,27),(16,703),
        (17,4255),(20,4591),(22,31911),(25,77671),
        (26,113383),(28,159487),(30,270271),
```

with the displayed value constant between change points through `h_36`, and
proves `h_37>300000`.  The record source `270271` completes 36 outward blocks
but then reaches the `1--2` cycle.  This is a finite lower bound on the atomic
gate, not evidence of an infinite escape.

The construction gate is now equally exact.  Let `r(u)` be the least
nonnegative initial residue for a concatenation `u in F^n`, and

```text
h_n=min_(u in F^n) r(u).
```

Compatible residues only gain nonnegative high-bit carries, so `h_n` is
nondecreasing.  An ordinary positive infinite survivor exists exactly when
`h_n` is bounded, equivalently eventually constant; companion commit
`8959436` kernel-checks this finite-window compactness equivalence directly
for literal shortcut executions.  A projectively
consistent schedule measure can force such a path if its canonical residues
are uniformly tight (uniformly bounded first moment is sufficient).  The
natural critical `q`-flow is provably not tight:

```text
mu_q{r_n<=B} <= B*(3/4)^n.                         (KC-FP3)
```

Hence diffuse pressure, KL branching mass, and universality do not supply the
missing atom.  The preferred constructive target is now an arithmetic
Doob transform or adaptive rule that keeps `h_n` bounded—an explicitly
atomic, aperiodic raw Collatz controller.  This is materially smaller than a
YAH tag machine and stronger than another prefix scan.

The executable artifact
[`outward_first_passage_audit.json`](experiments/kontorovich/outward_first_passage_audit.json)
has `counterexample:null`.  Separately, companion commits `0c6587b` and
`0e3fcf8` now kernel-check the full one-hit public-theta lattice converse and
the elementary bivariate ruler system.  Commit `45dd08b` now kernel-checks
the first-passage foundation and exact `3/2` overshoot inequality.  Commit
`8959436` proves the minimum-address compactness criterion.  Version 7
of the branch-pressure artifact adds an exact eventual `2`-adic
monomial-separation algorithm along the Jordan orbit; the multivariate value
theorem remains open and secondary to the minimal raw construction lane.

### 2026-07-23 14:34 EDT

There is still no counterexample.  Closing the ordinary valuation ruler
revealed a sharper next candidate that genuinely lies outside the one-variable
Wang theorem rather than merely missing a numerical threshold.

For the place-value target schedule

```text
m_n=j+8*17^v_17(n+1),       1<=j<=8,
```

put `A_n=sum_(1<=t<=n)17^v_17(t)`.  Its exact block law

```text
A_(17n+r)=17A_n+16n+r
```

turns the inclusive theta series into

```text
H(C,Z)=sum_(n>=0)C^A_n Z^n,
1+Theta=H(c,z_j),
H(C,Z)=P_17(CZ)H(C^17,C^16Z^17).
```

The Mahler map `T(C,Z)=(C^17,C^16Z^17)` has a defective Jordan matrix and
is genuinely bivariate.  Its iterates are

```text
T^k(C,Z)=(C^(17^k),C^(16k17^(k-1))Z^(17^k)).
```

At every specialized rail the prime-exponent vectors of `c` and `z_j` have
the exactly audited determinant `16`.  A research-side real dominant-monomial
argument makes the forward orbit Zariski-dense and therefore rules out an
invariant algebraic curve that quietly reduces this to the now-closed
one-variable ruler; QM154 asks Lean to package this if cheap.

This schedule also survives the exact height gate for a principled reason:
`A_(17^k-1)=16k17^(k-1)`, so cumulative `k17^k` depth eventually dominates
each fresh `17^k` spike.  The live seam is now precise—a multivariate
`2`-adic Mahler value theorem for this Jordan map, or a direct auxiliary-
function proof—not a longer prefix scan.  Version 6 of the exact artifact
checks the block/digit laws, matrix iterates, rank determinants, and boundary
sums; it still records `counterexample:null`.  QM154 requests the elementary
Lean package without making a special-value claim.

### 2026-07-23 14:21 EDT

There is still no counterexample, but the KL-driven slow-counter candidate is
now closed by the same source-audited p-adic Mahler theorem that previously
closed geometric clocks.

For the only valuation ruler surviving the public-theta height gate,

```text
m_n=j+8*v_17(n+1),       1<=j<=8,
```

Legendre's formula and `kappa=16/27` give the exact digit-sum function

```text
G(x)=sum_(n>=0)kappa^(-s_17(n))*x^n
    =product_(k>=0)P_17(x^(17^k)/kappa),
G(x)=P_17(x/kappa)G(x^17).
```

The required orbit value is

```text
G(2^(19+8j)/3^(14+6j))=1-2^20*Wbar(r),
```

an ordinary integer in `Q_2`.  The product zeros approach every point of the
complex unit circle, so `G` has a natural boundary and is transcendental as a
function; rational-coefficient scalar descent gives the required
`C_2(x)` transcendence.  Wang's 2006 theorem then applies with
`rho=17`, functional degree one, and exact size condition `17<17^2`.
It makes all eight displayed special values transcendental in `Q_2`, a
contradiction.  Thus neither a standard nor an amplified 17-ruler can supply
the orbit.

This exposes a broader theorem-driven warning for the positive first-order
controllers considered here.  A rational solution is defeated by the
two-place sign separator, while a function meeting Wang's transcendence,
small-degree, and nonvanishing hypotheses has a transcendental
algebraic-point value.  A successful self-writing counter therefore has to
escape this trap, not merely use an aperiodic ruler.  Version 5 of the exact
artifact checks the digit-sum identities, all eight arguments, and every
elementary Wang parameter.  Companion commit `3f7cc7c` kernel-checks the
theta tail equation, automatic integrality of all suffixes from one initial
integer hit, and the grouped natural-number pressure kernel.  QM153 requests
the slow-ruler endpoint bridge, while the final `Wbar` lattice propagation in
the converse remains open.  The artifact still records `counterexample:null`.

### 2026-07-23 14:06 EDT

There is still no counterexample, but the KL theta reduction now gives a
converse construction theorem and recovers the existing universal EC17
branch-growth budget directly in the public-payload coordinate.

For a positive schedule, write the suffix equation as

```text
Theta_t=alpha_(m_t)*(1+Theta_(t+1)).
```

If the initial value alone is a negative integer `Theta_0=-X_0`, its unique
lowest dyadic term forces every suffix to be a negative integer and

```text
X_t=2^(8m_t+15)h_t,
X_(t+1)=3^(6m_t+11)h_t+1.
```

If `X_0=2^20*Wbar(r_0)`, the reduced determinant identity and the exact
resonances `3^6=2^8 (mod 473)` and
`32Wbar(0)=Zbar(0) (mod 473)` propagate the full affine packet lattice.
Thus one exact hit

```text
Theta=-2^20*Wbar(r)
```

is sufficient to construct the entire accepted public orbit after the known
one-step shift.  There is no hidden suffix-integrality condition.  Companion
commits `1c322d4` and `685f6ca` kernel-check the full `Q_2` theta endpoint and
its unit-slice integer specialization; QM151 asks for the converse.

The same series gives an exact two-place form of the earlier scale-budget
theorem.  Put

```text
M_N=sum_(i<N)m_i, D_N=11N+6M_N, V_N=15N+8M_N.
```

If `Theta=-K` with `K>0`, then

```text
2^V_(N+1) < (K+1)*3^D_N.
```

Combining this with `3^41<2^65` bounds

```text
328m_N-62M_N-100N+615.
```

So branch counters may grow, but a fresh branch cannot outrun the cumulative
depth that paid for it.  This agrees with the already kernel-checked core
ceiling and excludes superincreasing and naive exponentially deep clocks in
the theta language.  The v4 artifact checks the constants, exponent
identity, 1,278 finite theta telescopes, and retains `counterexample:null`.

The slower valuation ruler `m_n=j+8*v_17(n+1)` survives this sieve and reduces
exactly to a 17-Mahler equation.  That is now a principled nonlinear target,
not an invitation to widen a prefix scan.  Its function is nonrational, but no
applicable `2`-adic Mahler-value irrationality theorem has yet been verified;
claiming that its special value is irrational would be premature.

The design principle is now adelic: a successful closed form must have a
terminal boundary that vanishes in `Q_2` but approaches a positive nonzero
real limit.  Any telescope whose boundary vanishes in both completions gives
the same positive rational value twice and cannot hit the required negative
integer.

### 2026-07-23 13:43 EDT

There is still no counterexample.  The public-payload carry theorem and the
KL paper now combine into a single exact variable-exponent theta problem.

For a target branch `m`, define

```text
alpha_m=2^(8m+15)/3^(6m+11),
A=83499104/(473*3^11),
B=494251421/(473*2^20),
epsilon=A-B=17/(473*2^20*3^11).
```

For a branch schedule `m_0,m_1,...`, let
`R_0=1`, `R_j=product_(i<j)alpha_(m_i)`.  Exact finite unrolling of the public
recurrence gives

```text
q_0+A+epsilon*sum_(1<=j<N)R_j=R_N*(q_N+B).
```

The v3 artifact verifies this identity on all 1,278 schedule cylinders through
160 written bits.  Along an ordinary infinite public orbit the right-hand side
vanishes 2-adically, so

```text
q_0=-A-epsilon*Theta,
Theta=sum_(j>=1)R_j=-2^20*W(q_0)/17.
```

Since

```text
R_j=(2^15/3^11)^j*(2^8/3^6)^M_j,
M_j=sum_(i<j)m_i,
```

this is one KL/Tschakaloff series whose exponent positions are written by the
payload.  Fixed-rate `M_j` is exactly the already-closed partial-theta lane.
The live construction question is sharper: find nonlinear, aperiodic exponent
positions for which this `Q_2` series lands on the displayed rational lattice.
Its tail equation `Theta_t=alpha_(m_t)*(1+Theta_(t+1))` recovers the branch
from `v_2(Theta_t)=8m_t+15`, so it is equivalent to, not weaker than, the
public carry program.

On the invariant unit slice `q_0=17r`, the rational target becomes the
negative ordinary integer `Theta=-2^20*Wbar(r)`.  The eight shallow rails are
therefore exact 17-adic selectors inside a one-series **integer-value**
problem, rather than an unrelated checksum experiment.

Companion commit `3ebde99` also proves universally that every finite word in
any of the eight shallow rails has a strictly positive exact public-payload
realization in the fixed class modulo `17^2`.  Thus no bounded rail-prefix
search can prune the language; its compatible representatives may simply
escape upward.  Literal stabilization of the canonical public residues is
the only infinite gate.  QM150 asks Lean to expose the finite theta telescope;
no irrationality or existence claim is made for arbitrary nonlinear
`M_j`, and `counterexample:null` remains unchanged.

### 2026-07-23 13:13 EDT

There is still no counterexample, but the theorem-driven unit slice has now
separated a writable counter from the true ordinary-address obstruction and
removed one redundant promotion gate.

The mod-17 transport has one shallow fixed rail for every target branch class:

```text
m mod 8       1  2  3  4  5  6  7  0
r=q/17 mod17 12  2 13  3 15  6  9  0.
```

All eight avoid the two deep-core residues `1,14`.  Thus, conditionally on
remaining in one rail, every normalized core contains exactly one factor of
`17`.  The safe graph on the other 15 residues is strongly connected, so the
base checksum is a live component rather than a no-go.

For the highest-pressure rail, write `r=12+17s`, `m=1+8j`.  The next digit is

```text
s'=6s+10j+13 (mod 17).
```

The coefficient of `j` is a unit; the seven other rails have the same
property.  More generally, the source and target payloads modulo `17^k`
decode the branch modulo `8*17^(k-1)`.  Higher 17-adic precision is therefore
a writable branch clock, not an obstruction.  A stationary all-depth lift
would force stationary branch data and is impossible, but an evolving
aperiodic counter remains live.  Restricting to one rail changes the pressure
equation to `x^64+x^(8j+15)=1`; its largest dimension is
`0.0250459467556681664...` on the `m=1 mod 8` rail.

The more important simplification concerns promotion.  For any positive bare
EC17 step,

```text
2^(8m+15)u'=3^(6n+11)u+17,
E=3^(6n)u-494251421,
```

subtraction of the determinant identity gives

```text
3^11*E=2^20*(2^(8m-5)u'-83499104).
```

Hence `2^20|E` is automatic.  Packet color zero is exactly `473|E`, and
`0<494251421<473*2^20` makes the resulting affine height positive.  Therefore
a positive bare EC17 ray plus color zero at one state already lies on the full
self-writing packet rail.  In bare-core coordinates this leaves two gates:
eventual-zero canonical dyadic carry and one color-zero seed.

Companion commit `d4a8edf` then folds both into the correct public coordinate.
For the branch-only program with step defect `D(m)=delta_m`, eventual-zero
canonical **public-payload** carry directly constructs a self-writing tail,
with a necessary one-step shift in the branch sequence; every supplied orbit
has eventual-zero public carry.  This is now the single exact search target.
The updated exact workers certify all eight lifted digit laws and 1,024
bounded color-zero bare-step promotions; both artifacts still record
`counterexample:null`.  Companion commits `13a7ce3`, `519063b`, `d4a8edf`,
and `ded9c30` kernel-check the base unit slice, all shallow rails, the
public-payload carry criterion, and the exact one-color promotion iff.

### 2026-07-23 12:46 EDT

There is still no counterexample.  Re-reading the Krasikov--Lagarias work as
a pressure argument, rather than as a direct core-edge model, gives two exact
structural reductions of the self-writing map.

For target branch `m`, put `P_m=8m+15`, `Q_m=6m+11`.  Its complete affine
cylinder satisfies

```text
2^P_m q'=3^Q_m q+delta_m,
delta_m=(3^(6m)W0-2^(8m-5)Z0)/473>0.
```

The target cylinders are disjoint exact-valuation codewords of lengths
`23,31,39,...`.  Hence their Kraft mass and complete schedule generating
function are

```text
sum_m 2^(-P_m)=1/(255*2^15),
A(x)=(1-x^8)/(1-x^8-x^23).
```

The associated prefix-code pressure equation is `x^8+x^23=1`, with standard
dimension `d=-log_2(x)=0.07065929109419928758...`.  This makes precise why a
flat branch box is a poor search measure and why a typical infinite schedule
is merely 2-adic.  It does not exclude an exceptional eventually-zero address,
which is exactly what an ordinary counterexample requires.

More constructively, `17|q` is an invariant component.  Writing `q=17r`
divides out the EC17 collision particle:

```text
Zbar(r)=29073613+495976448r,
Wbar(r)=4911712+83790531r,
3^11 Zbar(r)+1=2^20 Wbar(r),
2^(8m+15)v'=3^(6n+11)v+1.
```

The reduced cores are odd and `2 mod 3`.  Modulo `17`, every accepted step
obeys

```text
r'-14=6*(-2)^(m-1)*(r-1).
```

This proves the all-depth theorem

```text
min(v_17(u_t),v_17(u_(t+1)))=1:
```

two consecutive cores in this component can never both contain `17^2`, so
deep-17 events have upper density at most one half on any hypothetical orbit.
Every finite branch pair remains CRT-solvable inside the component; this is a
new invariant filter, not a nontermination witness or a no-orbit theorem.

The exact artifact checks target branches through `m=64`, all 1,278 schedule
cylinders through 160 source bits, the mod-17 transport, and the higher
17-adic checksum clock through precision 12.  It records
`counterexample:null`.  Companion commits through `8d59350` now also
kernel-check the complete fixed-target CRT strides, the exact dyadic
ordinary-ray gate, reflection of packet color, equivalence between eventual
zero carry and a positive bare EC17 ray, and the stronger full-rail promotion
criterion.  None asserts existence of a self-writing orbit.

### 2026-07-23 12:02 EDT

There is still no counterexample.  The KL center now gives a substantially
smaller exact state space, rather than only a finite calibration.  Every
genuine packet can be written in one nonnegative coordinate `q` as

```text
Z(q)=494251421+495976448*q,
W(q)= 83499104+ 83790531*q,
3^11*Z(q)+17=2^20*W(q).
```

The current ether length is stored as `v_3(Z)=6n`.  If
`v_2(W)=8m-5`, put `h=W/2^(8m-5)`.  The next state is accepted exactly when

```text
q'=(729^m*h-494251421)/(473*2^20)
```

is a nonnegative integer; then `Z(q')=729^m*h`, so the binary delay `m` has
been written back as exactly `6m` ternary zeros.  After one packet-valid seed,
the unit condition propagates automatically.  This is a deterministic
self-writing mixed-radix controller, not a prescribed branch schedule.

In the centered coordinate `Z=473R+4`, one step is exactly

```text
D(R)=(3^11*R+1221)/2^15,
E(R)=(729*R+4)/256,
R'=E^m(D(R)).
```

The literal KL boundary is `C=2^18*R+2215`, so `E` is conjugate to the
previously isolated ether cycle `C |-> (729C+881)/256`.  The rational center
has therefore exposed the actual recharge--delay decomposition of the packet
map.

For every fixed target `m`, exact CRT gives the complete affine branch

```text
q=a_m+2^(8m+15)t  ->  q'=b_m+3^(6m+11)t.
```

The remaining ternary source condition is coprime, so every finite `n -> m`
link exists.  This proves why neither the new `r=2` synchronization nor the
factor `473` can be an all-depth obstruction by itself.  It also exposes a
missing semantic premise in the bare EC17 carry model: nonzero colors modulo
`473` can form abstract EC17 rays but never glider packets.  One packet-valid
seed (color zero) repairs the bridge and is then preserved.

Every accepted step strictly increases `q`, because
`3^(6m+11)>2^(8m+15)` for every `m>=1`.  Thus the answer to the resource
question is now exact: the branch counter need not tend to infinity, but any
infinite escape in this compiler carries a genuine strictly growing public
payload counter.  The new artifact reconstructs all target families through
`m=32` and replays 4,096 literal linked packet transitions exactly.  It has
`counterexample:null`; no infinite accepted `q` orbit is known.
Companion commit `7ca6d4f` kernel-checks the determinant identity, the bridge
from any supplied self-writing orbit to EC17, strict payload growth, and the
impossibility of an eventually periodic branch schedule.

### 2026-07-23 11:28 EDT

There is still no counterexample, but the KL paper has now identified the
correct rigid spine inside the returning-glider compiler.  For a free
branch-`n` packet tail

```text
K=R_n+2^(8n+15)q,
Z(K)=2^35*K-358513857,
r=v_3(Z),
C(K)+1=3*2^(r+1)*(Z/3^r),
```

the coefficient of `q` in `Z` is a 3-adic unit.  Thus free tails have the
exact geometric valuation histogram
`#(r=j)=2*3^(d-j-1)` modulo `3^d`, with one depth-`d` root cylinder.  That
distribution is not a law along a linked orbit.  The normalized core is

```text
u=u_base(n)+473*2^20*3^10*q,
```

so `u=1 mod 3` is automatic and imposes no condition `q=1 mod 3`.

The coherent-chain algebra collapses the apparent randomness completely.
Using `9591553=17*(2^15+3^12)`, every linked EC17 transition satisfies

```text
2^(8m+15)u'=3^(6n+11)u+17,
2^(8m+30)u'-9591553
  =3^12*(2^15*3^(6n-1)u-17).
```

The bracket is a 3-adic unit for every positive branch `n`.  Hence every
genuine successor has exactly `r'=2`, not a random rail.  Its literal Collatz
boundary obeys the sharper identity

```text
473*C'+881=2^18*3^(6n)u,
v_3(473*C'+881)=6n.
```

Thus any linked chain with unbounded branch lengths approaches the explicit
3-adic center `-881/473`.  At every fixed depth `d<=6n+1`, the successor
macro tail modulo `3^d` is already fixed by the target branch `m`; there is
no exceptional free tail left to choose at that precision.

The router skeleton is now symbolic.  Every post-initial length-`n` macro has

```text
R2=2n+4,  R8=4n+7,  S=0,
odd steps=6n+11,  halvings=8n+15.
```

One repeated ether cell is the exact six-edge KL cycle with two class-2 and
four class-8 chords and affine map

```text
F_E(x)=(729*x+881)/256,
fixed point x=-881/473.
```

At the exactly reverified level-12 certificate, linked macros `n=2..6`
factor as `Dev(n)=Dev_base*Dev_E^n`; the exact ether factor is
`Dev_E=2.973148268...`, with one selected and five nonselected lifts and
calibrated slack `Dev_E/W_E=1.217522341...`.  This is fixed-precision exact
calibration, not a critical-limit theorem.

The rational cycle was then audited independently against every stored exact
certificate at `k=12..19`.  Its exact `Dev_E/W_E` ratios are all greater than
one and strictly decrease, by integer cross-products, through

```text
1.217522341, 1.164166565, 1.148289542, 1.113495646,
1.097093460, 1.076368695, 1.066265371, 1.051569573.
```

The selected/nonselected split changes from `1/5` at `k=12..15` to `2/4` at
`k=16..19`.  This is unusually coherent finite evidence that the ether spine
is approaching a KL-critical direction, but the artifact explicitly records
`limit_theorem:null`; no convergence or critical tower is claimed.

The artifact checks 1,200 affine chart instances, 192 lifted macro links,
the synchronization theorem through depth 49 in its bounded box, literal
router skeletons, and exact certificate products.  It records
`counterexample:null`.  The remaining existential seam is now clean: build
one positive infinite EC17/glider chain.  The existing all-branch Lyapunov
theorem would make any such chain an outward Collatz escape, but no chain or
ordinary initial seed is known.

### 2026-07-23 10:54 EDT

There is still no counterexample.  The reset-cylinder program now has an
exact ordinary-height endpoint.  Companion commit `73601f7` proves that the
following four conditions are equivalent for every infinite reset schedule:

```text
the canonical initial residues are bounded in Nat;
the canonical initial residues are eventually constant;
the exact extension carries are eventually zero;
there is a nonnegative ordinary integer chain.
```

Thus either a construction proves an exact bounded address, or a no-go proves
that its canonical representatives are unbounded.  More finite precision is
not intermediate evidence between those alternatives.

The first proper signed-controller language was then audited exactly.  In the
box `-96<=c<0`, `1<=N<=8`, its 246 outward modes collapse to the four minimal
shortcut-parity blocks

```text
1, 011, 001111, 010111.
```

Their ordinary Kraft mass is `21/32` (168 of 256 resolved residues), while
their tilted mass is `1905/2048`.  All 768 current affine maps pull this
proper language back to exactly 168 residues, and 41,328 source-positive,
strictly growing reset transitions pass literal exact replay.  The bounded
depth-nine tree contains zero-lift tails, but its strongest one lasts only
eight blocks under deterministic lookahead and then fails.  The artifact says
`counterexample:null` and does not infer anything infinite from that failure.
Companion commit `1aa3e52` proves the first all-depth closure: no periodic or
ultimately periodic concatenation of these four outward blocks can be a
positive ordinary shortcut orbit.  Only a genuinely aperiodic path with an
eventually zero address carry remains in this thin language.

The most tempting attempt to combine the period-three EC17 program with the
Krasikov--Lagarias paper has also been closed at its first semantic seam.
The normalized boundary residues really do form a ternary odometer:

```text
m_(t+1)=4^(-4*Delta_t)*m_t (mod 3^d),
m_(3(q+1))=4^(-4K)*m_(3q) (mod 3^d).
```

If `3` does not divide `K`, a complete macro orbit visits every state of
`Y_d`.  But these boundary pairs are not KL full-lift edges.  At depths 3 and
4, each phase of the test schedule `(-1,1,1)` has exactly one class-2 chord,
one class-8 chord, no transports, and respectively 7 or 25 nonedges.  The
stronger affine-defect check explains why: a KL word with `r` divided letters
has defect at least `3^r-2^r`, whereas one normalized EC17 core step has
`r>=17` and defect only 34.  Therefore no Haar-averaged KL tax can be attached
directly to the core odometer.  This does **not** rule out the actual packet
compiler, whose ordinary Collatz endpoints are different; the next valid KL
test must expand those literal packet paths first.

That corrected finite audit now exists.  For returning glider macros with
ether lengths `1..6` and tail zero, it expands every breakoff step to linked
accelerated-Collatz words, expands every valuation to one-halving Syracuse
states, samples the `2 mod 3` visits, and reverses them into genuine KL paths.
The exact edge counts are

```text
n       1       2        3        4        5        6
R2      6       8       10       12       14       16
R8      9      13       18       22       25       29
S       0       0        0        0        0        0.
```

The stored level-12 KL certificate is independently reverified, and every
prescribed chord lift passes its exact rational potential inequality before a
tax row is emitted.  Each finite packet is outward and pays nonselected-lift
tax.  This restores KL as a valid finite calibration on the actual compiler,
but it is not a coherent period-three ray or a precision-uniform theorem.
Companion commit `82c01dd` upgrades the sampled-edge classification from the
six traces to all positive Syracuse trajectories: successive visits to
`2 mod 3`, read backwards, are exactly the KL transport, class-2, or class-8
principal edges.
The next KL question is whether the actual macro-tail dependence forces these
lift choices to spread across fibers, or permits one exceptional ordinary
tail to track the low-tax lifts cofinally.

### 2026-07-23 08:59 EDT

There is still no counterexample.  The theorem-driven period-three audit has
separated a genuine quadratic arithmetic feature from two bookkeeping traps.
Companion commit `7aad758` proves that the full `3*nu` Skolem root family is
one consecutive geometric grid and kernel-checks its Vandermonde
factorization.  At the auxiliary primes `11` and `43`, the cleared gap
numerator has exact valuation

```text
choose(3*nu,2)*(1+v_p(K))
  +sum_(1<=d<3*nu)(3*nu-d)*v_p(d).
```

This gain is genuinely quadratic, unlike the fixed three-point determinant.
It is not yet a linear-independence theorem: primitive cofactor normalization
appears to cancel all but a linear residue of the common Vandermonde factor.
Commit `847027b` kernel-checks the determinant-minus-cofactor multiplicity and
its subquadratic limit.  Applying it to a concrete Padé system still needs the
generic cofactor alternation divisor; no threshold improvement is claimed.

Scalarization does not evade the rank-three obstruction.  The full-support
coefficient sequence

```text
u_n=s_0+s_1*R^n+s_2*R^(2n)
```

has a cubic recurrence with roots `1,R,R^2`, and its `3 x 3` Hankel
determinant is

```text
s_0*s_1*s_2*R^2*(R-1)^6*(R+1)^2>0.
```

Thus the friendlier one-value Tschakaloff threshold cannot be imported by
calling the three forced theta modes one scalar.  Companion commit `847027b`
kernel-checks the cubic recurrence, determinant identity, positivity for the
literal ray, and the converse that every recurrence of order at most two has
zero `3 x 3` Hankel determinant.

At Simon's suggestion, the original Krasikov--Lagarias paper was then reread
from the counterexample side, excluding its already documented faulty
deletion proof and false printed equation (2.1).  The critical eigenvector is
a calibrated potential: every edge retained by its minimizing policy obeys
`lambda^w*c(target)<=c(source)`.  Multiplying around a cycle cancels the
potential, and irrationality of `log_2(3)` makes every selected-policy cycle
strictly retarded.  KL criticality comes from branching entropy, not from one
growing ray.  Leaving the policy through a non-minimal lift of factor
`d=c_alt/c_min` gives the exact necessary escape-tax inequality

```text
lambda^(sum cycle shifts) <= product d.
```

Companion commit `9f307a9` kernel-checks these generic path/cycle statements,
strict KL cycle negativity, the exact branch-count budget, and the literal
minus-one rail obstruction.  Commit `ddff8d7` strengthens the tax to arbitrary
paths with a fixed-level potential condition-number cost.  Commit `7aa7c0d`
packages the selected-edge corollary: if `cmax/cmin<=lambda^B`, then every
selected path of every length has total shift at most `B`.  These results
replace an undirected search by a precise target: an autonomous mixed
recharge/discharge ray with minimal KL deviation tax.
The existing exact separator `3^41<2^65` also gives a pure integer pruning
law: an outward word with class counts `(n8,n2,ns)` must satisfy
`24*n8>17*n2+82*ns`.  Transport-heavy recharge is therefore expensive before
any integrality or closure constraint is imposed.

The first exact diagnostic isolates the exceptional class-8 loop at the
3-adic point `-1`.  It SHA-checks the stored KL certificate vectors at every
level `k=12..19` and proves by exact cross-products that its deviation factor
exceeds the certified class-8 weight.  The eight exact surplus ratios decrease
strictly from `1.00491098975441` to `1.00029914602351`, finite evidence that
the nonordinary `-1` loop saturates the tax.  The same audit records the
fixed-level endpoint factor suggested by the certified feasible
subeigenvectors: their exact condition number increases from
`146.967160601293` to
`2782.61599307298`.  Thus pathwise telescoping is strong at every fixed level
but is not yet uniform as precision grows; controlling that spike is now an
explicit rigidity target.  Companion commit `cc9f441` proves the first exact
cross-precision constraint:

```text
n mod 3^k = 3^k-1  ->  3^k <= n+1.
```

No fixed natural can occupy the all-`2` inverse-limit spine; a moving diagonal
can do so only at exponential ordinary size.  Its positive finite
approximation is the exact outward rail

```text
T^L(2^L*t-1)=3^L*t-1.
```

Splicing another pure rail consumes its length from the finite counter
`v_2(t)`, so a fixed positive payload cannot repeat this discharge forever.
A counterexample must include a self-writing recharge phase.  Commits
`408cb2c`/`814fb00` now sharpen that statement: the three KL predecessor
branches merely move the negative center among `-1,-2,-4`, and `v_2(n+1)` is
exactly the length of the next forced consecutive odd burst.  Recharge depth
is discharged immediately; it is not an independent stored counter.

The exact follow-up calibrates all three explicitly supplied signed cycles
through `-1`, `-5`, and `-17`.  Their deviation/weight surpluses decrease over
`k=12..19` from respectively `1.00491`, `1.14003`, and `1.86455` to
`1.00030`, `1.06409`, and `1.48130`; `-1` is exactly cheapest in every row.
This is finite evidence from feasible subeigenvectors, not a limit theorem.
Commit `e15c6f0` proves the safe product-level consequence: if every one of a
`q`-chord cycle's deviations is at most `M`, its calibrated weight is at most
`M^q`.  Thus outward cycles force a fiber defect, but not on one persistent
named edge across levels.
Commit `35200ca` proves the first structural consequence: coherent
moving-center branches preserve the `2,3`-primitive part of the centered
distance.  Commit `616ace8` proves the universal dyadic reset cost: any
`N`-step shadow of a fixed signed orbit needs a fresh congruence modulo `2^N`,
so distinct ordinary positive/negative orbits cannot share an infinite parity
itinerary.  Commit `2fcddea` proves the converse and explicitly constructs a
negative representative in every finite parity cylinder, so finite signed
shadowing is automatic.  Commit `2700d1e` proves that switching distinct
fixed/bounded controllers through ternary precision `k` requires connector
length growing with `k`; it does not forbid unbounded reset words.  The exact
count-sensitive bound and live reset interface are kernel-checked in
`aab22e7`.  For reset payloads,

```text
2^N_(j+1)*m_(j+1)=3^O_j*m_j+T^N_j(c_j)-c_(j+1).
```

Eventually periodic coefficients reduce to the already closed rational
fixed-point audit.  Hence the live freedom is a genuinely aperiodic,
payload-written sequence of increasingly precise controller resets, not three
independently growing counters.

The ternary side has now collapsed just as sharply as the dyadic side.
Commits `8c20163`/`54eb749` prove that the controller numerator slope is a
power of two, so every fixed word and target has one exact input class and
every dyadic/ternary pair of finite address constraints is CRT-compatible.
Commit `961c692` proves the stronger legality theorem.  If a word has `r>0`
divided letters and numerator `A*h+B`, then

```text
LegalWord(w,h) <-> A*h+B = 3^r (mod 3^(r+1)).
```

For every target center `g=1 (mod 3)` and precision `k>=1`, exactly one
positive legal input class modulo `3^(k+r)` reaches `g mod 3^k`.  Thus finite
legality search, finite target search, and finite mixed CRT search are all
provably automatic.  The actual obstruction is simultaneous inverse-limit
coherence at the 2-adic and 3-adic places together with outward real KL
height.  Individual counters need not grow monotonically; the cumulative
written precision must be unbounded and must come from one ordinary payload.
Commits `2acceaa`, `d8d8337`, `2963a8d`, `ca8dc5c`, and `18b8c93` prove this last
sentence, the full finite local-universality statement, and the ordinary
stabilization obstruction exactly for reset programs.  Their
accumulator obeys

```text
(S,P,D)->(S+N,P+O,3^O*D+2^S*delta),
2^S*m_end=3^P*m_start+D.
```

Thus each finite block selects one dyadic input cylinder.  The terminal
congruence is equivalent to existence of every intermediate integer quotient,
and shifting by a sufficiently large multiple of the cylinder width makes
the entire finite payload chain strictly positive.  Unbounded cumulative `S`
permits at most one ordinary initial payload for an infinite program.  Such a
payload makes the nested nondecreasing canonical residues eventually
constant.  The exact extension digit obeys

```text
r_(J+1)=r_J+2^S_J*q_J,  q_J<2^N_J,
q_J=0 <-> 2^N_J divides 3^O_J*z_J+delta_J.
```

Lean proves the complete gate

```text
EventuallyZeroCarry(e)
  <-> exists m, Follows(e,m) and 0<=m(0).
```

Thus nonzero carry blocks arbitrarily late rule out every nonnegative
ordinary chain, while an exact zero tail constructs one.  Infinite
positivity and outward real growth remain open.

Commit `302ce3b` packages the complementary abstract certificate consumer:
a finite residue table which already proves exact resets, threshold
preservation, positivity, and strict reset-state growth generates an infinite
growing affine orbit.  The module intentionally has no signed-Syracuse
semantic bridge.  A total semantic table is not the live target: under the
proposed affine-preimage reduction it becomes the existing Two-Kraft
complete-code obstruction.  The surviving architecture is a proper invariant
thin language of reset cylinders.

Both exact artifacts have `counterexample:null`.  The original minus-one
artifact SHA-256 is
`b6204c3964b880e3c5857114f7bcd112e2e1592ca3653ad79445ce470dc14577`.
The three-cycle artifact SHA-256 is
`f52afeca61dc4bd0683a2ab72e285377355e86edd5e52fec85e89a84ab534249`.
See [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md).

### 2026-07-23 07:20 EDT

There is still no counterexample.  The period-three search has been turned
around from finite-depth exclusion clocks to an exact construction criterion.
For the canonical future residues at consecutive cycle boundaries, write

```text
2^m(q)*y_q=3^Q(q)*r_q+D(q),
p(q)=U(q)-m(q)>0,
r_(q+1)-y_q=2^p(q)*C_q.
```

An eventual tail of exact equalities `C_q=0` supplies consecutive literal
three-step EC17 factors.  Companion commit `daae4a8` removes the circularity
from this statement: it proves canonical residue reduction and splitting from
the bare backward recurrence, then kernel-checks that any compatible positive
chain of three-step factors glues to an infinite positive EC17 orbit.  Commit
`40835c0` kernel-checks the strict defect bound and abstract balanced-carry
equivalence; `5769c85` checks the long-block last-carry theorem; `122680b`
supplies the canonical upper-block range bounds; and `f79192e` proves the
displayed three-step identities, translates zero carry to the exact replay
factor, and constructs an infinite positive orbit from any eventual zero-carry
tail.  Commit `4516a03` upgrades that endpoint to the project's literal
period-three `Ray`, and `fff0dec` formalizes the canonical range hypotheses
under which the worker's full ternary congruence forces exact zero carry;
`732da20` instantiates that gate at the worker's actual logarithmic precision.
Thus the construction implication and the finite-row gate are kernel-checked.
The workers contain no finite zero-carry row to feed into them.

The corresponding exact Akdeniz audit covers all 71 positive schedules with
increments in `[-1,1]`, starts through branch eight, and every `q=14..256`
(17,253 rows).  Every row checks the compact identity, the three literal
valuations, covered binary mass, low-bit compatibility, and the reverse full
predecessor congruence; deterministic checkpoint residues and all anomalies
also use an independent series evaluator.  The result is

```text
exact zero carries                                      0
full 3^Q predecessor divisibilities                     0
rows with |C|<3^Q                                  16,870
zero-forcing exponent-gate rows                     8,339
positive / negative carries                   8,748 / 8,505
maximum observed v3(C)                                  8
counterexample                                        null
```

The gate is exact: `D(q)<3^Q(q)` makes a fully divisible carry nonnegative,
and on rows with `2^(U(q+1)-p(q))<=3^Q(q)` its allowed range is too small for
any nonzero multiple of `3^Q`.  Thus nearly half the finite rows reduce to one
full moving-depth congruence which would force an exact construction link.
None hits it.  Commits `fff0dec`/`732da20` kernel-check this implication with
both canonical representative bounds explicit and at the actual logarithmic
precision; they do not prove that an exact zero tail cannot begin later.

A construction-only normalization sharpens the same idea.  Choose precisions

```text
P_(q+1)=P_q-m(q)+floor(log2(3^Q(q))).
```

Then `|C_q|<3^Q(q)` on every row, so the full ternary congruence is equivalent
to exact zero carry.  The independently reconstructed balanced artifact tests
1,136 such precision paths (`h=1..16`) across all 71 schedules and every
`q=14..60`, 53,392 exact rows in total.  It finds zero links and zero nonempty
hit runs.  These misses are construction evidence only; this precision path
does not dominate the exclusion budget.

Finally, exact signed 2-adic rational reconstruction at 2,048 and 4,096 bits
finds no candidate with `|numerator|,denominator<=2^512` and odd positive
denominator for any of the 71 `q=0` schedule values.  The uniqueness bound is
checked and both residue evaluators agree in all 142 rows.  This is a finite
height exclusion, not an irrationality theorem.

The companion then removed another conceptual ambiguity rather than widening
the scan.  Commits `2cad6e1`/`b518d2b` split any literal period-three ray's
completed backward series into exactly three explicit 2-adic theta values and
prove that linear independence of those values together with `1` excludes the
ray.  The relevant published 1989 sufficient criterion has theta count three,
but its threshold inequality fails here in the strict reverse direction.
Commit `a2e940e` pins the paper's inverse-parameter convention and functional
equation.  The live analytic target is therefore a sharper independence
theorem for these special three geometric arguments, not a reapplication of
the known general bound.

The general long-block identity also explains why deeper diagonal clocks are
not the construction route: modulo `3^d`, every earlier consecutive carry is
killed by a later ternary factor, leaving only the last carry multiplied by a
unit.  Exact long-block zero can additionally arise by signed cancellation.
That lane is now in the failure ledger; further compute is reserved for exact
consecutive links or a theorem controlling canonical representatives.

```text
consecutive-cycle artifact 18e65eb08d8d9960cacd88868779d17fdcca8f6912c97530c76fd91c851b951e
balanced-carry artifact    6a619989230c623cecdc8c10b8fb963c1f395568a1e5867d0e0186031cef9187
rational-reconstruction    356994f129961e385b0dd6b0423d8ea96c96411c15a19ce501559c1d315bab93
```

A fresh 8,794-target Lean build and `Audit.lean` pass at `f79192e`; the new
theorems use only the standard audited axioms.  An earlier failure occurred
while the companion was actively rewriting `EtherCounterBareGlue.lean` and
was a transient edit/build race, not a committed regression.  PSC remains
unused: these exact variable-size integer recurrences do not map usefully to
the GPU.

### 2026-07-23 06:28 EDT

There is still no counterexample.  The theorem-directed period-three search
now has an exact fixed-depth hierarchy and two explicit carry objects; the
computation has been used to select symbolic congruence targets, not to widen
an undirected seed range.

Companion commit `a9ed874` proves that every hypothetical period-three ray
eventually satisfies the predecessor congruence modulo any fixed `3^d`, and
that its required coefficient has clock period dividing `3^(d-1)`.  Its paired
no-ray theorem needs only cofinally many failures at one fixed depth.  The
independently reconstructed Akdeniz artifact checks all 71 positive schedules
with increments in `[-1,1]`, starts through branch eight, and every
`q=5..256` (17,892 exact rows):

```text
modulus      matches    failures   zero-match phase cells   schedules w/ no-match
   3           6,025      11,867              0                       0
   9           2,014      15,878              0                       0
  27             635      17,257            218                      69
  81             217      17,675          1,709                      71
 243              76      17,816          5,676                      71
counterexample                                                       null
```

Thus modulus 27 is the first discriminating finite window in this box; mod 9
is too shallow.  This remains finite evidence.  QM118, also in `a9ed874`,
kernel-checks the necessary warning: a sufficiently wide free binary block
can hit any prescribed fixed-depth ternary class.  Periodicity of the target
clock alone therefore implies neither rationality nor automaticity; an
all-`q` proof must use EC17's canonical carry or its three-theta coupling.

Companion commits `40f4265` and `2e8010c` formalize the same-cycle carry above
the sharp bit budget.  If `r_(U+D)` is the future residue modulo `2^(U+D)`,

```text
carry_D(q)=r_(U+D) // 2^U.
```

Every ray forces this carry to vanish eventually, for arbitrary covered
`D(q)`.  In the independently reconstructed dense 24-bit extension audit,
8,869/17,892 first extension bits are nonzero and every row has a nonzero bit
among the first 18.  The longest observed zero run above `U` is 17 bits.  This
locates the finite anomalies exactly but gives no bound on future zero runs.

The strongest mod-27 cell now has a concrete EC17 recurrence.  For word
`(1,1,0)`, start branch eight, and source `q=0 mod 9`, composing nine cycles
gives

```text
2^(432q+4221)*y_q = 3^(324q+3051)*r_q + D9(q),
y_q = 13 (mod 27).
```

For `q>=99`, set `p=U(q)-(432q+4221)>0` and define the signed cross-cycle
carry by

```text
r_(q+9)-y_q = 2^p*C_q.
```

Exact arithmetic gives the equivalence

```text
r_(q+9)=13 (mod 27)  <->  C_q=0 (mod 27).
```

The new reproducible artifact verifies all formulas at sources
`q=99,108,...,243`; the 17 values of `C_q mod 27` are

```text
14,11,5,24,16,3,22,23,12,3,6,19,13,17,18,14,5,
```

all nonzero.  The requested all-`q` nondivisibility statement would exclude
this entire schedule, but the 17 rows do not prove it.  Companion commit
`6b96f89` kernel-checks the nine-cycle arithmetic and signed-carry equivalence.
The two schedules without a zero-match mod-27 phase lift cleanly to 27-cycle
carries modulo 81; one checked row genuinely matches through mod 27 and then
fails mod 81.  Commit `6f05ff5` kernel-checks both depth-four modular, budget,
and carry interfaces.  Neither commit asserts the missing cofinal premise.

The strategic limitation is now equally explicit.  Exact research-side block
composition shows that the next clock block multiplies the previous
fixed-depth carry by a huge power of three, so it vanishes modulo the same
`3^d`; the next terminal carry replaces it.  A naive fixed-depth carry
induction therefore forgets precisely the state it would need to propagate.
The live targets are a direct cofinal valuation theorem, a moving-depth carry
invariant, or a sharper arithmetic theorem for the evaluated three-theta form.
PSC remains unused because none of these exact big-integer modular tasks
benefits from the available GPU allocation.

### 2026-07-23 05:45 EDT

There is still no counterexample.  The period-three search has been reduced
from product-modulus CRT growth to one explicit ternary digit of one canonical
future residue.

Companion commit `5a3413a` kernel-checks the next exact upper separator

```text
3^971 < 2^1539,        485*971-1539*306=1.
```

Put

```text
G0(q)=q*(462*B+2235+K*(693*q-3141)),       U(q)=ceil(G0(q)/306),
G1(q)=q*(1466*B+7092+K*(2199*q-9967)),     V(q)=ceil(G1(q)/971).
```

Lean proves

```text
core(3q)^971 < 2^(971*L0+G1(q)),

971*G0(q)-306*G1(q)
  =q*(6*B+33+9*K*(q-1)).
```

The positive quadratic gap eventually pays for the fixed initial bit length,
so every hypothetical period-three ray eventually has

```text
core(3q) < 2^U(q).
```

Consequently its canonical normalized CRT lift is eventually exactly zero.
This strengthens the earlier bounded-lift pigeonhole result: the only
asymptotic lift that matters is `0`.

Commits `78a6d05` and `43cdba7` eliminate the CRT candidate itself.  Let
`r_q` be the canonical future-forced residue modulo `2^U`.  A ray forces,
eventually,

```text
2^(8*branch(3q)+15)*r_q
  = 17  (mod 3^(6*branch(3q-1)+11)).
```

Commit `d9398a8` reduces this further.  The power-of-two exponent is odd, so
the displayed congruence implies simply

```text
r_q = 1 (mod 3).
```

Lean now proves that arbitrarily late failures of even this one-trit condition
exclude the entire prescribed period-three ray.  The open hinge is therefore
an exact nonstabilization/equidistribution statement for the canonical
`U(q)`-bit representatives, not an unstructured seed search.

Three Akdeniz artifacts have been independently reconstructed.  They cover
the nine genuine positive-gain increment words in `[-1,1]^3`, all 71 positive
starts through branch eight, and `q=5,8,16,...,512` (568 exact rows each):

```text
normalized residues failing replay                 568 / 568
weakest replay-derived initial-core bound           1,057 bits
normalized CRT representatives failing replay       568 / 568
weakest CRT-derived initial-core bound               3,084 bits
raw U-bit residues missing the full predecessor class 568 / 568
raw U-bit residues already missing r_q=1 mod 3       350 / 568
counterexample                                             null
```

The other 218 raw residues match the first trit but fail at a higher ternary
digit.  All figures are finite diagnostics: they do not establish arbitrarily
late failure.  The exact artifact hashes are

```text
normalized margin  2c51f510e4b86f0fafae489df8ad54749eb78e4aadf70511dcf5b0bcd073b720
normalized CRT     f0754083c04d5912b7719f6f7c72455905d7eb23d265efde2eeb9b5d612da20c
tight raw residue  c964e93d7290832cb61f3beac17892b148b8319096411865e07c9dbb46c2832a
```

A research-side exact-algebra audit, not yet kernel-checked, explains why the
dyadic sampling should be treated as a probe rather than an induction: its
formula says that the binary mass between `q` and `2q` already exceeds
`U(q)`, so reduction modulo `2^U` erases all terminal information from cycle
`2q`.  Until that audit is formalized, use it only as search guidance.  Its
warning is that a proof of one-trit nonstabilization must control the canonical
reduction carry rather than infer the next ternary digit from a naive dyadic
residue recurrence.

### 2026-07-23 04:55 EDT

There is still no counterexample.  The period-three search is now driven by
an exact cofinal obstruction rather than raw precision widening.

Companion commit `a6619c5` first cancels the two adjacent continued-fraction
bounds exactly.  If `E_lower,E_upper` are the sharp exponents, `K` is the
cycle gain, `B=n_0+n_1+n_2`, and `L0` is the initial core bit length, then

```text
665*(E_upper+306) = 306*E_lower + W,

W = 203490*(L0+1)
    + q*(307230*(B-3)+51)
    + 9*K*q*(q-1).
```

Lean traps the scaled terminal bit length between `306*E_lower` and that
quantity plus `W`.  The leading uncertainty is only `K*q^2/22610`; this is
a narrow normalized coordinate, not an exclusion.

Companion commit `52cd3e1` then kernel-checks QM100--QM107.  With

```text
A(q)=q*(462*B+2235+K*(693*q-3141)),
U(q)=ceil(A(q)/306),
```

every ray satisfies

```text
bits(core(3q)) <= L0+U(q).
```

If the future-forced residue modulo `2^(U(q)+R)` has normalized margin
`bits(residue)-U(q)`, that margin is at most the same fixed `L0`.  If the
canonical residue fails exact replay, the stronger conclusion is `R<L0`.
Thus unbounded margins or replay failures with unbounded padding exclude the
entire prescribed schedule; finite rows only raise a lower bound on its
unknown initial core.

The sharper worker uses the immediate predecessor as well.  At precision
exactly `U(q)`, combine the future residue modulo `2^U` with EC17's predecessor
residue modulo `3^(6*n_previous+11)`.  If the canonical CRT representative
fails replay, Lean proves

```text
6*n_previous+11 < L0.
```

Since `n_previous` grows with `q`, failed CRT rows at a cofinal sequence of
cycle indices would rule out that period-three schedule without any guessed
padding or real logarithms.  Commit `44c43b0` closes the exact replay semantics,
including the important distinction between under-divisibility and an even
over-divisible quotient, which needs one additional transition.

The two exact workers now emit replay lengths and hashes of all reconstructed
intermediate cores:

```text
experiments/kontorovich/breakoff_ether_period3_normalized_margin.py
experiments/kontorovich/breakoff_ether_period3_normalized_crt.py
```

Their self-tests and a stable local 8,790-target Lean build pass.  Akdeniz is
probing the cofinal dyadic indices through `q=512` for every positive
period-three schedule with increments in `[-1,1]` and starting branch at most
eight.  This bounded run is a theorem-facing diagnostic, not an assertion of
unbounded failure.  PSC remains unused because arbitrary-precision modular
arithmetic has no credible GPU advantage here.

### 2026-07-23 04:08 EDT

There is still no counterexample.  Period three now has a machine-checked
resource theorem: a hypothetical positive EC17 survivor may keep its branch
counter linear, but its ordinary core cannot remain small or even have
eventually linear bit length.

Companion commit `2d016ab` first makes the earlier recurring slowdown local.
Starting at any time `K`, a branch-ceiling step occurs before

```text
K + Nat.log 2 (core(K)+1) + 1.
```

Companion commits `17de520`, `6aeb427`, and `3ebdb72` then prove, for every
period-three ray with positive cycle gain `G` and every `q>=5`,

```text
2^(q*(435+G*(84*q-412))) < core(3*q)^41,

(q*(435+G*(84*q-412)))/41
  < Nat.log 2 (core(3*q)) + 1.
```

In particular, for every proposed affine bit budget `C*q+B` and every
cutoff, Lean gives an explicit later cycle where the core exceeds it.  This
answers the counter-growth question precisely: not every individual counter
must grow monotonically, but a period-three survivor must transfer
quadratically growing bit mass into the ordinary core.  Raw bounded-core
enumeration is therefore the wrong representation; a useful search must
track normalized residues or theta data that can encode that growth.  This
is a necessary condition, not a survivor.

Companion commit `e385967` sharply narrows the same resource law.  Put
`B=n_0+n_1+n_2` and `L0=Nat.log 2 (core(0))+1`.  From the exact continued-
fraction separators `2^1054<3^665` and `3^306<2^485`, Lean proves

```text
2^(q*(7869+G*(1506*q-6826))) < core(3*q)^665,

core(3*q)^306 <
  2^(306*L0+q*(462*B+2235+G*(693*q-3141))).
```

Thus the leading quadratic coefficient of the core's binary length lies
between `(1506/665)G` and `(693/306)G`, approximately
`2.264661654G` and `2.264705882G`.  The initial condition enters the upper
bound only through its bit length.  This suggests a theorem-driven residue
test: subtract the explicit quadratic bit budget from each forced 2-adic
residue and ask whether the residual margin is unbounded.  If it is, one fixed
finite initial core is impossible.  The formal residue-margin implication is
the next requested endpoint; until it is proved and its margins are shown
unbounded, the sandwich is still only a necessary invariant.

The published-theorem audit also closed two tempting shortcuts.  Amou and
Väänänen's 2005 qualitative theorem controls a relation simultaneously at
every place where the common parameter expands; for the EC17 parameter that
set includes both the real and 2-adic places, whereas the candidate relation
is only 2-adic.  Väänänen's 2013 non-archimedean theorem is closer, but tracing
it to Amou--Matala-aho--Väänänen (2007) exposes an explicit threshold.  In the
three-value specialization Lean commit `92416b1` proves uniformly

```text
B/A < 13/12 < 3*log(3)/(4*log(2)),
```

with the logarithmic comparison reduced exactly to `2^13<3^9`.  Thus that
sufficient criterion cannot reach period three either.  Neither failure
proves that the three-theta value is rational or irrational.

A stable local full build passes all 8,790 targets.  The current dirty
`unit_charge_morphic_audit.json` does not reconstruct from its checked-in
verifier and is not cited.  Akdeniz was used for primary-source retrieval;
PSC remains idle because no theorem-guided GPU computation is yet available.

### 2026-07-23 03:23 EDT

There is still no counterexample.  The theorem-driven schedule search now has
an unconditional geometric closure and a general exact pruning inequality.

Companion commit `a6ce60a` proves, for every positive EC17 execution, that the
weighted defects contract by a factor smaller than `1/15` and their every
finite partial sum is smaller than one.  Exact finite backward unrolling
therefore gives the schedule-independent scale trap

```text
core(0) <= P_N*core(N) < core(0)+1,
P_N=prod_(t<N) 2^(8*n_(t+1)+15)/3^(6*n_t+11).
```

For a geometric schedule `n_t=n_0*d^t`, `d>=2`, every factor of `P_N` is
strictly larger than two.  Taking `N=core(0)+1` contradicts the trap.  Thus
geometric EC17 schedules are now unconditionally impossible by finite ordered
rational arithmetic; Wang, Hadamard gaps, and the Mahler-value irrationality
premise are no longer on this soundness path.

Companion commit `26cacdb` turns the same trap into the sharper search-facing
QM89 theorem.  If `S_N=sum_(i<N)n_i` and `N>0`, every positive EC17 execution
must satisfy

```text
328*n_N < 62*S_N + 328*n_0 + 100*N + 41*core(0).
```

The proof uses the exact separator `3^41<2^65`; the history coefficient
`62/328` is about `0.189`, close to the optimal logarithmic slope.  A proposed
schedule that violates this at one prefix can now be discarded before its
enormous forced core is generated.  This clarifies the resource question:
the branch counter need not grow monotonically, while the combined public
register must escape; branch growth itself is subject to the displayed global
budget.  Companion commit `007c252` supplies the local form: after every time
`K` there is a later step `t>=K` with

```text
2^(8*n_(t+1)+15) <= 2*3^(6*n_t+11).
```

Thus a survivor must slow its branch expansion infinitely often; eventual
uniform over-expansion is impossible.  Companion commit `eb06dcb` converts
this to the direct exact branch threshold

```text
328*n_(t+1) < 390*n_t+141
```

at arbitrarily late steps.  The asymptotic ratio is below `390/328≈1.1891`.
Positive-mean period-three schedules grow only linearly and are not excluded
by these ceilings, so their separate arithmetic gap remains open.

A fresh local full build and axiom audit pass.  The new endpoints use only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.  The bounded
period-three CRT result remains a finite lower bound, not an orbit.

### 2026-07-23 02:54 EDT

There is still no counterexample.  Two theorem-driven advances sharpen what
period three and geometric growth now mean.

First, companion commit `1d3721a` kernel-checks the universal geometric-EC17
bridge requested in QM78--QM81: exact finite backward unrolling, terminal
vanishing in `Q_2`, the Mahler functional equation, and the literal endpoint

```text
u_0=-17/3^(6*n_0+11)*G(2^(8*n_0*d)/3^(6*n_0*d)).
```

Thus every geometric counter `n_t=n_0*d^t` is now conditionally excluded by
the one explicit external premise that this Mahler value is irrational.  The
journal PDF of Wang's 2006 theorem has now been recovered and transcribed at
the companion's request: definitions are on printed page 187 and Theorem 1
on page 188.  The exact substitution is recorded in
`docs/FOR_CLEAN_LEAN.md`; Wang plus Hadamard/scalar descent supplies the cited
analytic premise, while Lean supplies the whole EC17-to-value bridge.  This
is a conditional no-go, not an orbit.

Second, EC17 itself gives a stronger finite period-three sieve.  If one step
comes from branch `n`, then independently of the predecessor core,

```text
u_next = 17*2^(-(8*n_next+15))  (mod 3^(6*n+11)).
```

The infinite prescribed future already fixes `u_next modulo 2^P`.  CRT fixes
one combined representative modulo `2^P*3^(6*n+11)`.  The new exact worker
recomputed all 2,340 genuine words in `[-8,8]^3`, all 72,156 positive
previous-branch/word schedules through branch 32, at `P=4096`.  Every least
CRT representative fails after 7--47 required EC17 transitions.  Therefore
the checked successor core is at least its rowwise modulus, uniformly at
least `2^4096*3^17`.  This is a larger finite lower bound, not an infinite
certificate; `counterexample` is null.  QM82--QM83 ask the companion to
package the modular and CRT bridge in Lean.

The strongest newer general Tschakaloff theorem found in the primary
literature does not close period three.  Koivula--Sankilampi--Väänänen (2006)
packages our three values exactly as one `d=3` family, but its sufficient
condition compares

```text
kappa=6*log(3)/(8*log(2)) > (1+sqrt(37))/6,
```

so it misses by the same narrow margin as the 1989 theorem.  This validates
the boundary rather than opening a new search lane.

```text
python3 experiments/kontorovich/breakoff_ether_period3_crt_sieve.py selftest
python3 experiments/kontorovich/breakoff_ether_period3_crt_sieve.py verify \
  experiments/kontorovich/breakoff_ether_period3_crt_sieve_audit.json --jobs 12

artifact SHA-256  4706196c2ba7f5eb5edb78ae9936349674e62d1e5239a63e8b5558ff97b17b40
verifier SHA-256  8ac1eea9e627d7277c83d5a12b422f94a5cf6963c3f40ee32382a0c6c5885916
```

### 2026-07-23 02:34 EDT

The theorem-driven nonlinear search has a new exact target.  For the genuinely
aperiodic geometric branch schedule

```text
n_t=n_0*d^t,  n_0>=1, d>=2,
```

finite backward unrolling of EC17 reduces the only possible initial core to

```text
u_0=-17/3^(6*n_0+11)*G(z),
G(z)=sum_(j>=0) (2^15/3^11)^j z^((d^j-1)/(d-1)),
z=2^(8*n_0*d)/3^(6*n_0*d),
G(z)=1+(2^15/3^11)*z*G(z^d).
```

The new exact artifact replays nine literal schedules through six EC17
transitions and checks 3,584 coefficient identities.  More importantly, the
previously unaudited literature seam is now precise: Wang's 2006 p-adic
Mahler-value theorem has parameters `rho=d`, theorem degree `n0=1`, and
`M0=d`, so its numerical condition is just `d<d^2`.  The needed function
transcendence follows by the classical Hadamard gap theorem and scalar descent
from rational coefficients.  This gives a source-checked proposed conditional
no-go for every geometric counter, but the universal EC17-to-value bridge is
still a research derivation; QM78--QM81 ask the companion to kernel-check it.
It is not a counterexample.

Companion commits `d0faf96` and `82198ac` also complete the natural homogeneous
rational period-three coboundary no-go.  A reduced denominator must divide its
scaled copy, hence is a monomial; least- and greatest-support coefficients then
contradict the quadratic forcing.  This excludes every homogeneous rational
potential `x^-1 f(y/x)`.  It does not yet exclude an arbitrary nonhomogeneous
bivariate rational potential or an accidental rational value of the three
theta sums at one orbit.

```text
python3 experiments/kontorovich/breakoff_ether_geometric_mahler.py selftest
python3 experiments/kontorovich/breakoff_ether_geometric_mahler.py verify \
  experiments/kontorovich/breakoff_ether_geometric_mahler_audit.json

artifact SHA-256  39ab4d6025729d2eced00cb8a4a331ba5640c41832cd05bc270c078823b85bbe
verifier SHA-256  d22be4b977f9f6ba98d96b1426533634514237dc6ebfccfecd37b48f7f303e81
```

### 2026-07-23 02:20 EDT

Two more theorem-shaped period-three checks are complete.  Companion commit
`1154476` represents a homogeneous Laurent potential by a finitely supported
coefficient sequence and proves that its least and greatest exponents cannot
both match the three quadratic defect monomials.  Slicing an arbitrary finite
Laurent polynomial by total degree then proves the full finite obstruction:
the period-three EC17 defect is not a coboundary of any finite Laurent or
exponential-polynomial potential.  This closes the simplest rationality-
engineering lane, but not a non-Laurent rational function, an infinite
series, or an accidental rational value of the three theta sums at one orbit.

Companion commit `a732905` sharpens the public-resource theorem
quantitatively.  For the canonical normalized ether register `Y`, the exact
coefficient comparison is

```text
15*2^(8*n+23) < 3^(6*n+17),
```

and every legal step therefore satisfies

```text
15*Y_t < Y_(t+1),
15^t*Y_0 <= Y_t.
```

Thus branch and core do not each have to grow monotonically, but their
canonical combined public magnitude grows exponentially.  Any infinite legal
ether execution is automatically an outward escape; the constructive problem
is now purely to make legality and the ordinary address regenerate forever.
This theorem supplies no such execution, and no counterexample is known.

### 2026-07-23 02:12 EDT

Companion commit `def4c52` turns the next theorem-driven period-three seams
into kernel-checked statements.  First, the finite residue consumer now has
its exact infinite endpoint: if one prescribed EC17 schedule has certified
least-residue failures at an unbounded cofinal sequence of precisions, then no
ordinary positive orbit follows that schedule.  The existing 4,096-bit box is
still only finite data; it does not supply the required infinite certificate
family.

Second, Lean now composes three literal EC17 balances under the affine
three-phase branch law.  At cycle `q` the defect is exactly the sum of the
three monomials

```text
Y^(2q),  (X*Y)^q,  X^(2q),
```

with their explicit nonzero phase coefficients.  This is the algebraic source
of the three theta values and the input to the finite-Laurent coboundary
obstruction; it is not itself a no-orbit theorem.  The same commit proves that
positive derivative order only lowers the Väänänen--Wallisser sufficient
threshold: for every `sigma>=1`,

```text
Gamma(3,sigma) < 1/12 < 5/32 < gamma.
```

Thus derivatives cannot repair the period-three gap in that 1989 theorem.
A sharper fixed-linear-form theorem could still do so.

The companion's source formalization also caught and corrected a semantic
parenthesization bug in the round-188 Skolem root product.  The corrected
product now has a kernel-checked factorwise vanishing regression before the
Hilfssatz valuation layer.  A fresh local full build and axiom audit pass with
only the standard mathlib logical axioms.  No counterexample or infinite
ordinary execution is known.

### 2026-07-23 01:54 EDT

Companion commit `4f93346` gives an exact answer to the public-resource
question.  The EC17 state map

```text
t -> (branch(t),core(t))
```

is injective.  A repeated state would make the target and source branch
products equal, while `2^(8*n+15)<3^(6*n+11)` at every positive branch and
the accumulated `+17` defect force opposite strict inequalities.  Therefore
an infinite execution must escape every finite `(branch,core)` box: for every
`B`, some time has `branch>B` or `core>B`.  This does not force the branch
counter alone to diverge; the core payload may supply the unbounded resource.

The finite residue theorem also suggests a sharper search observable.  At
the full accumulated binary precision of an `N`-step schedule, let `k_N` be
the least forced initial residue.  Any fixed ordinary initial core must equal
`k_N` for all sufficiently large `N`.  Equivalently, a least terminal residue
modulo the accumulated ternary factor succeeds at the next step exactly when
`k_(N+1)=k_N`.  Five representative period-three schedules had no such
extension success at any of their first 80 boundaries.  That is finite
guidance, not a theorem; the useful target is an unbounded sequence of exact
extension failures, which would exclude the whole schedule without assuming
an initial-core bound.  The generic unbounded-precision consumer has been
sent for Lean checking before any larger scan.

A source audit also closed one tempting literature shortcut.  Bézivin's 1988
`p`-adic theorem proves independence for series
`sum p^(M(n))*z^n`, but the EC17 theta values retain the quadratic-height
unit denominator `3^(6*K*L*choose(n+1,2))`; it cannot be absorbed into the
argument.  His 1990 extension is archimedean.  Neither removes the narrow
period-three Väänänen--Wallisser gap.  The live arithmetic target remains a
special fixed-linear-form sharpening or an unbounded residue-stabilization
theorem.  No counterexample is known.

### 2026-07-23 01:31 EDT

The first search at the period-three theorem boundary is an exact
ordinary-core stabilization sieve, not an undirected Collatz seed search.
For each prescribed EC17 schedule and precision `P`, backward substitution
forces one residue `r_P modulo 2^P`.  Any positive ordinary core below `2^P`
would have to equal the least representative `r_P`; if exact forward
execution of that integer fails a required EC17 division, every ordinary
core on the schedule is at least `2^P`.

The 32-core Akdeniz run built and independently recomputed all genuine
period-three increment words with components in `-8..8`, positive cycle sum,
and positive starts `1..32`, at 4,096-bit precision.  Across 2,340 words and
72,156 start/word schedules, every least representative fails after 7--47
steps.  Companion commit `75a6829` now kernel-checks the generic QM57--QM59
consumer: terminal independence modulo `2^P`, recovery of the forced initial
residue for every literal EC17 prefix, and the abstract least-representative
failure implication.  Therefore every ordinary core in this exact box is at
least `2^4096`.  The largest leading-zero run was only 16 bits, so the scan
found no stabilization anomaly worth promoting.

This is a rigorous finite lower bound, not a counterexample and not an
all-parameter exclusion.  Merely increasing the box would have diminishing
mathematical value.  The live theorem-driven questions are now whether a
stronger three-value `Q_2` independence result applies to the special
geometric arguments, or whether EC17 admits a special modular/coboundary
identity that isolates one period-three program.

Companion commit `11eaba0` has meanwhile kernel-checked the complete
period-two EC17 splitter, convergence, two-argument separation, and exact
external-theorem seam.  Accepting the cited 1989 result, all positive-mean
period-two increment tails are dead.  The companion has also begun an
independent formalization of that paper: the theta functional equation now
compiles, but the Skolem--Hermite linear-independence argument does not yet.
The source formulas (12)--(17) have now been visually transcribed from the
rendered scan for that formalization; this is a source audit, not a proof.

There is also a new exact research-side resource dichotomy awaiting Lean
checking.  No positive EC17 execution can repeat the same `(branch,core)`
pair: over a closed branch segment, the source and target branch multisets
agree, but `2^(8*n+15)<3^(6*n+11)` at every positive branch and the
accumulated constant-`17` defect is positive.  Consequently an infinite
execution cannot keep both registers bounded.  This does not prove that the
branch level alone tends to infinity; an unbounded core payload is the other
possibility.

```text
python3 experiments/kontorovich/breakoff_ether_period3_sieve.py selftest
python3 experiments/kontorovich/breakoff_ether_period3_sieve.py verify \
  experiments/kontorovich/breakoff_ether_period3_sieve_audit.json --jobs 32

artifact SHA-256  bd7cf4b64a68c8146a6144c37d3a20098e2b84285a75bec2d2f393944f71848b
verifier SHA-256  82ac3a9e463a95c573c4f8f30aa66eac420cf89bd85de40869a5e10fd2908d56
```

### 2026-07-23 01:22 EDT

The theorem-guided ether search now works with the smaller exact core exposed
by companion commit `2150534`.  After one successful step the public odd part
is exactly `3u`, not a multiple of nine, and in positive branch coordinates

```text
2^(8n_(t+1)+15)u_(t+1)=3^(6n_t+11)u_t+17,
u_(t+1)=1 (mod 3).
```

This makes a repeated branch-increment program algebraically tractable.  If
the integer increments have period `L` and positive cycle sum `K`, splitting
the backward series by positions in the period produces `L` partial-theta
values with common inverse parameter

```text
Q=2^(8KL)/3^(6KL)
```

and arguments whose consecutive ratio is `2^(8K)/3^(6K)`.  The new bounded
artifact literally executes 15 public schedules through nine core steps,
including positive-mean words with down-steps, and checks all finite rational
and 2-adic identities plus 624 theta coefficients.

For the ether exponent ratio, the Väänänen--Wallisser sufficient size bound
passes at period two but fails already at period three.  The exact separators
are

```text
gamma<1/6<Gamma(2,0),
Gamma(3,0)<5/32<gamma.
```

Companion commit `11eaba0` kernel-checks the universal period-two bridge,
including the exact two-value independence proposition needed from the
external paper.  Accepting that cited result, all positive-mean period-two
increment tails are impossible.  Period three is the first escape from this
external sufficient estimate, not an orbit or counterexample.  It is
nevertheless a much more principled next search space than raw seeds: first
test period-three increment programs against EC17's exact modular and
coboundary constraints, then admit fully payload-dependent controllers only
if that structured class closes.

```text
python3 experiments/kontorovich/breakoff_ether_periodic_theta.py selftest
python3 experiments/kontorovich/breakoff_ether_periodic_theta.py verify \
  experiments/kontorovich/breakoff_ether_periodic_theta_audit.json

artifact SHA-256  2d1e80094f494776f6a6fb3338a41403e806695db34b8feffab98ce391962f68
verifier SHA-256  e0c29f74b3c4b34513309f056428a4767faa9d30e860177be9a570b8689e65cc
```

### 2026-07-23 01:09 EDT

The principled ether search now has a theorem-driven trichotomy.  Companion
commit `1c449e6` proves that any ordinary accepted source eventually exhausts
its canonical binary extension digits; commit `bf8b7c2` proves that an
infinite positive ether orbit cannot have an eventually periodic branch
sequence.  Thus neither an infinite preloaded stack nor a finite-state branch
clock can be the missing counter.  A survivor needs genuinely unbounded public
state and a genuinely aperiodic schedule.

The simplest such proposal is an arithmetic valuation counter

```text
n_t=n_0+k*t,  n_0,k>=1.
```

Writing the public register as `Y_t=2^(8n_t-5)h_t`, the exact ether law is

```text
2^(8n_(t+1)+15) h_(t+1) = 3^(6n_t+11) h_t + 51.
```

Finite backward unrolling identifies its sole 2-adic initial payload as

```text
-51/3^(6n_0+11) *
 F(2^(8k)/3^(6k), 2^(8(n_0+k)+15)/3^(6(n_0+k)+11)).
```

Coefficientwise conversion puts this at the Väänänen--Wallisser parameters

```text
q=3^(6k)/2^(8k),
alpha=2^(8n_0+15)/3^(6n_0+11).
```

The new exact artifact replays all 16 schedules with `n_0,k=1..4` for eight
transitions, verifies their rational and 2-adic finite identities, and checks
4,096 conversion coefficients.  It also checks the published theorem's
elementary hypotheses uniformly for every `n_0,k>=1`; the sharp exponent
ratio is `3*8=4*6`, and `2^8>3^5` supplies the strict logarithmic inequality.

Accepting the same inspected 1989 Väänänen--Wallisser theorem already used for
the unit bank, the candidate is irrational in `Q_2` and cannot be an ordinary
integer.  This conditionally closes every fixed-rate growing ether counter,
not nonlinear or payload-dependent counters.  The external irrationality
theorem is cited rather than reproved; no Collatz counterexample is claimed.

```text
python3 experiments/kontorovich/breakoff_ether_linear_theta.py selftest
python3 experiments/kontorovich/breakoff_ether_linear_theta.py verify \
  experiments/kontorovich/breakoff_ether_linear_theta_audit.json

artifact SHA-256  9190bf6ea1a85d3bffc81c9f066a3af8e96529fc75267b147096c3e2c2491dc2
verifier SHA-256  1a53504df1091e65054c5647b6ef59ff2ed04f4ca58840604de277469821b7a5
```

### 2026-07-23 00:53 EDT — adversarial correction

The autonomous ether counter has produced an exact finite **zero-tail
transition**, but not a counter write.  If branch `n` is followed by branch `m`, its
packet tail has the all-parameter successor law

```text
q  = a_(n,m) + 2^(8m+15)*t,
q' = b_(n,m) + 3^(6n+11)*t.
```

The residual tail is multiplied by a power of three, so its affine scale can
grow faster than the next address modulus.  That does not create independent
binary storage.  The new exact worker exhausts
all `160^3=4,096,000` canonical three-branch prefixes against the minimum
23-bit next branch.  It finds exactly one zero-address extension:

```text
115 -> 59 -> 9 -> 1.
```

The three address blocks have widths `487,87,23` and the exact address digits
are

```text
253011375082594840946181492673896274035460390409773499439088332045860417958511512792922515817364797677003558821916246716044707729607838737010028739,
103202970569942805738160702,
0.
```

The adversarial audit exposes the exact interpretation.  The first two widths
sum to `574`, exactly the bitlength of the initial tail.  The final zero starts
after that natural has no nonzero bits left: it is ordinary binary padding,
not newly written storage.  The three affine tail slopes are expanding, with
floor log-scale excesses `624,491,80`, but scale growth is not information
regeneration.

The resulting public register is a positive 463-digit integer.  The artifact
replays all four autonomous counter steps and independently expands them into
192 linked affine members / 384 literal gate macros, starting from one
ordinary positive Collatz state.  After branch one, the public register has
valuation two and the ether transition is undefined.  Thus this is a finite
payload-free transition at source exhaustion, not a self-write, infinite
escape, or counterexample.

The frequency is also calibrating: one hit in about four million candidates
is compatible with an isolated 23-bit congruence.  The exact ordinary-source
criterion is an infinite public itinerary whose canonical address digits are
eventually all zero.  The next target is therefore a nonhalting deterministic
tail-zero orbit, not a wider arbitrary-tail census.

```text
python3 experiments/kontorovich/breakoff_ether_dynamics.py selftest
python3 experiments/kontorovich/breakoff_ether_dynamics.py verify \
  experiments/kontorovich/breakoff_ether_dynamics_audit.json

artifact SHA-256  a2b0eeddb2667c0eb74305405585f479e2a861923cb01a7fc117c9c13a14395f
worker SHA-256    f5c93af8af44fd7f789feaa92dd738d253c9a8e0d916a0040a29c947855f7497
```

### 2026-07-23 00:45 EDT

The restorative-chart search has reached a structural stopping point.  A new
exact worker, `yah_chart_clock.py`, certifies a third edge on

```text
w=249+256z,
256*U=3^7*T+1.
```

Its five queue macros have heads `01021`, terminal carries
`[0],[1,1],[1],[1,1],[1,1]`, eight quotient sweeps, seven odd sweeps, net
space gain `+2`, and a restored seven-trit reservoir.  The output retains the
two-adic register isometry and exposes `U(z) mod 2=z mod 2`.  Companion Lean
now checks the all-parameter modular arithmetic, parity, and isometry; the
finite word schedule remains in the exact research artifact.

At macro boundaries the normalized leading scale follows the abstract clock

```text
rho_0=269001/262144,
rho' = 3*rho/2  on head 0,
rho' = 3*rho/4  on heads 1 and 2,
```

with prefix `01020210102101020210...`.  This abstract clock is aperiodic: a
repeated block would force `3^p=2^q`.  It is not yet an infinite literal YAH
itinerary—the exact finite correction has been proved harmless only for the
five new macro phases.  A second exact identity calibrates every segment of
`M` macros, `S` sweeps, and `J` odd sweeps:

```text
3^J/2^S = 3^(J-M) * rho_end/rho_start.
```

Because both endpoint scales lie in `[1,2)`, positive space gain forces slope
strictly above `3/2`; a nonexpanding positive-space chart edge is impossible.
Companion commit `9021e86` kernel-checks these abstract clock and slope
statements.

More decisively, every edge constructed so far only restricts an existing
lasso parameter,

```text
t_n=a_n+2^(k_n)t_(n+1),  k_n>0.
```

Commit `9021e86` proves that any natural-number tower of this form is
eventually zero, even when the addresses and bit widths vary.  Thus the current
restriction-only architecture cannot contain an ordinary infinite execution.
The tempting reblocking escape also fails exactly: the 19-sweep carry map on
one 65,536-trit atom is

```text
f(r)=(262145*r+449133) mod 2^19,
f^2(r)=r+111834 mod 2^19,
v2(111834)=1.
```

Every state therefore has the full period `2^19`; the nominal third block is
one whole carry-state cycle, not a two-atom counter-writing block.  The worker
checks the general full-cycle hypotheses through 24 sweep layers and exhausts
cycles through 18; the universal all-depth LCG/reblocking theorem has been
sent to Lean and is not yet cited as kernel-checked.

This closes the present fixed-lasso route, not YAH and not Collatz.  The live
constructive target is now a genuinely contextual opcode whose block action
depends on a surviving public payload and rewrites its next address.  The
autonomous breakoff ether-counter is the most concrete existing interface for
that test.  No counterexample or infinite execution is claimed.

```text
python3 experiments/kontorovich/yah_chart_clock.py selftest
python3 experiments/kontorovich/yah_chart_clock.py verify \
  experiments/kontorovich/yah_chart_clock_audit.json

artifact SHA-256  2c55cec21f81b563f181803a26ef5dc7489e13c668317af17438ace6220a29ab
worker SHA-256    6cd98e32a22c47432d5d22d31a551afed0c5175f9abd094b7cea36385191d8ab
```

### 2026-07-22 20:53 EDT

The returned-chart bursts now have an exact compressed artifact.  The new
`yah_returned_burst.py` worker represents the 65,536-trit chart by a
straight-line program and composes the exact two-state quotient transducer by
binary exponentiation.  It therefore certifies whole parameter cylinders
without expanding their repeated blocks.  Through depth `g=4` it checks

```text
g   source u mod 2^(3g)   heads       block length   gain   reservoir
1   3 mod 8               01              524,288     +1       10
2   27 mod 64             0102          4,194,304     +2       13
3   411 mod 512           010202       33,554,432     +3       16
4   2971 mod 4096         01020210    268,435,456     +4       19
```

Every row has exactly `2g` macros and `3g` odd quotient sweeps, hence the
exact defect law `D'=(27/8)^g D`.  The first two rows are also independently
materialized and replayed as 219,942- and 1,792,806-trit literal words with
stage hashes.  This validates the two shutdown observations and adds two
larger compressed finite certificates.

The computation also prevented two false extrapolations.  The head word is
neither `(01)^g` nor `01(02)^(g-1)`; the latter already fails at `g=4`.
Only the finite rows above are claimed.  The source residues are nested roots
of the returned register modulo increasing powers of two, not a simple
repeating base-eight address.  The companion's all-depth register-isometry
argument shows that these roots form a nonordinary 2-adic tower: no one fixed
natural parameter funds arbitrarily deep bursts.

The same artifact now finds the first post-burst collision edge.  On the
whole cylinder `u=35 (mod 2048)`, seven macros have heads `0102021` and carry
lists

```text
[1], [1,1], [0], [1,1], [1], [1,1], [1,1].
```

They burst once, collide evenly, then recharge and return to head zero with
seven trailing twos and net `+3` cells.  If `R` is the incoming returned-chart
register and `T` the new register, the exact map is

```text
2048*T = 3^10*R + 8.
```

This is genuinely different from `256*R'=3^6*R+1`.  A separate literal
regression replays all seven macros on the least 2,317,094-trit source and
pins every endpoint hash.  It is still not closure: the output block is not
identified with an earlier chart.  Moreover, if the two known affine edges
were simply alternated as a periodic two-chart loop, their composite has
coprime multipliers `B=2^19 < A=3^16`; companion commit `2037f54` provides a
kernel-checked generic obstruction to precisely such an expanding periodic
natural-register schedule.  A survivor needs a nonperiodic dispatcher or a
different nonexpanding composite.  No counterexample or infinite execution
is claimed.

```text
python3 experiments/kontorovich/yah_returned_burst.py selftest
python3 experiments/kontorovich/yah_returned_burst.py verify \
  experiments/kontorovich/yah_returned_burst_audit.json

artifact SHA-256  e6c9aae7b804f616a1fb5b9640f693f641156d995666e5e275f4d641680d6293
worker SHA-256    f552fb0a4fa754ef4313f678dcfb4b45448de6d21fc05312ea6d6994def569fa
```

### 2026-07-22 17:18 EDT — shutdown checkpoint

The first search from the returned 65,536-trit chart has been stopped cleanly
for restart tonight.  A generic exact lasso brancher—not yet promoted to a
committed certificate—found two nested all-odd spatial bursts:

```text
u=3  (mod 8):   heads 0,1;   carries [1],[1,1];       net +1 cell;
u=27 (mod 64):  heads 0,1,0,2; carries [1],[1,1],[1],[1,1]; net +2 cells.
```

The first returns to head zero with ten trailing twos and transforms the
defect by `D -> 27D/8`; the second returns to head zero with thirteen trailing
twos and transforms it by `D -> 729D/64`.  These are exact finite-state lasso
observations at block lengths 524,288 and 4,194,304, respectively, but they
are not yet artifact-backed headline results.  They look like a nested delay
line which converts stored dyadic charge into space.  They do not supply
closure: commit `64bccb8` already forbids an infinite all-growing tail.

The next restart task is to replace the memory-heavy explicit blocks with a
compressed carry-transducer/straight-line certificate, derive the general
residue and reservoir law, and ask whether a collision between these bursts
and the restorative edge yields a second, genuinely different recharge map.
The companion's in-progress QM26--QM30 Lean files were left untouched.

### 2026-07-22 17:08 EDT

The bit-one collision now has an exact **restorative opcode**.  Restrict the
decoder to the arithmetic cylinder

```text
t=91+256u,  q=11665+32768u.
```

If `R` is the incoming stripped register, its residue is `R=151 (mod 256)`,
so the collision is followed by a neutral recharge and writes

```text
R'=(3^6 R+1)/2^8.
```

Three more safe queue macros spend five odd steps and return to a head-zero
word with an exact seven-trit reservoir.  Across the five-macro instruction
the word gains one cell.  The artifact constructs all six lasso stages by
finite-state carry composition, proves the repeated block remains 65,536
trits, and independently materializes `u=0,...,4` with exact integer values,
carries, defects, reservoirs, lengths, and hashes.  This is the first complete
`read -> collide -> recharge -> reproduce` instruction in the project.

It is not closure.  The returned lasso is a genuinely new type, and companion
commit `f96e621` proves its register lies strictly between consecutive members
of the original decoder family; no reindexing sends it back to that chart.
Commit `24b2dd5` separately kernel-checks the register-bit arithmetic and the
generic fixed/flipping-lasso engine.  The winning next step is therefore a
finite recurrent **chart graph**, not more depth in one congruence tower: give
the new type its own decoder and find a cycle whose forward edges keep writing
fresh register information.  Companion commit `0da1058` also proves that an
eventual tail repeating only this restorative update is impossible: after the
translation `C=473R+1`, it would force every `256^n` to divide one fixed
positive `C`.  A survivor therefore needs at least two genuinely different
restorative chart edges in its recurrent component.  No infinite execution or
Collatz counterexample is claimed.

### 2026-07-22 16:49 EDT

The amplifier now has its first exact decoder opcode.  At the smallest useful
charge, every phase-one address is

```text
q=17+128t.
```

Four queue macros turn `2(01)^q` into a regular lasso word `U V^t Z`, with
block length 256.  This is not a fitted pattern: the new
`yah_lift_decoder.py` constructs it by composing the two-state quotient
transducer and checks that the repeated block fixes the carry at every one of
the four stages.  The number 256 is exactly `ord_(2^10)(3)`, so the surviving
lift register is a base-three repetend stored across the entire digit span.

Strip the endpoint's seven trailing twos and call the remaining defect

```text
R(t)=(41*9^(17+128t)+15)/(3*2^10).
```

Then `R(t)=t (mod 2)`.  The next macro has head zero and reads that least
significant register bit exactly:

```text
R=2r:    3^7 R-1 -> 3^8 r-1,
R=2r+1:  3^7 R-1 -> (3^7 R-1)/2.
```

Thus bit zero shifts the register and extends the clean reservoir from seven
to eight twos; bit one removes the reservoir and enters a different chart.
At word level, the 256-trit block splits into two explicit 512-trit lasso
blocks for `t=2s` and `t=2s+1`.  This is an actual LSB-first branch
instruction of the sort suggested by Brainfuck/tag-machine thinking, and its
branch bit is globally encoded rather than locally adjacent to the head.

The artifact constructs the all-parameter finite-state certificate and
independently replays all 65 parameters `0<=t<=64`: 33 zero branches and 32
one branches, with exact values, carries, space charges, and word hashes.
The remaining closure problem is now concentrated in one opcode: make the
bit-one collision restore a recharge packet and write a new unbounded
register.  No counterexample or infinite execution is claimed.

Meanwhile commits `1a69d5b`, `6b5e34c`, and `0b8179a` kernel-check the
all-parameter lift-register isometry, its exact triadic reservoir valuation,
and the word theorem equating that valuation with the number of trailing
twos.  The new bit decoder has been sent to the companion as the next formal
target.

### 2026-07-22 16:26 EDT

The highest-leverage closure step is now explicit: combine a space amplifier
with a register that survives amplification.  The phase-one packet

```text
P(q)=2(01)^q
```

has a unique recharge address `q=q_0 (mod 2^(K+2))` determined by
`41*9^q+15=0 (mod 2^(K+5))`; automatically `q=1 (mod 4)`.  Its first queue
macro is length-neutral and writes at least `K` units of `v2(N+1)`.  A maximal
subsequent prefix containing only odd shortcut steps reaches a pure-ternary
macro boundary after at least `K-1` such steps.  If `K=4G+1`, exact scale
comparison forces at least `G` new ternary cells.  Thus this hardware can
perform arbitrarily large **finite** reproduction, rather than merely grow one
cell in a lucky packet.  This is still not nontermination.

The free lift is more important for closure.  Put `L=2^(K+2)` and

```text
A_K(t)=3*(41*9^(q_0+L*t)+15)/2^(K+5).
```

The lifting-the-exponent identity gives
`v2(A_K(t)-A_K(u))=v2(t-u)`.  Consequently the parameter left over after
recharge is a lossless 2-adic register: modulo every `2^h`, it can transmit
any `h`-bit address bijectively.  Recharge therefore supplies both unbounded
finite workspace and an unbounded nonlocal state channel.  The one remaining
win condition is brutally precise: make the exhausted register write the
next `q_0` recharge address by a forward finite type rule, instead of choosing
that address externally.

The exhausted state is also spatially typed.  The normalized defect has
exact `v3=2`, so after `J` safe odd steps the pure-ternary endpoint ends in
exactly `J+2` copies of `2`.  The amplifier therefore emits a contiguous
right-hand reservoir while its arbitrary prefix retains the register.  The
next decoder test is whether the established carry/comb opcodes can make that
prefix and reservoir regenerate the alternating phase-one packet.

The new exact `yah_recharge_amplifier.py` artifact checks 32 symbolic recharge
targets, exhausts all 1,024 ten-bit lift residues for each of the first four,
and replays the exact queue transducer for guaranteed gains one through four.
Those concrete packets have 35, 547, 41,507, and 369,187 trits and actually
gain 2, 3, 5, and 6 cells in their conservative all-odd prefixes.  The
all-`G` scale and LTE arguments are research-side proof schemas sent to the
Lean companion; no infinite orbit or counterexample is claimed.  The prior
queue/battery checkpoint was pushed as `54adf02`.

The adversarial companion has independently closed the surrounding algebra.
Commits `e293f7d` and `22ce54d` kernel-check the complete six-case battery
ledger, the packet value formula, and all four phase-dependent recharge
formulas.  Commit `8bed065` proves that ever-deeper recharge addresses cannot
stabilize to one fixed ordinary packet coordinate.  This does not touch the
live amplifier, whose coordinate evolves and whose lift register is meant to
write the next one; it prevents us from mistaking a compatible nested 2-adic
address for an ordinary program.
Commit `67eabe3` also kernel-checks the all-parameter scale theorem: any two
canonical ternary words joined by `J>=4G` all-odd defect steps gain at least
`G` cells.  The remaining formal seams are the packet-to-maximal-safe-prefix
wrapper, the LTE register isometry, and the exact trailing-reservoir theorem.

### 2026-07-22 16:12 EDT

The carry lane now has a fundamental instruction architecture rather than a
single promising rewrite.  Group the YAH rules from one visit to the left
delimiter until the word is pure ternary again.  If `Q_c` is the two-state
base-three long-division sweep with incoming carry `c`, the three head
opcodes factor exactly as

```text
M(0v)=Q_1(v),
M(1v)=Q_0(Q_0(v)),
M(2v)=Q_0(Q_1(v)).
```

Each sweep rewrites the *entire* suffix and deposits one terminal `2` exactly
when the corresponding shortcut-Collatz step is odd.  Hence there is an exact
space-charge law

```text
length(M(w))-length(w) = number of odd sweeps - 1.
```

One head cell is consumed; remote odd carries are the only source of fresh
program space.  The complete reproduction type is unexpectedly sharp.  A
zero head never grows.  A head `1` or `2` grows by one exactly when the
canonical integer is `3 (mod 4)`.  Because `3=-1 (mod 4)`, that enable bit is
the alternating signed checksum of **every trit in the word**, including the
slash's implicit leading one.  This is a precise realization of Simon's PL
and nonlocality suggestion: the opcode has a local head but its branch bit is
spread across the entire digit span.

The new exact
[`yah_queue_macro.py`](experiments/kontorovich/yah_queue_macro.py) worker
implements the quotient transducer independently of the literal rewrite
engine.  Its artifact compares both semantics on all 88,572 nonempty ternary
words through length ten, including values, parity bits, checksums, and space
charge.  It also literally replays 16,769 structured opcode instances through
coordinate 64.  The exact fixed-length census is equally clean: among all
`3^m` programs, `3^(m-1)` shrink, `(3^m+1)/2` are neutral, and
`(3^(m-1)-1)/2` grow.  Only asymptotic density `1/6` reproduces a cell, and
the uniform mean space drift tends to `-1/6`.  This is Kontorovich's typical decay in
literal program-space form, while leaving room for a thin exceptional
language.  The structured cases include a genuine chained splash:

```text
M(1^(2q) 2^n)   = (01)^(q-1) 0 1^(n+1),
M(1^(2q+1) 2^n) = (01)^q (02)^ceil(n/2).
```

The spent contiguous reservoir becomes a distributed alternating comb—it is
not simply erased.  Its next head-`2` macro is already a four-phase block
compiler: both `0012` and `01` advance a public phase modulo four, and phase
two emits the two-cell terminal deposit `22`.  Thus the chained packet grows
exactly when the two block counts sum to `2 mod 4`.  This is a real
distributed opcode address, although the emitted block alphabet has not yet
closed back to its input alphabet.  The closure target is now a finite cycle of comb/packet
*types* whose checksum enables the next reproducing opcode and whose total
space charge is positive.  A research-side coefficient argument shows why its
clock cannot be fixed: a fixed shortcut block returning a family
`A*3^n+B` with exponent shift `n -> n+d` would require
`2^L*3^d=3^O`, impossible for positive `L,d`; commit `99d3405`
kernel-checks this fixed-clock no-go.  A real glider therefore needs
an unbounded public clock or a genuinely mixed dyadic--triadic scale.

The adversarial audit also caught up completely.  Commit `bfe12f0`
kernel-checks that identity is the only productive nonerasing marker-fixed
digit-word morphism even at arbitrary, unequal image widths.  Commit
`0365c72` kernel-checks the positive carry defect and all four carry/run
opcodes for arbitrary words and run lengths; `f81ff21` also proves CR4's exact
`2E=3S+1` semantics and strict outwardness.  Commit `1a88c3e` kernel-checks the
all-length queue-sweep traces, all three macro factorizations, and the exact
space-charge law.  Commit `b1dd87a` now proves the mod-four growth table and
the global alternating checksum.  Commit `64bccb8` goes further: an ordinary
natural orbit cannot grow by one cell at every macro, because every such step
satisfies `4(N'+1)=9(N+1)` and would force arbitrarily large powers of four
into one fixed positive `N+1`.  Commit `db13d82` sharpens every finite burst:
`r` consecutive reproductions force `4^r | N+1` and satisfy
`4^r(N_r+1)=9^r(N_0+1)`.

That no-go exposes a better recharge potential.  Put

```text
B(w)=2*length(w)+v2(N(w)+1).
```

Every reproducing macro conserves `B`: its new cell spends exactly two units
of dyadic charge.  Neutral/shrinking macros are therefore not mere failures;
they are the only places where a collision can recharge the battery.  The
worker now checks the exact battery transition at every one of its 88,572
words and lists the four congruential recharge formulas.  Commit `288fb09`
kernel-checks the all-length conservation law for every growing macro.  The live closure
target is a comb/packet type cycle whose occasional battery gains pay for
more later cells than its collision phases lose.  Commit `b794b2f` also proves
that the first packet `2(0012)^s(01)^q` can never map directly to another
packet of the same family: its endpoint starts with `0` or `1`, never `2`.
It must therefore be one opcode in a genuinely multi-type cycle, not a
self-loop.  No counterexample, infinite orbit, or closure certificate is
known.

### 2026-07-22 15:31 EDT

The mixed-base lane now has its first fundamental internal opcode.  The six
YAH auxiliary base-conversion rules have an exact digit-complement symmetry

```text
bin0 <-> bin1,       tri0 <-> tri2,       tri1 fixed.
```

The terminal hardware breaks it by a clean carry rather than an amorphous
collision.  If a digit buffer `V` acts by `x -> s*x+t`, the complemented even
rule would need `bin1 V` to match `V bin0`; their intercept defect is exactly
`s-t>=1`.  Saturated buffers attain the minimum `s-t=1`, and the leftover unit
becomes the literal counter instruction

```text
bin1 tri2^n .  ->+  tri2^(n+1) .
```

The new exact
[`yah_carry_opcode.py`](experiments/kontorovich/yah_carry_opcode.py) artifact
checks the complement permutation, exhausts all 488,281 digit buffers of
length at most eight for the defect and equality case, and replays 1,443 run
macros.  The key two-block instruction is

```text
/ tri0^k tri2^n .  ->+  / tri1^(k-1) tri2^(n+1) .,   k>=1.
```

Every one of the 1,056 tested `(k,n)` cases with `1<=k<=32`, `0<=n<=32`
contains exactly one dynamic step, satisfies `2*y=3*x+1`, and is strictly
outward.  This is a genuine increment instruction, but not closure: it spends
one left `tri0` token and changes the phase of the rest.  The real synthesis
problem is now explicit—use the incremented right counter to regenerate the
left token block.  That is a contextual two-block recharge, precisely the
nonlocal “splash the gap” operation Simon asked for.

The adversarial boundary tightened at the same time.  Commit `2d50381`
kernel-checks the complete rewriting seam excluding every delimiter-fixing
uniform digit morphism of width at least three; the exact Python classifications
cover widths one and two.  Commit `9ca4360` universally collapses every proper
outer-context embedding whose start and endpoint are canonical `/digits.`
words.  I have sent a stronger variable-width derivation to the companion:
the six affine A-rule equations appear to force identity for *every*
nonerasing marker-fixed independent digit-word morphism.  That claim remains
a research derivation until its in-progress Lean audit lands.

These no-gos explain why the new opcode matters.  A global letter morphism
must repair each boundary separately and cannot move the carry across the
word.  A viable program must be a typed contextual macro in which the left
token block and right counter co-evolve.  The exact recharge equation, not a
wider literal-word search, is next.  No counterexample or infinite orbit is
known.

### 2026-07-22 15:05 EDT

The first mixed-base closure audit is complete, and it has changed the target
rather than produced a counterexample.  The new exact
[`yah_context_loop.py`](experiments/kontorovich/yah_context_loop.py) checker
pins Yolcu--Aaronson--Heule's 11 rules, replays their `12 -> ... -> 1`
example, and checks finite literal and morphic pumping certificates.  Its
bounded structural audit covers all 513,916 words of length at most eight
with one ordered delimiter pair.  The 694,458-edge induced graph is acyclic;
all 825,708 raw rule applications preserve both marker counts and the two
outer-flank diagnostics; and no whole-word context loop occurs from any of
10,791 cores of length at most six within 20 rewrites.  The same finite graph
does contain a 299-rewrite delay from the canonical word for 834 to the word
for 1079, including 52 genuine Collatz updates.  This is exact evidence for
spatial motion, but also a clean demonstration that motion is not
reproduction.

Two companion results make that distinction structural.  Commit `ef1b888`
kernel-checks that a proper embedding `endpoint=left++start++right` collapses
to `left=right=[]` whenever marker counts and outer flanks are preserved.
The small universal bridge from each concrete YAH rule to those invariants is
still being formalized, but the worker now emits the four diagnostics and
checks them on every raw application in the stated finite graph.  A proper
whole-word splash is therefore retired as the primary construction target;
the live spatial object is an **internal, scale-changing template** whose
active block rewrites or moves inside fixed outer boundaries.

Uniform scale changes are also sharply constrained.  Exact search finds the
identity as the only delimiter-fixing letter morphism among all 3,125 maps
and no rule simulation among all 9,765,625 uniform width-two block maps.
Commit `b4a48a6` kernel-checks the all-width arithmetic endpoint
`eval_3(block)<=2*3^w<4^w=2^(2w)` for `w>=3`; the rule-simulation-to-block
shape implication remains explicit.  The next constructive lane is therefore
variable-width, delimiter-changing, or multi-block morphic closure—closer to
a self-interpreter or a nonlocal stack than to a cellular-automaton tile.

The formal proof boundary also advanced.  Commit `da9fa59` derives both Kraft
bounds from finite prefix-freeness and closes the complete finite
two-Kraft obstruction; only the countable prefix-free version remains behind
an abstract interface.  Commit `298f5a3` kernel-checks that one explicit
canonical splash seed plus a locally closed, strictly outward predicate
really constructs an infinite Collatz orbit and refutes the conjecture.  So
the endpoint is ready.  Commit `1b3459d` also kernel-checks both generic YAH
closure consumers: a literal context loop and the full productive morphic
certificate `u ->+ L sigma(u) R` with nonempty simulations of every generating
rule each construct nonempty rewrite chunks at every scale.  Commit `b733caa`
pins the exact seven-symbol, 11-rule carrier in Lean, proves context closure
and marker-count preservation, and specializes both glider consumers to it.
Commit `442826d` further connects an actual trace over those rules to the
boundary-collapse theorem: marker counts are discharged internally, while
the two flank equalities remain certificate inputs.
What is missing is exactly the thin invariant or a concrete morphic glider.
Akdeniz's
detached Thue solve remains active after 4 hours 49 minutes of CPU with no
`R23_DONE` line; it remains secondary.  Ganesha and PSC remain idle.  No
counterexample or infinite orbit is known.

### 2026-07-22 14:37 EDT

A fundamental coding obstruction now tells us what kind of closure **not** to
seek.  For a valuation word `w` of length `n` and total halving exponent `S`,
there are two exact cylinder weights

```text
p(w)=2^(-S),             q(w)=3^n/4^S.
```

Both are Kraft weights, since their one-letter masses are respectively
`sum 2^(-k)=1` and `sum 3/4^k=1`.  On an outward word,
`3^n>2^S`, so `q(w)>p(w)`.  A prefix-complete decoder has total `p`-mass one;
if all its leaves were outward, its `q`-mass would exceed one, contradicting
the second Kraft bound.  Thus a complete valuation ISA cannot make every
instruction grow.  This is the negative-drift heuristic converted into an
exact coding law, with no optional-stopping assumption.

The verification scope is deliberately narrow.  Lean commit `29c1d22` checks
both geometric sums, the leafwise comparison, and abstract finite and
countable two-Kraft contradictions.  The generic theorem deriving both mass
bounds from prefix-freeness remains an explicit interface.  The research derivation and
quantitative consequence are recorded in the [closure
doctrine](docs/notes/kontorovich-closure-principles.md#53-two-kraft-measures-forbid-a-complete-all-outward-isa):
if every accepted macro expands by at least `lambda>1`, the surviving ordinary
address mass after `N` closed generations is at most `lambda^(-N)`.

The same commit independently closes the total-affine opcode-chain model.  It
kernel-checks the direct handoff progression and proves that a length-`N`
everywhere-defined affine gauge forces the initial slope to absorb every
successive power of two.  With positive binary precision at each step, no
fixed positive natural slope can persist indefinitely.  Nonlinear cylinder
restriction or multiple address rails are genuine escapes from that theorem.

This reverses the constructive target.  We now want a **thin-trap
certificate**: one explicit ordinary canonical-splash state, a public
predicate `L`, and a finite successor rule which maps every state in `L` to a
larger state in `L`.  That is a loop invariant and a self-writing program, not
an externally supplied itinerary.  The companion has been asked to connect
this finite certificate directly to its existing literal Collatz refutation
endpoint.  In parallel, Yolcu--Aaronson--Heule's mixed binary/ternary rewrite
system offers a spatial version of the same target: a finite contextual
self-embedding would produce an infinite rewrite, and their Theorem 3.17
would then turn it into a Collatz counterexample.  The next step is to define
and check that pumping certificate before doing any bounded search.

The detached computation is being demoted, not expanded.  Akdeniz's exact
1,198-digit Thue solve is still active; the Ganesha morphic workers have
stopped after only shards 4 and 12 completed, and they will remain stopped
because the thin-invariant program is now the better-targeted attack.  PSC is
idle.  No counterexample or infinite orbit is known.

### 2026-07-22 14:25 EDT

Opcode chaining now has a sharper fundamental interpretation.  A compiled
word always has the form

```text
rho+2^P u  ->  sigma+3^Q u.
```

The actual handoff to a next word is the coprime equation
`sigma+3^Q u=rho'+2^P' v`, whose solutions are another progression

```text
u=u_0+2^P' t,       v=v_0+3^Q t.
```

The revised exact [phase-swap
artifact](experiments/kontorovich/unit_charge_phase_swap_conjugacy_audit.json)
constructs positive bases and replays two members of this direct handoff
lattice for both `W_1->W_2` and `W_2->W_3`.  This carefully narrows the prior
failure: Lean commit `3a6d285` proves that the *conjugacy-selected* next ray
never meets the current output, not that no finite link exists.  The direct
links are fresh dyadic cylinder selections and therefore finite compilers,
not reproduction.

This gives the new [closure principle](docs/notes/kontorovich-closure-principles.md#52-chaining-is-a-renormalization-not-yet-a-program):
chaining recompiles the same binary-reader/ternary-writer one level higher.
It does not escape the ordinary-address problem.  Moreover, an
everywhere-defined affine node gauge
`u_i=c_i+s_i z`, `z'=a_i z+b_i` would have to satisfy

```text
3^Q_i s_i=2^P_(i+1) s_(i+1) a_i.
```

Thus it strictly spends the 2-adic valuation of its slope at every step; no
fixed positive slope can support an infinite such rail.  This elementary
finite-divisibility theorem has been sent to the adversarial Lean agent.  The
constructive target is correspondingly less blind: a true program must pop a
decoded binary cylinder and nonlinearly write its replacement, or rotate the
address debt between multiple public rails.

The companion has also added two independent exact barriers.  Commit
`3a6d285` checks both concrete failed conjugacy handoffs, and commit `cc09f1b`
proves that nonnegative TI3 correction rails strictly accumulate debt for the
smallest phase-swap coefficient `2^423/3^296<1`.  A turnaround must therefore
regenerate three things at once: phase separation, typed correction, and the
spent dyadic address.  No counterexample or infinite orbit is known.

### 2026-07-22 14:08 EDT

The most attractive phase-glider counter has failed for a structural reason,
and that failure sharpens the programming target.  For every fixed jump
`k>=1`, the public phase-up policy has

```text
h=391k+1,       m_i=m_0+4ki,
2^(154h+23m_(i+1))w_(i+1)+(3^(114h)-2^(154h))
  =3^(114h+17m_i)w_i.
```

Lean commit `466e381` kernel-checks the exact public-step bridge, finite and
completed `Q_2` unrolling, and coefficientwise identification of the unique
initial cofactor with a nonzero rational multiple of

```text
f_q(alpha),
q=3^(68k)/2^(92k),
alpha=2^(23m_0+154h)/3^(17m_0+114h).
```

The unnumbered main theorem on pp. 200--201 of Väänänen--Wallisser (1989)
applies with `ell=1`, derivative order zero, and `p=2`; its ratio condition is
vacuous, while Lean checks the coprimality and exact logarithmic size bound.
Accepting that inspected external theorem, `f_q(alpha)` is irrational in
`Q_2`, so it cannot be an ordinary positive cofactor.  Thus **every fixed
positive jump phase-up walk is closed**, including `U(m)=(m,392,m+4)`.

This is useful negative guidance rather than a retreat to blind search.  The
[closure doctrine](docs/notes/kontorovich-closure-principles.md) now rewrites
the ordinary-address problem as one forced 2-adic debris series.  A viable
opcode chain should make that series a public coboundary—its entry and exit
potentials telescope to an integer.  The surviving phase-glider language must
therefore choose jump size or direction from changing public payload
infinitely often; a linear counter is too weak.  The next theorem-shaped
attack is the variable-jump series, beginning with short periodic jump
patterns and their multi-theta decomposition, not larger seed simulation.

The adversarial worker caught and retracted an initially overbroad periodic
claim.  Lean commit `8b3d9f5` checks that the 1989 theorem's period-dependent
size hypothesis succeeds for two and three theta values but fails already at
four: `Gamma(4,0)<1/8<gamma`.  Period four is therefore the first escape from
this *theorem*, not a candidate orbit.  Commit `772a6e8` has now completed the
generic flattened `Q_2` residue-class splitter, including summability,
nonzero coefficients, and pairwise argument separation.  Accepting the
external theorem, periodic positive phase-up jump words of periods one through
three are closed; four remains outside this particular bound.

More importantly, opcode chaining now has a principled type obstruction.  A
research derivation sent to the Lean adversary rewrites every public step as

```text
w-3^(-17m)
  = (2^(154h+23m')/3^(114h+17m))*(w'-2^(-23m')).
```

Every up or down opcode is therefore ternary-entry to binary-exit.  At an
internal boundary the two charts differ by
`3^(-17m)-2^(-23m)<0`, exactly the normalized `-H_m` defect already seen in
the opcode semigroup.  Chaining more bare cells only accumulates this
same-sign interface tax; returning the phase does not by itself create
closure.  Lean commit `772a6e8` proves this typed normal form for every exact
public step, its finite-word expansion, strict negativity of the internal tax,
and the resulting no-clean-bare-adapter theorem.  The constructive target is
therefore an affine conjugacy intercept or paired public rail that carries the
opposite correction and regenerates the ternary entry chart.

The same review request contains a second closure invariant.  Each resonant
parallel cell shrinks the separation between its two opcode charts from
`2622k` to `2618k`.  Linking its output pair to another such input pair would
force `1311*k_(i+1)=1309*k_i`; since the coefficients are coprime, an
`N`-cell ladder needs `1311^N|k_0`.  Commit `772a6e8` kernel-confirms this and
kills an
infinite rail made solely from the current conjugacy cells before tail
arithmetic enters.  It also specifies the missing instruction: a phase
booster must regenerate the chart gap by the inverse factor, alongside the
payload adapter.  That is now the fundamental target—not an unguided opcode
enumeration.

The first principled booster now exists at word level.  For

```text
W_r=[(r,h_0,L-r),(L-r,h_1,r+d)],
```

consecutive words differ in boundary phase by `(+d,-d,+d)`: the charts cross
internally and recover their separation.  Their total gains are independent
of `r`.  The new exact
[`phase-swap artifact`](experiments/kontorovich/unit_charge_phase_swap_conjugacy_audit.json)
constructs `1->3->2`, `2->2->3`, `3->1->4`; both adjacent pairs have
`P=423,Q=296`, gcd-one positive integral affine conjugacies, exact nested
cylinder checks, and sixteen arithmetic-bouncer step replays.  The adversarial
check then catches the remaining failure: the conjugacy-selected next input
strictly exceeds the current output in both constant and slope for every
nonnegative tail.  The squares are parallel embeddings, not orbit handoffs.
The closure problem is now concrete but twofold: make the node-gauge correction
compose, then make the terminal collision replace exhausted `L` by a larger
public `L'`.  No literal or infinite orbit is claimed.

Remote jobs remain secondary and unchanged: Akdeniz's exact 1,198-digit Thue
solve is active after 3 hours 30 minutes of CPU with no completion line;
Ganesha still has 22 search workers and only shards 4 and 12 complete.  No
counterexample or infinite orbit is known.

### 2026-07-22 13:09 EDT

The opcode-chain question now has a fundamental answer rather than a larger
word search.  Lean's all-period no-go implies that any autonomous controller
with only finite effective state is impossible here: its opcode stream would
eventually repeat.  A viable Collatz program must therefore carry an
**unbounded, publicly decoded register**.  The [closure
doctrine](docs/notes/kontorovich-closure-principles.md) now grades every chain
through seven gates—affine, typed, cylinder-compatible, causally decoded,
ordinary-realizable, literal-semantic, and finally nonhalting—so an algebraic
matrix product cannot be mistaken for reproduction.

The resonant phase glider supplies the first concrete escape from that lower
bound.  With `k=1`, the rule

```text
U(m)=(m,392,m+4)
```

is an autonomous one-counter policy, not an externally pasted aperiodic word:
`m=v2(y+1)/23` is public, and the next instruction increments it by four.
This solves causal opcode selection.  It does **not** solve the harder address
problem: the affine tail must lie in every successive source cylinder, and
the resulting inverse-limit address may still be a nonordinary 2-adic
integer.  The next attack is therefore symbolic stabilization or obstruction
for this exact counter policy, plus telescoping of its phase-dependent tail
embeddings—not a broad simulation.

Independent Lean commit `6619b49` has meanwhile verified the complete public
packet endpoints for the universal one-cell `E,H,E` glider.  Combined with
the prior gate semantics, its bottom layer now has an exact executable
Collatz word, endpoint, and strict growth for every free tail `q`; only the
upper unit/charge compositions remain.  The three new exact research
artifacts have been rebuilt and pass their verifiers.  No counterexample or
infinite orbit is known.

### 2026-07-22 12:59 EDT

Opcode chaining has produced its first nontrivial exact conjugacy rather than
an equal-matrix collision.  The determinant-four identities

```text
114*391=17*2622,       154*391=23*2618
```

make the shift `(m,h,m')->(m+2622k,h-391k,m'+2618k)` preserve the complete
public-tail gain `(P,Q)` while slipping the defect boundary by `4k` cells.
For parallel branches `F_i(t)=(3^Q t+kappa_i)/2^P`, the exact affine
conjugacy condition is

```text
(3^Q-2^P)c=s*kappa_a-kappa_b.
```

The new [resonant-conjugacy
artifact](experiments/kontorovich/unit_charge_resonant_conjugacy_audit.json)
constructs both directions of the first phase motion.  The pair
`(1,392,1) -> (2623,1,2619)` becomes a four-cell phase-down glider; the pair
`(1,392,5) -> (2623,1,2623)` is the phase-up chart.  Both integral public-tail
embeddings have 21,330-digit slopes and intercepts.  The verifier checks the
conjugacy and both cylinder faces coefficientwise and replays two members of
all four branches through the exact arithmetic bouncer.

This is the first structure at Simon's proposed program scale which literally
moves a boundary while preserving a remote affine tail.  It is still not
reproduction.  Down cells make only a finite delay line; up cells give an
infinite *prescribed* phase schedule whose ordinary-tail realization is
unknown; and the embeddings change with phase.  A fixed periodic bounce is
already obstructed.  The new [phase-glider
note](docs/notes/kontorovich-resonant-phase-glider.md) therefore makes the
closure targets explicit: telescope successive embeddings, let the payload
choose the jump/direction, or prove that the phase-up schedule has one
ordinary positive address.  No large search has been launched.

The semantic audit is advancing in parallel.  Lean commits `faf4df1` and
`21bed2c` now kernel-check the concrete `E->H->E` glider prefix and strict
literal growth for every nonempty finite breakoff run.  The upper
charge/unit/level-two link remains the semantic seam.  No counterexample or
infinite orbit is known.

During this update the adversarial side also completed two general closures.
Commit `e8585c4` rules out every fixed finite bouncer-opcode period, including
after a transient.  Commits `cda9bd3`/`a458267`/`904c1de` compile arbitrary
finite `E,H,E^N` gliders to legal growing Collatz words and eliminate their
hidden dyadic witnesses; the upper charge/unit/level-two link is now the only
semantic layer left.

### 2026-07-22 12:39 EDT

The adversarial audit found—and the research side has now repaired—a crucial
semantic layer error.  The public cofactor equation PC3 compiles exactly to an
*arithmetic* `ChargeBouncerStep`, but normalized `y` is not the odd Collatz
integer.  Even the hierarchy field formerly called `ordinary_start` is still
the breakoff coordinate `k`; the literal state appears only after the router
decode `literal_step(k).collatz_start`.  Lean round 115 has accordingly
replaced the false global monotonic-encoding premise by the honest edgewise
growth obligation.

The new exact [semantic compiler
artifact](experiments/kontorovich/unit_charge_semantic_compiler_audit.json)
now descends the whole bounded chain

```text
y -> charge packet -> unit packet -> level-two packet
  -> level-one glider -> breakoff k -> odd Collatz state.
```

It expands the fixed substitutions `charge(N)->unit[N,1]`,
`unit(N)->glider[1,2,1^N]`, and `glider(N)->gate[E,H,E^N]`, then obtains the
actual valuation words from the router.  A complete rebuild checks all 54
members with `m,h,m'<=3`: 756 glider macros, 4,968 breakoff macros, and 14,057
accelerated instructions, each independently replayed by direct exact
`3x+1` arithmetic.  Every tested literal endpoint agrees with the encoded
target and grows.  This is a bounded semantic regression, not the universal
composition theorem or an infinite orbit.

The [closure doctrine](docs/notes/kontorovich-closure-principles.md) now begins
with five fundamental conservation laws: semantics, public state,
synchronization, endomorphism, and control rather than scale.  They answer the
main concern about blind search: no large computation is now licensed unless
a hit would supply a public self-map, a finite semantic rewrite, or a whole
ansatz-class obstruction.  Opcode chaining remains live only at that level;
equal one- and two-letter matrices are closed, while a decoder-compatible
conjugacy or substitution is meaningful.

The adversarial agent has also kernel-closed constant and genuinely
alternating period-two `(m,h)` schedules (commits `737e8de` and `f1ba1c8`) at
the arithmetic bouncer level.  The natural universal extension is a
compressed no-go for every fixed periodic opcode word.  Constructively, the
next target is still nonperiodic public feedback: a mixed binary/ternary
tail rule that regenerates its own delimiter and whose three finite compiler
layers compose universally to `WordLegal`.  No counterexample or infinite
orbit is known.

Lean rounds 116--117 have already consumed the first part of that compiler:
commit `2be4a95` derives legal ordinary valuation words from every successful
finite breakoff run, and `76d60d8` composes arbitrary linked gate lists.  The
remaining semantic seam is now only the two upper affine substitutions
`charge -> unit -> level-two -> glider`; their exact link-tail formulas have
been sent to the companion agent.

The detached jobs remain secondary.  Akdeniz's exact 1,198-digit Thue solve
is still active after roughly 2 hours 25 minutes of CPU, with class number one
and no completion line.  Ganesha still has the 22 unfinished nonuniform
morphism workers; only shards 4 and 12 have completed.  They remain scoped
falsifiers and are not steering the closure program.

### 2026-07-22 12:12 EDT

The closure doctrine has produced a more fundamental public programming
language.  Every accepted bouncer boundary has a *unique* canonical
cofactor state

```text
y=D^m w-1,       w=w_m+S*t,       S=2*F*M,
```

where `m=v2(y+1)/23`, `w` is odd, and `w_m` is the least fixed-register
representative.  Consecutive public states are equivalent to the single
mixed-radix recurrence

```text
A^h(C^m w-1)=B^h(D^m' w'-1),
2^(154h+23m') t'=3^(114h+17m)t+kappa.
```

For fixed `(m,h,m')` this is a literal prefix instruction

```text
t=rho+2^P*u  ->  t'=sigma+3^Q*u.
```

It reads a low binary address and writes a ternary-scaled tail, but—unlike the
quadratic coordinates—every symbol here is uniquely recoverable from the
ordinary integer.  Positive odd endpoint cofactors also force the collision
quotient odd, so the recurrence supplies exact valuation equality rather than
mere divisibility.  The new [public-cofactor
artifact](experiments/kontorovich/unit_charge_public_cofactor_audit.json)
reconstructs the canonical bases and all 27 branches with
`1<=m,h,m'<=3`, then literally replays two members of each branch through the
bouncer and reverse decoder.  This is 54 exact public transitions and a
compiler interface, not an invariant language or infinite orbit.

This language is sparse but not obviously underpowered.  Its exact Kraft mass
is `1/((2^154-1)(2^23-1))`, so the shortest instruction reads 177 low binary
bits.  On the same-defect branches, however,
`3^(114h+17m)>2^(154h+23m)`: the surviving tail gains more scale than the
address cylinder consumes.  The hard issue is therefore not raw capacity but
semantic feedback—converting that surplus into the *right* next 177-plus-bit
delimiter.

The binary cofactor and ternary payload are two canonical rails of one
`S`-unit ladder:

```text
D^m w=1+A^g(C-D)r,
C^m w=1+B^h(C-D)r',
D^m' w'=1+A^h(C-D)r'.
```

This restores Kontorovich's spatial picture at the algebraic level.  A true
“splash and regenerate” is now a renormalization of the entire adjacent
square, not a fresh representation of one corner.

Independent Lean commit `5a9324b` kernel-checks both directions of the
*arithmetic* public compiler: the coordinates are unique, PC3 constructs a
`ChargeBouncerStep` surrogate, and every such step in public coordinates
satisfies PC3.  It does not itself construct a legal Collatz valuation word;
the 12:39 update records that corrected semantic scope.  The same commit
proves that two-letter opcode products with fixed
start/end recharge phases are injective: the diagonal
exponents recover total defect and middle recharge, while the debris is
strictly increasing in the split point.  Together with single-letter
injectivity, this makes equal short matrix products a dead target.  The live
object is now a conjugacy or invariant language for the canonical tail
transducer—especially a finite two-stack/mixed-radix feedback which turns the
written ternary structure into the next binary delimiter.  No counterexample
or infinite orbit is known.

### 2026-07-22 12:05 EDT

Simon challenged the quadratic search for drifting from the real objective:
reproduction.  I agreed and have made that objection an explicit
[closure doctrine](docs/notes/kontorovich-closure-principles.md).  A viable
construction must be an integer-decodable invariant graph
`T^tau(E(s))=E(f(s))`: every instruction-changing coordinate must be
recoverable from the public integer, the output must automatically expose the
next exact valuation, and one finite ordinary seed must generate all future
states.  Fresh norm representations, new CRT choices, or longer finite
prefixes are points of a correspondence, not closure.  The present
two-step norm parameterization is therefore retained only as a diagnostic; I
stopped before launching its proposed prime search.

There is nevertheless a sharper exact programming interface.  The smallest
squarefree correction `d=7 (mod 8)` without an inert public-register prime is
`d=31`, and

```text
C-D = 7706^2+31*1407^2.
```

After cancelling this principal norm, every consecutive typed bouncer step
would obey

```text
2^(23m+154h) r' = 3^(17m+114g) r + H_m,
H_m=(C^m-D^m)/(C-D).
```

The new [opcode audit](experiments/kontorovich/unit_charge_norm_opcode_audit.json)
checks the complete small discriminant sieve, the exact identity, and the
first literal outward `N_31`-typed transition: a 184-digit input goes to a
193-digit output and both underlying unit macros replay.  Crucially, it also
checks the failure which prompted the doctrine.  The output's next collision
valuation is `153`, leaving `130 (mod 154)` after its defect block, so it
cannot execute another positive recharge.  This is one real typed step, not a
chain or counterexample.

Opcode chaining is now being attacked symbolically rather than by searching
for a longer lucky prefix.  For the recharge-free defect matrices

```text
J_m = [[C^m,H_m],[0,D^m]],
```

the audit proves `J_n J_m=J_(m+n)` and checks the general finite decorated
chain formula.  The independent adversarial agent then kernel-checked the
debris law `H_(m+n)=C^n H_m+D^m H_n` in round 106.  Thus defect-only chains
collapse to one additive clock; all possible computation must come from the
noncommuting recharge decorations and, above all, their regeneration of the
public dyadic boundary.  The next searches are theorem-shaped: exact rewrite
or conjugacy relations in that decorated semigroup, a mixed-radix feedback
which turns the bouncer's ternary output register into its next binary
delimiter, or a universal obstruction to one of those classes.

The external jobs remain unchanged.  Akdeniz's exact 1,198-digit Thue solve
is active after about 1 hour 45 minutes with class number one and no
completion line; its runtime is not predictable enough to promise an ETA.
Ganesha still has 22 workers alive and only shards 4 and 12 complete.  Both
jobs remain useful scoped falsification tasks, but neither is steering the
closure theory.  PSC remains idle.  No counterexample or infinite orbit is
known.

### 2026-07-22 11:13 EDT

The hidden cofactor left by the public 23rd-power type is now an exact
instruction register rather than a hoped-for second divisibility obstruction.
If `w` is its current value modulo the 179-bit fixed divisor `F`, then a
recharge of length `ell` writes

```text
B D^m' w' = B C^m w-5ell                       (mod F).
```

All coefficients are units, so every target `w'` has one recharge class
modulo `F`; the least positive instructions can have 54 decimal digits.  The
[hidden-register audit](experiments/kontorovich/unit_charge_hidden_register_audit.json)
Hensel-lifts the collision through `F^3`, checks the first nonlinear carry and
the complete quadratic second-digit formula, and shows by CRT that the visible
register does not force `F^2`.  This is Simon's nonlocal programming-language
idea in literal arithmetic form.  It is still only a necessary `F`-adic ISA:
the exact 2-adic collision decoder has not yet been made to execute a selected
instruction.  Lean commit `34e166b` independently kernel-checks the universal
Taylor/carry law, geometric output identity, first-digit divisibility, and
existence and uniqueness of every recharge class modulo `F`.

A less rigid reproduction type has also emerged.  Since `A=3^114` and
`B=2^154` are squares, every quadratic norm

```text
N_d(x,u)=x^2+d*u^2
```

reproduces automatically across recharge.  The tempting sum-of-two-squares
case `d=1` fails universally: accepted states and collision quotients are both
`7 (mod 8)`.  The [quadratic-norm
audit](experiments/kontorovich/unit_charge_quadratic_norm_audit.json) therefore
uses the hardware-matched
`d=13(C-D)=5*13*19*1271069=7 (mod 8)`.  Exact CRT witnesses inhabit the input
and output endpoint types for several opcodes, and exact replay of a
PARI-discovered vector proves that the core `m=h=1` collision quadric has a
rational point.  The endpoints are deliberately separate: no integral
transition is claimed.  Lean commit `2743350` independently proves automatic
quadratic recharge closure, connects the compulsory `7 (mod 8)` residue to
accepted bouncer semantics, and closes the `d=1` type.  Commit `90c9b6c` adds
the crucial one-way semantic bridge: an already accepted typed step supplies
the literal collision quadric and its actual output coordinates.  It does not
turn a bare integral quadric point into a step.

The live closure equation is now the rank-four integral quadric

```text
C^m*(x^2+d*u^2+1)=D^m*(1+B^h*(t^2+d*v^2)).
```

This is a genuine two-rail “splash and regenerate” type and is much more
flexible than the 23rd-power Thue equation.  A first rank-one specialization
reduced to a generalized Pell solve but did not finish promptly; I stopped it
rather than turn the attack into another computation sink.  Next is to couple
the quadric's three free parameters to the writable hidden-`F` instruction and
the exact 2-adic opcode, seeking a parametric integral return rather than a
large isolated point.

Lean commit `07352a9` also completed the elementary public-power Roth bridge:
every generalized transition now kernel-supplies the exact approximation
bound and, once `alpha<s`, the exponent-11 inequality.  Roth itself remains an
external theorem, and the finite-class pigeonhole, reduced-rational
distinctness, and sequence-level finiteness consumer are still missing; no
global no-run result is promoted.

The detached jobs are healthy and should remain running.  Akdeniz's `kc-r23`
service is still inside the exact 1,198-digit Thue solve, with no solution or
completion line yet.  Ganesha still has the 22 unfinished non-uniform morphism
workers at roughly fifteen hours of CPU apiece; shards 4 and 12 are the only
completed files.  (An initial process-count command looked for the wrong
filename; direct inspection confirmed the workers.)  PSC remains idle because
this arithmetic is not GPU-shaped.  No counterexample or infinite orbit is
known.  This diary/artifact checkpoint was pushed as commit `f31a74d`.

### 2026-07-22 10:20 EDT

The first literal public-state reproduction type is now sharply understood,
but it has not produced a counterexample.  Writing the autonomous bouncer
state as `y=s^23`, every transition which preserves that type must have
recharge `h=23*ell` and collision quotient `t^23`, hence

```text
C^m*(s^23+1)=D^m*(1+(B^ell*t)^23),
y'=(A^ell*t)^23.
```

Lean commits `4c56925`, `f61f569`, and `9f00894` check the exact 23-class
normalization, rule out the complete-power class `m=0 (mod 23)`, retain the
valuation data in a cyclotomic cofactor balance, and expose a second hidden
register modulo the fixed divisor `F`.  A plain prime sieve which forgets
those registers has no traction.  The other 22 classes may contain isolated
transitions; no such transition or orbit is claimed.

There is a stronger proposed global obstruction.  In every nonzero class a
transition gives a rational approximation to `alpha=3^(e/23)` satisfying

```text
0 < p/q-alpha < alpha/s^23,       q < s^2,
```

and the next root is strictly larger than `s`.  This is eventually an
exponent-11 approximation, so Roth's theorem would allow only finitely many
of them in each class and would exclude an infinite run wholly inside the
pure 23rd-power type.  The exact normalization is in the new
[state-power audit](experiments/kontorovich/unit_charge_state_power_quine_audit.json),
but the universal elementary bridge still awaits Lean; the conclusion is
therefore recorded in the [strategy map](#kc-strategy-and-failure-map), not
promoted as a machine-checked result.  Corrected and multi-rail encodings are
the constructive escape: they must reproduce while evading this one-number
algebraic approximation trap.

The uncorrected `h=23` payload rail has independently collapsed to one exact
1,198-digit Thue equation, `3^15 X^23-Y^23=5 Phi_23(A,B)`.  Its global PARI
solve is now a detached, file-logged Akdeniz service.  Older bounded Akdeniz
batches were stopped because they no longer attack the live closure seam.
Ganesha's exact 24-shard non-uniform morphic-program search remains detached;
two shards have finished with no nontrivial cycle and 22 continue.  PSC has
only a GPU allocation and is idle until a genuinely CUDA-shaped symbolic
search appears.  No counterexample or infinite orbit is known.

### 2026-07-22 09:25 EDT

The shortest perfect-power rail is now closed, but the bouncer is not.  Lean
commit `5fbacf5` kernel-checks the entire one-way semantic chain: any accepted
`h=1`, `u=F*r^23 -> u'=F*r'^23` transition would supply integers satisfying

```text
3^15 X^23-2^16 Y^23=5.
```

PARI/GP 2.15.4 then ran the complete Bilu--Hanrot Thue algorithm for
`P(x)=3^15*x^23-2^16`.  It checked that `P` is irreducible, reported attached
tentative class number `1`, and returned the complete solution list `[]` for
right-hand side `5`.  PARI's documentation explicitly makes a flag-zero
result unconditional in the class-number-one case.  The precise verification
scope is therefore: no integer solution, conditional on PARI's documented
algorithm and implementation; this last step is not a Lean proof.  The
[executable GP audit](experiments/kontorovich/unit_charge_power_quine_thue.gp)
and [transcript](experiments/kontorovich/unit_charge_power_quine_thue_audit.txt)
record the version, class-number gate, and empty enumeration.

The failure is informative.  Recharge `h=23` is the first exact resonance:
both `A^23` and `B^23` are complete 23rd powers, while
`A^23=3^4 C^154` and `B^23=D^154`.  The three local sieves that almost killed
`h=1` leave all 23 exponent classes at this resonance, but that three-prime
diagnostic is not a global freedom result.  Four further exact local checks,
now kernel-checked in Lean, reduce the uncorrected single rail to `e=15`,
`m=9 (mod 23)`, and the one equation
`3^15 X^23-Y^23=5 Phi_23(A,B)`.  Next I am treating the
small residual `3^4` as a carry rail and looking for a multi-packet correction
which absorbs the fixed divisor `F` and regenerates its remote end cap.  That
is Simon's proposed “splash the gap” mechanism in algebraic form, rather than
another seed-range simulation.  The [exact resonance
artifact](experiments/kontorovich/unit_charge_power_resonance_audit.json)
checks both identities, the cyclotomic forcing, `gcd(F,Phi_23(A,B))=1`, and
complete survival of all 23 exponent classes modulo `47`, `139`, and `461`.
No counterexample or infinite orbit is known.

GP audit SHA-256:
`c4541ea4c0cdcac65d2738bef9fffd378ae0fe4c7495409b46be08cd80d76e48`.

### 2026-07-22 09:03 EDT

The search is now attacking reproduction inside the already autonomous charge
bouncer.  At one accepted transition write

```text
C^m u=1+B^h q,       D^m' u'=1+A^h q,
A=3^114, B=2^154, C=3^17, D=2^23.
```

The fixed register forces `F | u,u'` for `F=(A-B)/5`.  The encoding

```text
u=F*r^23,        u'=F*r'^23
```

is therefore a literal reproduction candidate: because `D=2^23`, the same
23rd-power payload form writes an integral number of next defect cells.  It is
not a fresh CRT word at each generation.  Eliminating the collision quotient
gives the exact closure equation

```text
A^h C^m r^23-B^h D^m' r'^23=(A^h-B^h)/F.
```

For the shortest recharge `h=1`, this becomes 23 generalized Fermat equations.
Complete 23rd-power residue enumeration modulo `47`, `139`, and `461` kills
22 exponent classes.  The sole survivor is

```text
m=5 (mod 23),       3^15 X^23-2^16 Y^23=5.
```

This is both progress and a failure: the first genuinely self-similar payload
has been reduced to one hard Diophantine equation, but it has not reproduced
yet.  The independent Lean agent checked that the last class is locally
soluble at all 429 primes `p<100000`, `p=1 (mod 23)`, so more blind modulus
sweeps are not the next move.  PARI/GP's fast Thue solver reports no integer
solutions but may use GRH; its unconditional certification mode is still
running on Akdeniz.  Next: certify or replace that computation, kernel-check
the semantic reduction, and if the rail is closed, vary the payload exponent
or recharge phase while preserving the same address-regeneration principle.

Artifact SHA-256:
`c60741d605a1c669bd89fe3a0b4d06d1dd883ec0a03792d3e44aab5331d474eb`.
Verifier file SHA-256:
`da18a787a4dd3e1fd1f56ae9eadb1fa7010594b9ba8e1764d7c9d395529496b2`.

### 2026-07-22 08:23 EDT

Simon correctly challenged the search for optimizing finite gadgets instead
of making the program reproduce.  A source/target audit then found a decisive
semantic error in the 07:44--08:10 synthesized-marker work.  The unit law is

```text
n -> m: 3^q(n)h-1=2^p(m)h'.
```

The claimed three-step route reached state `1` after its second transition but
then used `q(g)` from state `g`.  The exact raw divisions and coefficient
comparisons therefore did not compose in the public unit ISA.  I retracted the
two headline claims, removed both workers and artifacts (recoverable in git),
and told the Lean agent not to formalize their concrete semantics.

The replacement begins with the legal return

```text
1 -> 1 -> g -> g -> 1.
```

It has the exact composition

```text
3^(114+2Q)h-C_g=2^(154+2P)h',
P=23g+54, Q=17g+40,
C_g=3^(2Q+57)+2^77*3^(2Q)+2^(77+P)*3^Q+2^(77+2P).
```

The new verifier literally replays all four compatible valuations for
`g=1..16`.  More importantly, it makes **closure** the entry ticket:

```text
3^R(g)F(g)-C_g=2^S(g)F(f(g)).
```

A fresh CRT solution at every generation is now classified as preloaded
2-adic software, not progress toward reproduction.  For `f(g)=g+1`, exact
normalization gives a mixed-base Mahler equation.  No rational function solves
it: Lean now proves that a reduced denominator must be a monomial,
coprimality makes it constant, and the top-degree term contradicts the
nonzero linear forcing.  The next
constructive attack is a nonlinear/automatic self-writer, beginning with the
base-squaring opcode `g -> 2g`, while using the impossibility work to identify
which address mechanisms cannot represent one ordinary integer.

Artifact SHA-256:
`fbc46c761aec4319407dc091f2b089f3fba0e4f89e288601f9b2d83cf9ad6ce2`.
Verifier file SHA-256:
`6b18d52e67904212d8d91f0549b26362d4baa0fe550cb1641792948ff471bdb4`.

### 2026-07-22 08:10 EDT — RETRACTED at 08:23

**Correction to 08:00.**  The first bank artifact varied the marker lift `s`
while holding the remote register phase fixed.  Its three raw Collatz
divisions were exact, but that variation left the level-two invariant class;
the claimed public free family therefore omitted a necessary coupling.

The correction preserves the rank-one result and positive drift.  If
`u_j` is the exact catcher/register base, the register-preserving lift is

```text
u=u_j+2^(P_j-D)*((M-1)s+M*w).
```

The equal dyadic coefficients make the `M-1` term cancel the marker change
modulo `M`.  Both source and output now depend on

```text
v=s+w,
x_j=X_j+2^(P_j+155)*M*v
 -> y_j=Y_j+2*M*3^(q_j+114)*v.
```

The common `M` cancels from the coefficient ratio, so every opcode remains
strictly outward.  The corrected small-model replay additionally checks that
each source difference is divisible by its odd register modulus.  No broader
claim depended on the erroneous uncoupled parameterization.

Corrected artifact SHA-256:
`8a3bd0fc4ee0788541ed5b6974286ff86e58496404a7fcf2979c5a460c3da1af`.
Corrected verifier file SHA-256:
`8d9b01da1c7c786117725dd24fc87a625abff495b49def2075ff7474c1ca8971`.

### 2026-07-22 08:00 EDT — RETRACTED at 08:23

The stronger turnaround seemed to expose two free nonlocal registers: the
lift `s` of the synthesized marker and the remote catcher tail `w`.  Exact
valuation accounting shows that this is an illusion—but a useful one.

Allow every later legal third division

```text
P_j=D+2+23j,       q_j=q_0+17j,       j>=0.
```

The marker lift `t=t_j+2^(P_j+1)s` enters the source at binary exponent

```text
154+(P_j+1)=P_j+155.
```

For the remote contribution not to spoil the exact `P_j` division, it must
satisfy

```text
1+3^57u_j=0 (mod 2^(P_j-D)),
u=u_j+2^(P_j-D)((M-1)s+Mw).
```

That tail enters at

```text
155+D+(P_j-D)=P_j+155.
```

After the collision their output coefficients coincide as well.  Thus the
whole bank is rank one:

```text
v=s+w,
x_j=X_j+2^(P_j+155)Mv
 -> y_j=Y_j+2M*3^(q_j+114)v.
```

This rules out using the two spatial islands as two independent stacks.
The surviving object is nevertheless a promising unbounded tag language:
every opcode is outward.  Opcode zero has the previous exact gain, and each
increment multiplies it by

```text
3^17/2^23=129140163/8388608>1.
```

The [exact artifact](experiments/kontorovich/unit_marker_bank_audit.json)
reconstructs public opcodes `0..15` and fully materializes six small analogues,
each with three exact collision replays and both rank-one coefficient checks.
The live task is now to make the natural register `v` select an unbounded,
aperiodic sequence of opcodes.  A fixed opcode would merely repeat a periodic
valuation word and is already closed.  No counterexample is known.

Artifact SHA-256:
`8a3bd0fc4ee0788541ed5b6974286ff86e58496404a7fcf2979c5a460c3da1af`.
Verifier file SHA-256:
`8d9b01da1c7c786117725dd24fc87a625abff495b49def2075ff7474c1ca8971`.

### 2026-07-22 07:44 EDT — RETRACTED at 08:23

Simon's “other bits lined up” idea improves the fixed-marker turnaround more
than expected.  Fixing `H=17` made the preceding instruction an uncontrolled
class modulo a power of two whose exponent is the entire gap.  Reverse the
roles: keep that instruction at one cell and let the distributed marker carry
the alignment information.

The first two collisions require only one explicit ternary class:

```text
H=h_3+3^114*t,
2^154*h_3+2^77+3^57*(2^155+1)=0 (mod 3^114).
```

This gives, identically,

```text
3^57*A-1=2^77*C+2^155,
3^57*C-1=2^77*H,
```

so the same carry `B=1` reaches the repetend scrubber.  For
`D=2*3^56`, `P=D+2`, and target length
`g=45508489828466133670740130`, choose `t` by the single odd-coefficient
congruence

```text
3^(q(g)+114)t=1+2^P-3^q(g)h_3 (mod 2^(P+1)).
```

Existence and uniqueness are exactly the dyadic-writer lemma now
kernel-checked in Lean commit `a0073fd`.  The resulting marker has at most
`D+185` bits.  With the ordinary source-register restriction
`u=u0+4Mw`, the tail coefficients are

```text
input  =2^(D+157)M,
output =2M*3^Q,
Q      =773644327083924272402582364.
```

This time the macro is outward.  Since `Q` is even, `3^Q=9^(Q/2)>8^(Q/2)`,
and the certified excess over the input power of two is
`113771224571165334176850348` bits.  Lean commit `d085050` kernel-checks this
generic `9>8` comparison.  The
[exact artifact](experiments/kontorovich/unit_marker_turnaround_audit.json)
also materializes a small analogue and replays all three exact divisions.

This is the first same-scale expanding strike--scrub--turnaround family.  It
is not yet closed under its own output: the next task is to make the enlarged
tail select and satisfy the next marker cylinder without preloading an
infinite 2-adic address.  No counterexample is known.

Artifact SHA-256:
`475beaa146173295f49c382bc694bc9e11cec247df4d3fe43566f7147906a3a5`.
Verifier file SHA-256:
`809c95233c79c495ac2222127bd58d70f14d719e0ffbe13bb6d29b28d0b000c0`.

### 2026-07-22 07:30 EDT

The carry glider now has a formula-compressed turnaround.  Work in the
sign-negative level-two unit ISA

```text
p(n)=23n+54,       q(n)=17n+40.
```

Choose source and target length one, carry `B=1`, marker `H=17`, and

```text
D=ord_(3^57)(2)=2*3^56
 =1046695266054721074427023042.
```

The next legal division beyond the returned packet boundary is exactly
`P=D+2`, corresponding to target length
`45508489828466133670740130`.  Eliminating the first two collision prefixes
gives one power-of-two target modulo `3^114`.  Exact ternary digit lifting
finds

```text
l =985704136832889032287826201378021826095996227497733368
    (mod 2*3^113).
```

This class is even.  The formula-compressed turnaround condition

```text
3^(17l+40)*17 =1+2^P  (mod 2^(P+1))
```

also selects an even `l`, because `17=1 (mod 8)` lies in the even-power
subgroup generated by three.  The exact order theorem already kernel-checked
as `KontoroC.orderOf_three_twoPow` supplies the subgroup size, and CRT gives
an ordinary finite length without expanding its roughly `10^27` bits.

After the third collision, choose the invariant tail in the class
`u=u0+4*M*w`.  Exact cancellation gives

```text
h_out=R+2*M*3^(q(l)+114)*w.
```

The coefficient after the displayed factor two is odd.  Therefore, for every
finite width `E` and every odd word `T`, one unique `w mod 2^(E-1)` makes
`h_out=T (mod 2^E)`.  This completes Simon's strike--scrub--reseed picture as
a universal *finite* compiler: collision debris is translated, the vast gap
turns around, and the surviving payload can write any next finite catcher.

The [exact artifact](experiments/kontorovich/unit_carry_turnaround_audit.json)
does not claim an infinite ordinary tail.  Externally prescribing catcher
after catcher would still build only a 2-adic stack; the next attack is an
autonomous payload recurrence whose extension residues vanish eventually.
No counterexample is known.

Artifact SHA-256:
`f65eae7c602a6fc38bc7ba528bc090184dcf160e398c01e913099158581f47fe`.
Verifier file SHA-256:
`114c1ce6bb53fc396f5c06902ae12d55aef59f7a450080b3ab6440f52977a5cd`.

### 2026-07-22 07:00 EDT

The formalizer has reduced the ordinary-program question to a particularly
clean collision seam.  If a compiled prefix is

```text
K=R+2^P*t -> K'=S+3^Q*t
```

and the next block restricts `t=rho+2^E*u`, one ordinary natural can realize
the whole infinite program only if `rho=0` eventually.  Lean commits
`af1a934` and `ba121d9` prove the positive and necessary directions.  It is
therefore enough to force nonzero splashes at arbitrarily late scales.

The new [exact audit](experiments/kontorovich/unit_charge_zero_lift.py)
compiled every bouncer word of depths `1..4` over `(m,h) in {1,2,3,4}^2` and
tested all 16 possible next blocks: 69,904 prefixes and 1,118,464 extensions.
There are zero zero-lift events.  The closest case shares only 16 of the 177
low bits required by its next input.  Maximum terminal public valuations at
the four depths are `3,9,13,16`, so I am not claiming a fixed low-modulus
invariant; agreement can grow.

Artifact SHA-256:
`1c6f863dbe2c83adda3821bcd7f1f082c2e08e0880b708630640196af3568988`.
Verifier file SHA-256:
`b71feafab1c56e80b27e8e006eae640056831a249ab9cb427113e52526bbd33f`.

Simon's new metaphor suggests the next construction: do not ask one collision
to clean and reproduce itself.  Lay down a distributed bank of timed bit
islands so one splash strikes, a second eats the unwanted carry/debris, and a
third reseeds the next large gap.  I am translating that spatial
strike--scrub--reseed picture into a vector affine macro whose regeneration
condition is an exact CRT identity, with the zero-lift criterion as its kill
test.

That translation has already produced one exact glider cell.  If the first
correction leaves carry `B` after multiplying by `3^q`, let

```text
r=v3(B),
D=ord_(3^(q-r))(2),
z=B*(2^D-1)/3^q.
```

Then the catcher word obeys

```text
B+3^q*z=2^D*B.
```

So `B` is not just erased: it reappears unchanged beyond `D` clean zero bits.
The [formula-compressed verifier](experiments/kontorovich/unit_carry_repetend.py)
embeds this identity in the genuine unit register at all six compiled levels.
For the canonical one-cell header, `q=17,57,188,621,2051,6774`; the resulting
gap-length integers `D` have `8,28,90,297,979,3231` decimal digits.  Neither
`2^D` nor the `D`-bit catcher word is expanded.

Artifact SHA-256:
`57328afb5c10edbbedfb3e14881e0d1b53925bb2bc67ecd57e5f32f187c97c83`.
Verifier file SHA-256:
`3f9690acf60481d560c2eddc7056da3b186e0679e1f1c9fae077cdccb6ee96f2`.

This validates the metaphor but does not yet falsify Collatz.  A finite train
of these blocks is a long ether with a carry glider; an infinite preloaded
train is only a 2-adic tape.  The next target is an ordinary end cap whose
surviving payload writes another catcher block ahead of the glider—the
reseed phase.  No counterexample is known.

### 2026-07-22 06:45 EDT

The obvious way to add aperiodicity to the reversible bouncer does not pass
the ordinary-address gate.  I audited three standard low-description binary
clocks:

```text
Thue--Morse,
period doubling,
Fibonacci substitution 0 -> 01, 1 -> 0.
```

Each symbol was mapped injectively to every ordered pair of distinct opcodes
from

```text
(m,h) in {1,2,3,4}^2.
```

For all 240 codings and every prefix through 48 bouncer transitions, the
[exact worker](experiments/kontorovich/unit_charge_morphic.py) compiles the
complete charge-macro word, links it to the next defect, and reconstructs the
least positive fixed-form `y`.  None of the 34,560 successive prefixes leaves
that canonical address unchanged.  The closest nonstabilizing event is the
period-doubling coding

```text
0 -> (4,4),     1 -> (3,4),     depth 48,
```

whose consecutive addresses share 33,128 low bits but have respectively
33,386 and 34,092 bits.  That is a vivid 2-adic approximation, not one
ordinary program.

Artifact SHA-256:
`6beff79aa6fe363f4bbe7cd84a42d7cd69c232bbb13ac1d610201dd4927c52dc`.
Verifier file SHA-256:
`c823867bccbc2001c4a3d3c58d4dbd32741f362eced027ed16a5fb7cbf7893b3`.

This failure is deliberately narrow.  It does not touch general morphic
words, larger opcodes, or—most importantly—the bouncer's evolving odd payload.
Morita's reversible-counter result also makes clear why a canned aperiodic
clock is the wrong compiler target: actual universality needs conditional
counter operations.  The next search will use the payload to implement a
counter update or zero-test, with the determinant-four resonance as the
candidate transfer gadget.

### 2026-07-22 06:16 EDT

The fixed-form bouncer is lossless: every accepted output uniquely recovers
its predecessor and both variable opcodes.  If

```text
y'=3^(114h)*q,       3 does not divide q,
```

then necessarily

```text
h=v3(y')/114,
m=v3(1+2^(154h)*q)/17,
y=2^(23m)*(1+2^(154h)*q)/3^(17m)-1.          (KC-REV)
```

Substitution into the forward equations returns `y'` exactly.  The reverse
read is genuinely nonlocal: the forward defect length is written into a
ternary valuation at the opposite end of the transformed state, while the
recharge length is the exact power of three carried by the output.  This is
much closer to an ultra-simple reversible programming language than to a
local bit rewrite.

There is also a small arithmetic resonance hidden inside the enormous cell
sizes:

```text
114*23-154*17=4,
2^(23*154)=2^(154*23),
3^(114*23)=3^4*3^(17*154).
```

Thus exchanging 154 defect units against 23 recharge units cancels the
binary scale exactly and leaves only a factor `3^4`; the transposed exchange
cancels the ternary scale and leaves `2^4`.  This is not yet a glider—the
affine `+1/-1` seams and the fixed register still have to close—but it is a
specific formula-scale place to look for one rather than a request for more
simulation.

The bouncer artifact now checks `(KC-REV)` on all 128 linked members as well
as their forward macro replays.  Updated artifact SHA-256:
`5f2d6bfdcc6c48692e40e000ad8550262ac74b102c1e0b06238ab9783efbd4c2`.
Updated verifier file SHA-256:
`c434c7ddf57b15f271b7c22be66d6614199a76f41cc7ba36346ca53f7a2df754`.

The live attack is to exploit the determinant-four resonance to build an
invariant formula family for `(KC-REV)`.  Repeating one fixed `(m,h)` is
already excluded by the periodic-affine obstruction; any survivor must use
the reversible odd payload `q` to vary these counts unboundedly.

### 2026-07-22 06:05 EDT

The recursive splash has yielded a fixed-level autonomous bouncer rather than
another nested address.  Let

```text
A=3^114,      B=2^154,
F=(A-B)/5
 =493006936424420884140154671288273660376560866054730997.
```

The factor is integral because the background's difference is exactly the
collision constant times `F`.  In the level-two charge register define

```text
Z=F*G-2^26.
```

The offset was not fitted: `F*register_offset-2^26` is exactly divisible by
the register stride.  In this coordinate, the complete one-cell instruction
loses every affine constant:

```text
2^154*Z'=3^114*Z.                            (KC-BG)
```

This is a literal homogeneous delay wire.  A length-`N=m+1` defect injects
the exact difference-of-powers carry

```text
2^(154+23m)*Z'
 =3^(114+17m)*Z
  +2^26*3^114*(3^(17m)-2^(23m)).             (KC-DF)
```

At a defect boundary `Z=2^26*y`, where `y` is positive odd and lies in the
two fixed classes `y=0 (mod M)`, `y=-1 (mod F)`.  The state itself selects

```text
m=v2(y+1)/23,
E=3^(17m)*(y+1)-2^(23m),
h=(v2(E)-23m)/154.
```

If `m,h>=1` are integers, the defect followed by `h-1` background cells
returns

```text
y'=3^(114h)*E/2^(23m+154h).
```

Continuation asks only that `v2(y'+1)` be another positive multiple of 23;
the two fixed congruences are preserved by the literal register execution.
This is the first genuinely state-dependent, fixed-level programming
language found here: `y` reads a defect length, its collision reads a recharge
length, and the odd remainder becomes the next program state.  Every accepted
transition is outward.  Hence an infinite accepted positive `y`-orbit is an
ordinary Collatz counterexample.

The [exact bouncer worker](experiments/kontorovich/unit_charge_bouncer.py)
constructs all complete linked families with input/output defect extras
`m,m'=1..4` and `h=1..4`.  It checks 64 families and two members each,
comparing the displayed valuation map with literal execution through 320
charge macros and 640 original unit macros.  Artifact SHA-256:
`5f2d6bfdcc6c48692e40e000ad8550262ac74b102c1e0b06238ab9783efbd4c2`.
Verifier file SHA-256:
`c434c7ddf57b15f271b7c22be66d6614199a76f41cc7ba36346ca53f7a2df754`.

No infinite orbit is supplied.  The next work is now focused and
non-simulative: derive an invariant formula family for this two-valuation map,
or prove a proposed family impossible.  In programming-language terms, the
map is a one-register machine with two unbounded, state-read opcodes; in
Simon's spatial terms, `(KC-BG)` is the delay line and `(KC-DF)` is the splash
that must reproduce its own next timing word.

### 2026-07-22 05:46 EDT

The `-5` charge--discharge machine really does splash away its own next
collision, at every finite recursive depth.  Suppose one level has

```text
G=2^(23N+3)g -> (3^(17N+d)g-5)/2^e.
```

Following its length-`N` branch by its one-cell branch creates debris

```text
5*(3^(17+d)+2^(26+e)).
```

Restricting to the unique register class divisible by the parenthesized
factor and quotienting leaves `-5` again.  The offsets obey

```text
d_(j+1)=2*d_j+17,      d_j=114*2^j-17,
e_(j+1)=2*e_j+26,      e_j=154*2^j-26,
D_j=3^(114*2^j)+2^(154*2^j).
```

The key coprimality is now proved for all depths, not inferred from a finite
pattern.  Let `M=671265207750760396088265`, the fixed 80-bit register stride.
If a prime `r!=3` divided both `M` and `D_j`, then
`(3^114/2^154)^(2^j)=-1 (mod r)`.  Its multiplicative order would be divisible
by `2^(j+1)`, forcing `2^(j+1)<=r-1<M`.  Therefore only `j=0..78` can possibly
fail.  The verifier checks those 79 exact modular gcds; every one is `1`.
The prime `3` cannot divide `D_j` because its second summand is nonzero
modulo `3`.

The [hierarchy worker](experiments/kontorovich/unit_charge_hierarchy.py)
materializes eight exact levels.  At each level `N=1..8`, its direct CRT
branch agrees coefficient-for-coefficient with the restricted composition of
two parent branches.  It checks 64 branches and 128 members, then recursively
expands one varying-length member at each depth through 510 original unit
macros.  Artifact SHA-256:
`6ae387f7cc5db514a5314378121986540bda0f1741e8b97a566c7510cb643981`.
Verifier file SHA-256:
`71f9d2014225ec4a937bc8e489c11307139121b7a2a01cca1c59266b62adb1b9`.

This is a real regenerative splash, but the naive infinity is still the
wrong one.  A positive child packet lifts to its parent as

```text
K_j=rho_j+D_j*K_(j+1)>K_(j+1).
```

Consequently deeper canonical nestings make the root packet strictly larger;
they cannot stabilize to one ordinary natural.  The hierarchy is an
arbitrarily deep finite compiler, not a counterexample.  The useful residue
is its family of exact outward fixed-level machines.  The next attack is to
derive a packet-selected length law *inside one fixed level*, so that the
ordinary state evolves forward rather than being rewritten backward at ever
deeper addresses.

### 2026-07-22 05:34 EDT

The requested charge phase has collapsed to a small exact instruction set.
At sign-negative hierarchy level two, compose one unit instruction of length
`N` with the one-cell instruction.  Eliminating the intermediate core gives

```text
2^(p(N')+p(1))*h'
  =3^(q(N)+q(1))*h-(3^q(1)+2^p(1)).
```

Here `p(1)=77`, `q(1)=57`, and the collision debris has the useful
factorization

```text
3^57+2^77
 =5*314038802961906688057474567.
```

The large factor `D=314038802961906688057474567` is coprime to the odd
register stride.  There is therefore one exact packet class on which both
ends are divisible by `D`.  After quotienting, the whole two-instruction
composition is the autonomous public map

```text
G=2^(23N+3)g
  -> G'=(3^(17N+97)g-5)/2^128.               (KC-CD)
```

This is the first literal charge--discharge interface: the long instruction
amplifies the packet, the one-cell instruction eats almost all fixed collision
debris, and division leaves only `-5`.  Moreover every successful branch is
strictly outward for every `N>=1`, since already at `N=1`
`3^(17N+97)>2^(23N+131)` and the exponent gap increases thereafter.  An
infinite successful positive orbit of (KC-CD) would consequently be an
outward ordinary Collatz macro-orbit and a counterexample.  We do not yet
have that orbit.

The [exact worker](experiments/kontorovich/unit_charge_discharge.py) builds
each complete branch independently by CRT and by composing the two original
unit branches, then compares both affine coefficients.  The artifact checks
`N=1..32`, four members per branch, and 256 literal unit-macro replays.
Artifact SHA-256:
`e7af475f153a2e444b84f91dda8f4f395f1a048abde2383f40ac48eda4bef564`.
Verifier SHA-256:
`5c6cb46cec58720ef3d215651312556a05a3970a089792c3cd29ba7f3831e05a`.

This `-5` is not being inferred from the old signed-cycle pilot: it is a new
positive quotient register with exponents `(23N+3,17N+97,128)`.  The next
test is exactly Simon's regenerative metaphor at one scale higher: compose
this machine with its own one-cell discharge, quotient the new debris, and
ask whether the same `-5` instruction reappears rather than accumulating
damage.

### 2026-07-22 05:24 EDT

The exact second splash also reveals why a pure repetend tower cannot be the
counterexample.  At a sign-negative marker-one splash, integrality forces

```text
T=(2j+1)*3^(q-1).
```

For every `q>=3`, an elementary induction gives
`3^(q-1)>=2q+1`.  Therefore

```text
2^T >= 2^(2q+1)=2*4^q > 2*3^q.
```

The exact unit recurrence is

```text
2^T*h_next=3^q*h-1,
```

so `h>2*h_next`: a giant repetend splash consumes more than half of its odd
core.  After `N` consecutive splashes one would have
`h_0>2^N h_N>=2^N`, impossible for one fixed positive integer `h_0` as `N`
grows.  This closes even a hypothetical self-writing implementation of the
pure consecutive instruction, not merely the externally preloaded nesting.

The [energy audit](experiments/kontorovich/unit_repetend_energy.py) checks the
generic integer separators and the actual marker-one exponent classes at all
three sign-negative finite levels `2,4,6`.  Artifact SHA-256:
`33ed88a031967a3012c5609add1959ea5bb6afda84479267c6c58fc2bfe61efa`.
Verifier SHA-256:
`9bcf9d11dc867f95d44d80203d7d0ee5c4d01edcd3531bb066617de010767853`.

This does not undo the two-splash construction; it explains its energy bill.
The initial core can pay for two enormous erasures but no finite core pays
forever.  The live architecture must alternate phases: many outward
small/medium instructions charge real core magnitude and ternary bank, then
one repetend splash spends that stored resource to relocate and clean the
gap.  I am moving from a pure splash staircase to this charge--discharge
controller; bounded seed simulation would not expose the required balance.

### 2026-07-22 05:16 EDT

The sign-negative unit splash renews once exactly.  This is the first result
past the isolated nonlinear launch.  At level two the first jump has

```text
q_0=57,
T_0=21457252954121782025753972361,
n_1=932924041483555740250172709,
q_1=15859708705220447584252936093.
```

To retain the first `3^q0` packet through a second minus-one repetend, define

```text
c_m=(2^(3^(m-1))+1)/3^m.
```

Cubing `-1+3^m c_m` gives the exact recurrence

```text
c_(m+1)=c_m-3^m*c_m^2+3^(2m-1)*c_m^3.
```

Hence `c_(m+1)=c_m (mod 3^m)`: after precision `P`, this quotient is stable
modulo `3^P` forever.  The level-two register has `v_3(M)=33`, so precision
`P=q_0+33=90` simultaneously retains the first ternary bank and resolves the
whole register conductor.  Exact CRT produces the odd multiplier

```text
k=376213925255524775706446580991916826376956379,
T_1=3^(q_1-1)*k.
```

It satisfies both `k*c_(q_1)=1 (mod 3^90)` and
`T_1=54 (mod 23)`, making `T_1=p(n_2)`.  If

```text
R_i=(2^T_i+1)/3^q_i,
A=(R_1-1)/(2*3^q_0),
```

then an exact unbounded family is

```text
h_0=R_0+2^(T_0+1)*(A+2^(T_1+D-1)*L)
 -> R_1+2^(T_1+D)*3^q_0*L
 -> 1+2^D*3^(q_0+q_1)*L.
```

The [symbolic verifier](experiments/kontorovich/unit_double_repetend.py)
reduces unmaterializable exponents modulo the exact Carmichael exponent of
the register.  It checks 89 quotient-recurrence stages, the retained-bank
congruence, bridge integrality, and the source, intermediate, and final
register phases for `D=1,64`.  `T_1` has about `7.57*10^27` decimal digits;
neither it nor the corresponding states are expanded.  Artifact SHA-256:
`76ce98689eef74589937e05b3c3295844f49620ab8e2e9fb0a4889b5749a61f5`.
Verifier SHA-256:
`05dfc41a661089c68fa57cebbb850cc5109bec24803efda227c16825ede0453c`.

This is a genuine second collision renewal, not a counterexample.  A third
externally prescribed repetend can again be nested, but doing so merely
pushes another changing binary address into the initial packet.  The live
test is now sharper: can the final ordinary free packet `L` autonomously
select and synthesize the third correction, so that one fixed initial address
survives?  That is the self-writing case; another backward-preloaded tower is
rejected by the ordinary-tail gate.

### 2026-07-22 05:05 EDT

The two-layer splash has a formula-compressed nonlinear specialization.  For
one unit collision, choose an odd marker `C` and an exponent `T` with

```text
2^T C = s  (mod 3^q),
R=(2^T C-s)/3^q.
```

Then `R` is an ordinary positive rational-base repetend and, identically for
every `D>=1` and packet `K`,

```text
3^q(R+2^(T+D)K)+s = 2^T(C+2^D 3^qK).        (KC-R)
```

The collision annihilates the entire periodic correction rail, emits `C`,
and leaves `D` zero bits before the surviving packet.  This is not a long
prefix found by search; it is a short formula for a spatial wire.

Because `2` has order `2*3^(q-1)` modulo `3^q`, `T` lies in one explicit
discrete-log class.  Intersecting that class with the unit schedule
`T=p(n')=a*n'+B` by CRT succeeds at every one of the six constructed levels.
The exact symbolic audit uses source length one and obtains:

```text
level        1    2    3    4     5     6
marker C     5    1    1    1     1     1
digits(T)    9   29   91  299   980  3235
digits(n')   8   27   89  296   977  3231
```

At level one the values are already `T=105734623` and `n'=13216826`, so the
explicit correction rail would have about 31.8 million decimal digits.  The
higher rows are vastly beyond materialization.  The
[worker](experiments/kontorovich/unit_repetend_splash.py) therefore checks the
exact order, discrete logarithm/CRT, divisibility, and source/target register
phases by modular arithmetic without constructing `2^T`.  The artifact has
twelve symbolic families, for gaps `D=1,64` at each level.  Artifact SHA-256:
`fc73032df9114e59ca3f8926509616b66455d69b61536866cc50728fc7a2d170`.
Verifier SHA-256:
`d1991059ec7be5b754d9352395d3053ce305496bc2dc85f849ea21eb9b0d3554`.

This is the first unit construction whose next length is not remotely
constant-rate: it jumps from one cell to millions of cells at level one and
to formula-sized astronomical lengths above that.  It is still only one
jump.  The emitted core `C+2^D3^qK` must now be made to launch another
repetend splash from its own packet contents.  That renewal equation—not a
larger simulation—is the live test.

### 2026-07-22 04:49 EDT

Simon's proposed collision cleanup is now an exact two-layer instruction in
the invariant unit register.  Write the current unit recurrence as

```text
2^p h' = 3^q h+s.
```

Choose `C` to be the complete low binary prefix which makes `h'` execute the
next desired branch, including the extra bit certifying that its valuation is
exact.  Modular inversion constructs

```text
3^q A+s = 2^p C+2^(p+L)B.
```

The first correction `A` therefore emits `C` but leaves carry `B`.  Now use
exactly `D` low bits of the remote packet to solve

```text
B+3^q z=2^D B_2.
```

For every remaining natural tail `u`, the two equations combine to

```text
h=A+2^(p+L)(z+2^D u)
  -> h'=C+2^(L+D)(B_2+3^q u).
```

This is the literal “other bits eat the bad parts and regenerate the gap”
mechanism: `z` disappears into the collision carry, `D` clean zeros appear
above the next instruction, and the untouched high packet survives under an
affine power-of-three update.

The [exact worker](experiments/kontorovich/unit_gap_regenerator.py) also
intersects this family with the odd invariant register and checks two actual
compiled unit branches.  Its artifact reconstructs 486 families at all six
finite hierarchy levels—every triple of lengths `1..3`, gaps `1,4,12`, and
two tail members—for 972 linked two-branch replays.  The level-one worked
case `(1,2,3,D=12)` is

```text
96640062369165269810946648141077
 -> 5811505674703125430887858069149
 -> 995193873655264956279801575123,
```

with the middle 103-bit core containing the complete 40-bit next instruction,
then twelve zero bits, then its residual packet.  Artifact SHA-256:
`3337b99b291894f6338716a1a2d1e459f3ae414086c239bca693258052212f3d`.
Verifier SHA-256:
`c737953183b760a9411ad5d2d6e57cad7eb3560578353c78166e2afe8381772a`.

This is a finite compiler identity, not an infinite orbit.  It locates the
remaining problem exactly: after each splash the surviving affine packet must
produce the next sacrificial word from its own state.  Preloading infinitely
many such words merely reconstructs a nonordinary 2-adic stack.  I am now
treating the residual update as a mixed-base pop/push language and searching
for a self-writing, packet-selected word rule.

### 2026-07-22 04:29 EDT

The unary factor-bank obstruction extends to every positive constant rate.
For `n_t=n_0+kt`, exact backward unrolling gives

```text
h_0=-s/3^(q(n_0)) *
    F(2^(ak)/3^(ck), 2^(p(n_0+k))/3^(q(n_0+k))).
```

Coefficientwise conversion uses theorem parameter
`3^(ck)/2^(ak)`, but the rational argument simplifies to
`2^(p(n_0))/3^(q(n_0))`, independent of `k`.  The theorem's logarithmic size
ratio is also unchanged because `k` cancels.  Thus the cited full-source
Väänänen--Wallisser theorem excludes an ordinary integer core for every
`n_0>=1` and fixed integer `k>=1` at all six compiled unit levels.

The rebuilt [exact artifact](experiments/kontorovich/unit_linear_theta_audit.json)
checks the generalized symbolic coefficient law and elementary hypotheses;
its literal linked branch replay remains explicitly scoped to the finite
step-one schedules `1,...,9`.  Artifact SHA-256:
`682d5636c66f1ea2a8f2cad7e58027da1e821513f248726175c839907bad312a`.
Verifier SHA-256:
`944eeaa73a8b860d36531b90e866941ab282633b0ebd2736839fd00b8d870e28`.
The irrationality is still an external published-theorem application.

This sharpens Simon's “splash the gap” proposal.  A viable cleanup rail
cannot merely fire every fixed number of cells.  Its sacrificial bits must
both absorb the collision debris and use unbounded packet state to choose
where the regenerated clean gap appears.  The next target is therefore a
two-rail, packet-controlled return equation, not a longer constant delay.

### 2026-07-22 04:17 EDT

The first factor-bank clock is closed.  If one tries to advance the unit
length linearly, `n_t=n_0+t`, then

```text
2^(p(n_(t+1)))*h_(t+1)=3^(q(n_t))*h_t+s
```

unrolls to the unique 2-adic candidate

```text
h_0=-s/3^(q(n_0)) *
    F(2^a/3^c, 2^(p(n_0+1))/3^(q(n_0+1))).
```

The identity

```text
F(2^a/3^c,z)=f_(3^c/2^a)((3^c/2^a)z)
```

puts it exactly in Väänänen--Wallisser's 1989 theorem.  Their result applies
uniformly to all six compiled levels and every `n_0>=1`.  The only delicate
size condition has a short integer audit: `2^8>3^5` gives
`log(2)/log(3)>5/8`; `3a>=4c` then gives the relevant ratio greater than
`5/6`; and `45<64` gives `1/6<(3-sqrt(5))/2`.  The candidate is irrational in
`Q_2`, hence cannot be an ordinary integer core.

The new exact artifact separately compiles eight linked transitions at each
of the six levels and checks the finite rational and 2-adic truncation
identities.  The level-six regression reaches 172,972 bits of terminal
2-adic precision.  Artifact SHA-256:
`fa6a00ae1e91e901440fff05cbda7ba5648049351924b88ad1a154f1136f43cf`.
Verifier SHA-256:
`62f282afbd3472eb514bec34b36a499d7863ddb0bcef345b263cab2b6b4569fa`.

This is a published-theorem application with an exact hypothesis audit, not
a reproof of that theorem and not a Collatz result.  Architecturally it is
decisive: synchronizing the ternary bank to a unary `n -> n+1` counter simply
recreates the rigid partial-theta obstruction.  The next bank must let its
ordinary packet contents choose a nonlinear, aperiodic change of length.

### 2026-07-22 04:07 EDT

The surviving unit machine is an exact signed radix swap.  Put
`p=an+b+e`, `q=cn+d`, and scale the public register by `W=2^eH`.  Every legal
member has a core `h` coprime to six and obeys

```text
W =2^p*h,
W'=3^q*h+s,              s in {+1,-1}.
```

Thus the instruction reads an exact binary zero-gap, preserves the whole
nonlocal core, writes an exact ternary zero-gap, and changes only one signed
unit.  If `y=W-s` and `y'=W'-s`, comparison with the signed router gives

```text
3^(p-1)*(y+s)/2^p = 3^(p-1-q)*y'.
```

The apparent collision debris is therefore not amorphous: it is the precise
missing factor `3^d`, `d=p-1-q>0`.  Across the six compiled levels,

```text
d(n)=2n+3, 6n+13, 20n+45, 66n+151, 218n+501, 720n+1657.
```

The rebuilt exact artifact verifies the two factorizations, exact ternary
valuation, and signed-router trim on all 768 previously checked members; the
32 literal first-level members still expand through 336 links and 672 gates.
Artifact SHA-256:
`459bd3feb5a30d931caf43c601db8713354696d9ae072e223e3603d77838b753`.
Verifier SHA-256:
`4057b56485ea1570d0b5abd2f50415f909e8afbc4b8f04f0c04baaf73ce265ff`.

This is not a counterexample.  It turns Simon's “other bits eat the bad
parts” idea into a concrete design specification: a second separated rail
must catch or represent `3^d` and re-inject it on the next collision.  Merely
cleaning a binary suffix, or nesting another splash, cannot do that.

### 2026-07-22 03:41 EDT

The splash hierarchy now has a universal ordinary-seed obstruction.  For one
renormalization step let `E=E_B+E_H` be the combined parent input exponent,
let `q_raw>0` be its least raw input, let `r>=0` be the inherited binary
valuation, and let `K>=1` be any child packet.  Direct substitution gives

```text
q=(q_raw-2^E)+2^(E+r)K
 =q_raw+2^E(2^rK-1)>0.
```

So a child can splash through its parent and regenerate the capped gap, but
it always leaves a positive ancestral tail.  Every further nested extension
therefore differs from the canonical parent packet; by the ordinary-tail gate,
an infinite adjacent-defect tower is a 2-adic phantom rather than one ordinary
Collatz program.  This subsumes the bounded canonical quine failures.  It does
not touch a genuinely autonomous orbit of any fixed finite-level register.

The exact checker now asserts the identity on every constructed step and
records it in the rebuilt six-level artifact.  Its SHA-256 is
`b568fb1b5228ced1f1198ad6375ba7f256e5f6f3dcf158dfc60d3d018dcdaf50`;
the verifier SHA-256 is
`a0c05f28c9e585194e64b1df755e13ea7c5e4fbbc43cc7a0346f23e8c836b1e9`.
The dependent unit-slice artifact was also rebuilt; its current hash and
scope are recorded in the experiment README and the next diary entry.  Next I
am abandoning deeper towers and attacking the fixed-level unit law
`2^B h'=3^A h+/-1` as an evolving, aperiodic odd-packet machine.

### 2026-07-22 03:31 EDT

The `17` collision particle has an invariant unit slice.  At any certified
hierarchy level the register is `V=r+mK` with `m` odd and invertible modulo
`17`.  Exactly one packet class

```text
K=-r*m^(-1) (mod 17)
```

makes `V=17H`.  Since an executable branch also has odd part `g=17h`, its
whole update divides by `17`:

```text
H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e,   s in {+1,-1}.
```

The slice is automatically preserved; no new congruence is needed at the
output.  In Simon's splash language, the aligned nonlocal bits have eaten all
but one unit of collision debris.

The new [unit-slice artifact](experiments/kontorovich/breakoff_unit_slice_audit.json)
checks the six finite hierarchy levels.  For `n=1..32`, each unit branch is
built independently and compared coefficientwise with the unique mod-17
subcylinder of its `±17` parent: 192 branches and 768 members.  Thirty-two
level-one members are also replayed literally through 336 lower links and 672
gate macros.  The packet residues at levels one through six are
`3,16,0,2,6,8 (mod 17)` and the collision signs alternate `+,-,+,-,+,-`.

This does not produce an infinite orbit.  It does isolate the irreducible
arithmetic problem: a positive odd packet must repeatedly arrange a high
power-of-two division of `3^A h +/- 1` while the selected exponent changes
aperiodically.  Fixed odd payload is impossible (`h(2^B-3^A)=+/-1` reduces
to the excluded tiny power-difference cases), so the next search concerns a
genuinely evolving unit packet, not another static quine.

### 2026-07-22 03:18 EDT

Ran the first exact finite-quine kill test on the variable splash alphabet.
A meta-word `(j_1,...,j_L)` is compiled so that depth `L+1` begins with the
whole depth-`L` macro program.  Equality of their canonical first-scale
packets would therefore be a genuine ordinary-seed stabilization event: the
old finite seed would already contain the new source code.

The rebuilt artifact exhausts every meta-word through depth three with
`1<=j_i<=8`:

```text
depths:                   1    2    3
nodes checked:            8   64  512
canonical stabilizations: 0    0    0
canonical decreases:      0    0    0
```

All 576 extensions strictly increase the packet.  The closest depth-two and
depth-three words are `(1,1)` and `(1,1,1)`, with 23 and 155 shared low bits;
these are precisely the 2-adic tower already diagnosed.  This is a scoped
failure of zero-top-tail quines in a small but complete symbolic meta-tree,
not a search over ordinary seeds and not an exclusion of nonzero evolved
tails.  The next quine ansatz must feed the *output* packet back as high-level
state rather than repeatedly choose the least CRT representative.

### 2026-07-22 03:08 EDT

The recursive splash has a variable instruction alphabet.  At a parent level

```text
V=2^(an+b)g -> (3^(cn+d)g+s*17)/2^e,
```

choose any background branch `j>=1`, use the adjacent branch `j+1` as its
defect, and retain the background valuation `aj+b`.  Whenever the exact phase
identity is evaluated, the primitive child again has collision constant
`-s*17`.  Its visible parameter update is

```text
a' = aj+b+e,                 c' = cj+d,
b' = aj+b-r0,                d' = c(2j+1)+2d,
e' = a(j+1)+b+2e+r0,         s' = -s,
```

with `r0` the defect's computed inherited binary valuation.  This replaces
the fixed morphism `1 -> 1,2,1` by a meta-instruction `j -> j,j+1,j^N`.

The rebuilt renormalization artifact checks every level-one adjacent choice
`j=1..64`; all 64 return to the capped interface and normalize to `-17`.
It also follows the nonconstant background words `(2,2,2,2)`, `(3,1,4,2)`,
and `(8,5,3,1)` through four successive renormalizations, obtaining collision
signs `+,-,+,-,+` in each case.  Exact artifact/verifier hashes changed and
are updated in the experiment guide.

This is a stronger programming-language result, but still not a survivor.
An externally chosen infinite meta-word consumes unbounded nested binary
address and generally names a 2-adic program.  The next useful event must be
finite self-reference: an evolved packet choosing its own next `j` while its
ordinary lower address has stopped changing.

### 2026-07-22 02:57 EDT

The capped splash renormalizes repeatedly.  A level has primitive register

```text
V=r+mK,
V=2^(an+b)g -> V'=(3^(cn+d)g+s*17)/2^e.
```

Use branch one as background, branch two as defect, and retain the background
branch-one valuation instead of exhausting the gap.  At each of the five
checked renormalizations the cap phase returns to the defect and the normalized
collision is exactly `-s*17`.  The certified parameter table is

```text
level       1      2       3        4         5          6
sign        +      -       +        -         +          -
cell a      8     23      77      254       839       2771
offset b   -5      3      24      100       354       1192
divide e   20     51     153      485      1578       5189
```

The new [renormalization artifact](experiments/kontorovich/breakoff_renormalization_audit.json)
checks six levels and five sign flips.  For each step it builds child branches
`N=1..8` independently by public-register CRT and by direct parent defect/ether
composition: 40 coefficient comparisons, 80 replayed members, and 520 parent
macro blocks.  Its verifier hash is recorded in the experiment guide.

I also expanded the most tempting infinite-program candidate: choose branch
one and top tail zero at every depth.  The induced substitution is
`n -> 1,2,1^n`.  Depth six expands to 360 linked first-scale glider macros,
1,189 lower links, and 2,378 literal gate macros.  Its generated ordinary
start has 22,284 bits (6,708 decimal digits), close to Simon's proposed
program scale.  But this is precisely the ordinary/2-adic trap: first-scale
packet sizes at depths `1..6` are `7,46,177,606,2021,6698` digits, and each
packet is strictly larger than the preceding one.  Their exact shared-low-bit
counts are `23,155,589,2013,6715`; the address converges 2-adically while the
ordinary integer never stabilizes in the checked tower.

So the result is a genuine recursive hardware language and a large finite
program, not a counterexample and not an all-level theorem.  Extending the
same zero-tail tower is no longer the priority.  The next attack is a finite
quine or state-dependent high-level tail that makes the *ordinary* lower
packet stabilize while the macro word remains aperiodic.

### 2026-07-22 02:45 EDT

Simon's suggestion to let aligned bits "eat the bad parts and regenerate" is
exactly the missing move at the next scale.  Use the one-cell returning glider
`B=M_1` as a background super-cell.  In its macro-tail `q`,

```text
B: K=R+2^23*q -> K'=S+3^17*q,
F(q)=(3^17-2^23)q+(S-R),
2^23 F(q')=3^17 F(q).
```

Thus a `B` self-link consumes 23 binary bits of `F`.  A fully exhausted
second-scale ether has odd `F` and the wrong parity to enter *any* glider
defect.  The useful splash does not erase everything: retain exactly three
bits.  Modulo `16`, that capped boundary is always the input phase of the
`B -> M_2 -> B` defect, independently of the ether length.

After removing the defect's common factor `3^7`, its primitive register is

```text
V=-8744697538656344367967+671265207750760396088265*K.
```

For every requested super-ether length `N>=1`, the returning branch becomes

```text
V=2^(23N+3)g  ->  V'=(3^(17N+40)g-17)/2^51,
K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t.
```

The huge cancellation is exact:

```text
2^54*(-8744697538656344367967)
 - 3^33*(50679661 + 120751555*(-234676942119623))
= -2^3*17.
```

The new [super-ether artifact](experiments/kontorovich/breakoff_superether_audit.json)
checks 64 affine branches and 256 members.  It literally replays 32 members
through 336 returning glider macros, 1,040 lower links, and 2,080 gate macros;
the verifier hash is recorded in the experiment guide.  This is a finite
two-scale constructor, not a counterexample.  The conceptual gain is the
renormalization `+17 -> -17`: the same collision residue survives, while the
three-bit splash cap reverses its phase.  Next I am testing whether the
sign-flipped machine nests again and whether any resulting hierarchy has an
ordinary positive realization rather than only a coherent 2-adic address.

### 2026-07-22 02:24 EDT

The returning glider ISA has an unexpectedly small autonomous normal form.
Define

```text
Y=83790531*K-874281.
```

For a length-`n` macro, write `Y=2^(8n-5)h` with `h` odd.  Boundary return is
one congruence `3^(6n+11)h+51=0 (mod 2^20)`, and the transformed register is

```text
Y'=(3^(6n+11)h+51)/2^20.                            (**)
```

The constant `51` is exact: the large defect terms cancel through
`2^20*(-874281)-3^11*(-5175081)=51`.  The persistent packet invariant is
`Y=-874281 (mod 83790531)`.  For each `n`, that odd-modulus condition and the
binary boundary condition have one CRT solution for `h` modulo
`83790531*2^20`.  Translating the resulting affine branch back to `K` gives
*exactly*, coefficient for coefficient, the returning macro `R_n,S_n` from
the previous diary entry.

This is the precise version of Simon's "splash the gap" picture: the collision
debris is the residual `+51`, while the nonlocal CRT-selected bits absorb it
and regenerate the next clean packet boundary.

The new [ether-counter artifact](experiments/kontorovich/breakoff_ether_counter_audit.json)
checks all 128 branches `n=1..128` at four tails each and verifies the public
partial map, invariant, strict growth, and equality with the compiled glider
macro.  It also repeats the literal executable checks through `n=32`: 64
macro members, 1,184 links, and 2,368 gate macros.  The disjoint input
cylinders have total dyadic mass

```text
sum_(n>=1) 2^-(8n+15) = 1/(255*2^15),
```

so this software language is extraordinarily sparse, as Kontorovich's
argument predicts.

No infinite orbit of `(**)` is known.  The advantage is conceptual and
practical: the counterexample search has been reduced from 10,000-digit
Collatz seeds to one exact public register with a valuation-selected exponent,
a fixed division by `2^20`, and constant `51`.  The next attack is a
self-generated aperiodic valuation orbit of this map, including nested-ether
and Mersenne/carry ansätze; raw seed simulation remains secondary.

### 2026-07-22 02:14 EDT

The exposed ether boundary now returns to a defect.  First, a useful parity
kill: every exact finite ether ends with an odd tail.  For an immediate
`E -> H_j -> E` defect, collision opcode `j>=2` forces the target coefficient
to be `1 mod 4`, hence its `E`-tail address is even.  This rules out
`H=(1,136,1)` as a self-regenerator at every depth, not just in a search box.
The opcode-one defect `H=(1,1,1)` is the parity-compatible receiver.

Its links are strikingly small:

```text
E -> H:  67+2^7*v   -> 381+3^6*v,
H -> E: 151+2^8*w   -> 144+3^5*w,
v=170+2^8*u,             w=485+3^6*u.
```

On `u=2^5*K-1`, the returned `E` tail satisfies

```text
473*t+12=2^5*(83790531*K-874281),
```

so one odd class of `K` writes exactly `n` ether cells for every `n>=1`.
Solving one further binary congruence makes the exposed odd boundary equal the
next defect input `X(K')=2^20*K'-10941`.  The whole block therefore compresses
to the returning macro

```text
K=R_n+2^(8n+15)*q  ->  K'=S_n+3^(6n+11)*q.          (*)
```

The new [ether-glider artifact](experiments/kontorovich/breakoff_ether_glider_audit.json)
constructs `n=1..32`, replays two ordinary members of every family, and checks
1,184 exact links / 2,368 literal gate macros.  This is a true finite glider
ISA: defect, periodic medium, exposed boundary, and return to the same defect
family are all exact.  It is not yet an infinite glider.

The simplest controller fails cleanly.  Every pair `n -> n+1` can be linked,
but if the remaining higher macro tail is exhausted immediately, the generated
`n+1` state misses the `n+2` cylinder for all `n=1..128`.  The maximum is two
linked macros.  The [strategy/failure map](#kc-strategy-and-failure-map) now
targets a nonzero payload recurrence for `(*)`—or a branching length rule—so
that the hardware, not an infinite preloaded address, chooses successive
ether lengths.

### 2026-07-22 02:03 EDT

The nonlocal amplifier has now been coupled to an exact finite spatial ether.
Let `E=(1,2,1)`.  Its self-link is

```text
t=20+2^8*v  ->  t'=57+3^6*v,
```

and direct elimination gives

```text
2^8*(473*t'+12)=3^6*(473*t+12).
```

Thus the 2-adic fixed tail is `-12/473`, and an ordinary tail with
`v_2(473t+12)=8n` executes exactly `n` outward ether cells before its finite
defect reaches the boundary.  Infinite bare ether is still only the forbidden
2-adic periodic program; the useful object is a finite background plus a
moving defect, as in Kontorovich's Game-of-Life picture.

The new point is a regenerative defect.  The gate `H=(1,136,1)` supplies an
exact two-link return `E -> H -> E`.  After a Mersenne residual substitution,
the returned tail has

```text
473*t+12 = 2^8*(r+A*K),
```

for two fixed odd integers `r,A`.  Consequently one explicit odd class of the
remote packet `K (mod 2^(D+1))` makes the returned ether depth exactly `8+D`.
Setting `D=8n-8` writes any prescribed finite `n`-cell delay line.  The new
[ether-defect artifact](experiments/kontorovich/breakoff_ether_defect_audit.json)
constructs `n=2..32`, performs 589 exact linked-member checks, and replays
1,178 literal gate macros.  These are formula-selected programs, not a seed
range scan.

This is still not an infinite glider.  When the `n` cells are consumed, the
exposed boundary is not yet proved to lie in the input cylinder of a fresh
defect with a larger `n'`.  The live [strategy/failure
map](#kc-strategy-and-failure-map) now asks for precisely that boundary return,
with `n'` generated from the surviving packet rather than encoded by an
ever-growing initial 2-adic address.

### 2026-07-22 01:41 EDT

Simon's proposal that other bits could “eat” the collision debris and
regenerate the gap has produced an exact nonlocal instruction.  In the
five-trit dispatcher, select one of the seven words

```text
b=3^5-2^L,       1<=L<=7,
```

and feed it a residual packet `v=K*2^L-1`.  The native tail write then
satisfies

```text
b+3^5v = 2^L(3^5K-1).
```

Thus the collision sacrifices the input's `L` trailing one-bits to create
`L` zero-bits.  More importantly, choosing the *remote* packet by
`3^5K=1+2^D (mod 2^(D+1))` creates exactly `L+D` zeros.  This is the
nonlocality we were looking for: widely distributed bits of `K`, rather than
a neighboring cleanup symbol, determine how far the regenerated gap extends.
The new [amplifier artifact](experiments/kontorovich/splash_gap_amplifier_audit.json)
checks all seven concrete writer links and `D=1..32`, performing 224 exact
linked-member checks and 448 literal gate-macro replays.  The identity and
the odd residue class for `K` are algebraic for every `D`; Lean formalization
has been requested.

This is not a counterexample.  The amplified zero run is nested in the
residual tail rather than yet installed as the next public delay.  The next
attack is a two-stroke turnaround: expose that internal run at a later
collision while retaining enough of its odd part to recreate another
Mersenne packet.  The [strategy/failure map](#kc-strategy-and-failure-map)
now treats this payload-generated repair as the live escape from the negative
tail-zero base graph.

### 2026-07-22 01:19 EDT

The first attempt to satisfy the ordinary-tail theorem by immediate address
stabilization is exact and sharply negative.  Every delay shape has a
canonical least coefficient.  Requiring its output to equal the next shape's
least coefficient gives a literal tail-zero edge: no additional bit of a
preloaded 2-adic tape is requested.  The new [base-graph
artifact](experiments/kontorovich/delay_base_graph_audit.json) exhausts all
1,010,000 shapes with `q,q'=1..100` and `j=0..100`.  It finds ten apparent
edges, but seven have coefficients divisible by eight and merely relabel
whole delay cells.  After maximal-gap normalization only three ordinary edges
remain:

```text
(1,1,90) -> (90,5,1),
(1,2,61) -> (61,4,1),
(2,2,61) -> (61,4,1).
```

All three target gates fail at their next collision, so the maximum canonical
base-edge chain is one.  Their two 59-digit and one 85-digit starts are
literally replayed and reach `1` after respectively 1,272, 1,277, and 330
ordinary Collatz steps.  This is not a seed-range experiment: it is an
exhaustive symbolic shape test of the most stringent stabilized-address
program.  Failure redirects the two-stack attack toward nonzero payload state
created by earlier instructions, or a nonlinear two-packet encoding; simply
walking between least affine representatives cannot be the glider.

### 2026-07-22 01:01 EDT

The mixed-radix linker and its central failure test are now kernel-checked.
Commit `1711620` shows that a collision factorization plus the single
subtraction-free balance

```text
2^(j+3(q'+1))c' + 3^j = 3^(j+2q+2)c + 2^j
```

reconstructs the renewal factorization.  Commit `54e506f` packages the
research worker's affine gate and link families: two base identities and two
stride identities prove coefficient linkage, exact two-gate execution, and
strict outwardness for every common tail.  Commit `5254194` then applies the
ordinary/2-adic kill test at precisely this layer.  If one natural tail lies
in nested link-address cylinders of unbounded binary precision, their
canonical residues must eventually equal that natural literally; if the
addresses keep changing, the apparent program is only a coherent 2-adic
phantom.  This sharpens the returning-dispatcher target: it must use the
binary-read/ternary-write instructions to generate an aperiodic execution,
yet its constraints on the one initial ordinary tape must eventually stop
requesting new low bits.  Next: look for a counter architecture where later
instructions are generated by evolved payload state rather than by an
ever-growing exogenous address.  A primary-source PL check also prevents a
new overclaim: Cocke--Minsky prove universality for deletion-two tag systems
by implementing a state plus two binary stacks, but De Mol's particular
three-rule Collatz tag system is not thereby universal.  Our complete
five-trit writer likewise lacks a certified remote-rear append.  The more
honest spatial compiler target is now the two-stack move
`(M,N)->(2M+b,floor(N/2))`, with the collision boundary shuttling between
separated packets.

### 2026-07-22 00:55 EDT

The regenerative splash is now kernel-checked and has exposed a native
mixed-radix programming instruction.  Lean commit `eac55d3` proves the full
`q`-cell delay in one theorem, reconstructs the collision opcode from the
factorization, proves exact landing in the new gap, and proves every such
nonempty run strictly outward.  At the affine-tail level, any gate links to
any next positive-opcode gate with the same boundary gap.  If the first output
and second input cylinders are

```text
c_out=o+2*3^A t,       c_in=r+2^(m+1)s,
```

their odd bases make the link congruence automatically soluble, and its whole
family is

```text
t=t_0+2^m v  ->  s=s_0+3^A v,       0<=s_0<3^A.
```

This literally deletes a low binary address and appends an `A`-trit word to
the surviving nonlocal tail.  The rebuilt [delay
artifact](experiments/kontorovich/breakoff_delay_gate_audit.json) checks all
4,608 linked shapes with delays at most four and opcodes at most eight, two
tails each (18,432 gate-macro replays), in addition to the earlier 8,704 gate
replays.  More strikingly, the fixed dispatcher `(q,j,q')=(1,1,1)` has
`A=5`; exact enumeration of next gates `j<=34,q'<=44` finds a certified
address for every one of the 243 possible five-trit output words.  This is the
nonlocal binary-read/ternary-write PL primitive Simon anticipated.  It still
does not solve the ordinary-integer boundary: arbitrary finite words compile,
while an infinite nested tape may be merely 2-adic.  Next: build a returning
dispatcher/counter architecture from these writers and demand an aperiodic
all-level coefficient formula.

### 2026-07-22 00:38 EDT

Simon's image of bits “eating” a dirty collision and regenerating its gap is
not just metaphor: the minimal break-off map contains an exact three-bit
delay/collision instruction.  A clean state `9*2^(3q)c-1` executes `q`
opcode-zero steps, each replacing `(q,c)` by `(q-1,9c)`, then reaches
`3^(2q+2)c-1`.  For every desired collision opcode `j>=0` and new delay
`q'>=1`, one residue of `c modulo 2^(j+3q'+4)` makes the collision's odd
garbage satisfy

```text
3^(2q+2)c-1 = 2^j u,
3^j u+1 = 2^(3(q'+1))c'.
```

Thus it consumes the old gap and emits the fresh clean state
`9*2^(3q')c'-1`.  The new [exact
artifact](experiments/kontorovich/breakoff_delay_gate_audit.json) constructs
all 1,088 parameter triples `q,q'<=8,j<=16` and literally replays eight
affine tails each through the canonical router (8,704 macro replays).  Its
small regression is `935 -> 1052 -> 2663`: one delay tick, an opcode-2
collision, and one regenerated delay tick; exact continuation still reaches
`1`.  The [headline](#kc-headline-results-with-verification-scope) and
[strategy/failure map](#kc-strategy-and-failure-map) record the scope.  Lean
commit `a1a5fd0` also proves that any infinite break-off witness's rail and
opcode sequences must be genuinely non-eventually-periodic.  Commit `7293975`
implements the actual executable `v_2`/odd-part map in Lean, proves successful
evaluation equivalent to the small factorization equation, and turns any
infinite successful executable orbit into `¬Collatz`.  Next: solve the
coefficient linkage problem across an aperiodic sequence of these gates; the
finite spatial instruction and its final checker are now compiled, but an
ordinary self-renewing tape is not.

### 2026-07-22 00:08 EDT

The “splash the gap” mechanism now has a kernel-checked universal form.  Lean
commit `fedb5ca` proves every odd catcher `(r,0,1,L)` outward for arbitrary
parameters and payload, and separately proves the exact ordinary/2-adic
boundary: unbounded nested dyadic addresses belonging to one natural must
eventually stabilize literally at that natural.  Eliminating the external
router schedule gives a sharper self-programming target.  Consecutive router
payloads must obey

```text
2^(r_(n+1)+3) P_(n+1) = 3^(r_n+2) P_n + 3.
```

The equation forces `3 | P_(n+1)`.  Writing `P_n=3H_(n-1)` after the first
gate gives the deterministic two-register update: form
`A=3^(r_n+2)H_(n-1)+1`; if `v_2(A)>=3`, set
`r_(n+1)=v_2(A)-3` and `H_n=A/2^v_2(A)`.  Every surviving step is an outward
Collatz macro, so an infinite positive odd orbit would be a counterexample.
This is a reduction, not such an orbit.  Lean commit `e9f791b` now
kernel-checks the entire interface: the equation constructs the hidden odd
catcher, agrees with the unique canonical decoder, forces linkage and growth,
and yields `¬Collatz` from an infinite solution.  Commit `c10e5b5` additionally
proves `3|P'` and identifies the next delay and payload as the exact
`padicValNat`/`divMaxPow` decomposition.  The recurrence compresses again
after setting `H_n=P_n/3` and
`y_n=3^(r_n+2)H_n`:

```text
e_n=v_2(y_n+1),
y_(n+1)=3^(e_n-1)*(y_n+1)/2^e_n.
```

Here `9|y_n`, `y_n=7 (mod 8)`, and every defined step strictly increases;
survival asks that the output again be `7 mod 8`.  Its shortcut parity blocks
are `1^(r+1)01`, so zeros are separated by at least two ones.  Next: treat
this one-register radix swap as a mixed-base invariant-set problem and seek a
formula orbit, not a wider ordinary-seed census.  In the still smaller
coordinate `y=8k-1`, the invariant is just `k=8 (mod 9)` and the instruction is
`k=2^j u -> (3^(j+2)u+1)/8`; when integral, it preserves the mod-9 class and
strictly grows automatically.  Lean commit `0b12d44` now packages an infinite
break-off counter, proves these invariance/growth facts, and compiles it to
`¬Collatz`; the same commit proves the interior mod-24 payload skeleton.  The
new [break-off
artifact](experiments/kontorovich/router_breakoff_audit.json) makes each opcode
an exact affine binary-read/ternary-write branch and replays 4,160 bounded
members through the canonical Collatz decoder.  The next task is to find a
formula invariant for this map, not merely another long finite survivor.

### 2026-07-21 23:50 EDT

The compiler dead end was spatial, and Simon's extra splash repairs it.  With
one ordinary gate between the 11 two-outward saturated nodes, exact affine
intersection gives 22 four-gate relays, but their only cycle is a fixed
periodic self-loop and therefore impossible for an ordinary infinite orbit.
The missing degree of freedom is supplied by the universal odd router
`(r,0,1,L)`: its word `[1]^r[2,1]` is outward because
`3^(r+2)>2^(r+3)`, while `L` chooses any next gap.  The new [router
artifact](experiments/kontorovich/complete_u_router_audit.json) checks all 121
ordered pairs and proves the two-relay compiler graph complete, with every
five-gate family universally outward.  The least transition grows
`71675 -> 120953 -> 136073 -> 153083 -> 258329 -> 290621` and then reaches
`1`.  Lean commits `64bf677`/`88e2577` independently certify the first odd
saturated bridge and expose the unique complete decoder as a deterministic
macro ISA; `b023700` supplies the canonical partial dynamics and a direct
conditional endpoint to `¬Collatz`.  Lean commit `fedb5ca` now proves both the
router's universal outwardness and the exact boundary behind the caveat: at
unbounded dyadic precision, the canonical residues of any fixed natural must
eventually become that natural.  Next: exploit the now-complete finite router
to search for a self-describing public payload recurrence; finite instruction
routing is solved, while ordinary-integer realization of an aperiodic infinite
program is the live obstruction.

### 2026-07-21 23:32 EDT

The complete splash language materially enlarges the rational-base compiler
graph, but has not yet made it renew.  An exact [shape-graph
artifact](experiments/kontorovich/complete_u_bridge_graph_audit.json) checks
25,600 parity-complete sources and all 2,751,680 coefficient-compatible
targets in the stated box.  It finds 18 universal saturated bridges—14 using
the odd catcher—and 11 have outward linked target subfamilies; the complete
718-candidate audit from those target shapes finds no second compiler edge.  The positive side is
Simon's “splash the splash” literally realized: restricting the `U^12` tail
to `t=16u` gives three universally outward gates and the least chain
`2199021754367 -> 2229023590399 -> 5083728186203 -> 8578791314219`.
That seed still reaches `1`.  Lean commits `afb86a5`/`f7ac880` certify the
odd instruction, its complete affine cylinders, and cross-branch
prefix-freeness; `78d1048` proves total existence of a certified halt/even/odd
outcome for every positive odd payload, and `92f237c` proves it unique.  Next:
search strategically beyond the closed first-edge box
and, more promisingly, allow a bounded ordinary catcher cascade between
saturated compiler edges while forcing the overall decoded schedule to remain
aperiodic.

### 2026-07-21 23:22 EDT

Simon’s “splash the gap” metaphor exposed a real missing instruction.  The
old grammar rejected odd intermediate gaps, but their terminal collision is
exactly `1+2*3^sQ -> 2+3^(s+1)Q=-1+2^LP'`; allowing `L=1` also turns a
one-bit output into a legal zero-delay rail.  The resulting
[parity-complete ISA](experiments/kontorovich/complete_splash_isa.py) has
exact Kraft mass `1/3+2/3=1` and uniquely decodes every positive odd payload
unless the macro reaches `1`.  The new exact `U^12` bridge has two universally
outward gates, and its formerly rejected third payload is now caught.  The
failure has moved rather than vanished: that catcher shrinks, and the full
120-digit witness parses into 290 gates before reaching `1`.  The
[headline](#kc-headline-results-with-verification-scope) and [strategy/failure
map](#kc-strategy-and-failure-map) record the exact scope.  Next: treat the
total decoder as the actual programming language and search symbolically for
an invariant aperiodic tape with positive long-run drift, especially a
saturated cylinder whose catcher cascade is also net outward.  In parallel,
Lean commit `dbe0e5a` now reduces a disproof through this compiler to exactly
such an outward renewing variable bridge chain, and `afb86a5` kernel-checks
the new odd catcher; the total decoder and chain existence remain open in
Lean and mathematics, respectively.

### 2026-07-21 23:04 EDT

The rational-base lane has crossed from analogy to compilation.  A universally
outward splash gate maps its nonlocal family index by
`95+128t -> 1640+2187t`, and exact algebra identifies this with seven steps of
Eliahou--Verger-Gaugry's divergent saturated-word map `U` for every `t>=0`.
Equivalently, one Collatz gate executes the base-`3/2` append block
`[1,1,1,1,1,2,1]` on an unbounded tape family.  The saturated orbit itself
enters at `U^41(0)=26906975`, producing the literal Collatz step-block
`440843894591 -> 470764451891`.  The result is also sharply scoped: the target
gate shrinks, its endpoint does not renew, and the ordinary seed reaches `1`.
The [certificate](experiments/kontorovich/two_rail_u_bridge.json) also audits
67,500 bounded shape links, finding three exact `U` blocks and only this one
outward source.  Next: search compositions whose choice of `U` block is read
from the changing payload, so the compiler follows the aperiodic saturated
word instead of stopping after one instruction.

### 2026-07-21 22:56 EDT

The payload-dependent controller now has an exact instruction grammar.  For a
fixed rail length, every splash shape is one LSB-first binary prefix; four
successive valuations uniquely decode `(a,s,b,L)`, so the prefixes are
disjoint.  Their exact Kraft mass among odd 2-adic payloads is `1/6`.  After
that sparse binary address is consumed, the affine handoff writes globally by
multiplying the residual tape by a power of three.  This is a concrete
binary-read/ternary-write tag machine, not just a PL analogy.  The new
[artifact](experiments/kontorovich/two_rail_prefix_code_audit.json) checks
1,344 codewords and 902,496 pairs for each `r=1..16` through 20 bits, plus
21,504 independent literal decodes; the [headline](#kc-headline-results-with-verification-scope)
states the universal derivation separately from those bounds.  Lean commit
`96f2357` meanwhile proves every fixed proposed word-period must be broken
infinitely often.  Next: represent the unique decoder as a payload-driven
transition system and search for a formula tape whose binary prefixes keep
selecting gates while the ternary writes force every fixed period to break.

### 2026-07-21 22:47 EDT

Two exact corrections sharpen the search.  First, a self-link or one fixed
finite affine return cannot be the bouncer: it repeats a nonempty valuation
word, and coefficient matching would require an integer slope
`3^N/2^S` with `S>0`.  The regenerative splash must rewrite its instruction
tape so the future gate sequence is genuinely aperiodic—precisely the
branching tag-machine interpretation, not a simple oscillator.  Second, the
full 1989 Väänänen--Wallisser theorem closes the rigid standard schedule.
Our partial theta is exactly `f_(3/2)(4096/6561)`; their `p=2` size hypothesis
follows without floating point from `2^8>3^5` and `5*4^2<9^2`, so the value is
2-adically irrational and cannot be the required integer payload.  Lean commit
`806bf8c` independently formalizes the recurrence, finite unrolling, `Q_2`
limit, and candidate obstruction; `3fc63a6` kernel-checks the all-coefficient
function mapping, size inequality, and citation endpoint; commits
`b741a14`--`560fcc5` independently
rule out fixed affine, eventually periodic, and autonomous finite-state
controllers.  The new [exact application
audit](experiments/kontorovich/standard_two_rail_irrationality_audit.json),
[headline](#kc-headline-results-with-verification-scope), and [failure
map](#kc-failure-ledger) record the scope.  Next: build the branching
payload-index transducer and hunt an invariant aperiodic tape orbit; apply the
same special-function sieve to any low-description schedule it proposes.

### 2026-07-21 22:31 EDT

The splash now has exact programming semantics.  A two-rail collision reads a
dyadic address from a nonlocal payload index, deletes those low bits, maps the
remaining tail by a power of three, and appends an offset.  Lean commits
`4789a80`/`1076954` certify affine instructions and their composition for all
natural tails; `2f2e24e` proves that an outward affine return
`u -> c+m*u`—expanding is allowed—would literally disprove Collatz.  A bounded
canonical-member audit checked 128,000 gate shapes, found only 25 links and a
two-gate maximum; its witness `45247 -> 48319 -> 103199` reaches `1`.  This is
a scoped zero-preload failure, not evidence against affine loops.  Separately,
the rigid standard schedule reduces to one 2-adic Tschakaloff value; its exact
247-round truncation reaches 33,333 bits of precision, but no applicable
irrationality theorem has yet been verified.  The [headline](#kc-headline-results-with-verification-scope),
[failure map](#kc-failure-ledger), and [special-function
note](docs/notes/standard-two-rail-theta.md) record the scope.  Next: search
coefficientwise for affine self/return circuits, audit the p-adic theorem, and
try to compile the base-`3/2` “append `2`” instruction or a Stérin--Woods
diagonal defect into the exact gate ISA.

### 2026-07-21 22:02 EDT

The “gap splash” has become an exact two-rail circuit rather than only a
metaphor.  A `-1`/valuation-one rail pumps a remote payload, a collision emits
a `+1`/valuation-two cleanup rail, and a second collision regenerates the
`-1` rail one bit farther out.  The first standard gate is
`94751 -> 101183`.  More strikingly, symbolic intersection of the complete
affine gate families—not an interval search—constructs a 10,040-digit seed
executing 247 strict outward rounds and growing its gap from 5 to 252 bits.
Every one of its 32,110 designed accelerated steps replays exactly.  It is
also a clean failure: the depth-248 canonical seed is different, and full
exact continuation reaches `1` after 155,190 accelerated steps.  The new
[certificate](experiments/kontorovich/two_rail_chain_247.json), [verifier](experiments/kontorovich/two_rail_gate.py),
[headline](#kc-headline-results-with-verification-scope), and [failure
entry](#kc-failure-ledger) record both facts.  Lean commit `6229e7a` meanwhile
kernel-checks the generic `+1` delay line and Colussi order-10 wire.  Next:
replace finite affine-family intersection by a recursive payload relation and
attack its ordinary-integer stabilization directly.

### 2026-07-21 21:47 EDT

Simon proposed “splashing the gap”: line up other packets so collision carries
eat the dirty bits and regenerate a sparse wire.  The metaphor survives exact
algebra.  For any incoming and outgoing `+1` delay lengths and collision
extra, [`splash_gate.py`](experiments/kontorovich/splash_gate.py) constructs a
whole arithmetic progression of payloads realizing the requested splash; its
15,360-case literal regression passes.  The same derivation gives a clean
failure: every pure `+1` splash strictly decreases the integer.  The strategy
map now promotes a two-rail machine—an amplifying `-1`/`k=1` Mersenne rail plus
a timing/cleanup `+1`/`k=2` Colussi rail, joined by phase-changing splash
gates.  Lean commit `f1cb0e2` meanwhile proved the unbounded dyadic--triadic
packet gate and unique payload theorem requested at 21:28.  Next: synthesize
an exact two-rail phase switch whose `k=1` pump pays for the cleanup loss and
emits a larger pair of gaps.

### 2026-07-21 21:40 EDT

Restored the spatial half of Kontorovich's picture inside the nonlocal ISA.
Colussi's formula-generated order-10 seed—11,846 decimal digits—has an exact
ten-instruction decoder to `1+2^39348`.  That is a literal separated packet
crossing a 39,348-bit delay line for 19,673 valuation-two ticks before a
precisely timed collision.  The new [certificate and
verifier](experiments/kontorovich/README.md#formula-generated-colussi-delay-line)
reconstruct the seed, replay all steps, and then continue it to `1` after
95,146 accelerated steps.  A 1,024-step collision audit finds no renewed gap
wider than 10 bits, so the unmodified wire is now a scoped failure; a defect
must rewrite the collision.  In parallel, Lean commit `b205e40` completed the
scale-free `Q_2` candidate construction for every Mersenne schedule, leaving
only candidate nonintegrality for a useful controller class.  Next: treat a
Collatz program as spatial delay-line segments wired together by nonlocal
dyadic--triadic gates, and search for a defect which makes the first collision
emit a longer wire.

### 2026-07-21 21:28 EDT

At Simon's direction, pivoted from widening packet ranges to reverse-
engineering a possibly nonlocal programming language.  The new
[instruction-set map](docs/notes/kontorovich-delocalized-isa.md) audits the
mixed-base rewrite, three-symbol tag, Colussi repetend, and Busy Beaver
bouncer presentations; it explicitly credits Simon's PL and whole-digit-span
hypotheses.  The first exact decoder is a dyadic--triadic packet gate: a fixed
low address transforms an arbitrary high payload affinely and schedules the
next packet modulo `3^m`.  Its dependency-free checker passes 8,192 direct
family cases and an exhaustive small converse audit.  No new GPU range sweep
was launched; the drafted level-array launch was discarded.  PSC job
`42499002` then timed out at two hours with only 7 of 64 length-eight
nonuniform-morphism shards complete, so it proves nothing and will not be
relaunched in the same form.  The 24 Ganesha length-seven workers remain
healthy in the background.  In parallel, Lean commit `7370489` proved
uniqueness of the ordinary realization of a fixed symbolic stream and the
exact finite backward series for Mersenne controllers, opening a non-search
2-adic nonintegrality sieve.  Next: mine formula defects on Colussi's order-`h`
background in the mixed-base rewrite system and test whether a precise p-adic
gap/automaticity theorem can eliminate periodic controllers wholesale.

### 2026-07-21 21:05 EDT

PSC H100 job `42500602` completed the independent `h<2^36` packet census in
eight seconds.  Its exact counters and all 243 stored hit triples agree with
the RTX 4090 artifact, and arbitrary-precision Python replay passes.  The
separate artifacts and hashes are in the [experiment
guide](experiments/kontorovich/README.md#direct-gpu-packet-census).  This
corroborates the inner run without extending the `h<2^42` frontier.  The
Ganesha length-seven nonuniform-morphism workers remain healthy; the PSC
length-eight search is producing partial shards but is approaching its first
walltime.  Next: preserve or cleanly relaunch that finite census as needed,
and scan packet starts above level one rather than spend more compute only on
larger level-one packets.

### 2026-07-21 20:51 EDT

Completed nested direct state-dependent packet censuses on Akdeniz's RTX
4090.  The wider run covers all `274,877,906,944` odd packets below `2^39`,
with eight renewal attempts each and zero 64-bit overflows.  Independent
Python big-integer replay verifies all 14 seven-renewal hits; none reaches
eight.  A final nested scan covers all `2,199,023,255,552` odd packets below
`2^42`, again with zero overflows and no eight-renewal hit.  The inner
`h<2^36` run retains all 243 six-or-more hits for motif
mining.  The best finite tail has four consecutive outward macros but then
fails and reaches `1`.  Exact bounds and hashes are in the [experiment
guide](experiments/kontorovich/README.md#direct-gpu-packet-census).  PSC H100
job `42500602` remains queued as a hardware-independent rerun, while the two
nonuniform-morphism jobs continue.  Next: mine the 14 length-seven packet
chains against Lean's modulo-`3^m` scheduler for a compact state-dependent
feedback invariant.

### 2026-07-21 20:08 EDT

Added the previously omitted signed fixed controller `-1`, which encodes long
Mersenne-like runs of valuation one.  Its exact `376,800`-path sweep found
three finite all-outward seed-stabilization events.  The best seed,
`24,017,279`, grows at all three controller macros through `1,579,334,395`,
then misses the next precision class and reaches `1` after 108 accelerated
steps.  This is the closest bounded glider motif so far, but it is explicitly
not a counterexample.  Lean commits `843387b`--`d6fb8b2` now remove all finite-
prefix, growth, sign, and rotated-phase proof burdens from a future witness:
the sole missing object is an infinite exact bounded-extra renewal stream.
Lean commit `768f4d0` separately kernel-checks the `-1` controller, its exact
macro identity, the outward finite regression, and the specialized implication
from an infinite Mersenne renewal to Collatz failure.
Next: search arithmetic feedback rules for the `-1` collision extras rather
than enumerate another fixed-depth rectangle; PSC/Ganesha morphic jobs remain
active.

The first feedback test is complete: every constant extra `1..32` was checked
through depth 40 and start level 20 (`51,200` paths).  Constant `e=1` gives
seed `121` two unchanged-prefix extensions, then fails at level five and
reaches `1`; no other constant rule matches it.  Next moves to short periodic
and state-dependent extra rules.

The periodic sweep then checked `2,726,400` exact prefixes from every primitive
period-at-most-three template over extras `1..8`, through start level 30 and
depth 80.  It finds no improvement: constant `1` remains the unique two-
extension event, and `(4,3,1)` remains the best outward event.  Lean commits
`32a0896`--`a2652f2` reduce the next search to a pure packet recurrence and
provide a modulo-`3^m` scheduler; state-dependent arithmetic feedback is now
the active Mersenne lane.

The direct Akdeniz packet census described below has now completed and passed
independent replay.  PSC H100 job `42500602` remains queued as an independent
rerun of the same range.

### 2026-07-21 19:54 EDT

Allowed carry collisions to change phase around the same negative cycle.  This
unlocked 15 exact `-5/-7` precision renewals and 10 one-extension ordinary-seed
stabilizations, including seed `53,403,857`; every event is finite, shrinking,
and fails on the next collision.  The complete bounded phase grammar checked
`1,950,864` positive paths; all seven phases of the `-17` controller were
negative.  Counts, bounds, and replayable events are in the [KC headline
table](#kc-headline-results-with-verification-scope) and [experiment
guide](experiments/kontorovich/README.md#phase-changing-shadow-collisions).
PSC/Ganesha morphic shards continue in parallel.  Next: extract a collision
grammar that renews at start level at least seven, where bounded-extra shadow
macros can become outward, rather than widening the now-failing low-level box.
Lean commits `3d9cedc` through `0d8c3d2` simultaneously checked the signed
controllers, all rotated phases, macro endpoint, eventual-growth inequality,
and the implication from an infinite phase renewal to literal Collatz
failure.  The research gap is therefore the renewal sequence itself, not a
missing bridge from such a sequence to the conjecture.

### 2026-07-21 19:34 EDT

Recovered posts 14--17 of Kontorovich's thread and restored their concrete
separated-bit/carry-timing proposal to the [live strategy
map](#kc-strategy-and-failure-map).  Lean commit `63c3b3d` now kernel-checks
the full finite compiler specification; `121cb13` proves the packet clock, and
`ad36f08` proves canonical-seed stabilization equivalent to the ordinary-
integer gate.  Ganesha passed the exact worker self-test
and is running 24 shards over nonuniform morphisms of image length at most
seven.  PSC job `42499002` passed the same test and is running 64 shards over
the complete length-at-most-eight class.  Next: verify and merge both complete
shard sets, then use their best ordinary-seed stabilization motifs to seed the
packet-collision search.

The first packet-collision sublane is also complete: a positive state can
shadow a supercritical negative cycle while a high packet grows, but the carry
must replenish one more level of 2-adic precision.  Exact search of `112,320`
bounded `-5`/`-17` controller programs found no such renewal and no ordinary-
seed stabilization; the scoped failure is now in the [KC failure
ledger](#kc-failure-ledger).  The next version will vary the collision grammar
and controller phase rather than enlarging this same rectangular box.

### 2026-07-21 19:15 EDT

Pivoted the project to the Kontorovich challenge and pushed the first exact
checkpoint.  The finite-word compiler, Python replay verifier, kernel Lean
cycle-disproof seam, parametric-glider endpoint, and all-level periodic-word
obstruction all pass.  Bounded
composition and uniform-morphism searches found no nontrivial cycle; the
small uniform morphism ansatz is now in the [KC failure
ledger](#kc-failure-ledger), with scopes in [KC headline
results](#kc-headline-results-with-verification-scope).  PSC, Akdeniz, and
Ganesha are reachable; next is a distributed search over non-uniform morphic
and one-counter-adjacent templates, while Lean checks the periodic-word
obstruction.

## The Kontorovich Challenge

The active goal is now to **try to disprove the Collatz conjecture**.  A
disproof means an exact positive-integer certificate: either a nontrivial
cycle, or a seed whose forward orbit is infinite and never reaches `1`.
Large excursions, floating-point evidence, and long prescribed prefixes are
search clues, not counterexamples.

The challenge comes from [Alex Kontorovich's 2019
thread](https://x.com/AlexKontorovich/status/1172715174786228224) and the
[Kontorovich--Sinai structure
theorem](https://arxiv.org/abs/math/0601622).  For the accelerated odd map

```text
T(x) = (3x+1)/2^k,   k = v_2(3x+1),
```

the structure theorem says, in particular, that every prescribed finite
`k`-word `(k_1,...,k_N)` occurs: for either admissible class modulo `6`, the
seeds realizing that prefix form one arithmetic progression modulo
`6*2^(k_1+...+k_N)`.  On each such progression the endpoint is another affine
arithmetic progression, with scale changed from `2^(sum k_i)` to `3^N`.
Consequently the finite path statistics are exactly those of independent
geometric `k_i`, and normalized logarithmic trajectories converge in density
to Brownian motion with drift `log(3)-2 log(2)=log(3/4)<0`.  This explains why
typical seeds descend; it does not control a sufficiently sparse exceptional
orbit.

Kontorovich's proposed reversal is to regard the map as fixed **hardware** and
the initial integer as **software**.  Verification through `b` bits has tested
all programs only through that input length.  The structure theorem lets us
compile any finite instruction word into an arithmetic progression of seeds,
so the disproof search should not sample typical seeds: it should synthesize a
highly structured instruction stream, a Collatz “glider”, whose binary pattern
reproduces while its scale grows.

Simon Dedeo suggested two refinements which now govern the KC strategy.  First,
mine ultra-simple programming languages—Brainfuck, tag systems, and FRACTRAN—
for macro, loop, counter, and nonhalting-certificate ideas, without assuming
that `3x+1` is universal.  These languages are sources of mechanisms, not the
preferred state space: the YAH packet compiler is now known to impose a very
sparse address code, and the canonical raw first-passage outward system below
is the lower-power construction target.  Second, and more importantly, do **not** assume that
a Collatz instruction is spatially local.  Its natural unit may be a
congruence, a carry phase between remote packets, or a mixed-base relation
spread across the whole digit span.  The active instruction set therefore
includes formula configurations and dyadic--triadic bridge gates, not only
contiguous repeated bit blocks.  See the [delocalized-ISA
map](docs/notes/kontorovich-delocalized-isa.md).

Nonlocality does not replace Kontorovich's spatial picture.  Long zero gaps
remain literal delay lines and separated packets remain signals; the new
working architecture is **spatial wires joined by delocalized collision
gates**.  Simon further suggested a “gap splash”: align sacrificial packets so
their collision carries eat a dirty suffix and emit a new empty gap.  Exact
splash gates below show that the mechanism is real, while also exposing the
need for an amplifying rail.  The first exact large wire is now in the
headline table below.

The scale reinforces this choice.  Barina's current published verification
covers every seed below `2^71`, already about 21 decimal digits.  A putative
10,000-digit program is not a larger interval-search target: it must be emitted
by a short generator and proved nonhalting by a finite symbolic certificate.

The thread also proposes a more concrete glider mechanism.  After a suitable
prefix, its example becomes three widely separated `1`-bits.  Until a carry
arrives from the right, an isolated high packet is acted on by multiplication
by `3`, while the rightmost packet feels the `+1`.  For `m>=3`, the order of
`3` modulo `2^m` is `2^(m-2)`, so distant packets can in principle be placed
and timed to collide with a low-bit trajectory selected by the structure
theorem.  The challenge is to make those collisions replenish a packet farther
left forever—not merely arrange any finite sequence of spectacular-looking
collisions.

There is a crucial exact caveat.  Nested progressions for an arbitrary infinite
`k`-word determine a 2-adic integer, not necessarily a positive ordinary
integer.  Equivalently, if `S_j=k_1+...+k_j`, then

```text
T^N(x) = (3^N*x + A_N)/2^S_N,
A_N = sum_(j=0)^(N-1) 3^(N-1-j) 2^S_j.
```

Every proposed glider must therefore pass three gates simultaneously: exact
valuation legality, an ordinary positive seed rather than only a 2-adic one,
and certified nontermination.  Finite-prefix realizability alone passes only
the first gate.  Lean commit `ad36f08` makes the middle gate exact: for a fixed
mod-6 class, an infinite positive valuation stream belongs to an ordinary
integer `x` if and only if its canonical finite-prefix seeds are eventually
identically `x`.

### KC Strategy and failure map

#### Live disproof programs

- **Thin invariant program languages.**  The two-Kraft obstruction rules out
  a prefix-complete valuation decoder whose every leaf is outward.  Search
  instead for a proper public language `L` containing one explicit ordinary
  state and a finite successor rule `f` with
  `next(x)=f(x) in L` and `start(f(x))>start(x)`.  This is a program-verification
  loop invariant: it constructs the infinite orbit by forward iteration and
  cannot hide an externally preloaded 2-adic tape.  Uniformly outward traps
  must become exponentially thin in dyadic address measure, so algebraic
  self-writing predicates, pushdown stacks, and multi-rail rotations are more
  plausible than finite-width complete routers.
- **Internal-template and morphic closure.**  In the YAH mixed-base rewrite
  language, fixed outer boundaries cannot host a proper whole-word context
  splash when their marker/flank invariants are preserved.  Treat those
  boundaries as a stationary tape frame and make an *interior* active block
  reproduce, translate, or change scale.  A finite certificate has the form
  `u ->+ L sigma(u) R` plus nonempty simulations of every rewritten rule under
  `sigma`; commit `1b3459d` kernel-checks that this finite data constructs an
  infinite chunked derivation.  Commit `bfe12f0` now proves that identity is
  the only productive nonerasing delimiter-fixing independent digit-word
  morphism, with no common-width assumption.  The live PL architectures must
  therefore change delimiter charts or use contextual/multi-block opcodes
  whose global invariant is nonlocal.
- **Carry-defect two-block machine.**  Digit complement is an exact symmetry
  of the six auxiliary YAH rules.  At the terminal boundary its minimal
  defect is one unit, and a saturated `tri2` buffer turns that unit into the
  exact counter increment `bin1 tri2^n . -> tri2^(n+1) .`.  The left boundary
  compiles this into the outward transfer
  `/ tri0^k tri2^n . -> / tri1^(k-1) tri2^(n+1) .`.  Treat the two run lengths
  and the left phase as public registers.  The live opcode is a contextual
  recharge from the `tri1` phase back to a nonexhausted `tri0` block, selected
  by the incremented right counter.  A passive adapter is impossible because
  its affine defect is positive; success must coordinate both blocks across
  the entire word.
- **Queue-macro checksum machine.**  One complete left-boundary opcode is an
  exact two-state quotient transducer over the entire remaining ternary tape.
  The space law is `delta length = odd terminal carries - 1`; only head
  `1`/`2` with global value `3 mod 4` reproduces a cell.  The enable bit is the
  alternating checksum of the whole digit span, while successive carry
  opcodes turn a contiguous reservoir into alternating combs and period-four
  packets.  Perpetual `+1` macros are kernel-impossible.  Use the exact battery
  `B=2*length+v2(N+1)`: growth converts two valuation units into one cell, so
  a viable grammar must use a neutral/shrinking collision to raise `B` before
  spending it again.  The phase-one packet now gives an explicit amplifier:
  a unique `q mod 2^(K+2)` writes `K` dyadic charge units, `K=4G+1`
  guarantees `G` later cells, and its free lift is a 2-adic isometric register.
  Its safe endpoint ends in an exact run of `J+2` twos.  Search for a finite
  grammar that makes the surviving prefix register and this emitted reservoir
  write their own next recharge address.  At `K=5` the first such decoder is
  exact: it reads one lift-register bit, with zero extending the reservoir and
  one changing chart.  On `t=91+256u`, the bit-one chart now recharges, writes
  `R'=(3^6R+1)/2^8`, returns to head zero with seven reservoir trits, and gains
  one cell.  Its output is a new chart provably disjoint from the original
  register family.  The live edge is to close a finite graph of such chart
  transitions rather than generate an infinite tower of one-use types.
  Fixed-time returns on a
  simple ternary exponential family are multiplicatively impossible, so the
  type cycle must carry an unbounded clock or mixed dyadic--triadic scale.
- **Delocalized instruction synthesis.**  Represent an instruction as an
  arithmetic relation across the entire state: a dyadic address, triadic
  phase, carry boundary, and affine high payload.  Search for formula
  configurations `C(n)` with a bounded exact return rule
  `C(n) ->+ C(f(n))`, where the rule lifts to every `n` by induction.  This is
  the Collatz analogue of a Busy Beaver bouncer and directly implements
  Simon's nonlocality proposal.
- **Handoff lattices and address rotation.**  Compile opcode chains through
  their exact dynamic interface
  `sigma+3^Q u=rho'+2^P v`, not through a parallel conjugacy alone.  Every
  finite handoff is another dyadic-cylinder/ternary-ray transducer, so the
  chain has made progress only if its surviving payload writes the next
  cylinder rather than selecting it by a new CRT choice.  A one-register
  total affine gauge spends 2-adic slope at every step and cannot persist;
  the live PL-shaped architecture is a nonlinear decoder or a public
  multi-rail stack rotation which restores that address budget.
- **Colussi repetend-defect bouncers.**  Use the exact periodic grammar of the
  halting classes as a structured background, then search for a finite or
  congruential defect which reproduces from order `h` to order `h+1`.  The
  order-10 background has 39,366 padded bits and an 11,846-decimal-digit
  integer value, so this route reaches the proposed program scale by formula,
  not enumeration.  Its unmodified background has now been decoded into an
  exact 19,673-tick spatial delay line; because the ensuing collision does not
  renew the gap, the live variable is a distributed defect in the header or
  packet phase.
- **Mixed-base and tag-system bouncers.**  Mine the exact Yolcu--Aaronson--Heule
  binary/ternary rewrite system and De Mol's three-symbol deletion-2 tag
  system for formula-tape or run-length returns.  These presentations make
  whole-word carry, moving-base-boundary, and head--tail nonlocality explicit.
  The regenerative delay linker now supplies a native Collatz instruction of
  exactly this kind: on an affine tail it reads a low binary address and maps
  the residual `v` by `v -> s_0+3^A v`, appending `A` ternary digits.  One
  fixed dispatcher has a bounded exact realization of all 243 five-trit
  output words.  Lean commits `54e506f`/`5254194` prove the affine link
  semantics and its ordinary-tail acceptance test.  The next PL task is to
  arrange a returning dispatcher or counter loop whose changing instruction
  stream is genuinely aperiodic while its nested binary addresses eventually
  stabilize to one natural tail.  Cocke--Minsky's universality proof supplies
  a precise kill test: a real tag compiler must pop the front of one binary
  stack and push onto the remote end of another.  A complete local write
  alphabet is not enough.  The spatial target is therefore two separated
  packet registers implementing those push/pop moves at a regenerating
  collision boundary.  The strongest immediate ordinary-address specialization
  has now been exhausted through delay/opcode/output-delay 100: among
  1,010,000 canonical-family base shapes, only three normalized tail-zero
  links exist and none has a second link.  The live controller must therefore
  transform a nonzero evolved payload or use a genuinely nonlinear packet
  encoding; a chain of canonical least representatives is not enough.
  One such nonzero mechanism is now exact: the five-trit word
  `b=3^5-2^L` maps a residual packet `K*2^L-1` to
  `2^L(3^5*K-1)`.  Hence remote low bits of `K` can amplify an inherited
  length-`L` bit boundary by any prescribed finite extra valuation `D`.
  The live turnaround problem is to expose this nested amplified gap as the
  next active delay and make its surviving packet reproduce the construction.
  A returning finite glider now exists.  The ether gate `(1,2,1)` has fixed
  2-adic tail `-12/473`; the unique parity-compatible immediate defect
  `(1,1,1)` writes any prescribed finite number `n` of eight-bit cells and
  returns the exposed boundary to its own defect family.  The complete macro
  is `K=R_n+2^(8n+15)q -> K'=S_n+3^(6n+11)q`.  The next target is one ordinary
  payload whose changing `q` generates an infinite aperiodic sequence of
  lengths, not another externally prescribed list of finite ethers.
  In the affine register `Y=83790531K-874281`, the whole ISA is the autonomous
  partial map `Y=2^(8n-5)h -> (3^(6n+11)h+51)/2^20`.  This small map, not the
  original huge defect constants, is now the primary synthesis target.  A
  second spatial scale is also exact.  Repeating the one-cell glider as a
  23-bit super-ether fails if its gap is completely exhausted, but Simon's
  proposed collision overhang has a canonical realization: retain exactly
  three low bits.  The two-cell glider then acts as a returning defect and
  the primitive super-register obeys
  `V=2^(23N+3)g -> (3^(17N+40)g-17)/2^51`.  Thus one capped splash changes the
  first-scale `+17` law into the same law with sign `-17`.  The next target is
  to iterate this renormalization symbolically and pass the ordinary-integer
  gate, not merely construct deeper finite address cylinders.  Exact
  renormalization now reaches six levels with alternating signs and cell
  widths `8,23,77,254,839,2771`.  The canonical tail-zero tower already
  illustrates the danger: at depth six it compiles a linked 6,708-digit
  finite program, but its first-scale packet has changed at every depth.
  Search now targets a finite self-describing address or an ordinary-tail
  theorem for a different recursive branch, not a seventh certificate made
  by extending the same changing tower.  The meta-language is not unary:
  choosing any background branch `j` and the adjacent defect `j+1` gives the
  same exact sign flip after retaining the background valuation.  This has
  been checked for `j=1..64` at level one and along three nonconstant
  four-step choice words.  A universal positive-tail identity now closes the
  whole infinite-nesting interpretation, not just that bounded tree.  If
  `E` is the combined parent input exponent, `r` the inherited valuation,
  `q_raw>0` the least raw input, and `K>=1` a child packet, then its parent
  tail is

  ```text
  q=q_raw+2^E*(2^r*K-1)>0.
  ```

  Thus every recursive extension lies strictly above the canonical parent
  base; its nested ordinary addresses can never eventually stabilize.  The
  hierarchy is a finite compiler, not one infinitely nested ordinary program.
  This does **not** exclude an autonomous orbit at any fixed finite hierarchy
  level.  There is also an invariant one-in-seventeen packet slice:
  when the primitive register is divisible by `17`, division gives the unit
  law `H=2^(an+b)h -> (3^(cn+d)h+s)/2^e`.  All collision debris has then been
  reduced to `s=+1` or `-1`; this unit machine is now the smallest autonomous
  search interface.  Scaling by `2^e` exposes its exact instruction:
  `W=2^p h -> W'=3^q h+s`.  Relative to the signed radix router, every level
  then trims the positive ternary factor `3^(p-1-q)`.  The new two-rail target
  is to bank that factor in a separated packet and feed it back, rather than
  losing it or adding another hierarchy level.  Every constant-rate clock is
  already closed: `n_t=n_0+kt`, for arbitrary fixed `k>=1`, makes the unique
  2-adic core a partial-theta value which is irrational by the cited
  Väänänen--Wallisser theorem at all six levels.  Any bank must branch
  nonlinearly on its packet contents.  In Simon's spatial language, the live
  architecture is a two-rail regenerator: a payload rail survives the
  collision while a delocalized sacrificial rail absorbs the dirty carry
  suffix and recreates the next clean gap.  The distance to that next gap
  must itself be packet-selected, not a fixed-rate delay.  This mechanism is
  now exact in the unit ISA.  For any three successive branch lengths and any
  desired `D>=1`, one correction block emits the complete next instruction;
  a second `D`-bit word cancels its carry and leaves `D` literal zero bits
  before an affinely surviving high packet.  The remaining quine problem is
  sharp: that high packet must generate its own future correction words.  An
  externally preloaded infinite stack would again be only a 2-adic program.
  Simon's proposed catcher can be made regenerative in one exact sense.  If
  the isolated carry is `B`, put `r=v3(B)`,
  `D=ord_(3^(q-r))(2)`, and use the formula-compressed word
  `z=B(2^D-1)/3^q`.  Then `B+3^qz=2^D B`: the collision swallows `B`, opens a
  `D`-bit gap, and recreates the *same* carry beyond it.  The canonical
  one-cell header embeds this carry translator in the true invariant register
  at all six compiled levels; the respective `D` values have
  `8,28,90,297,979,3231` decimal digits.  This is a literal finite glider cell
  in Kontorovich's spatial sense.  It still needs a self-writing ordinary end
  cap; preloading infinitely many catcher blocks would only hide a 2-adic
  tape.
  A much more compressed special case now uses the rational repetend
  `R=(2^T C-s)/3^q`.  Choosing `T` simultaneously in a discrete-log class
  modulo `2*3^(q-1)` and in the affine unit exponent class makes
  `R+2^(T+D)K -> C+2^D*3^qK`.  This gives formula-generated, enormously
  nonlinear gap splashes at all six levels; the live question is still
  renewal of the emitted marker rather than production of one spectacular
  jump.  At the sign-negative second level that marker now renews once
  exactly.  The stable quotients
  `c_m=(2^(3^(m-1))+1)/3^m` let the first ternary bank be absorbed into a
  second repetend, producing two consecutive formula-sized nonlinear jumps.
  The remaining target is a third/self-writing renewal from one fixed
  ordinary packet, not an externally nested tower.  But the pure staircase
  is now closed even before the ordinary-address gate: every sign-negative
  full-order splash more than halves its odd core.  The live hardware design
  must therefore alternate an amplifying **charge phase** with a sparse giant
  **discharge splash**.  The charge phase must rebuild both real core energy
  and the next nonlocal correction word from the surviving packet.
  The first exact charge--discharge compiler is now autonomous.  At the
  sign-negative level-two unit register, execute a length-`N` instruction and
  then the one-cell instruction.  The fixed collision debris factors as
  `3^57+2^77=5D`, where
  `D=314038802961906688057474567` is coprime to the register stride.  On the
  unique packet class divisible by `D`, quotienting gives the new ISA

  ```text
  G=2^(23N+3)g -> (3^(17N+97)g-5)/2^128.
  ```

  Every complete branch of this machine is strictly outward, and each is
  literally two legal unit macros.  Thus any infinite successful positive
  orbit of this much smaller `-5` machine would already refute Collatz.  No
  such orbit is known.  This is distinct from the earlier bounded search near
  the signed cycle `-5 -> -7 -> -5`: the same small debris appears in a new
  positive quotient register with different exponents.  The live task is to
  make its packet select infinitely many legal lengths.  Its own one-cell
  discharge now provably regenerates the same `-5` interface at every finite
  recursive depth: at depth `j` the offsets are
  `d_j=114*2^j-17`, `e_j=154*2^j-26`, and the removed divisor is
  `3^(114*2^j)+2^(154*2^j)`.  An exact multiplicative-order argument reduces
  coprimality at all depths to 79 gcd checks against the 80-bit register
  stride; all pass.  This is a true self-similar splash compiler, but not an
  infinite natural: every positive child packet lifts to
  `rho_j+D_j*K>K`, so nesting forever changes its ancestor address.  Search
  must use an autonomous orbit at one fixed finite level, not confuse the
  infinite hierarchy with a seed.
  A fixed-form change of coordinate now exposes exactly such a level-two
  bouncer.  Put `A=3^114`, `B=2^154`,
  `F=(A-B)/5`, and `Z=F*G-2^26`.  The one-cell instruction is the pure delay
  wire `B*Z'=A*Z`.  At defect boundaries write `Z=2^26*y`.  The normalized
  odd coordinate `y` then reads its own two opcodes

  ```text
  m=v2(y+1)/23,
  E=3^(17m)*(y+1)-2^(23m),
  h=(v2(E)-23m)/154,
  y'=3^(114h)*oddpart(E).
  ```

  When `m,h>=1` are integral and `y'` has another defect phase, this executes
  one length-`m+1` defect followed by `h-1` recharge cells.  The fixed register
  is simply `y=0 (mod M)`, `y=-1 (mod F)`.  Research-side finite hierarchy
  expansion shows how accepted members descend to Collatz words; the
  universal descent is still being formalized.  Only after that bridge does
  an infinite accepted positive `y`-orbit become a certified outward Collatz
  counterexample.  Accepted normalized transitions
  are reversible without stored history: `v3(y')=114h`, and after removing
  that power, `v3(1+2^(154h)q)=17m` recovers the predecessor opcode and state.
  The exponent matrix has determinant
  `114*23-154*17=4`, leaving exact resonance identities with only `2^4` or
  `3^4` imbalance.  Morita's reversible two-counter universality result makes
  this a legitimate compiler analogy, while Dudenhefner's certified
  instruction-set-sensitive results supply the kill test: reversibility and
  two valuations are not enough.  We must compile actual increment,
  decrement/zero-test, and finite control operations inside the accepted
  arithmetic classes.  This valuation
  bouncer—not a further nested address—is now the primary synthesis target.
  The first closure ansatz now uses the bouncer's own cell width.  Write the
  odd payload as `u=F*r^23`; if the output has the same form
  `u'=F*r'^23`, then `D=2^23` makes `v2(r')` generate the next defect address
  in whole cells.  This is genuine type reproduction inside the arithmetic
  surrogate, not yet a Collatz counterexample compiler.
  Exact elimination gives

  ```text
  A^h C^m r^23-B^h D^m' r'^23=(A^h-B^h)/F.
  ```

  At the shortest recharge `h=1`, three complete finite-field tests eliminate
  22 of 23 exponent classes.  Lean commit `5fbacf5` proves that every remaining
  transition would solve `3^15 X^23-2^16 Y^23=5`, corresponding to
  `m=5 (mod 23)`.  PARI/GP 2.15.4 returns the complete empty solution list and
  reports attached class number one, which its documentation identifies as an
  unconditional case.  Thus this particular reproduction rail is closed
  (external-PARI scope, not kernel scope).  The first resonant escape is
  `h=23`, where both hardware coefficients are complete 23rd powers and the
  determinant leaves only a `3^4` carry for a corrected or multi-rail payload.
  Lean's four-prime sieve reduces the uncorrected single rail further to
  `m=9 (mod 23)` and one global equation
  `3^15X^23-Y^23=5 Phi_23(A,B)`; its detached Akdeniz solve remains live.
  A more literal closure ansatz encodes the *public* state as `y=s^23`.
  Every type-preserving recharge has `h=23*ell`, and the next state is
  `(A^ell*t)^23`, so the data type really reproduces without a fresh CRT word.
  Lean kills the coefficient class `m=0 (mod 23)` and kernel-checks the
  valuation-preserving cofactor law

  ```text
  w Q(s)=v Q(B^ell*t),       Q(x)=(x^23+1)/(x+1),
  ```

  together with a hidden residual register modulo `F`.  For the other 22
  classes Lean commit `07352a9` now turns each transition into the exact
  approximation bound and, past the explicit threshold `alpha<s`, an
  exponent-11 approximation to one of 22 algebraic numbers.  Roth remains an
  external theorem, and its sequence-level consumer—one residual class,
  reduced distinct rationals, then finiteness—is not yet formalized.  This is a useful
  failure specification: a viable “splash the gap” construction now needs a
  corrected sum of packets, a switching algebraic type, or another multi-rail
  mechanism which changes the approximated target instead of remaining in one
  fixed binomial field.
  The hidden quotient now supplies such a nonlocal control rail.  Exact
  `F`-adic lifting gives
  `B D^m' w'=B C^m w-5ell (mod F)`, so the recharge length can write an
  arbitrary next value of a 179-bit register; the next `F`-adic digit is
  already nonlinear.  This realizes Simon's suggestion that one instruction
  may be distributed across the entire digit span.  The compiler obligation
  is now precise: couple that writable congruence to the exact 2-adic collision
  valuation, positivity, and ordinary output register in one parametric
  family.
  A second escape lowers the algebraic degree rather than adding another
  23rd-power packet.  The two-coordinate type
  `N_d(x,u)=x^2+d*u^2` reproduces automatically because both recharge
  multipliers are squares.  Hardware parity kills `d=1` outright—every legal
  endpoint is `7 (mod 8)`.  A second local sieve shows why the smallest parity
  correction `d=7` is also a poor instruction type: the register primes 5 and
  19 are inert, forcing `95|m` at every typed step.  The first squarefree
  `d=7 (mod 8)` with no inert register prime is `d=31`, and the exact identity
  `C-D=7706^2+31*1407^2` cancels the public register to the normalized payload
  recurrence

  ```text
  2^(23m+154h)r' = 3^(17m+114g)r + H_m,
  H_m=(C^m-D^m)/(C-D).
  ```

  The exact worker has found and replayed one 184-to-193-digit outward
  transition whose input, quotient, and output all have this type.  It fails
  the very next decoder: the collision valuation `153` cannot contain a
  23-bit defect followed by a positive 154-bit recharge.  Lean commit
  `4112267` independently checks the normalized recurrence, the concrete
  `d=7` tax, the one-step valuation failure, and the debris addition law.
  This has changed the search order.  A two-step quadratic parameterization
  exists and has no cheap local obstruction, but it is only a diagnostic
  unless it supplies a depth-independent public update.  The live target is
  the [closure doctrine](docs/notes/kontorovich-closure-principles.md): first
  construct an integer-decodable invariant graph which regenerates the next
  exact opcode; only then use norm or class-form representations to certify
  its arithmetic type.
  Simon's suggestion to chain opcodes is now implemented at the symbolic
  level.  The recharge-free matrices
  `J_m=[[C^m,H_m],[0,D^m]]` obey `J_nJ_m=J_(m+n)`, so defect-only words retain
  only their total length.  Programming power, if any, must come from exact
  relations among the recharge-decorated matrices together with their dyadic
  boundary cylinders.  Searches for those relations, mixed-radix
  binary-reader/ternary-writer feedback, and public debris recurrences replace
  blind norm-point enumeration.
  The determinant-four resonance now supplies the first surviving relation.
  Shifting opcodes by `(2622k,-391k,2618k)` preserves the full affine gain but
  translates the defect phase by `4k`.  Whenever the two branch constants
  pass one gcd condition, an exact integral affine map conjugates their
  canonical public tails and automatically maps the source cylinder.  The
  first up/down examples have 21,330-digit embedding coefficients.  This is a
  spatial phase-glider cell, not closure: successive embeddings still need to
  telescope.  For fixed `k=1`, however, the up family already gives the
  autonomous public one-counter policy `U(m)=(m,392,m+4)`; it is not an
  externally pasted word.  That policy and every fixed `k>=1` nevertheless
  fail the ordinary-address gate: commit `466e381` identifies the forced
  cofactor with a Väänänen--Wallisser partial-theta value, irrational in
  `Q_2` under their inspected 1989 theorem.  The relation remains a useful
  cell, but closure now requires variable jump or direction generated by
  public payload, with its debris series telescoping to an integer.  See the
  [resonant phase-glider
  note](docs/notes/kontorovich-resonant-phase-glider.md).
  The resulting primary interface removes auxiliary coordinates entirely.
  Every legal state is uniquely

  ```text
  y=D^m(w_m+S*t)-1,       S=2FM,
  ```

  and every branch `(m,h,m')` is exactly

  ```text
  2^(154h+23m')t'=3^(114h+17m)t+kappa,
  t=rho+2^P u -> t'=sigma+3^Q u.
  ```

  The fixed-register base `w_m`, opcode `m`, and tail `t` are canonical
  functions of the normalized public integer.  Odd endpoint cofactors turn
  the equation back into the exact normalized collision valuation and output,
  so this arithmetic language has no hidden representation metadata.  Its
  cofactor artifact checks all 27 branches with `m,h,m'<=3`; no invariant tail
  language is supplied.  Lean commit `5a9324b` proves uniqueness of the
  public coordinates and both directions between this recurrence and the
  arithmetic `ChargeBouncerStep` surrogate—not yet `WordLegal`.  The new
  semantic-compiler artifact separately descends 54 bounded members through
  14,057 literal accelerated instructions and independently replays them.
  A universal linked-composition theorem remains open.  The same commit
  closes single-letter and
  fixed-boundary two-letter product collisions, so the constructive target is
  a conjugacy or self-synchronizing invariant language for this transducer,
  not equality of short matrices.
  The ordinary-address gate now has a more useful cohomological form.  For a
  chain in canonical cofactors,

  ```text
  2^P_i w_(i+1)=3^Q_i w_i+s_i,
  s_i=2^(154h_i)-3^(114h_i),
  ```

  backward unrolling forces one convergent `Q_2` series for `w_0`.  The local
  debris is already the exact two-chart difference

  ```text
  -s_i/3^Q_i = 3^(-17m_i)
                -(2^P_i/3^Q_i)*2^(-23m_(i+1)).
  ```

  The principled constructive target is therefore a public coboundary: align
  the ternary entry potential with the next binary exit potential so the
  infinite address series telescopes to a positive integer.  Fixed-rate
  policies instead lead to partial-theta irrationality; variable payload
  jumps are justified only when they alter this rationality problem.
  Lean commit `772a6e8` now gives every public cell the same cohomological
  interface type:

  ```text
  w_i-3^(-17m_i)
    =a_i*(w_(i+1)-2^(-23m_(i+1))).
  ```

  Composing a multi-cell word inserts the internal taxes
  `3^(-17m)-2^(-23m)<0`; equivalently these are normalized copies of the
  positive defect polynomial `H_m`.  Consequently phase-up and phase-down do
  not form a bare typed pair, and a period-four word is not a sensible search
  target merely because the present multi-theta theorem first loses its size
  bound there.  The required second opcode is an actual chart adapter whose
  public payload or affine intercept supplies the opposite correction.
  The resonant geometry imposes another resource law: source-chart separation
  `2622k` exits as `2618k`, so a chain of the same cells would require
  `1311*k_(i+1)=1309*k_i` and unbounded `1311`-divisibility in its first jump.
  The same commit proves the finite divisibility law and infinite no-go.  It
  turns Simon's regeneration picture into a precise search specification:
  find a public phase booster which replenishes both the chart type and the
  lost separation.
  The two-opcode phase-swap family is the first exact exponent-level response.  Its words
  `W_r=[(r,h0,L-r),(L-r,h1,r+d)]` cross their charts with signed boundary
  differences `(d,-d,d)`, making their total `P,Q` independent of `r`.  The
  bounded arithmetic artifact constructs two adjacent parallel conjugacies in
  the `L=4,d=h0=h1=1` line and replays all sixteen bouncer steps.  Exact
  constant/slope inequalities prove that neither conjugacy hands the current
  output to the next source.  A node-dependent typed gauge must solve that
  first; only then does the turnaround `L->L'` become relevant.
  The first low-description clocks do not solve it: an exact audit of
  Thue--Morse, period-doubling, and Fibonacci words, all 240 injective
  two-symbol codings by `(m,h)` in `{1,...,4}^2`, and every prefix through 48
  transitions finds no canonical-address stabilization.  Search should now
  target an arithmetic payload-generated counter law, not merely paste a
  familiar aperiodic word over two fixed opcodes.
  The ordinary-ray seam is sharper than that finite test: Lean commits
  `af1a934`/`ba121d9` prove that a realizing natural would force the canonical
  extension lift `rho_k` to vanish eventually.  Thus it is enough to prove
  `rho_k!=0` infinitely often; universal positivity is unnecessary.  An exact
  bounded audit finds no zero lift among 1,118,464 extensions of all words of
  depth at most four over the 16 opcodes `(m,h)` with `1<=m,h<=4`.  This is
  evidence about the compiler seam, not an all-depth theorem.
  A survivor must start at a canonical positive integer and contain infinitely
  many genuine Collatz steps; a loop on a malformed representation is rejected.
- **Rational-base and spatial-grid gliders.**  In the Stérin--Woods exact
  quasi-cellular automaton, Collatz iterates are binary rows while ternary
  columns perform base conversion; search for a diagonal defect or boundary
  signal with a formula return.  In Eliahou--Verger-Gaugry's base-`3/2`
  picture, try to compile the divergent saturated-map instruction “append
  `2`” from bounded exact Collatz/two-rail macros.  Seven- and twelve-append
  blocks now compile exactly on unbounded index families; in the latter both
  linked gates are universally outward.  Restricting its nonlocal tail modulo
  `16` makes the next odd catcher outward too, giving an unbounded three-gate
  growing family.  A complete bounded source-shape graph finds 18 saturated
  bridges, 11 with outward linked targets, but all 11 target shapes have no
  second compiler edge.  One ordinary relay leaves only a forbidden periodic
  self-loop, but a second relay changes the picture: the universal outward
  catcher `(r,0,1,L)` chooses any next spatial gap, making the 11-node compiler
  graph complete.  The live task is therefore no longer finite spatial
  routing; it is an ordinary payload recurrence realizing an aperiodic
  infinite path.
  Lean commits
  `401d494`/`6ab99fc` prove the universal saturated-cylinder law and package a
  reusable affine-bridge certificate; `64bf677` kernel-checks the first
  odd-to-odd bridge, and `dbe0e5a` proves that any supplied
  outward renewing variable bridge chain refutes Collatz.  Commit `fedb5ca`
  proves every router shape outward uniformly and proves that dyadic-cylinder
  addresses of any ordinary natural must eventually equal that natural
  literally.  No infinite chain is known, and neither presentation transfers
  divergence by itself.
- **Two-rail splash bouncers.**  Implement Simon's collision idea with a
  `-1`/valuation-one Mersenne rail, which amplifies a separated packet by
  `3/2` per tick, and a `+1`/valuation-two Colussi rail, which supplies timing
  and carry cleanup.  Exact `+1` splash gates can emit an arbitrarily longer
  empty gap but always decrease the integer.  The phase switch now exists:
  `94751 -> 101183` is the smallest standard regression, and symbolic affine-
  family intersection compiles 247 consecutive outward rounds into a
  10,040-digit seed.  That seed nevertheless reaches `1`, and its canonical
  value changes when a 248th constraint is imposed.  Each affine handoff is
  now an exact tag instruction: it consumes a low binary address block from a
  nonlocal payload index and maps the surviving tail affinely by a power of
  three.  A fixed affine return is now ruled out: it would repeat one valuation
  word forever, and its putative natural tail slope would be `3^N/2^S` with
  `S>0`.  Lean commits `b741a14`/`26f3584`/`560fcc5` strengthen this to every
  eventually periodic word schedule and every autonomous finite-state
  controller.  The live splash target is a tag controller whose changing
  unbounded tail selects a genuinely aperiodic gate sequence, or an unbounded
  shape counter—not a fixed route through gate shapes.  Exact valuation
  decoding makes the gate shapes an LSB-first prefix code of Kraft mass `1/6`
  among odd 2-adic payloads: a valid tape is necessarily sparse, but its
  unbounded arithmetic contents can supply the required nonautonomous state.
  Simon's “splash the gap” suggestion also repairs the apparent missing
  collision mechanism in a more ambitious form.  Treat a long zero gap as a
  delay line and place several nonlocal bit islands across the full digit span:
  the first island triggers the main collision, later islands arrive as timed
  carry catchers which absorb its debris, and a surviving island writes the
  spacing and residues of the next catcher bank.  This is a three-phase
  **strike--scrub--reseed splash code**, not a single local rewrite.  Because a
  fixed finite valuation word is affine, any proposed code can be synthesized
  by simultaneous dyadic congruences and then checked exactly.  The hard
  obligation is regeneration: the post-collision catcher vector must lie in
  the same parameterized family with a larger delay, while retaining an
  ordinary positive tail.  This explicitly combines Simon's programming-
  language/nonlocality idea with Kontorovich's spatial delay-line picture.
  The finite strike--scrub--reseed path is now complete at level two.  Take
  carry `B=1`, turnaround marker `H=17`, and
  `D=ord_(3^57)(2)=2*3^56`.  An explicit base-two discrete logarithm modulo
  `3^114` selects one even class of following lengths; the class making
  `3^(17l+40)*17=1+2^(D+2) (mod 2^(D+3))` is also even, so CRT supplies a
  finite ordinary `l`.  Three collisions then return the surviving tail as
  `R+2*M*3^(q(l)+114)w`.  The coefficient after the factor two is odd, so it
  can write any prescribed finite odd binary catcher/header word.  This
  solves finite turnaround and reseeding without expanding the roughly
  `10^27`-bit gap.  The live problem is now exactly the global one: make the
  successive words payload-generated so the nested tail is one ordinary
  natural, rather than an externally prescribed 2-adic stack.
  **Retraction (08:23 EDT).**  The proposed three-collision synthesized-marker
  turnaround and its rank-one bank were not legal linked unit paths.  The unit
  transition `n -> m` uses `q(n)` from its source and `p(m)` from its target.
  After the claimed second transition reached state `1`, the third calculation
  incorrectly used `q(g)` as though the source were `g`.  Its raw divisions
  and coefficient algebra were exact, but they described incompatible state
  labels.  The two workers and their artifacts have been removed; their Lean
  boundary theorem was only an abstract warning and does not validate the
  bank.

  The corrected return skeleton is the four-transition route

  ```text
  1 -> 1 -> g -> g -> 1.
  ```

  Put `P=23g+54`, `Q=17g+40`, `R=114+2Q`, and `S=154+2P`.  Exact composition
  gives

  ```text
  3^R h-C_g=2^S h',
  C_g=3^(2Q+57)+2^77*3^(2Q)+2^(77+P)*3^Q+2^(77+2P).
  ```

  For every fixed `g` this again gives an outward affine return family, but
  that fact is deliberately not the target.  Promotion now requires a single
  finite description `F,f` satisfying the **reproduction equation**

  ```text
  3^R(g) F(g)-C_g=2^S(g) F(f(g))
  ```

  with all four valuations exact and every `F(g)` positive odd.  Fresh CRT
  choices at successive generations are preloaded software, not closure.  For
  the simplest `f(g)=g+1`, writing
  `z_g=2^(23g+54)/3^(17g+40)` turns this into a first-order mixed-base Mahler
  equation.  The exact worker proves that no finite Laurent-polynomial
  `F(g)=f(z_g)` can solve it; a pole-propagation argument appears to exclude
  rational `f` as well and has been sent for independent formalization.  The
  live constructive target is therefore a genuinely self-generating
  nonlinear/automatic payload, especially the base-squaring update `g -> 2g`,
  not another finite catcher bank.
  instructions: an odd intermediate gap has a parity-dual terminal collision,
  and a one-bit outgoing gap is a legal zero-delay rail.  The even cleanup and
  odd catcher families have exact Kraft masses `1/3` and `2/3`, so every
  positive odd payload uniquely decodes unless that macro explicitly reaches
  `1`.  Hardware jamming is therefore gone; the target is an ordinary decoded
  tape with aperiodic positive long-run drift.  Lean commits `afb86a5` and
  `f7ac880` certify the new odd catcher, its affine cylinders, and
  cross-branch prefix disjointness, including `r=0,L=1`; `78d1048` proves in
  Lean that every positive odd payload has an exact halt, even-cleanup, or
  odd-catcher outcome, and `92f237c` proves that outcome unique.  The
  parity-complete hardware semantics are now kernel-closed.  Commit `88e2577`
  exposes the unique decoder as a deterministic macro transition and reduces
  a disproof to linked public payloads whose decoded macros are all outward;
  `b023700` packages the actual canonical partial state map and proves that any
  infinite surviving outward orbit of it refutes Collatz.  Commit `e9f791b`
  removes the last hidden gate data for the universal-router submachine: an
  infinite positive-odd solution of
  `2^(r_(n+1)+3)P_(n+1)=3^(r_n+2)P_n+3` alone refutes Collatz.  Simon's
  spatial “splash the gap” picture is now literal in the minimal break-off
  coordinate: `9*2^(3q)c-1` executes `q` three-bit delay ticks, collides with
  chosen opcode `j`, and can emit a fresh state `9*2^(3q')c'-1`.  For every
  `q,q'>=1,j>=0` one residue class of `c` gives this exact finite
  delay-to-delay gate.  The live target is to link such gates through one
  ordinary coefficient with a genuinely aperiodic, unbounded collision
  schedule; Lean commit `a1a5fd0` proves eventual periodicity of the opcodes
  impossible for any infinite break-off orbit.
- **Exact cycle synthesis.**  Search valuation words and cyclic compositions
  for which `2^S_N-3^N` divides `A_N`; the quotient is then a candidate cycle
  seed whose valuations and closure can be checked directly.  Use modular
  meet-in-the-middle, lattice, and branch-and-bound searches aimed at long,
  low-description words rather than another undirected small-seed sweep.
- **Minimal raw first-passage controller (preferred low-power lane).**  Let
  `F` contain each shortcut parity word whose slope `3^O/2^S` first exceeds
  one at its last bit.  It is the maximal outward prefix-free code; its first
  four words are `{1,011,001111,010111}`.  Exact stopped-mass conservation
  gives ordinary Kraft mass `P` in the rational interval recorded by
  [`outward_first_passage_audit.json`](experiments/kontorovich/outward_first_passage_audit.json)
  and tilted mass exactly one.  For the least compatible initial residues,
  `h_n=min_(u in F^n)r(u)` is nondecreasing, and boundedness is equivalent to
  an ordinary infinite strictly growing shortcut orbit.  Diffuse critical
  flow is insufficient (`mu_q{r_n<=B}<=B(3/4)^n`).  Compress completed
  boundaries as `x=3H-1`: forced `1` blocks drain `v_2(H)`, while every
  nontrivial recharge defines a strictly increasing partial map `R` on odd
  `H` with `v_3(R(H))>=v_2(K)+1`.  An infinite `R`-orbit is exactly the
  counterexample target.  In the inverse direction, propagate the min-plus
  profile of least survivors in classes modulo `3^k`; the scalar `h_n` loses
  this phase.  Seek a coherent path with `rho_n=o(2^n)`, which already forces
  eventual zero carry.  Do not promote critical pressure or longer finite
  survival by itself.
- **Parametric gliders.**  Search for a finite symbolic transducer, substitution,
  or arithmetic family `x_t` with a machine-checkable macrostep
  `T^(ell(t))(x_t)=x_(t+1)` and `x_(t+1)>x_t`.  The existing exhaustive
  small-DFA failures rule out only their tested regular certificate classes;
  the next targets are one-counter, morphic, and recursively nested binary
  templates with unbounded but finitely described memory.
- **Separated-bit packet gliders.**  Treat long zero gaps as delay lines: evolve
  each high packet under multiplication by `3`, use the exact order of `3`
  modulo powers of `2` to schedule its first interaction with the controlled
  low packet, and search for a symbolic collision rule that emits a fresh
  packet at a larger scale.  Certify the whole construction through exact
  macrosteps, including every carry at the collision boundary.  Lean commit
  `121cb13` now supplies the exact order and scheduling theorem; packet renewal
  remains open.
- **Negative-cycle shadow controllers.**  A positive state congruent to a
  negative periodic point modulo a high power of two shadows its supercritical
  valuation block while a high packet grows.  Search one-counter programs in
  which the terminal carry collision raises, rather than consumes, the shadow
  precision.  The negative orbit is only a finite controller; the sought seed
  and every certified macro-state remain positive.
- **2-adic rationality sieve.**  For a fixed infinite extra stream, Lean commit
  `7370489` proves that there is at most one ordinary packet realization and
  unrolls every finite prefix as an exact backward affine series.  Commit
  `b205e40` proves the corresponding series converges in `Q_2` for every
  schedule and that any ordinary renewal must equal its negative 2-adic
  candidate.  For periodic or morphic controllers, the remaining arithmetic
  task is to prove that candidate is not a negative ordinary integer.  This
  can eliminate an infinite program family without enumerating any seeds.
- **Normalized period-three residues and carry hierarchy.**  Commits
  `e385967`/`5a3413a` give adjacent exact upper budgets `U(q)` and `V(q)` whose
  difference grows quadratically.  Every hypothetical ray eventually has
  `core(3q)<2^U`, so its normalized CRT lift is eventually exactly zero.
  Commits `78a6d05`/`43cdba7` identify this with one raw future-residue
  congruence, without constructing a CRT candidate.  Commit `d9398a8` proves
  the cheapest necessary consequence: the canonical `U(q)`-bit residue must
  eventually equal `1 mod 3`.  Commit `a9ed874` extends this to every fixed
  ternary depth and its finite target clock; commits `40f4265`/`2e8010c`
  expose the canonical same-cycle binary extension carry and prove that every
  ray eventually makes it zero.  The dense audit identifies modulus 27 as the
  first discriminating finite phase window, while an exact nine-cycle
  composition reduces its strongest cell to one signed carry modulo 27;
  commits `6b96f89`/`6f05ff5` kernel-check that reduction and both necessary
  depth-four lifts.  The construction-facing refinement now compares
  consecutive cycle residues by an exact signed carry `C_q`.  Commit `daae4a8`
  proves bare residue coherence and kernel-checks that compatible positive
  three-step factors glue to an infinite EC17 orbit; `40835c0` proves the
  strict defect bound and abstract balanced-width equivalence; `5769c85`
  proves that every fixed-depth long block retains only its last carry;
  `122680b` supplies the remaining canonical upper-block bounds; and `f79192e`
  closes the displayed three-step specialization and proves that an eventual
  zero-carry tail constructs an infinite positive EC17 orbit.  Commit
  `4516a03` promotes it to the literal period-three `Ray`, while `fff0dec`
  formalizes the canonical range gate that turns full ternary divisibility
  into equality of the source and target upper blocks; `732da20` specializes
  it to the worker's exact logarithmic precision.  Exact zero carries are both
  the right candidate macro and, eventually, the necessary ordinary-ray
  behavior; the dense 17,253-row `U` audit and 53,392-row balanced-precision
  audit find no such link.  The balanced precision recurrence makes full
  `3^Q` predecessor divisibility equivalent to exact zero, while the rational
  reconstruction audit finds no height-`2^512` exception at 2,048/4,096 bits.
  QM118 blocks generic rationality from a periodic fixed-depth target, and the
  exact block identity shows that long fixed-depth compositions remember only
  their final consecutive carry.  Commits `2cad6e1`/`b518d2b`/`a2e940e` now
  identify a literal ray with `1` plus exactly three paper-normalized 2-adic
  theta values, prove that their linear independence excludes the ray, and
  kernel-check that the available 1989 sufficient threshold fails in the
  strict reverse direction.  Commits `7aad758`/`847027b` prove the full
  geometric root determinant and its exact 11/43 LTE ledger, then show that
  primitive cofactor multiplicities leave only subquadratic savings and that
  the scalar full-support coefficient sequence has irreducible recurrence
  rank three.  The live targets are now an inductive law for
  exact consecutive compatibility, a cofinal theorem forcing or excluding
  zero carries, or a sharper independence theorem exploiting the special
  three theta arguments.  Do not return to raw precision widening; it only
  raises finite lower bounds.
- **Self-writing KL/EC17 two-rail coordinate.**  The rational ether center
  reduces every genuine packet to one nonnegative integer `q` with
  `3^11*Z(q)+17=2^20*W(q)`.  The current branch is `v_3(Z)/6`; the next branch
  is `(v_2(W)+5)/8`; and the fixed 20-bit return gate writes it back as the
  next ternary valuation.  Every accepted step strictly increases `q`, while
  every prescribed finite branch pair remains CRT-solvable.  This is now the
  preferred constructive state space: search for a finitely described
  aperiodic invariant subset of the deterministic `q -> q'` map, or prove its
  exact canonical binary residues cannot eventually stabilize.  Do not
  enumerate `q` by size.  Commit `7ca6d4f` proves that every supplied orbit
  has strict payload growth and a non-eventually-periodic branch schedule.
  A bare EC17 ray additionally needs one packet-color
  condition modulo `473`; color zero then propagates.  See
  [`breakoff_ether_self_writing_kl_audit.json`](experiments/kontorovich/breakoff_ether_self_writing_kl_audit.json).
  The KL pressure reinterpretation gives the exact schedule-code generating
  function `(1-x^8)/(1-x^8-x^23)` and critical dimension
  `0.070659291094...`; use this cost, not flat branch boxes, for any finite
  falsification.  The live invariant component `q=17r` reduces the collision
  constant to `+1` and obeys
  `r'-14=6*(-2)^(m-1)*(r-1) (mod 17)`.  Consecutive cores there cannot both
  contain `17^2`.  Seek a genuinely aperiodic invariant family respecting
  that no-adjacent-deep-core law, or use the checked canonical-carry interfaces
  to prove its dyadic addresses never stabilize.  See
  [`breakoff_ether_branch_pressure_audit.json`](experiments/kontorovich/breakoff_ether_branch_pressure_audit.json).
- **Partial-theta integrality sieves.**  The standard two-rail schedule reduces
  to the sole 2-adic initial value
  `-(23/3^8) F(2/3,2^13/3^9)`.  Väänänen--Wallisser's full-source 1989 theorem
  applies and proves it irrational, closing this schedule.  Repeat the method
  for branching or morphic controllers: reduce a symbolic schedule to its
  `Q_2` special value, then prove nonrationality to reject it or exploit a
  rational exception as a possible ordinary program.
- **Constraint-guided falsification.**  SAT/SMT, modular dynamic programming,
  evolutionary search, CPUs, and GPUs may propose or aggressively reject a
  symbolic macro.  They no longer rank raw seeds by excursion length.  A
  survivor advances only when its low-description recurrence is replayed with
  exact integers and promoted to a universal algebraic certificate.
- **Backward invariant rays.**  Build with inverse steps
  `y -> (2^k*y-1)/3` and search for a sparse, explicitly parameterized set that
  maps into itself while moving outward.  This attacks the ordinary-integer
  gate directly and can reuse the project's side-bush disjointness, rational
  base-`3/2` coordinate, and affine product-of-places diagnostics.
- **KL-calibrated recharge/discharge rays.**  Treat the positive class-8
  chord as an immediately forced discharge of `v_2(m+1)`.  The minimizing KL
  policy has no outward cycle; every non-minimal lift pays `c_alt/c_min`, and
  every outward word obeys `24*n8>17*n2+82*ns`.  Commits
  `408cb2c`/`814fb00` prove that mixed branches move the exceptional negative
  center rather than freely resetting a battery, and that the complete
  dyadic depth is consumed by the next odd burst.  The exact `k=12..19`
  comparison makes the signed cycles through `-1,-5,-17` finite calibration
  templates, with `-1` cheapest at every audited level; it supplies no
  coherent critical tower or cross-level limit.  Commit `e15c6f0` proves only
  the safe product-level conclusion that an outward cycle forces some fiber
  defect.  Search
  only autonomous controller-switch blocks that beat the KL tax and close for
  one natural payload.  Commit `35200ca` proves the QM131 primitive-core
  invariant on arbitrary moving-center segments; `616ace8` proves QM132's
  exact exponential dyadic shadow-address cost and universal finite shadow
  depth, while `2fcddea` proves every finite parity cylinder has a negative
  representative.  Commit `2700d1e` proves QM133's coarse connector bound for
  fixed/bounded centers; `aab22e7` proves its count-sensitive strengthening
  and QM134's exact affine reset recurrence coupling one outgoing payload to
  the next address.  Commits `8c20163`/`54eb749` prove unique finite ternary
  targeting and mixed CRT solvability, while `961c692` proves that the same
  terminal congruence is equivalent to every local controller-legality test.
  Commits `2acceaa`/`d8d8337` supply the dual dyadic reset accumulator, prove
  that its terminal cylinder reconstructs every intermediate quotient, make
  every finite reset word positive after a cylinder shift, and prove uniqueness
  of an ordinary initial payload whenever cumulative written binary precision
  is unbounded.  Commits `2963a8d`/`ca8dc5c` prove that an ordinary
  nonnegative chain forces exact eventual stabilization and expose each
  bounded high-bit carry, so cofinally nonzero carries are now a kernel-checked
  no-chain certificate.  Commit `18b8c93` proves the converse and makes an
  exact zero-carry tail equivalent to existence of a nonnegative ordinary
  integer reset chain.  Commit `73601f7` strengthens this to an exact height
  dichotomy: bounded canonical residues, eventual constancy, eventual zero
  carry, and ordinary realization are equivalent.  Commit `302ce3b` adds an abstract covering-dispatcher
  consumer, explicitly without a signed-Syracuse bridge; semantically useful
  search must target a proper invariant thin language, not a total outward
  code already excluded by Two-Kraft.  The first exact proper-language audit
  finds `{1,011,001111,010111}` with mass `21/32`; commit `1aa3e52` closes
  every periodic or ultimately periodic path in that language.  The direct
  attempt to transfer KL tax to the period-three EC17 core odometer is also
  closed: almost every boundary pair is not a KL edge, and the core defect 34
  is smaller than the universal KL word bound `3^17-2^17`.  A valid KL audit
  must instead expand the actual packet-level Collatz path.  The new literal
  bridge does so for ether lengths `1..6` at KL level 12: all exact edge and
  path-product inequalities pass, with class-8-heavy chord paths and no
  transports.  The tail-chart theorem now relates those actual fibers to
  EC17 exactly: every linked successor has rail `r=2`, fixed-depth tails
  synchronize from the target branch, and unbounded branches approach the
  KL ether center `-881/473`.  At level 12 the mature tax is an exact repeated
  six-edge cycle factor, not a Haar average.  Across the stored `k=12..19`
  certificates its exact tax/weight ratio decreases from `1.21752` to
  `1.05157`, finite evidence of near-critical alignment but not a limit
  theorem.  What remains is the original
  hard seam—one positive infinite EC17 chain whose dyadic addresses cohere.
  The missing construction must self-write a genuinely aperiodic sequence of
  increasingly precise reset cylinders whose inverse limit is one positive
  ordinary payload and whose real KL cocycle stays outward.
  This is a search principle and finite calibration, not a counterexample. See
  [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md).
- **Exceptional-orbit obstructions in reverse.**  Re-read the proof program's
  exact capacity and carry constraints as a specification of what a
  counterexample must look like, then search on the thin boundary where those
  constraints are nearly sharp.  Negative-drift or density-one evidence is
  treated as a distributional filter, never as evidence against rare
  software.

#### KC failure ledger

| Ansatz or route | Calibrated verdict | Exact record |
|---|---|---|
| Treating critical first-passage/KL mass as an ordinary survivor | Invalid.  For the canonical maximal outward first-passage code, the slope-tilted Kraft mass is exactly one at every block depth, but its natural product flow satisfies `mu_q{r_n<=B}<=B(3/4)^n`.  Conditioning fair renewal on arbitrarily long survival gives the product block law `p(w)/P`, which is also diffuse, with fixed-window bound `B(1/(2P))^n`.  Thus conserved mass and the classical survival Doob transform both escape every bounded ordinary residue window.  Any successful selector must create an atom; a useful sufficient proof input is the weaker growth condition `rho_n=o(2^n)`, which forces eventual zero carry. | [`outward_first_passage_audit.json`](experiments/kontorovich/outward_first_passage_audit.json), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md#23-odd-charge-compression-and-triadic-min-plus-renewal) |
| Prefix-complete uniformly outward valuation ISA | Closed for finite positive prefix-free codes.  With `p(w)=2^-sum(w)` and `q(w)=3^length(w)/4^sum(w)`, every outward leaf has `q(w)>p(w)`; `p`-completeness and the `q`-Kraft bound are inconsistent.  Commit `da9fa59` constructs explicit binary and four-letter compilers, derives both Kraft inequalities from prefix-freeness, and proves the full finite contradiction and quantitative mass bound in Lean.  The countably infinite prefix-free theorem still uses an abstract `tsum` interface.  This does not touch a proper zero-measure trapping sublanguage containing one ordinary self-written orbit. | [Closure doctrine](docs/notes/kontorovich-closure-principles.md#53-two-kraft-measures-forbid-a-complete-all-outward-isa) |
| Periodic or ultimately periodic path in the four-word signed thin language | Closed.  The exact bounded controller audit extracts the proper code `{1,011,001111,010111}` with ordinary mass `21/32`, tilted mass `1905/2048`, and 41,328 literal growing reset checks.  Commit `1aa3e52` proves that any nonempty periodic concatenation of outward shortcut blocks gives an expanding coprime affine recurrence and cannot persist on positive naturals; an arbitrary finite prefix does not help.  Genuinely aperiodic paths with eventually zero address carry remain open. | [`kl_signed_thin_residue.json`](experiments/kontorovich/kl_signed_thin_residue.json), [`ShortcutParityPeriodicNoGo.lean`](KontoroC/KontoroC/ShortcutParityPeriodicNoGo.lean) |
| EC17 normalized core boundary as a KL full-lift path | Closed as a semantic identification.  The boundary clock is a genuine ternary odometer and is cofinal on `Y_d` when `3` does not divide the period-three gain.  Nevertheless each phase has only one class-2 and one class-8 KL chord over a full orbit; almost all pairs are nonedges.  More decisively, a KL word with `r` chords has defect at least `3^r-2^r`, while one normalized EC17 core step has `r>=17` and defect 34.  No KL/Haar tax may be attached directly to the core clock.  This does not close the actual packet compiler, whose ordinary endpoints must be expanded and sampled separately. | [`breakoff_ether_period3_kl_bridge_audit.json`](experiments/kontorovich/breakoff_ether_period3_kl_bridge_audit.json), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Free/Haar packet-tail model for one linked EC17 ray | Closed.  Free packet tails have an exact geometric `v_3(Z)` histogram, but EC17 linkage forces every successor to `v_3(Z')=2`, fixes `q' mod 3^d` from the target branch whenever `d<=6n+1`, and places the literal boundary at exact 3-adic distance `6n` from `-881/473`.  The post-initial edge counts are `(R2,R8,S)=(2n+4,4n+7,0)`, and fixed-level KL tax is the deterministic rational ether-cycle factor, not a Haar average.  This sharply narrows but does not construct or exclude a positive infinite EC17 chain. | [`breakoff_ether_glider_kl_tail_chart_audit.json`](experiments/kontorovich/breakoff_ether_glider_kl_tail_chart_audit.json), [`kl_rational_ether_cycle.json`](experiments/kontorovich/kl_rational_ether_cycle.json) |
| Using linked `r=2`, the factor `473`, or a finite shallow-rail prefix as an all-depth carry obstruction | Closed.  The packet color evolves bijectively as `chi' = 316*chi (mod 473)`.  On every positive bare EC17 step the balance equation already forces the missing `2^20` affine-rail factor, so color zero is equivalent to full packet promotion; it is a construction premise, not an obstruction.  The eight mod-17 shallow rails have writable higher branch digits.  Every finite reset cylinder remains CRT-compatible with color zero and any one shallow odd checksum, and can be shifted to make all finite quotients positive.  Only eventual stabilization of the least dyadic representatives can decide an ordinary infinite seed; do not widen finite rail-prefix scans. | [`breakoff_ether_self_writing_kl_audit.json`](experiments/kontorovich/breakoff_ether_self_writing_kl_audit.json), [`breakoff_ether_branch_pressure_audit.json`](experiments/kontorovich/breakoff_ether_branch_pressure_audit.json) |
| Treating small branch pressure/dimension as an ordinary-seed exclusion | Invalid.  The exact target code has lengths `23,31,39,...`, Kraft mass `1/(255*2^15)`, and pressure dimension `0.070659291094...`.  This proves the infinite 2-adic survivor language is very thin and supplies the correct cost measure for searches.  A countable set of ordinary naturals can still intersect a positive-dimensional thin set, so dimension alone cannot exclude or construct the required eventually-zero address. | [`breakoff_ether_branch_pressure_audit.json`](experiments/kontorovich/breakoff_ether_branch_pressure_audit.json), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Proper whole-word YAH context splash with canonical endpoints | Universally closed.  Commit `9ca4360` proves over the pinned 11 rules that if a nonempty derivation starts and ends at canonical `/digits.` words and claims `endpoint=left++start++right`, then both contexts are empty.  The earlier generic/flank theorem and the worker's 825,708 bounded rule checks remain diagnostics for noncanonical charts.  This is not YAH termination; internal/morphic templates remain live. | [`yah_context_loop_audit.json`](experiments/kontorovich/yah_context_loop_audit.json), [`YahRewriteSystem.lean`](KontoroC/KontoroC/YahRewriteSystem.lean) |
| Delimiter-fixing independent YAH digit morphism | Closed completely in the stated productive/nonerasing class.  The exact worker finds identity as the unique width-one simulation and none among all 9,765,625 width-two maps; commit `2d50381` excludes every uniform width `w>=3`.  Commit `bfe12f0` removes the common-width premise: over the pinned 11 rules, any marker-fixed morphism with nonempty digit-only images and nonempty simulations of all rules is literally identity.  Delimiter-changing and context-dependent/coordinated multi-block maps are not excluded. | [`yah_context_loop_audit.json`](experiments/kontorovich/yah_context_loop_audit.json), [`YahVariableMorphismRigidity.lean`](KontoroC/KontoroC/YahVariableMorphismRigidity.lean) |
| Perpetual one-cell YAH macro reproduction | Universally closed for ordinary natural seeds.  Commit `64bccb8` proves that every `+1` queue macro has `4*(N_next+1)=9*(N+1)`; an infinite all-growing macro orbit would force every power of four to divide one fixed positive `N+1`.  Commit `db13d82` gives the finite form: an `r`-macro growth burst forces `4^r | N+1`.  This does not close intermittent growth: a survivor must include neutral/shrinking collision phases which recharge enough dyadic battery to fund later cells. | [`YahPerpetualGrowthNoGo.lean`](KontoroC/KontoroC/YahPerpetualGrowthNoGo.lean), [closure doctrine](docs/notes/kontorovich-closure-principles.md#56-macro-space-conservation-exposes-the-nonlocal-instruction-bit) |
| One-macro backwrite from a right reservoir | Universally closed for the quotient/queue macro interface.  Commit `d801643` proves exact prefix/suffix factorization: an arbitrary suffix cannot alter the transformed prefix in one macro, while the prefix reaches the suffix through at most two carry bits.  The decoder's global bit read is compatible with this bound, but autonomous address regeneration must transport information over multiple macros. | [`YahQueueCausalityNoGo.lean`](KontoroC/KontoroC/YahQueueCausalityNoGo.lean) |
| Eventually only zero/bit-pop decoder steps | Universally closed for a positive ordinary register.  Commit `d801643` proves that an eventual tail `2R(n+1)=R(n)` would force arbitrarily high powers of two to divide one fixed positive `R`.  A survivor must revisit restorative chart-changing instructions infinitely often. | [`YahRegisterDrainNoGo.lean`](KontoroC/KontoroC/YahRegisterDrainNoGo.lean) |
| Fixed-clock ternary-run YAH glider | Closed in the stated phase-cycle class.  Commit `99d3405` proves that a fixed shortcut block with positive dynamic length cannot return a family with leading scale `A*3^n` to the same phase while shifting `n` by a fixed `d>0`: coefficient comparison would require `2^L*3^d=3^O`.  A live scale compiler needs counter-dependent time or a mixed dyadic--triadic/nonlinear scale. | [`YahFixedClockNoGo.lean`](KontoroC/KontoroC/YahFixedClockNoGo.lean), [closure doctrine](docs/notes/kontorovich-closure-principles.md#56-macro-space-conservation-exposes-the-nonlocal-instruction-bit) |
| Direct self-link of the first four-phase YAH packet | Universally closed.  Commit `b794b2f` proves `queueMacro(2(0012)^s(01)^q)` is never `2(0012)^s'(01)^q'`: the endpoint starts with `1` when the tail is empty and `0` otherwise, while every target starts with `2`.  The packet remains a routed opcode but requires at least one additional type to restore the head. | [`YahPacketFamilyNoGo.lean`](KontoroC/KontoroC/YahPacketFamilyNoGo.lean), [`yah_queue_macro_audit.json`](experiments/kontorovich/yah_queue_macro_audit.json) |
| Reindexing the restorative output into the original decoder chart | Universally closed.  Commit `f96e621` proves the output register `Rrest(t)=(3^6R(t)+1)/2^8` lies strictly between `R(t)` and `R(t+1)`, hence differs from every original decoder register.  The restorative opcode is a genuinely new chart; closure requires a finite multi-chart cycle, not a relabeling. | [`YahRestorativeChartNoGo.lean`](KontoroC/KontoroC/YahRestorativeChartNoGo.lean) |
| Eventually repeating only the first restorative update | Universally closed for positive ordinary registers.  Commit `0da1058` translates `256R'=729R+1` by `C=473R+1`, obtaining `256C'=729C`; iteration forces `256^n | C(0)` for every `n`.  A recurrent component must contain at least two distinct chart edge maps. | [`YahRestorativeLoopNoGo.lean`](KontoroC/KontoroC/YahRestorativeLoopNoGo.lean) |
| Stabilizing one fixed coordinate through ever-deeper YAH recharge addresses | Universally closed.  Commit `8bed065` proves that if `2^K` divides a positive target at every depth, its address cannot eventually equal one fixed natural.  The three packet recharge targets are exact specializations.  This rejects an ordinary program obtained by stabilizing nested congruence representatives; it does not reject an evolving dispatcher which computes a new unbounded coordinate after every burst. | [`YahRechargeAddressNoGo.lean`](KontoroC/KontoroC/YahRechargeAddressNoGo.lean) |
| Restriction-only restorative lasso tower | Closed for ordinary natural repetition parameters.  Every current edge has `t_n=a_n+2^(k_n)t_(n+1)` with `k_n>0`; commit `9021e86` makes `t_n` and `a_n` eventually zero.  The concrete 19-sweep reblocking candidate also fails: its affine carry map has exact full period `2^19`, so the nominal third block is one whole state cycle and writes no counter bits.  The worker checks the all-depth LCG hypotheses through 24 layers and exhausts cycles through 18; the universal LCG generalization is still awaiting Lean.  A survivor must use a contextual/nonuniform opcode that rewrites a public payload rather than another fixed lasso restriction. | [`yah_chart_clock_audit.json`](experiments/kontorovich/yah_chart_clock_audit.json), [`YahChartTowerNoGo.lean`](KontoroC/KontoroC/YahChartTowerNoGo.lean) |
| Treat a prescribed finite `k`-word as an infinite program | Invalid: the nested progressions generally select a 2-adic integer, not a positive ordinary seed. Lean commit `ad36f08` proves that eventual canonical-seed stabilization is exactly the ordinary-integer gate. | [Program-synthesis note](docs/notes/kontorovich-program-synthesis.md) |
| Literal periodic valuation glider | Closed: Lean commits `92b01ff`/`2f93df7` prove that an infinitely repeatable positive block has `3^N<2^S` and closes as a cycle. This does not touch morphic, counter, stack, or feedback streams. | [Section 4](docs/notes/kontorovich-program-synthesis.md#4-why-a-literal-periodic-glider-fails) |
| Small positive cycle words | Exhaustively negative through total halving count `S<=22`: `3,447,691` positive-denominator compositions, with only repeated encodings of seed `1`. This is a bounded ansatz exclusion, not a new verification frontier. | [`search_results.json`](experiments/kontorovich/search_results.json) |
| Fixed-width binary uniform morphisms | Exhaustively negative for nontrivial cycles at widths `2..4`, codings `1..4`, and expanded length at most `16,384`. The best `1`-avoiding seed-stabilization event dies at its next morphic extension. | [`search_results.json`](experiments/kontorovich/search_results.json) |
| Small negative-cycle shadow programs | Exhaustively negative for ordinary-seed stabilization or terminal precision renewal using controllers `-5` and `-17`, start levels `1..6`, collision extras `1..8`, and extra programs of depth at most four: `112,320` compiled paths in both mod-6 classes. This closes only the stated one-counter pilot. | [`shadow_results.json`](experiments/kontorovich/shadow_results.json) |
| Bounded phase-changing shadow grammar | `1,950,864` positive paths checked exactly. The `-5/-7` phases yield 15 terminal renewals and 10 one-extension seed stabilizations, all starting at level 1 or 2; every renewed path loses alignment on its next collision and none grows. All seven `-17` phases yield zero events within their separately stated bounds. | [Phase-shadow artifacts](experiments/kontorovich/README.md#phase-changing-shadow-collisions) |
| Bounded `-1`/Mersenne shadow grammar | `376,800` positive paths checked exactly for start levels `1..100`, extras `1..12`, and depth at most three. There are 522 terminal renewals, 80 seed stabilizations, and three all-outward stabilization events; none supplies a second stabilized extension. The best finite run reaches `1` on exact continuation. | [`mersenne_shadow_results.json`](experiments/kontorovich/mersenne_shadow_results.json) |
| Constant-extra Mersenne feedback | All `51,200` compiled paths for start levels `1..20`, constant extras `1..32`, depths `1..40`, and both mod-6 classes were checked. The unique two-extension event is seed `121` for extra `1`; its fifth macro fails and exact continuation reaches `1`. | [`mersenne_constant_results.json`](experiments/kontorovich/mersenne_constant_results.json) |
| Short-period Mersenne feedback | All `2,726,400` prefixes from 568 primitive extra templates of period at most three over `{1,...,8}`, start levels `1..30`, depths `1..80`, and both mod-6 classes were checked in compressed exact arithmetic; every hit was literally replayed. No template improves the constant-`1` two-extension event or the `(4,3,1)` outward event. | [`mersenne_periodic_results.json`](experiments/kontorovich/mersenne_periodic_results.json) |
| Direct state-dependent packet census | CUDA exhaustively checked all `2^41=2,199,023,255,552` odd packets `h<2^42` from start level one through an eight-renewal horizon, with zero arithmetic overflows and no length-eight chain. Nested replayed artifacts retain the 14 length-seven hits below `2^39` and 243 length-six-or-more hits below `2^36`; independent RTX 4090 and H100 runs reproduce all 243 inner hit triples exactly. | [`h<2^42` artifact](experiments/kontorovich/mersenne_packet_gpu_akdeniz_h42.json), [H100 replication](experiments/kontorovich/mersenne_packet_gpu_psc.json) |
| Unstructured range widening as the main attack | Deprioritized: published ordinary-seed verification already reaches `2^71`, while the contemplated software may have roughly 10,000 decimal digits. Bounded compute remains useful only as a falsifier or independent checker of a proposed symbolic relation. | [Delocalized-ISA scale calibration](docs/notes/kontorovich-delocalized-isa.md#1-scale-changes-the-object-we-should-search-for) |
| Unmodified order-10 Colussi wire | It is an exact, spectacularly long delay line but not a bouncer. After its certified collision, an exact 1,024-step audit finds no regenerated empty gap wider than 10 bits, versus the incoming 39,348-bit gap; full exact continuation reaches `1` after 95,146 accelerated steps. The next lane must alter the header/collision with a distributed defect. | [`colussi_delay_h10.json`](experiments/kontorovich/colussi_delay_h10.json) |
| Pure `+1` gap-splash bouncer | Closed as an outward macro: the exact gate can turn a gap of `2r+2` bits into any chosen `2r'+2`-bit gap by a congruential payload, but the whole macro has dissipative multiplier `3^(r+1)/2^(2r+2+a)<1` and in fact strictly decreases every positive member. It remains useful as the cleanup rail of a multi-phase program. | [`splash_gate.py`](experiments/kontorovich/splash_gate.py) |
| Even-gap-only splash decoder | Superseded as an obstruction.  Rejecting odd intermediate gaps or `L=1` outgoing gaps created artificial “renewal failures.”  The odd-gap collision `1+2*3^sQ -> 2+3^(s+1)Q=-1+2^LP'` and zero-delay rail make the decoder total away from explicit halting collisions.  This repairs syntax, not growth: the saturated `U^12` witness still reaches `1`. | [`complete_splash_isa.py`](experiments/kontorovich/complete_splash_isa.py) |
| First parity-complete saturated bridge graph | In the exact source box `r<=15,s<=4,a,b<=4,L<=16`, all 25,600 shapes and 2,751,680 coefficient-compatible links were checked.  Eighteen saturated bridges exist and 11 have outward linked target subfamilies.  Exhausting all 718 possible second edges from those target shapes finds zero renewal.  This closes only depth two for those 18 first edges; larger sources and non-saturated catcher cascades remain open. | [`complete_u_bridge_graph_audit.json`](experiments/kontorovich/complete_u_bridge_graph_audit.json) |
| One ordinary relay between compiler blocks | The 11 two-outward saturated nodes admit 22 universally outward four-gate relay families, but their graph has exactly one directed cycle: a fixed node-3 self-loop.  Every infinite path would therefore repeat one valuation block and is closed by the eventually-periodic theorem.  This excludes one-relay routing only on this node set. | [`complete_u_relay_graph_audit.json`](experiments/kontorovich/complete_u_relay_graph_audit.json) |
| Finite regenerative delay routing | Solved but insufficient.  Two delay gates with a shared gap always link when the second collision opcode is positive: both coefficient bases are odd, so one binary congruence gives the affine tail handoff `t=t_0+2^m v -> s=s_0+3^A v`.  Lean commit `54e506f` proves supplied affine families and links for every tail.  Commit `5254194` proves that an ordinary natural surviving unbounded nested address filters forces their canonical residues eventually to equal that natural; a perpetually changing address program is only 2-adic. | [`breakoff_delay_gate_audit.json`](experiments/kontorovich/breakoff_delay_gate_audit.json) |
| Canonical tail-zero delay dispatcher | Exhaustively negative at depth two in the symbolic box `q,j,q'<=100` (with `j` including zero): 1,010,000 gate shapes split into 992,129 with no next clean delay, 17,861 whose next gate needs positive tail, three canonical base-to-base links, and seven factor-of-eight coordinate aliases.  Every canonical link fails renewal after its target gate; their 59- and 85-digit ordinary seeds reach `1` in 1,272, 1,277, and 330 exact ordinary steps.  This closes only immediate stabilization at the canonical least coefficient, not evolved nonzero-tail or nonlinear two-packet programs. | [`delay_base_graph_audit.json`](experiments/kontorovich/delay_base_graph_audit.json) |
| Exhausted-tail ether staircase | The returning ether macros link every scheduled pair `n -> n+1`, but after setting the remaining higher macro tail to zero, the generated `(n+1)` tail misses the `n+2` input cylinder for every `n=1..128`; maximum linked depth is two macros.  This closes only the least-tail staircase controller.  Nonzero generated macro tails, branching length schedules, and other payload recurrences remain open. | [`breakoff_ether_glider_audit.json`](experiments/kontorovich/breakoff_ether_glider_audit.json) |
| Fully exhausted recursive glider ether | Closed for every immediate defect in the current returning-glider alphabet.  Every glider input packet is odd.  At the endpoint of a fully exhausted background macro-ether, its fixed form is odd, forcing the background-tail parity opposite the source cylinder of every possible next glider.  The obstruction is sharp rather than fatal: retaining the exact three-bit cap changes the phase modulo `16` and yields the certified returning super-ether. | [`breakoff_superether_audit.json`](experiments/kontorovich/breakoff_superether_audit.json) |
| Canonical tail-zero splash hierarchy | The most direct recursive program chooses the length-one branch and zero remaining tail at every new scale.  Exact expansion through depths `1..6` gives first-scale packet sizes `7,46,177,606,2021,6698` decimal digits and ordinary starts through 6,708 digits.  Consecutive packets agree in increasingly many low bits but are strictly larger and unequal at every checked depth (`v2` of the differences `23,155,589,2013,6715`).  It is therefore a growing sequence of finite 2-adic prefixes, not one stabilized ordinary seed.  This bounded diagnostic is now subsumed by the universal positive-tail row below. | [`breakoff_renormalization_audit.json`](experiments/kontorovich/breakoff_renormalization_audit.json) |
| Bounded canonical meta-quine tree | Exact recursive compilation checks all 584 meta-words of depths `1..3` over background choices `j=1..8`.  On every one of the 576 extensions, the canonical first-scale packet is strictly larger than its parent; there are zero stabilizations and zero decreases.  The closest paths are `(1,1)` and `(1,1,1)`, sharing 23 and 155 low bits respectively—the fixed tower already audited.  This bounded diagnostic is now subsumed by the universal positive-tail row below; another defect grammar or a fixed-level autonomous register orbit remains open. | [`breakoff_renormalization_audit.json`](experiments/kontorovich/breakoff_renormalization_audit.json) |
| Infinite capped-renormalization tower as one ordinary program | Closed for every successfully constructed adjacent-defect extension, independently of branch length or child payload.  With `q_raw>0`, combined parent exponent `E`, inherited valuation `r>=0`, and positive child packet `K`, exact substitution gives `q=q_raw+2^E(2^rK-1)>0`.  Every new nesting therefore has a strictly noncanonical parent tail, so the canonical dyadic addresses never eventually stabilize to one natural.  This subsumes the two bounded rows above as diagnostics.  It does not exclude an autonomous orbit in the unit register at a fixed finite level, or a different compiler grammar. | [`breakoff_renormalization.py`](experiments/kontorovich/breakoff_renormalization.py) |
| Infinite recursive `-5` charge hierarchy as one ordinary program | Closed, despite exact self-regeneration at every finite depth.  The depth-`j` quotient removes `D_j=3^(114*2^j)+2^(154*2^j)>1` and lifts a positive child packet as `K_j=rho_j+D_j*K_(j+1)>K_(j+1)`.  Iterated lifts make the root packet strictly grow, so the canonical addresses cannot stabilize to one natural.  This does not exclude an infinite autonomous orbit inside any fixed finite `-5` level; that is now the live target. | [`unit_charge_hierarchy.py`](experiments/kontorovich/unit_charge_hierarchy.py) |
| Infinite consecutive sign-negative full-order repetend splashes | Closed by exact core energy, including any hypothetical self-writing realization of this pure instruction.  Marker `C=1` forces `T=(2j+1)3^(q-1)`.  For `q>=3`, `3^(q-1)>=2q+1`, hence `2^T>2*3^q`; the recurrence `2^T h'=3^q h-1` gives `h>2h'`.  After `N` consecutive splashes a positive initial core would exceed `2^N`, impossible for fixed `h`.  The audit checks the concrete full-order exponent classes at sign-negative levels `2,4,6`.  This does not exclude sparse giant splashes separated by sufficiently amplifying charge phases. | [`unit_repetend_energy_audit.json`](experiments/kontorovich/unit_repetend_energy_audit.json) |
| Infinite externally preloaded carry-catcher rail | Invalid as an ordinary program.  Each finite catcher and the new turnaround can be linked by another dyadic tail congruence, but prescribing infinitely many such words generally defines a 2-adic stack.  Lean commits `5254194`/`ba121d9` show an ordinary realizing tail would force its canonical extension residues eventually to vanish.  The new finite writer therefore shifts the live target to an autonomous payload law; it does not license an infinite preloaded ether. | [`unit_carry_turnaround_audit.json`](experiments/kontorovich/unit_carry_turnaround_audit.json) |
| Three-collision synthesized-marker turnaround | **Retracted.**  The raw divisions used `q`-sequence `(57,57,q(g))`, but their state labels were `1 -> 1 -> 1` after the second transition.  A legal unit transition uses the source exponent, so the third step had to use `q(1)=57`, not `q(g)`.  Exact congruences and outward coefficients cannot repair this semantic mismatch.  The replacement audit uses `1 -> 1 -> g -> g -> 1`. | [`unit_return_quine_audit.json`](experiments/kontorovich/unit_return_quine_audit.json) |
| Outward affine banks without output-to-source closure | Closed as a promotion criterion, not as an architecture.  A bank of exact growing finite branches does not provide a trajectory.  It must exhibit `y_g(v)=x_f(g)(v')` under one autonomous finite rule, with one ordinary initial payload supplying all future addresses.  Fresh CRT extension at each generation is an externally preloaded 2-adic stack.  The corrected reproduction equation makes this missing link explicit. | [`unit_return_quine.py`](experiments/kontorovich/unit_return_quine.py) |
| Rational successor quine on the legal return bank | Closed in Lean for all rational functions.  Clearing a reduced numerator/denominator pair forces `Q(z) | Q(cz)`; equal degree and `0<c<1` make `Q` a monomial, coprimality plus the lowest coefficient makes it constant, and the nonzero linear forcing followed by the unmatched top-degree term gives a contradiction.  This does not exclude Mahler/automatic payloads or nonlinear opcode updates. | [`SuccessorQuineRationalNoGo.lean`](KontoroC/KontoroC/SuccessorQuineRationalNoGo.lean) |
| Shortest-recharge perfect-23rd-power bouncer quine | Closed.  Lean commit `5fbacf5` proves every accepted `h=1`, `u=F*r^23` reproduction transition supplies an integer solution of `3^15X^23-2^16Y^23=5`.  PARI/GP 2.15.4 checks the associated degree-23 polynomial irreducible, reports attached class number one, and returns the complete empty Thue solution list.  PARI documents this class-number-one fast case as unconditional; that final no-solution step is external-PARI scope, not kernel scope.  Higher recharge and multi-rail/corrected payloads remain open. | [`ChargePowerQuine.lean`](KontoroC/KontoroC/ChargePowerQuine.lean), [`unit_charge_power_quine_thue_audit.txt`](experiments/kontorovich/unit_charge_power_quine_thue_audit.txt) |
| Pure public-state 23rd-power rail, `m=0 (mod 23)` | Closed for every positive transition in this coefficient class.  Lean commit `4c56925` converts the transition to equal sums of two 23rd powers; exact input valuation makes `s` too large for the discrete gap.  Commits `f61f569`/`9f00894` reduce the remaining classes to scaled norm/cofactor equations and a hidden register.  Commit `07352a9` kernel-checks the elementary Roth approximation and exponent-11 bridge for the other classes; the external theorem and sequence-level finiteness consumer remain explicit seams.  Individual transitions, corrected types, and multi-rail packets remain open. | [`ChargeStatePowerQuine.lean`](KontoroC/KontoroC/ChargeStatePowerQuine.lean), [`ChargeStatePowerRoth.lean`](KontoroC/KontoroC/ChargeStatePowerRoth.lean) |
| Sum-of-two-squares public type | Universally closed before any search.  Every accepted bouncer state has `2^23 | y+1`, so `y=7 (mod 8)`; the next accepted state and `A^h=1 (mod 8)` force the odd collision quotient to be `7 (mod 8)` as well.  A sum of two squares is never `3 (mod 4)`.  This kills only `d=1`; the hardware-matched `x^2+d u^2` type with `d=7 (mod 8)` is live. | [`unit_charge_quadratic_norm_audit.json`](experiments/kontorovich/unit_charge_quadratic_norm_audit.json) |
| Naive `d=7` quadratic correction | Not closed, but locally taxed enough to abandon as the first search type.  The public-register primes 5 and 19 are inert for `x^2+7u^2`; exact prime-square collision arithmetic forces `5|m` and `19|m`, hence `95|m`, at every typed step.  The `d=31` replacement clears this particular tax. | [`unit_charge_norm_opcode_audit.json`](experiments/kontorovich/unit_charge_norm_opcode_audit.json), [`ChargeNormOpcode.lean`](KontoroC/KontoroC/ChargeNormOpcode.lean) |
| Norm representability without next-boundary synchronization | Closed as a promotion criterion.  One exact 184-digit `N_31` input has an `N_31` quotient and 193-digit `N_31` output, but the next collision valuation is `153`, leaving recharge remainder `130 (mod 154)`.  More isolated represented points—even a finite chain—do not supply a public self-map.  A new norm search must first exhibit a depth-independent update which regenerates `v2(A^g(C-D)r+1)=23m`. | [`unit_charge_norm_opcode_audit.json`](experiments/kontorovich/unit_charge_norm_opcode_audit.json), [closure doctrine](docs/notes/kontorovich-closure-principles.md) |
| Defect-only opcode chains as a dispatcher | Universally closed.  With `H_m=(C^m-D^m)/(C-D)` and `J_m=[[C^m,H_m],[0,D^m]]`, exact arithmetic gives `H_(m+n)=C^nH_m+D^mH_n` and `J_nJ_m=J_(m+n)`.  Such a chain remembers only total defect length.  Any programming power must come from recharge decorations and their public dyadic boundary, not from rearranging defect opcodes alone. | [`unit_charge_norm_opcode_audit.json`](experiments/kontorovich/unit_charge_norm_opcode_audit.json), [`ChargeNormOpcode.lean`](KontoroC/KontoroC/ChargeNormOpcode.lean) |
| Equal one- or two-letter decorated opcode products | Universally closed in the stated fixed-boundary class by Lean commits `90bdf21`/`5a9324b`.  Single decorated signatures are injective.  For two letters with fixed initial/final recharge phases, the two diagonal exponent equations recover total defect length and the middle recharge; the off-diagonal debris increases by the positive monomial `(A^h-B^h)C^eD^i` when the split moves one cell.  It therefore recovers both defect lengths.  This kills short matrix collisions, not conjugacies, renormalizations, longer relations, or invariant public tail languages. | [`ChargeNormOpcode.lean`](KontoroC/KontoroC/ChargeNormOpcode.lean) |
| Every fixed finite charge-bouncer period | Kernel-closed at the arithmetic-surrogate level by commit `e8585c4`, including arbitrary finite transients.  A generic nonempty list fold compresses one period to a single expanding coprime affine gain law; arbitrarily large denominator divisibility contradicts a fixed positive initial state.  This subsumes the earlier constant and alternating results.  Payload-driven genuinely aperiodic schedules and phase conjugacies remain live. | [`ChargeBouncerPeriodicNoGo.lean`](KontoroC/KontoroC/ChargeBouncerPeriodicNoGo.lean) |
| Fixed-jump resonant phase-up counter | Closed for every `k>=1`, despite its nonperiodic public phase `m_i=m_0+4ki`.  Lean commit `466e381` derives the exact public cofactor recurrence, constructs its unique `Q_2` candidate, identifies it coefficientwise with a nonzero rational multiple of `f_(3^(68k)/2^(92k))(alpha)`, and bridges every linked public-step ray to that recurrence.  The inspected main theorem of Väänänen--Wallisser (1989), pp. 200--201, applies with `ell=1,sigma=0,p=2`; accepting that external theorem makes the candidate irrational and rules out an ordinary cofactor.  Variable payload-dependent jumps/directions remain open. | [`ChargePhaseUpTheta.lean`](KontoroC/KontoroC/ChargePhaseUpTheta.lean), [phase-glider note](docs/notes/kontorovich-resonant-phase-glider.md) |
| Väänänen--Wallisser as an all-period phase-up obstruction | **Retracted beyond period three.**  Periodic jump schedules split into several theta values, and the paper's sufficient threshold depends on their number `L`.  Commits `8b3d9f5`/`772a6e8` kernel-check the complete flattened multi-theta decomposition and `gamma<Gamma(L,0)` for `L=2,3`, but also `Gamma(4,0)<1/8<gamma`.  Accepting the external theorem closes periods one through three; the citation cannot close period four or any larger period by the same estimate.  Period four is only the first theorem escape, not evidence of an ordinary ray. | [`ChargePhaseUpPeriodicTheta.lean`](KontoroC/KontoroC/ChargePhaseUpPeriodicTheta.lean) |
| Finite Laurent and homogeneous rational period-three EC17 coboundaries | Universally closed in the stated classes by companion commits `1154476`, `d0faf96`, and `82198ac`.  The exact three-step defect has three quadratic monomials.  Extreme support excludes every finite Laurent slice.  For a reduced homogeneous rational potential `x^-1 f(y/x)`, the scaled denominator divides the original, hence is a monomial; the same extreme-support contradiction then closes the quotient.  This does not exclude a general nonhomogeneous bivariate rational function, an infinite theta series, or rationality at one evaluated orbit. | [`LaurentCoboundaryNoGo.lean`](KontoroC/KontoroC/LaurentCoboundaryNoGo.lean), [`RationalCoboundaryReduction.lean`](KontoroC/KontoroC/RationalCoboundaryReduction.lean) |
| General 2005/2007/2013 theta theorems as an immediate period-three shortcut | Closed as applications of those sufficient statements, not as a no-period-three result.  Amou--Väänänen (2005) controls simultaneous relations over the full expanding-place set, which here contains both the real and 2-adic places; EC17 supplies only the latter relation.  Väänänen (2013), Theorem 4, allows a non-archimedean place, but tracing its criterion to Amou--Matala-aho--Väänänen (2007) gives `B/A<13/12`, while the EC17 height ratio is larger.  Commit `92416b1` kernel-checks the uniform threshold comparison and reduces its logarithmic part to `2^13<3^9`.  A sharper theorem specialized to this one evaluated three-theta form remains live. | [`AmouMatalaahoVaananenThreshold.lean`](KontoroC/KontoroC/AmouMatalaahoVaananenThreshold.lean), [`FOR_CLEAN_LEAN.md`](docs/FOR_CLEAN_LEAN.md) |
| Scalarizing the three theta values and importing a one-value threshold | Closed.  The scalar coefficient sequence is `u_n=s_0+s_1R^n+s_2R^(2n)`.  Commit `847027b` kernel-checks its cubic recurrence and the strictly positive literal Hankel determinant `s_0s_1s_2R^2(R-1)^6(R+1)^2`, then proves every recurrence of order at most two has zero such determinant.  The scalar relation therefore retains exact rank three.  The same commit shows that bare determinant-minus-cofactor multiplicity is only linear after primitive normalization; the generic cofactor divisor for a particular Padé matrix remains a seam. | [`ThetaScalarRank.lean`](KontoroC/KontoroC/ThetaScalarRank.lean), [`GeometricVandermonde.lean`](KontoroC/KontoroC/GeometricVandermonde.lean) |
| Pure KL class-8 / minus-one escape rail | Closed for ordinary positive payloads.  Commit `9f307a9` proves `T^L(2^L*t-1)=3^L*t-1`, exact splice balance `M+v_2(u)=v_2(t)`, and impossibility of infinitely many positive pure-rail splices; over `Q`, `-1` is the unique positive-period point of the class-8 predecessor map.  Commit `cc9f441` proves no fixed natural occupies its inverse-limit address.  Commits `408cb2c`/`814fb00` add the three-branch center ledger and prove `v_2(n+1)` is exactly the next forced odd-burst length, so mixed recharge is not stored fuel.  This does not close a growing diagonal with aperiodic controller resets. | [`KLMinusOneRail.lean`](KontoroC/KontoroC/KLMinusOneRail.lean), [`KLRechargeLedger.lean`](KontoroC/KontoroC/KLRechargeLedger.lean), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Coherent shadow of one fixed signed Syracuse orbit | Universally closed for distinct ordinary starts, with no periodicity assumption on the controller.  Commit `616ace8` proves `2^N*(x_N-y_N)=3^O*(x_0-y_0)` for a shared `N`-step parity itinerary, hence `2^N|(x_0-y_0)` and equality of two starts sharing an infinite itinerary.  The literal signed specialization excludes a positive orbit coherently following any one negative orbit forever.  This does not exclude increasingly expensive controller resets, which break the common itinerary and write a fresh dyadic address. | [`KLUniversalShadow.lean`](KontoroC/KontoroC/KLUniversalShadow.lean), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Arbitrarily deep but separately chosen finite negative shadows | Invalid as a promotion criterion because it is automatic.  Commit `2fcddea` proves two signed starts share their first `N` shortcut parities iff their difference is divisible by `2^N`, then explicitly constructs a negative representative in every finite cylinder.  Increasing finite shadow depth says nothing unless the controllers are independently constrained and compatible across resets; the live datum is the coupled quotient recurrence, not existence of each prefix. | [`KLUniversalShadow.lean`](KontoroC/KontoroC/KLUniversalShadow.lean), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Finite controller-legality, target, or mixed CRT hits | Invalid as a promotion criterion because they are automatic.  Commits `8c20163`/`54eb749` prove that every fixed controller numerator has power-of-two slope, hence one input class for every ternary target and a simultaneous class with any dyadic address.  Commit `961c692` proves `LegalWord(w,h)` is exactly the terminal cylinder `A*h+B=3^r mod 3^(r+1)` when `r>0`, and constructs the unique positive legal input class reaching every `g=1 mod 3` target at every finite precision.  Only cross-reset inverse-limit coherence, positivity, and real outward growth remain. | [`KLControllerReset.lean`](KontoroC/KontoroC/KLControllerReset.lean), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Independent finite reset-cylinder, integrality, or positivity hits | Invalid as a promotion criterion.  Commits `2acceaa`/`d8d8337` accumulate any reset block into `2^S*m_end=3^P*m_start+D`, prove its terminal congruence equivalent to existence of every intermediate integer quotient, and prove that every finite instruction word has a strictly positive payload chain after a cylinder shift.  Commits `2963a8d`/`ca8dc5c` prove nested canonical-residue monotonicity, eventual stabilization, and the exact bounded carry law.  Commit `18b8c93` proves that eventual zero carry is equivalent to existence of a nonnegative ordinary integer chain.  The unresolved gates are an exact zero-carry construction for a useful schedule, positivity of all its infinite quotients, and KL-outward growth. | [`KLDyadicReset.lean`](KontoroC/KontoroC/KLDyadicReset.lean), [`kl-calibrated-escape.md`](docs/notes/kl-calibrated-escape.md) |
| Periodic fixed-depth residue clock as a rationality or construction proof | Invalid without EC17-specific consecutive-carry control.  Commit `a9ed874` proves the target clock and its no-ray consumer, but QM118 constructs any prescribed fixed-depth class by one sufficiently wide appended binary block.  Commit `5769c85` kernel-checks the sharper failure: modulo `3^d`, every carry except the final consecutive one is annihilated by a later ternary factor, and even exact long-block zero may be signed cancellation.  Deeper diagonal scans therefore neither glue finite links nor imply rationality.  The replacement balanced-precision worker makes a full moving-depth congruence equivalent to exact one-cycle equality; `4516a03` proves an eventual equality tail constructs a literal period-three ray, while `fff0dec`/`732da20` check the exact finite-row canonical range gate at its logarithmic precision.  Its bounded 53,392-row audit has zero hits but is not an all-precision theorem. | [`breakoff_ether_period3_fixed_depth_audit.json`](experiments/kontorovich/breakoff_ether_period3_fixed_depth_audit.json), [`breakoff_ether_period3_balanced_carry_audit.json`](experiments/kontorovich/breakoff_ether_period3_balanced_carry_audit.json), [`EtherCounterResidualFold.lean`](KontoroC/KontoroC/EtherCounterResidualFold.lean), [`FOR_CLEAN_LEAN.md`](docs/FOR_CLEAN_LEAN.md) |
| Bare public words as binary-to-ternary chart adapters | Universally closed by Lean commit `772a6e8`.  Every exact public step has typed form `w-3^(-17m)=a*(w'-2^(-23m'))`.  A multi-cell word accumulates a strictly negative internal tax, exactly the normalized `-H_m` defect, so it cannot be a clean entry/exit coboundary.  This is not a no-orbit theorem; it proves that closure needs an auxiliary correction rail. | [`ChargeTypedInterface.lean`](KontoroC/KontoroC/ChargeTypedInterface.lean), [closure doctrine](docs/notes/kontorovich-closure-principles.md) |
| Infinite rail of the one-cell determinant-four conjugacy | Universally closed in that chart class by Lean commit `772a6e8`.  Self-linking successive cells requires `1311*k_(i+1)=1309*k_i`; a length-`N` rail forces `1311^N|k_0`, and an infinite natural rail has `k_0=0`.  The result is independent of affine intercepts and tail cylinders.  A live turnaround must reverse the separation loss or leave the one-cell resonant class. | [`ChargeResonantSeparationNoGo.lean`](KontoroC/KontoroC/ChargeResonantSeparationNoGo.lean), [phase-glider note](docs/notes/kontorovich-resonant-phase-glider.md) |
| Constant-rate fixed-level unit bank `n_t=n_0+kt` | Closed at all six compiled levels for every `n_0>=1` and fixed integer `k>=1`.  Exact unrolling gives a Tschakaloff value with theorem parameter `q=3^(ck)/2^(ak)` and rational nonzero `alpha=2^(p(n_0))/3^(q(n_0))`, independent of `k`.  The full-source Väänänen--Wallisser theorem makes it irrational in `Q_2`; the exact audit checks the function conversion and the uniform strict size bound, whose logarithmic ratio is unchanged because `k` cancels.  Six linked eight-transition regressions verify the finite `k=1` recurrence, while the symbolic coefficient identity and cited theorem give the all-`k` conclusion.  A factor bank must use nonlinear packet feedback, not any fixed-rate counter. | [`unit_linear_theta_audit.json`](experiments/kontorovich/unit_linear_theta_audit.json) |
| Fixed or eventually periodic break-off opcodes | Closed for the autonomous router subclass.  Lean commit `a1a5fd0` proves that every infinite growing `BreakoffCounterOrbit` emits macro-words `[1]^r[2,1]` and that neither its rail lengths nor its collision opcodes can be eventually periodic.  The six-class opcode acceptor is therefore syntax, not a cyclic generator; an infinite witness must encode unbounded aperiodic information. | [`BreakoffCounter.lean`](KontoroC/KontoroC/BreakoffCounter.lean) |
| Fixed defect opcode in the charge bouncer | Closed by Lean commit `5633c44`.  For a fixed affine gain law `B*Z_(t+1)=A*Z_t+C` with coprime `A,B`, `1<B`, and `A>B`, the fixed-point defect obeys `B*delta_(t+1)=A*delta_t`; hence every `B^n` divides one positive `delta_0`, impossible.  The concrete theorem applies to every fixed `m`.  It does not apply to the live bouncer, where `m` may decrease or oscillate and each block switches from its `m`-defect law to `h-1` homogeneous backgrounds. | [`AffineQuotientNoGo.lean`](KontoroC/KontoroC/AffineQuotientNoGo.lean) |
| Three named aperiodic two-opcode bouncer clocks | No canonical ordinary address stabilizes in the exact finite grammar: Thue--Morse, period-doubling, and Fibonacci control words; every injective coding of `0,1` by the 16 pairs `(m,h)` with `1<=m,h<=4`; all 34,560 prefixes through depth 48.  The closest pair shares 33,128 low bits but changes from a 33,386-bit address to a 34,092-bit address.  This closes only these named clocks and bounds, not payload-generated, larger-alphabet, or general morphic bouncers. | [`unit_charge_morphic_audit.json`](experiments/kontorovich/unit_charge_morphic_audit.json) |
| Bounded zero-extension charge-bouncer tree | Every word of depths `1..4` over the 16 opcodes `(m,h)` with `1<=m,h<=4`, followed by every one of the 16 possible next blocks, was compiled exactly: 69,904 prefixes and 1,118,464 extensions.  Zero canonical lifts found: none.  The closest nonlift agrees in only 16 of 177 required low bits, while the maximum terminal public valuations by depth are `3,9,13,16`; this does not imply a fixed-modulus obstruction or an all-depth theorem. | [`unit_charge_zero_lift_audit.json`](experiments/kontorovich/unit_charge_zero_lift_audit.json) |
| Standard two-rail schedule `[1]^r[2,2,3]` | Closed at all levels.  Exact affine-family intersection compiles 247 outward rounds from a 10,040-digit seed, but depth 248 changes the seed and exact continuation reaches `1`.  Lean reduces every infinite realization to `2^(r+8)P'=3^(r+3)P+69` and its sole 2-adic Tschakaloff candidate.  Väänänen--Wallisser's 1989 theorem applies at `q=3/2,p=2,alpha=4096/6561` and proves that candidate irrational, so it cannot be an ordinary payload.  This does not close branching or other aperiodic splash programs. | [Finite certificate](experiments/kontorovich/two_rail_chain_247.json), [theorem audit](docs/notes/standard-two-rail-theta.md) |
| Fixed affine or autonomous finite-state return | Closed as an outward bouncer.  Lean commits `b741a14`/`26f3584` prove fixed affine circuits and every eventually periodic macro-word schedule impossible; `560fcc5` proves an autonomous controller with any finite effective state eventually enters that obstruction.  Coefficientwise, a repeated word would require natural slope `m=3^N/2^S` with `S>0`.  Payload-dependent branching and unbounded shape counters remain open. | [Delocalized tag-ISA note](docs/notes/kontorovich-delocalized-isa.md) |
| Canonical zero-preload two-rail graph | Exactly checked 128,000 gate shapes in the stated box (`r<=40`, `s<=4`, collision extras `<=4`, output gap `<=41`): 98,760 canonical members are outward, 25 canonical links exist, and the longest linked chain has two gates. Its seed `45247` reaches `1`; a wider targeted audit finds no third canonical gate for that endpoint. This rejects only index-zero links, not branching affine-tail controllers. | [`two_rail_transducer_audit.json`](experiments/kontorovich/two_rail_transducer_audit.json) |
| Small regular invariant sets | Previously closed only in the stated exhaustive classes: no base-2 DFA divergence certificate through eight states and no base-3 certificate through five. One-counter and genuinely morphic single-orbit certificates remain open. | [Base 2](experiments/dfacert/README.md), [base 3](experiments/dfacert3/README.md) |

The first work product will be an exact `k`-word compiler and cycle/glider
search harness with replayable certificates.  New lanes and closed ansatz
classes will be recorded here with explicit bounds, just as in the proof
strategy's failure ledger.  Nothing will be called a disproof unless the
positive integer and its claimed behavior are machine-checked.

### KC Headline results (with verification scope)

| Result | Status |
|---|---|
| Two-Kraft architecture bound | Every valuation word has ordinary weight `p=2^-S` and tilted weight `q=3^n/4^S`; outward slope means `q>p`.  Commit `da9fa59` derives both Kraft inequalities from finite prefix-freeness via explicit self-delimiting compilers and proves that a positive nonempty, prefix-free, `p`-complete code cannot have every leaf outward.  It also proves the finite quantitative mass bound; the countable prefix-free bridge remains abstract.  The positive target is a proper invariant thin language, not a total growing decoder; no counterexample is claimed. |
| Kernel thin-trap endpoint | Commit `298f5a3` iterates any explicit canonical-splash predicate closed under its public successor, proves exact `next` linkage and strict outwardness, constructs `InfiniteCanonicalSplashOrbit`, and concludes `not Collatz`.  This is a fully checked certificate consumer, not a witness: no qualifying seed or invariant predicate is known. |
| YAH mixed-base closure audit | The exact artifact pins all 11 rules, replays the published `12 -> ... -> 1` example, classifies all letter and width-two uniform morphisms, proves its 513,916-state length-at-most-eight induced graph acyclic, and finds a longest 299-rewrite delay `834 -> 1079` but no pumping certificate.  Commit `1b3459d` makes literal/morphic pumping a kernel certificate consumer; `9ca4360` closes proper canonical outer growth; `bfe12f0` proves identity is the only productive nonerasing marker-fixed independent digit-word morphism at arbitrary widths.  Context-dependent/multi-block templates, the external YAH-to-Collatz seam, and any glider remain open. |
| YAH internal carry opcode | The auxiliary digit complement is exact, while its terminal affine defect is `s-t>=1` and equals one exactly on saturated buffers.  The exact artifact checks 488,281 bounded buffers and replays 1,443 run macros.  Commit `0365c72` independently kernel-checks the defect and the all-length zero/max-run and two-counter transfer opcodes; `f81ff21` proves the transfer's exact odd-step semantics and strict outwardness.  It spends one left `tri0` token to increment a right `tri2` counter and phase-changes the remaining block; it supplies a real instruction but no closure. |
| YAH queue macro and nonlocal type | A complete left-boundary opcode factors into one or two sweeps of a two-state ternary quotient transducer.  Commits `1a88c3e`/`b1dd87a` kernel-check the factorization, exact space charge, mod-four growth table, and global alternating checksum.  At length `m`, exactly `(3^(m-1)-1)/2` of `3^m` programs grow, giving asymptotic density `1/6` and mean space drift tending to `-1/6`.  Commits `64bccb8`/`db13d82` prove perpetual `+1` growth impossible and force `4^r | N+1` for an `r`-burst.  Commits `288fb09`/`e293f7d` prove battery conservation on growth and the complete nongrowing recharge ledger; `22ce54d` proves the packet value and four phase-recharge formulas.  The independent worker agrees with literal rules on all 88,572 words through length ten and replays 16,769 chained run/comb/packet cases through coordinate 64.  It exhibits a four-phase packet compiler; commit `b794b2f` proves that packet is not directly self-linked, so no battery-recharging multi-type cycle or infinite orbit is known. |
| YAH recharge amplifier and preserved register | For target gain `G`, the construction takes `K=4G+1` and the unique phase-one packet address `41*9^q+15=0 (mod 2^(K+5))`.  Its neutral macro writes at least `K` dyadic-charge units; commit `67eabe3` proves that `J>=4G` all-odd defect steps force at least `G` new ternary cells.  Commit `1a69d5b` kernel-checks the lift-register isometry `v2(A_K(t)-A_K(u))=v2(t-u)`; commits `6b5e34c`/`0b8179a` prove exact `v3=2` and the resulting run of `J+2` trailing twos.  The artifact checks 32 symbolic targets, all 1,024 ten-bit register values for four targets, and exact queue traces through a 369,187-trit packet.  The dynamical maximal-prefix wrapper remains to be packaged.  This proves neither autonomous address regeneration nor an infinite orbit. |
| YAH lift-register bit decoder | At charge `K=5`, all addresses are `q=17+128t`.  Four queue macros map the packet to an exact lasso `U V^t Z` with `|V|=256=ord_(2^10)(3)` and defect `3^7R(t)`.  The next zero-head macro reads `R(t) mod 2=t mod 2`: zero maps `3^7(2r)-1` to `3^8r-1`, extending the trailing-two reservoir, while one maps `3^7(2r+1)-1` to its half and changes chart.  The finite-state artifact constructs explicit 512-trit successor blocks and replays 65 parameters exactly.  This is a genuine LSB-first opcode, not closure; the restorative row records the first return from a thin bit-one cylinder. |
| YAH restorative bit-one opcode | On the exact cylinder `t=91+256u`, `q=11665+32768u`, the bit-one collision is followed by a neutral recharge because `2^8 | 3^6R+1`.  Five macros return to head zero with seven trailing twos, write `R'=(3^6R+1)/2^8`, and gain one cell relative to the incoming decoder state.  The all-parameter certificate consists of six generated lasso identities with a 65,536-trit block; the exact artifact independently replays `u=0,...,4`.  Commit `f96e621` proves the returned family disjoint from the original chart; `0da1058` proves an eventual tail repeating only this affine update impossible.  This is regeneration but not closure: no finite recurrent multi-chart graph or infinite ordinary orbit is known. |
| Program-scale calibration | Barina's published exhaustive check through `2^71` excludes every ordinary seed below that bound. Colussi's exact order-10 repetend has 39,366 padded bits and an 11,846-digit integer value, giving a literature-backed, formula-generated background at the scale Simon proposed. This is target calibration, not evidence of divergence. |
| Delocalized instruction-set audit | Exact published encodings expose four complementary units: valuation congruences, mixed binary--ternary boundary rewrites, De Mol's three-symbol tag rules, and Colussi's rotated repetend grammar. They motivate a nonlocal bouncer search but do not prove computational universality or nontermination. |
| Exact dyadic--triadic packet gate | Lean commit `f1cb0e2` proves universally that each supplied base collision generates exactly the affine family `h=r+2^(m+e+2)q`, `h'=s+2*3^m q`, with unique payload, literal valuation `e`, and the triadic next-packet scheduler. The Python checker passes 8,192 family members and an exhaustive converse over all 16,316 renewals found for odd `h<2^16` at levels `1..8`. No closed all-level gate controller is known. |
| Kernel stream uniqueness and 2-adic candidate | Lean commit `7370489` proves that a fixed positive valuation stream has at most one ordinary seed and kernel-checks every finite backward-series truncation. Commit `b205e40` proves convergence of the canonical series in `Q_2`, vanishing of the terminal term for an ordinary renewal, and the exact reduction: if the candidate avoids embedded negative naturals, that schedule has no positive renewal. Candidate nonintegrality for a useful controller class remains open. |
| Formula-generated 11,846-digit spatial wire | Colussi's order-10 value `(4^19683-1)/3^10` is reconstructed, not stored as a decimal literal. The exact header `(1,1,2,1,1,1,5,1,4,1)` sends it to `1+2^39348`; then 19,673 exact valuation-two steps obey `x_t=1+3^t 2^(39348-2t)` before a valuation-three collision. Lean commit `6229e7a` proves the general delay formula and kernel-checks this generated header and endpoint. Exact continuation reaches `1` after 95,146 accelerated steps, so this certifies a wire and its failed natural renewal, not nontermination. |
| Exact finite carry-splash families | For every positive `r,r',a`, research-side exact algebra constructs an arithmetic progression of odd payload pairs such that an `r`-tick `+1` delay line collides with valuation `2+a` and emits an `r'`-tick gap. The checker literally replays 15,360 members in the bounded regression `r<=8,r'<=10,a<=6`; e.g. `2961 -> 2221 -> 833` grows the gap from four to six bits. Every member shrinks, so a splash needs an amplifying phase. |
| Formula-generated 10,040-digit two-rail program | Exact congruence solving and affine-family intersection construct one seed with 33,351 significant bits, without storing its decimal literal. It executes 247 strict outward rounds of the schedule `[1]^(4+i) ++ [2,2,3]`, grows its clean gap from 5 to 252 bits, and reaches a 15,397-digit endpoint after 32,110 accelerated steps. Literal replay passes; Lean commits `39a3aba`/`5d3e0e3` certify the generic gate and finite-chain seams. Full exact continuation reaches `1`, and the 248-round canonical seed is different. This is a large finite Collatz program, not a counterexample. |
| Exact affine tag-transducer and branching target | Every affine two-rail handoff reads one dyadic residue of a nonlocal family index, deletes that address block, and maps the residual tail by a power of three plus an offset. Lean commits `4789a80`/`1076954` prove universal one- and two-instruction linkage.  Commits `b741a14`--`560fcc5` rule out fixed affine returns, every eventually periodic macro-word stream, and every payload-independent finite-state controller.  The live target must branch on unbounded tail data or carry an unbounded counter. |
| LSB-first splash instruction grammar | For fixed amplifier length, each positive gate shape `(s,a,b,L)` is one odd payload residue modulo `2^(a+b+2s+L+3)`.  Lean commit `1b7df1f` proves universal parameter decoding, the complete cylinder strides, and pairwise disjointness; the exact Kraft mass among odd 2-adic payloads is `1/6`.  The artifact checks 902,496 codeword pairs per `r=1..16` through 20 bits and independently decodes 21,504 bases.  This identifies a sparse mixed-base tag language, not an infinite survivor. |
| Parity-complete splash ISA | Simon's proposed sacrificial alignment supplies the missing odd-gap catcher `2+3^(s+1)Q=-1+2^L P'`; admitting `L=1` supplies a zero-delay next rail.  Lean commits `afb86a5`--`92f237c` certify the two branches and unique total decoding.  Commits `88e2577`/`b023700` expose the decoded macro and canonical partial next-state map and prove that any surviving outward public-state orbit refutes Collatz.  The exact Kraft split is `1/3+2/3=1`; no infinite orbit is supplied. |
| Exact base-`3/2` compiler bridge | The outward two-rail link `(5,0,2,1,2)->(1,0,2,1,2)` maps family indices by `95+128t -> 1640+2187t`, exactly `U^7` for every natural `t`, where divergent `U` appends digits `[1,1,1,1,1,2,1]` in rational base `3/2`.  Lean commits `401d494`/`6ab99fc` prove the universal dyadic-cylinder law and reusable compiler certificate; `dbe0e5a` proves the conditional variable-chain endpoint to `¬Collatz`.  The concrete target shrinks and the seed reaches `1`, so no infinite chain is supplied. |
| Two-outward-gate `U^12` bridge | Exact coefficient algebra gives `U^12(1023+4096t)=132860+531441t` with digits `[1]^10[2,1]`.  It links shapes `(10,0,4,2,11)->(10,2,1,3,2)`, and both complete families are universally outward.  The saturated orbit enters at time 622; the parity-complete decoder catches the next formerly rejected payload, but that catcher shrinks.  The resulting 120-digit seed parses into 290 exact splash gates, 101 outward, and reaches `1` after 1,016 accelerated steps.  This is a finite compiler cascade, not transferred divergence. |
| Universal three-gate outward `U^12` subcylinder | Restricting the `U^12` tail to `t=16u` makes the next decoded catcher `(1,0,1,2)` outward for every `u>=0`.  Exact affine formulas give `2199021754367 -> 2229023590399 -> 5083728186203 -> 8578791314219` at `u=0`, with nondecreasing state strides preserving all three inequalities universally.  The least seed reaches `1` after 133 accelerated steps.  This certifies Simon's “splash the splash” with net gain through three gates, not infinite renewal. |
| Bounded parity-complete saturated bridge graph | The exact shape search checks 25,600 sources and all 2,751,680 coefficient-compatible targets in its stated box, finding 18 universal `U^D` bridges—14 odd-source and four even-source.  Eleven linked target subfamilies are also universally outward.  The complete 718-candidate outgoing audit of those target shapes finds no second saturated edge.  This is a scoped compiler-graph dead end, not an exclusion beyond the source bounds or of intervening ordinary splash gates. |
| Universal outward splash router | For every `r>=0,L>=1`, the odd catcher `(r,0,1,L)` has word `[1]^r[2,1]`, arbitrary outgoing gap `L`, and multiplier `3^(r+2)/2^(r+3)>1`; hence every member is outward.  Exact affine composition uses it to connect every ordered pair of the 11 two-outward compiler nodes.  All 121 five-gate transition families replay exactly, making the two-relay shape graph complete.  Lean commit `fedb5ca` proves the all-parameter growth inequality and formalizes the natural-versus-2-adic boundary.  This supports arbitrary finite branching words, but an infinite word still generally selects only a 2-adic tail. |
| Autonomous router recurrence | Lean commit `e9f791b` proves that positive odd payloads satisfying `2^(r'+3)P'=3^(r+2)P+3` construct the canonical router `(r,0,1,r'+1)`, with exact linkage and strict growth.  Any infinite solution above initial state `4` therefore refutes Collatz.  Commit `c10e5b5` proves `3|P'` and the exact maximal-power-of-two/odd-part update.  The equivalent radix-swap candidate forms `e=v_2(y+1)` and `F(y)=3^(e-1)(y+1)/2^e` inside `9|y`, `y=7 (mod 8)`.  No infinite ordinary orbit is supplied. |
| Break-off instruction compiler | In the coordinate `y=8k-1`, one router instruction factors `k=2^j u` and executes `8k'=3^(j+2)u+1`.  For each `j`, legality is one exact `u`-class modulo `72`, and the unbounded tail map is `u=u_j+72t -> k'=b_j+3^(j+4)t`.  Lean commit `0b12d44` proves that any infinite proof-carrying break-off orbit stays `8 mod 9`, strictly grows, and refutes Collatz; commit `a1a5fd0` proves its opcode stream cannot be eventually periodic.  Commit `7293975` implements the executable `v_2`/odd-part partial map, proves it equivalent to the factorization interface, and derives `¬Collatz` from any infinite successful executable orbit.  The artifact lists opcodes `0..64` and literally replays 4,160 members through the canonical decoder.  No infinite orbit is supplied. |
| Regenerative three-bit delay gate | Simon's gap-splash suggestion has an exact spatial realization.  The state `9*2^(3q)c-1` performs `q` opcode-zero ticks before a chosen collision emits a fresh clean gap `9*2^(3q')c'-1`; Lean commit `eac55d3` proves the universal compressed run, collision renewal, and strict outwardness.  Commit `1711620` proves that the collision factorization plus one subtraction-free affine balance suffices to reconstruct renewal.  The artifact constructs 1,088 gate families and performs 8,704 literal macro replays.  The example `935 -> 1052 -> 2663` regenerates one delay cell but later reaches `1`. |
| Affine mixed-radix writer and ordinary-tail gate | Exact coefficient linking reads `m` low binary bits and appends `A` ternary digits: `t=t_0+2^m v -> s=s_0+3^A v`.  Lean commit `54e506f` proves every supplied affine gate family, coefficient link, composed run, and outwardness for all `v`.  Commit `5254194` connects its `2^m` address cylinders to the ordinary/2-adic boundary.  The artifact audits 4,608 linked pairs (18,432 macros) and shows one fixed dispatcher realizes every one of the 243 five-trit write words within stated bounds.  Finite instruction routing is solved; a returning aperiodic dispatcher with one eventually stabilized natural address is not. |
| Nonlocal sacrificial gap amplifier | In the five-trit writer choose `b=3^5-2^L` and residual `v=K*2^L-1`.  Exact arithmetic gives `b+3^5v=2^L(3^5K-1)`: trailing one-bits collide with the selected word to become zero-bits, while the remote congruence `3^5K=1+2^D (mod 2^(D+1))` supplies exactly `D` more.  All seven words `L=1..7` exist in the certified alphabet; the artifact replays 224 linked members for `D=1..32` through 448 literal gate macros.  This produces an internal tail gap, not yet a returning infinite controller. |
| Regenerative finite ether defect | The gate `E=(1,2,1)` self-links by `t=20+2^8v -> 57+3^6v` and satisfies `2^8(473t'+12)=3^6(473t+12)`, so exact divisibility of `473t+12` by `2^(8n)` is an `n`-cell spatial delay.  The defect `H=(1,136,1)` gives an exact `E -> H -> E` return whose Mersenne residual has `473t+12=2^8(r+AK)` with fixed odd `r,A`; one odd class of the remote packet therefore writes any prescribed finite ether depth.  The artifact constructs `n=2..32`, replaying 589 linked members and 1,178 literal gate macros.  It does not return the exposed boundary to another defect. |
| Returning finite ether glider ISA | Exact parity shows an exhausted ether boundary is odd and therefore cannot re-enter the `j=136` defect; among immediate `E -> H_j -> E` defects, `j=1` is the parity-compatible receiver.  Its small identities give defect input `X(K)=2^20K-10941`, return factor `473t+12=2^5(83790531K-874281)`, and for every `n>=1` a complete outward macro `K=R_n+2^(8n+15)q -> K'=S_n+3^(6n+11)q` which writes `n` ether cells and returns to the same defect family.  The artifact replays 64 macro members through 1,184 links and 2,368 gate macros.  No infinite linked macro orbit is supplied. |
| Autonomous ether-counter normal form | Put `Y=83790531K-874281`.  The length-`n` returning glider branch is exactly `Y=2^(8n-5)h -> Y'=(3^(6n+11)h+51)/2^20`, with `h` in one CRT class modulo `83790531*2^20`; the enormous defect constants cancel to `51`.  Commit `a732905` proves the stronger all-branch Lyapunov law `15*Y_t<Y_(t+1)` and its `15^t` iterate, so any infinite legal execution is automatically an outward escape.  The dynamics artifact proves the successor-cylinder law and exhausts `160^3` canonical three-branch prefixes into the minimum-width next branch.  Its unique zero-address hit `115->59->9->1` begins exactly when the 574-bit initial tail is exhausted, so it is padding rather than a counter write; 384 literal gate macros replay and then halt.  An infinite successful autonomous orbit would be a counterexample, but none is supplied. |
| Arithmetic-growth ether branch counter | Conditionally closed for every `n_t=n_0+kt`, `n_0,k>=1`.  Exact unrolling gives a single 2-adic partial-theta candidate with paper parameters `q=3^(6k)/2^(8k)` and `alpha=2^(8n_0+15)/3^(6n_0+11)`.  The artifact checks 16 finite eight-transition ether schedules, 4,096 conversion coefficients, and every elementary Väänänen--Wallisser hypothesis uniformly; accepting that inspected external 1989 theorem makes the candidate irrational and nonordinary.  This does not close nonlinear or payload-dependent unbounded counters. | [`breakoff_ether_linear_theta_audit.json`](experiments/kontorovich/breakoff_ether_linear_theta_audit.json), [`unit_linear_theta_audit.json`](experiments/kontorovich/unit_linear_theta_audit.json) |
| Universal EC17 scale budget and branch ceiling | Companion commits `a6ce60a`/`26cacdb` prove for every positive ternary-core execution that `core(0)<=P_N*core(N)<core(0)+1`, hence `P_N<core(0)+1`.  The exact separator `3^41<2^65` then gives the machine-checked necessary condition `328*n_N<62*sum_(i<N)n_i+328*n_0+100*N+41*core(0)`.  Commits `007c252`/`eb06dcb` prove the online form: arbitrarily late steps satisfy `328*n_(t+1)<390*n_t+141` (asymptotic ratio below `1.1891`), so every survivor slows its branch expansion infinitely often.  Violating either condition excludes a schedule before constructing the forced core.  These are universal pruning theorems, not an orbit. | [`EtherCounterGeometricMahler.lean`](KontoroC/KontoroC/EtherCounterGeometricMahler.lean) |
| Geometric ether branch counter `n_t=n_0*d^t` | Unconditionally closed for every `n_0>=1,d>=2`.  The universal defect sum is below one, so exact unrolling traps `P_N*core(N)` in `[core(0),core(0)+1)`; geometric growth makes every factor of `P_N` larger than two and yields a finite contradiction at `N=core(0)+1`.  Companion commit `a6ce60a` kernel-checks the abstract and literal-orbit endpoints.  The older Mahler reduction and exact nine-schedule artifact remain valid independent audits, but no external irrationality theorem is needed.  No orbit is supplied. | [`breakoff_ether_geometric_mahler_audit.json`](experiments/kontorovich/breakoff_ether_geometric_mahler_audit.json), [`EtherCounterGeometricMahler.lean`](KontoroC/KontoroC/EtherCounterGeometricMahler.lean) |
| Periodic-increment ether counters | The constant-`17` core turns any positive-mean period-`L` increment word into `L` separated theta values.  The exact artifact checks 15 literal period-two/three schedules through nine public core transitions and 624 coefficients.  Commit `11eaba0` kernel-checks the entire period-two EC17 bridge and exact external independence seam; accepting the cited 1989 theorem, all positive-mean period-two increment tails are dead.  Commit `def4c52` derives the literal three-step defect monomials and proves that every positive derivative order makes the theorem's period-three threshold still worse; commits `1154476`/`82198ac` close every finite Laurent and homogeneous rational potential for those monomials.  Period three remains an arithmetic infinite-series/evaluated-value gap, not a witness. | [`breakoff_ether_periodic_theta_audit.json`](experiments/kontorovich/breakoff_ether_periodic_theta_audit.json), [`EtherCounterPeriodicTheta.lean`](KontoroC/KontoroC/EtherCounterPeriodicTheta.lean), [`EtherCounterPeriodThree.lean`](KontoroC/KontoroC/EtherCounterPeriodThree.lean), [`LaurentCoboundaryNoGo.lean`](KontoroC/KontoroC/LaurentCoboundaryNoGo.lean), [`RationalCoboundaryReduction.lean`](KontoroC/KontoroC/RationalCoboundaryReduction.lean) |
| Period-three EC17 ordinary-core sieve | At precision `P`, the future fixes one core residue modulo `2^P`; the preceding EC17 step independently fixes the successor modulo `3^(6*n_previous+11)`.  Exact CRT therefore gives one representative below the product modulus.  The artifacts exhaust 2,340 increment words and 72,156 positive schedules in the box `d_i in [-8,8]`, previous branch in `[1,32]`, `P=4096`; every least representative fails after 7--47 steps.  The stronger rowwise bound is `2^4096*3^(6*n_previous+11)`, uniformly at least `2^4096*3^17`.  Companion commits `75a6829`, `def4c52`, and `cbc51f4` kernel-check the binary finite consumer, cofinal infinite endpoint, full ternary congruence, and CRT product-lower-bound logic.  These artifacts still supply only finite lower bounds, not the required cofinal family, an orbit, or a global exclusion. | [`breakoff_ether_period3_sieve_audit.json`](experiments/kontorovich/breakoff_ether_period3_sieve_audit.json), [`breakoff_ether_period3_crt_sieve_audit.json`](experiments/kontorovich/breakoff_ether_period3_crt_sieve_audit.json), [`EtherCounterResidueBound.lean`](KontoroC/KontoroC/EtherCounterResidueBound.lean), [`EtherCounterStateNoRepeat.lean`](KontoroC/KontoroC/EtherCounterStateNoRepeat.lean) |
| Three-bit-capped recursive super-ether | Regard the one-cell returning glider as a 23-bit background cell and the two-cell glider as its defect.  Exact parity kills a fully exhausted second-scale gap, but retaining three low bits makes the boundary re-enter the same defect cylinder.  After removing a common `3^7`, the public register is `V=-8744697538656344367967+671265207750760396088265K` and its length-`N` branch is `V=2^(23N+3)g -> V'=(3^(17N+40)g-17)/2^51`.  The affine super-macro is `K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t`.  The artifact checks 64 branches and 256 members, and literally replays 32 members through 336 glider macros, 1,040 lower links, and 2,080 gate macros.  This is a finite two-scale constructor, not an infinite orbit. |
| Six-level sign-alternating splash hierarchy | The capped construction renormalizes five more times without changing the magnitude `17`: public collision signs are `+,-,+,-,+,-` and binary cell widths are `8,23,77,254,839,2771`.  At every checked step exact phase arithmetic returns to the defect and normalization flips only the sign.  The artifact checks 40 child branches independently by CRT and parent-macro composition, replays 80 members through 520 parent blocks, and expands the canonical tail-zero programs through six levels to literal first-scale gliders.  It additionally checks all 64 level-one choices `B=M_j,H=M_(j+1)`, three nonconstant four-step meta-words, and every depth-three meta-word over `j=1..8`.  Beyond those bounds, the exact positive-tail identity proves universally that no infinite chain of these adjacent-defect nestings can stabilize its canonical ordinary address.  The depth-six canonical member is a generated 6,708-digit ordinary start executing 360 linked glider macros.  This is a finite compiler and a source of fixed-level ISAs—not an ordinary infinite orbit or an induction that the phase identities persist at all levels. |
| Invariant unit-debris register and signed radix swap | At every one of the six certified hierarchy levels, exactly one packet class modulo `17` makes the primitive `±17` register divisible by `17`; the class is preserved by every successful branch.  Dividing gives `H=2^(an+b)h -> H'=(3^(cn+d)h+s)/2^e`, `s=±1`.  With `W=2^eH`, every instruction is exactly `W=2^p h -> W'=3^q h+s`: it preserves the complete core `h`, swaps an exact binary delay for a ternary delay, and writes one signed unit.  Against the signed router it trims `d=p-1-q`, with the six formulas `2n+3,6n+13,20n+45,66n+151,218n+501,720n+1657`.  The artifact compares all 192 branches, checks this form on 768 members, and literally replays 32 level-one members through 336 lower links and 672 gates.  This identifies the factor a second rail must bank; no such rail or infinite unit orbit is supplied. |
| Two-layer unit gap regenerator | Simon's “splash the gap” question has an exact answer in the smallest surviving ISA.  Given any three positive branch lengths and `D>=1`, choose `A,B,z,B_2,C` so `3^qA+s=2^pC+2^(p+L)B` and `B+3^qz=2^D B_2`.  Then `h=A+2^(p+L)(z+2^D u)` maps to `h'=C+2^(L+D)(B_2+3^q u)`: `A` emits the complete valuation-exact next instruction `C`, the sacrificial `D`-bit word `z` eats the carry `B`, and the remote tail survives affinely beyond a regenerated `D`-bit zero gap.  The exact artifact reconstructs 486 families across six compiled levels and replays 972 linked two-branch unit members for cell lengths `1..3` and gaps `1,4,12`.  This is a universal finite compiler identity plus bounded macro regression, not a self-supplying infinite stack or counterexample. | [`unit_gap_regenerator_audit.json`](experiments/kontorovich/unit_gap_regenerator_audit.json) |
| Formula-compressed regenerative carry glider | For the carry `B` isolated by a unit splash, set `r=v3(B)`, `D=ord_(3^(q-r))(2)`, and `z=B(2^D-1)/3^q`.  Exact arithmetic gives `B+3^qz=2^D B`, so the sacrificial word consumes the dirty carry, creates `D` clean bits, and reproduces the identical carry remotely.  The verifier embeds the canonical `(1,1,1)` header family in the true invariant register at all six compiled levels, proves the concrete multiplicative orders and three register phases without expanding `2^D`, and obtains gap-length integers with `8,28,90,297,979,3231` decimal digits.  This is a finite spatial glider cell, not an infinite rail or self-writing end cap. | [`unit_carry_repetend_audit.json`](experiments/kontorovich/unit_carry_repetend_audit.json) |
| Formula-compressed strike--scrub--turnaround | In the sign-negative level-two unit ISA, `B=1`, `H=17`, and `D=2*3^56` make the next legal division `P=D+2`.  Exact ternary lifting computes an even following-length class modulo `2*3^113`; `H=1 (mod 8)` puts the formula-compressed power-of-three turnaround in an even class modulo `2^(P-1)`, so parity-compatible CRT gives a finite ordinary length.  The third collision returns `h_out=R+2*M*3^(q(l)+114)w`, an exact writer for every prescribed finite odd dyadic word.  The artifact checks the explicit discrete log, exponent classes, register/CRT conditions, and writer algebra without expanding the giant length.  This is a universal finite reseed interface, not an autonomous infinite tail or counterexample. | [`unit_carry_turnaround_audit.json`](experiments/kontorovich/unit_carry_turnaround_audit.json) |
| Legal returning macro and quine equation | The corrected level-two route is `1 -> 1 -> g -> g -> 1`.  With `P=23g+54`, `Q=17g+40`, it composes exactly to `3^(114+2Q)h-C_g=2^(154+2P)h'`, with the four-term mixed-base constant displayed in the strategy map.  The verifier literally checks all four source/target-compatible valuations and the outward affine lift for `g=1..16`, then exposes the actual autonomous gate `3^R(g)F(g)-C_g=2^S(g)F(f(g))`.  It also gives an exact all-degree Laurent-polynomial obstruction for the successor ansatz.  This is a reproduction interface and a narrowed failure, not a solution or counterexample. | [`unit_return_quine_audit.json`](experiments/kontorovich/unit_return_quine_audit.json) |
| Formula-generated nonlinear repetend splash | If `2^T C=s (mod 3^q)`, the ordinary repetend `R=(2^T C-s)/3^q` gives `R+2^(T+D)K -> C+2^D 3^qK` under the unit collision.  Intersecting the discrete-log class of `T` with `T=p(n')` produces a genuine enormous target length.  Exact modular certificates construct this at all six finite levels from source length one and gaps `D=1,64`; they verify the order `ord_(3^q)(2)=2*3^(q-1)`, exponent CRT, repetend integrality, and both register phases without expanding `2^T`.  Level one uses `C=5`, `T=105,734,623`, and `n'=13,216,826`; its low rail alone is about 31.8 million decimal digits.  Across levels the target exponents have `9,29,91,299,980,3235` decimal digits.  This is a short generator for one vast nonlinear splash, not renewal or nontermination. | [`unit_repetend_splash_audit.json`](experiments/kontorovich/unit_repetend_splash_audit.json) |
| Two consecutive sign-negative repetend splashes | At level two, put `c_m=(2^(3^(m-1))+1)/3^m`.  Exact cubing gives `c_(m+1)=c_m-3^m c_m^2+3^(2m-1)c_m^3`, so `c_m` stabilizes modulo every fixed `3^P`.  At precision `P=q_0+v_3(M)=90`, a 45-digit odd `k` makes `T_1=3^(q_1-1)k` both retain the first ternary bank and lie in the affine target-exponent class.  This yields the exact unbounded family `h_0 -> R_1+2^(T_1+D)3^q0 L -> 1+2^D3^(q0+q1)L`, with both enormous valuations exact.  The audit checks 89 quotient recurrences, bridge integrality, exponent congruence, and all three unit-register phases for `D=1,64`, without materializing `T_1`; `T_1` itself has about `7.57*10^27` decimal digits.  This is genuine one-time renewal, not a third splash or infinite ordinary orbit. | [`unit_double_repetend_audit.json`](experiments/kontorovich/unit_double_repetend_audit.json) |
| Repetend energy separator | The same exact construction closes its own naive infinite continuation.  Every sign-negative marker-one exponent is an odd multiple of `3^(q-1)`.  For `q>=3`, elementary integer inequalities give `2^T>2*3^q`, so each such collision more than halves the positive odd core.  No fixed positive core supports infinitely many consecutive events.  The artifact audits the actual exponent classes at finite levels `2,4,6`; the general proof is symbolic.  A viable delay-line program must recharge between giant erasures, not stack them back-to-back. | [`unit_repetend_energy_audit.json`](experiments/kontorovich/unit_repetend_energy_audit.json) |
| Autonomous `-5` charge--discharge register | Pairing a length-`N` sign-negative level-two unit instruction with the one-cell instruction gives fixed debris `3^57+2^77=5D`.  The divisor `D=314038802961906688057474567` is coprime to the register stride, so one exact packet class can be divided by `D` and is preserved.  The quotient ISA is `G=2^(23N+3)g -> (3^(17N+97)g-5)/2^128`; every branch is strictly outward because `3^(17N+97)>2^(23N+131)`.  The artifact constructs branches `N=1..32` twice—directly by CRT and by restricted composition—and checks 128 members through 256 actual unit-macro replays.  An infinite successful positive orbit would refute Collatz; none is supplied. | [`unit_charge_discharge_audit.json`](experiments/kontorovich/unit_charge_discharge_audit.json) |
| All-depth self-regenerating `-5` splash | Composing any depth-`j` charge branch with its one-cell branch, then quotienting by `D_j=3^(114*2^j)+2^(154*2^j)`, reproduces collision constant `-5` with offsets `d_(j+1)=2d_j+17`, `e_(j+1)=2e_j+26`.  Coprimality with the fixed 80-bit stride holds for every `j`: a failed prime would require `2^(j+1)<M`, so only `j=0..78` can fail, and all 79 exact gcds are one.  The artifact materializes eight levels, compares 64 direct/composed branches, checks 128 members, and recursively expands canonical members through 510 original unit macros.  Infinite nesting is not a seed because every positive child lift strictly enlarges its ancestor packet; fixed-level autonomous orbits remain open. | [`unit_charge_hierarchy_audit.json`](experiments/kontorovich/unit_charge_hierarchy_audit.json) |
| Autonomous reversible fixed-form valuation bouncer | The rational one-cell fixed point clears integrally: with `F=(3^114-2^154)/5` and `Z=F*G-2^26`, one background cell is exactly `2^154 Z'=3^114 Z`.  At a defect boundary `Z=2^26y`, the normalized coordinate reads `m=v2(y+1)/23` and `h=(v2(3^(17m)(y+1)-2^(23m))-23m)/154`, then returns `y'=3^(114h)*oddpart(3^(17m)(y+1)-2^(23m))`.  The output recovers `h=v3(y')/114`, then `m=v3(1+2^(154h)q)/17` and the unique predecessor; the opcode matrix has determinant four.  The arithmetic artifact checks all 64 `(m,h,m')` families with `m,m'<=4,h<=4`, 128 forward/reverse members, 320 charge macros, and 640 unit-macro replays.  `y` is not itself the odd Collatz state; an infinite accepted ray refutes Collatz only through the separate semantic compiler.  None is supplied. | [`unit_charge_bouncer_audit.json`](experiments/kontorovich/unit_charge_bouncer_audit.json) |
| Canonical public-cofactor transducer | Every fixed-register state has unique normalized coordinates `y=D^m(w_m+S*t)-1`, `S=2FM`.  Eliminating the collision quotient gives the exact branch `2^(154h+23m')t'=3^(114h+17m)t+kappa`, hence `t=rho+2^P u -> t'=sigma+3^Q u`.  Odd endpoint cofactors recover the exact normalized collision valuation and output, so this arithmetic interface has no hidden representation metadata.  Lean commit `5a9324b` proves coordinate uniqueness and equivalence with the arithmetic `ChargeBouncerStep` surrogate; commits `36d6633`/`afecb2c` expose the still-separate ordinary-state/`WordLegal` obligation.  The arithmetic artifact reconstructs all 27 branches with `m,h,m'<=3` and performs 54 forward/reverse formula replays.  It supplies no invariant tail language; the live target is a finite mixed-radix feedback which makes the written ternary-scaled tail decode its own next binary instruction. | [`ChargePublicCofactor.lean`](KontoroC/KontoroC/ChargePublicCofactor.lean), [`ChargePublicCofactorSemantics.lean`](KontoroC/KontoroC/ChargePublicCofactorSemantics.lean), [`unit_charge_public_cofactor_audit.json`](experiments/kontorovich/unit_charge_public_cofactor_audit.json), [closure doctrine](docs/notes/kontorovich-closure-principles.md) |
| Determinant-four resonant phase glider | The opcode shift `(m,h,m')->(m+2622k,h-391k,m'+2618k)` preserves both public-tail exponents `P,Q` while displacing the defect boundary by `4k`.  Parallel branches admit an integral public-tail conjugacy `E(t)=s*t+c` whenever `gcd(kappa_a,3^Q-2^P)|kappa_b`; the same equation automatically embeds the exact source cylinder.  The artifact reconstructs the first phase-down and phase-up cells, each with 21,330-digit coefficients, checks the conjugacy/cylinders coefficientwise, and performs eight arithmetic bouncer replays.  The cell survives, but commit `466e381` plus the external Väänänen--Wallisser theorem closes every fixed positive phase-up jump.  Commits `8b3d9f5`/`772a6e8` complete the period-three external-theorem obstruction and locate its period-four size failure.  Commit `772a6e8` also proves that bare words pay a nonzero typed chart tax and that an infinite rail of the one-cell conjugacies loses resonant separation.  The live target is a word-level chart crossing with a payload-carried turnaround, universal literal semantics, and an infinite orbit. | [`unit_charge_resonant_conjugacy_audit.json`](experiments/kontorovich/unit_charge_resonant_conjugacy_audit.json), [`ChargePhaseUpTheta.lean`](KontoroC/KontoroC/ChargePhaseUpTheta.lean), [`ChargePhaseUpPeriodicTheta.lean`](KontoroC/KontoroC/ChargePhaseUpPeriodicTheta.lean), [`ChargeTypedInterface.lean`](KontoroC/KontoroC/ChargeTypedInterface.lean), [phase-glider note](docs/notes/kontorovich-resonant-phase-glider.md) |
| Two-opcode phase-swap conjugacy, failed embedding, and direct finite links | The word family `W_r=[(r,h0,L-r),(L-r,h1,r+d)]` makes consecutive charts cross with boundary differences `(d,-d,d)`, so both composite gains are independent of `r`.  Lean commit `a05ca2e` proves this signed-area law and also that every exact two-step word still pays a negative typed tax.  The exact artifact constructs the smallest line `1->3->2`, `2->2->3`, `3->1->4`; both adjacent pairs have `P=423,Q=296`, gcd-one positive integral affine conjugacies, and exact nested cylinder faces.  Commit `3a6d285` proves that both conjugacy-selected next inputs strictly outrun the current outputs, so those parallel squares are not orbit links.  Separately, artifact version two constructs and replays the direct coprime handoff progressions `u=u0+2^423t`, `v=v0+3^296t`; these are fresh finite address selections, not conjugacies or closure.  Commit `cc09f1b` proves any nonnegative TI3 correction across these macros strictly grows.  No self-writing address, public `L->L'` turnaround, universal literal composition, ordinary infinite tail, or counterexample is supplied. | [`unit_charge_phase_swap_conjugacy.py`](experiments/kontorovich/unit_charge_phase_swap_conjugacy.py), [`unit_charge_phase_swap_conjugacy_audit.json`](experiments/kontorovich/unit_charge_phase_swap_conjugacy_audit.json), [`ChargePhaseSwap.lean`](KontoroC/KontoroC/ChargePhaseSwap.lean), [phase-glider note](docs/notes/kontorovich-resonant-phase-glider.md) |
| Bounded literal bouncer semantic compiler | The normalized coordinate descends canonically through charge packet, unit packet, level-two packet, level-one glider, and breakoff `k`; the final router conversion, not `k`, produces the literal odd Collatz state.  The fixed substitution grammar is `charge(N)->unit[N,1]`, `unit(N)->glider[1,2,1^N]`, `glider(N)->gate[E,H,E^N]`.  The exact artifact rebuilds all 54 members with `m,h,m'<=3`, expands 756 gliders and 4,968 breakoff macros, emits 14,057 accelerated instructions, and independently replays every valuation and endpoint by direct arithmetic; all tested literal endpoints grow.  This repairs the bounded semantic regression but is not the universal Lean composition theorem or an infinite ray. | [`unit_charge_semantic_compiler.py`](experiments/kontorovich/unit_charge_semantic_compiler.py), [`unit_charge_semantic_compiler_audit.json`](experiments/kontorovich/unit_charge_semantic_compiler_audit.json) |
| Perfect-23rd-power reproduction rail | Encoding the bouncer payload as `u=F*r^23` makes the output address self-similar because its binary cell base is `D=2^23`.  Lean commit `5fbacf5` kernel-checks the exact elimination and proves every accepted `h=1` transition would solve `3^15X^23-2^16Y^23=5`.  PARI/GP 2.15.4 checks the degree-23 polynomial irreducible, reports attached class number one, and returns the complete empty solution list; PARI documents that class-number-one fast results are unconditional.  Therefore the shortest-recharge rail is closed, with the final no-solution step trusted to PARI rather than Lean.  Higher recharge, corrected payloads, and the bouncer remain open. | [`ChargePowerQuine.lean`](KontoroC/KontoroC/ChargePowerQuine.lean), [`unit_charge_power_quine_thue.gp`](experiments/kontorovich/unit_charge_power_quine_thue.gp) |
| Recharge-23 determinant-four resonance | At `h=23`, exact arithmetic gives `A^23=3^4C^154` and `B^23=D^154`; the forcing is the 1,198-digit integer `G23=5 Phi_23(A,B)`.  Although the original three primes leave all classes, Lean's complete checks at `277,599,829,1151` reduce every uncorrected single perfect-power transition to `e=15`, `m=9 (mod 23)`, and `3^15X^23-Y^23=G23`.  The remaining global Thue equation is explicit and is running as detached Akdeniz service `kc-r23`; a multi-rail correction can change it and remains open. | [`ChargePowerResonance.lean`](KontoroC/KontoroC/ChargePowerResonance.lean), [`unit_charge_power_resonance_thue.gp`](experiments/kontorovich/unit_charge_power_resonance_thue.gp) |
| Public-state 23rd-power quine and hidden register | Encoding `y=s^23` makes every type-preserving recharge `h=23*ell` return the literal power `(A^ell*t)^23`.  Lean commit `4c56925` proves the `m=0 (mod 23)` no-go at `ell=1`; arbitrary positive `ell` is the same theorem after substituting `t'=B^(ell-1)t`.  Commit `f61f569` reduces every other class to a scaled norm equation, and `9f00894` retains exact valuation quotients in `w Q(s)=v Q(z)`, proves same-side cofactor gcd can contain no prime except 23, and exposes a residual congruence modulo `F`.  Commit `07352a9` checks the full elementary Roth bound and exponent-11 conversion; only the external finiteness theorem and sequence consumer remain. | [`ChargeStatePowerQuine.lean`](KontoroC/KontoroC/ChargeStatePowerQuine.lean), [`ChargeStatePowerRoth.lean`](KontoroC/KontoroC/ChargeStatePowerRoth.lean) |
| Writable nonlinear hidden-`F` instruction | Exact Taylor expansion and Hensel lifting turn the residual cofactor congruence into `B D^m' w'=B C^m w-5ell (mod F)`.  Since `5,B,C,D` are units modulo the 179-bit `F`, recharge length writes every desired first register digit; the audit synthesizes five targets, lifts collision balance through `F^3`, checks the explicit nonlinear second digit, and proves the visible register alone does not force `F^2`.  Lean commit `34e166b` kernel-checks the universal carry, geometric output, first-digit law, and unique recharge class.  This is a necessary `F`-adic transducer, not an accepted positive transition: exact collision valuation and ordinary realization remain open. | [`ChargeHiddenRegister.lean`](KontoroC/KontoroC/ChargeHiddenRegister.lean), [`unit_charge_hidden_register_audit.json`](experiments/kontorovich/unit_charge_hidden_register_audit.json) |
| Quadratic two-rail opcode interface | For `N_d(x,u)=x^2+d u^2`, both recharge scalings preserve type because `B^h` and `A^h` are squares.  Lean commits `2743350`/`90c9b6c` prove this and tie the collision equation to actual accepted semantics.  The new exact sieve shows `d=7` forces `95|m`, while `d=31` is the first squarefree `7 (mod 8)` candidate through 31 without an inert register prime and satisfies `C-D=7706^2+31*1407^2`.  Cancelling that norm gives `2^(23m+154h)r'=3^(17m+114g)r+H_m`.  One literal 184-to-193-digit accepted transition preserves `N_31` at input, quotient, and output, but its next collision valuation is `153` and cannot decode a recharge.  The exact artifact and independent Lean commit `4112267` verify the arithmetic and failure.  No two-step public recurrence, infinite orbit, or counterexample is claimed. | [`ChargeNormOpcode.lean`](KontoroC/KontoroC/ChargeNormOpcode.lean), [`unit_charge_norm_opcode_audit.json`](experiments/kontorovich/unit_charge_norm_opcode_audit.json), [closure doctrine](docs/notes/kontorovich-closure-principles.md) |
| Ordinary-ray extension-lift criterion | Lean commits `af1a934`/`ba121d9` prove that if nested dyadic compiler cylinders are realized by one ordinary natural, their extension residues are eventually zero.  Therefore nonzero residues at arbitrarily late scales exclude an ordinary realization.  This is a no-ray criterion for a proposed schedule, not a counterexample and not yet a theorem that the bouncer's residues are frequently nonzero. | [`DispatcherBoundary.lean`](KontoroC/KontoroC/DispatcherBoundary.lean) |
| Constant-rate unit-counter schedules | For any of the six certified unit levels, every `n_0>=1`, and every fixed integer `k>=1`, the schedule `n_t=n_0+kt` has the unique 2-adic initial core `-s*3^(-q(n_0)) F(2^(ak)/3^(ck),2^(p(n_0+k))/3^(q(n_0+k)))`.  Converting to Väänänen--Wallisser's `f_(3^(ck)/2^(ak))` is coefficientwise exact, and its argument simplifies to `alpha=2^(p(n_0))/3^(q(n_0))`.  Their 1989 theorem applies with `ell=1,sigma=0,p=2`; its size ratio is the same as for `k=1`, while `|3^(ck)/2^(ak)|_2=2^(ak)>1`.  The value is irrational in `Q_2`, so it cannot be an ordinary integer core.  The artifact's six linked eight-transition branch replays remain a finite `k=1` regression; the all-`k` conclusion is symbolic and theorem-dependent.  This closes every fixed positive step size, not nonlinear or packet-branching schedules. |
| Canonical ordinary base graph | The tail-zero specialization asks each gate to land literally on the next gate's least coefficient, so no further initial-address bits are consumed.  An exact exhaustive shape audit covers `q,q'=1..100,j=0..100`: only three of 1,010,000 shapes give normalized base-to-base links, and all three targets fail to regenerate another delay.  Seven additional hits are rejected as noncanonical aliases because their coefficient contains a whole factor of eight.  Every retained gate is literally replayed and every ordinary seed reaches `1`.  This is a scoped failure of the simplest stabilized-address counter, not evidence against nonzero evolved tails. |
| Standard schedule ruled out by a p-adic theorem | Lean commits `db0971c`/`806bf8c` reduce any infinite standard schedule to the sole `Q_2` value `U_5=-(23/3^8)F(2/3,2^13/3^9)`.  Commits `3fc63a6`/`08485d3` prove the all-coefficient and completed-sum identity `F=f_(3/2)(4096/6561)`, the exact Väänänen--Wallisser size inequality, preservation of irrationality under the nonzero scale, and the implication to no payload stream.  Their 1989 theorem supplies that irrationality externally.  This is a published-theorem application with a kernel-checked citation seam, not a reproof of the external theorem or a Collatz proof. |
| Exact finite `k`-word compiler | Python arbitrary-precision compilation and replay pass exhaustive complete-period regression for both classes modulo `6`, all words of length at most four with `1<=k_i<=4`; Kontorovich's `(1,1,2,2)` example gives seed `199`. Lean commit `63c3b3d` proves terminal congruence equivalent to all intermediate valuations, plus canonical existence, uniqueness, and endpoint stride. |
| Kernel cycle-disproof seam | `KontoroC.CycleArtifact.checkNontrivial=true` implies the literal negation of the ordinary Collatz conjecture. The package build and axiom audit pass; no nontrivial artifact is known. |
| Bounded composition search | All `3,447,691` positive-denominator compositions with `S<=22` were checked exactly. The only closure hits encode the trivial seed `1`; no nontrivial cycle was found within the bound. |
| Bounded morphic-program search | All `168` binary uniform prolongable morphisms of widths `2..4`, all `16` codings into `{1,2,3,4}`, and `20,224` bounded depth instances were checked exactly. No nontrivial cycle was found. |
| Parametric glider endpoint | Lean commit `2fc4459` proves that any supplied exact outward `MacroGlider` refutes Collatz, including the no-hidden-visit-to-`1` bridge. It supplies the checker endpoint, not a glider. |
| Periodic-itinerary obstruction | Lean commits `92b01ff`/`2f93df7` prove by an all-level coprime-divisibility argument that a positive eventually periodic valuation program is a cycle and that a supercritical repeated block cannot occur forever. |
| Ordinary-integer gate | Lean commit `ad36f08` proves `StreamLegal x k` iff the exact canonical prefix seeds eventually stabilize at `x` (in the fixed admissible mod-6 class). This validates the worker's stabilization diagnostic at the infinite level. |
| Separated-packet clock | Lean commit `121cb13` proves `ord_(2^(n+3))(3)=2^(n+1)` and exact residue scheduling corollaries. This certifies the delay-line clock, not a collision-renewal rule. |
| Negative-cycle shadow pilot | Exact Python checked `112,320` compiled paths for the `-5` and `-17` supercritical controllers through the bounds above. Every macrostep passed literal replay; no seed stabilization or next-level shadow renewal occurred. |
| Finite phase-changing carry renewal | Exact search found positive seed `53,403,857` with macro-states `53,403,857 -> 15,019,835 -> 2,376,185 -> 1,691,641 -> 1,354,843`, following `-7,-5,-7,-7` controller phases at levels `1..4`. Its canonical seed survives the fourth macro, but the endpoint misses every level-5 phase class. This verifies one finite renewal mechanism, not nontermination. |
| Finite outward Mersenne shadow | Exact seed `24,017,279` follows the signed `-1` controller at levels `7,8,9` with collision extras `(4,3,1)`, giving three strict macro increases `24,017,279 -> 25,647,359 -> 82,164,223 -> 1,579,334,395`. Its canonical seed stabilizes once, then misses level 10; exact continuation reaches `1` after 108 accelerated steps. |
| Two-extension constant-feedback event | For the constant rule `e_M=1`, exact seed `121` is canonical for depths two, three, and four, with macro-states `121 -> 91 -> 103 -> 175 -> 445`. Level five fails and the seed reaches `1` after 34 accelerated steps. This is the longest ordinary-seed stabilization found, but remains finite. |
| Kernel phase-shadow disproof seam | Lean commits `3d9cedc` through `d6fb8b2` prove the exact shifted-coordinate macro and the literal Collatz negation from any infinite bounded-extra renewal after an arbitrary finite prefix. Signed cycles automatically supply supercriticality and all rotated phases. No infinite renewal witness is known. |
| Kernel Mersenne-shadow seam | Lean commit `768f4d0` checks the signed `(-1,[1])` controller, proves the worker's exact Mersenne macro identity, and proves `MersenneShadowOrbit.not_conjecture` from infinite renewal data. It also kernel-replays the `24,017,279` event and its level-10 failure. |
| Pure packet-recurrence endpoint | Lean commits `32a0896`--`a2652f2` reduce a Mersenne disproof to positive odd packets and bounded extras satisfying `2^e(2^(m+1)h'-1)=3^m h-1` at every level. Lean derives exact legality, transitions, eventual packet growth, the unique necessary class of `h' mod 3^m`, and the literal Collatz refutation. |
| Seven-renewal state-dependent motif | Exact seed `30,603,607,965` has extras `(2,1,3,2,2,2,1)` and seven renewed Mersenne packet levels; its final four macrosteps grow and end at `318,374,253,823`. The eighth renewal fails, and exact continuation reaches `1` after 152 accelerated steps. |
| Independent packet-census replication | PSC H100 job `42500602` independently re-enumerated all `2^35` odd packets `h<2^36`. It reproduced the RTX 4090 run's zero-overflow counter, maximum renewal length seven, and all 243 stored `(initial h, length, extras)` triples exactly; both artifacts pass the Python big-integer verifier. This corroborates the inner census but does not enlarge its bound. |

The compiler and certificate seam is now live.  The dependency-free
[`path_compiler.py`](experiments/kontorovich/path_compiler.py) reproduces the
thread's `(1,1,2,2) -> 199` example, compiles both Kontorovich--Sinai seed
progressions, and replays every valuation with arbitrary-precision integers.
Lean commit `63c3b3d` independently proves that the compiler's final
congruence is equivalent to every intermediate exact valuation and proves the
canonical representative, progression uniqueness, and endpoint stride.  The
[`KontoroC/`](KontoroC/README.md) package also proves that a valid nontrivial
cycle artifact refutes the literal ordinary Collatz conjecture.  No such
artifact has been found.

The first bounded adversarial sweep tested all `3,447,691` positive-
denominator valuation compositions with total halving count at most `22`.
Only the eleven bounded repetitions of the seed-`1` trivial cycle closed.  A
separate low-description sweep tested `168` binary uniform morphisms of widths
two through four, all `16` codings by valuations in `{1,2,3,4}`, and `20,224`
depth instances through expanded length `16,384`.  Its `1,960` closure hits
are again all seed `1`; there is no nontrivial cycle in this stated template
class.  Seed stabilization was checked separately through length `512`.  Its
longest `1`-avoiding event is the length-nine prefix of seed `107`, which
exact continuation sends to `1` after `36` accelerated steps.  These are exact
bounded exclusions of small program classes, not a new global verification
bound and not evidence of convergence.

A kernel-checked theorem also closes the most literal glider: if one fixed
nonempty `k`-block repeats forever on a positive orbit, divisibility by
arbitrarily high powers of `2^sum(k)` forces the block endpoint to equal its
start.  Thus an eventually periodic valuation program is a cycle, not a
growing glider; a supercritical repeated block has only a negative 2-adic
seed.  Lean commits `92b01ff`/`2f93df7` prove the all-level statement and its
eventual-tail and sign corollaries.  The active search therefore moves to
aperiodic one-counter and recursively nested templates.
See [`docs/notes/kontorovich-program-synthesis.md`](docs/notes/kontorovich-program-synthesis.md)
for the exact algebra, bounds, result digest, and next attacks.

## Project guides

The front page is the state-of-the-project map.  These are the other README
entry points, grouped by role:

| Guide | Scope |
|---|---|
| [`NEW_RESUME.md`](NEW_RESUME.md) | Current Kontorovich handoff: semantic compiler, live theorem seams, remote jobs, and safe continuation order. |
| [`docs/notes/kontorovich-closure-principles.md`](docs/notes/kontorovich-closure-principles.md) | Fundamental closure laws, public-cofactor language, opcode algebra, semantic descent, and theorem-shaped search criteria. |
| [`docs/notes/kontorovich-resonant-phase-glider.md`](docs/notes/kontorovich-resonant-phase-glider.md) | Determinant-four opcode conjugacies, exact phase-up/down cells, and the remaining telescoping/ordinary-address closure tests. |
| [`experiments/kontorovich/README.md`](experiments/kontorovich/README.md) | Exact finite `k`-word compiler, replayable cycle artifacts, and bounded morphic-glider searches. |
| [`docs/notes/kontorovich-delocalized-isa.md`](docs/notes/kontorovich-delocalized-isa.md) | Simon's nonlocal-instruction hypothesis, exact packet gates, ultra-small-language encodings, and the formula-bouncer attack. |
| [`KontoroC/README.md`](KontoroC/README.md) | Independent Lean checker connecting a nontrivial accelerated cycle artifact to the ordinary Collatz conjecture. |
| [`CLEAN_LEAN/README.md`](CLEAN_LEAN/README.md) | Main Lean 4 formalization, build instructions, theorem inventory, and trust boundary. |
| [`formal/README.md`](formal/README.md) | Small original Lean scaffold: definitions, descent reduction, and a bounded `native_decide` check. |
| [`experiments/cycles/README.md`](experiments/cycles/README.md) | Finite-place obstruction tests for hypothetical Collatz cycles; calibrated negative verdict. |
| [`experiments/expsum/README.md`](experiments/expsum/README.md) | Transfer-matrix counts and floating spectral diagnostics at the cycle modulus. |
| [`experiments/modknots/README.md`](experiments/modknots/README.md) | Modular-knot/Ghys probe: the linear invariant collapses; the quadratic linking probe is unresolved. |
| [`experiments/dfacert/README.md`](experiments/dfacert/README.md) | Exhaustive base-2 regular divergence-certificate search, completed through eight states. |
| [`experiments/dfacert3/README.md`](experiments/dfacert3/README.md) | Independent base-3 regular divergence-certificate search, completed through five states. |
| [`experiments/wfar/README.md`](experiments/wfar/README.md) | Weighted finite-automaton/arctic certificate framework and soundness conditions. |
| [`experiments/family/README.md`](experiments/family/README.md) | Fate census for families of generalized Collatz maps. |
| [`experiments/gpu/README.md`](experiments/gpu/README.md) | Audited CUDA ports of the family and exponential-sum tools. |

The formalizer's final synchronized restart note is
[`CLEAN_LEAN/CLEAN_LEAN_RESUME.md`](CLEAN_LEAN/CLEAN_LEAN_RESUME.md).

The KL certificate directory has no separate README.  Its principal landing
pages are [`experiments/kl/RESULT.md`](experiments/kl/RESULT.md) and
[`experiments/kl/TERMINATION_AUDIT.md`](experiments/kl/TERMINATION_AUDIT.md).
The theoretical index is [`docs/STRATEGY.md`](docs/STRATEGY.md); individual
claims and failures live under [`docs/notes/`](docs/notes/).

## Proof boundary at the pause

The program now has two deliberately separate targets.  The ambitious one is
the conjecture itself: exclude both a nontrivial positive cycle and an
injective positive orbit escaping to infinity.  The quantitative one is
`λ_∞=2` for the Krasikov–Lagarias (KL) predecessor-counting systems. It would imply
`π_a(x)≥x^(1−ε)` for every `ε>0`. The finite bridge is complete: a mixed
exact-Python/kernel-Lean chain transfers the `k=19` certificate to the current
predecessor-count exponent, the `k=12` record is fully Lean-native, and Lean
constructs an infinite strictly increasing feasible ladder. What remains is a
dimension-free rate; strict growth by itself can converge below two.  Commit
`da029d4` also closes the conditional composition from a supplied positive
exact fixed tower and its gain estimate all the way to almost-linear counting.
It does not construct that tower or prove the estimate.

The distinction matters: even `λ_∞=2` would not prove Collatz.  We are now
using the KL tower as one input to full-proof interfaces, not treating its
endpoint as the finish line.  The first such interface cuts the inverse tree
into pairwise disjoint side bushes along any hypothetical divergent forward
spine.  Combining their disjointness with the explicit KL target bound gives
a weighted Carleson/capacity inequality.  This is a genuine constraint on a
counterexample, but present exponents make its certified load tiny and even a
linear endpoint would still need an arithmetic theorem preventing exponential
escape.  See `docs/notes/side-bush-capacity.md`.

In parallel, `docs/notes/thin-connection-atlas.md` works outward through
literatures not selected for mentioning Collatz.  Its most concrete junction
is a branched cyclic-voltage/character decomposition of the KL refinement;
its most ambitious forward-orbit junction is the adelic Poisson boundary of
rational affine products.  For cycles, the existing cycle-modulus exponential-
sum lane and compatible closed walks through the ramified residue tower remain
the only current mechanisms aimed at outright exclusion rather than another
density statement.  Every one of these is a program or kill test, not a proof.

The cleanest strong conjecture is the selected quadratic coarse-minimum law

```text
epsilon_(j+1) >= epsilon_j+(3/2)epsilon_j^2
```

It holds by exact arithmetic at every available stage of the selected
`k=12,...,19` records. It is false on the generic feasible cone. Lean commit
`38f1497` proves that an all-level selected-critical version would telescope to
`λ_∞=2`; it does not prove the selected law.  Uniform gain at every depth is
stronger than the endpoint actually needs.  Lean commit `4419b30` accepts
structurally chosen, increasing precision checkpoints with nonnegative net
coefficients `a_i`, as long as

```text
sum_i a_i/(1+a_i) -> infinity.
```

In the finest-to-coarsest convention used by the exact scripts, a checkpoint
gain is

```text
epsilon_(t_(i+1)) >= epsilon_(t_i)+a_i epsilon_(t_i)^2.
```

It also checks the exact bound
`epsilon_n <= 1/(1+sum_(j<n) a_j/(1+a_j))`.  The best current target is
therefore an amortized selected-pressure theorem; the observed uniform
coefficient `3/2` is a particularly clean sufficient case, not the minimal
obligation.

Three formulations sharpen that missing theorem:

- The defect is a three-way Doeblin overlap. Generic channel contraction is
  exponentially too weak, but a renewal-min-constrained Doeblin curve—or the
  equivalent weighted anti-alignment of endogenous argmin labels—would supply
  the observed quadratic gain. The finite frustration lower bound already
  clears the first-stage target on `k=12,...,15`.  A generic three-edge
  holonomy forces a label mismatch away from tie walls, but the spatial
  `5->2->8` transport orbit at one precision is not a block of three coarse
  projections.  The missing bridge must aggregate within-level frustration
  into cross-depth gain, possibly through a compensating tie-wall potential.
- Information geometry identifies the exact local quantity more sharply.
  Direct `D_KL`, Jeffreys, Jensen--Shannon, and Hellinger comparisons of the
  two conditional triples have the wrong zero set.  Projection by `D_KL` onto
  the shared-minimizer cone has the right zero set but is quadratically small
  near tie walls.  The hard mismatch itself is the zero-temperature rate of
  an order-dependent Rényi divergence between residual-cost Gibbs escorts,
  with uniform rowwise error `log(3)/beta`; Lean commits `8c3e1df`--`9ff6d64`
  check the two-copy, multiway, and literal-overlap cold-limit sandwiches.  An
  explicit slowly rotating family shows why local
  simplex geometry alone cannot yield global coercivity.
- For the homogeneous power means, `F_min≤F_(-β)≤3^(1/β)F_min` uniformly in
  the level. Power-mean projection also proves that `ρ_(k,λ,p)` is increasing
  in `k` and bounded by the annealed value `s(λ)`, so its fixed-temperature
  limit exists. It would therefore suffice to identify that limit with `s(λ)`
  for every fixed `λ<2` and finite `p<0`, choosing
  `−p>log(3)/log(s(λ))`. Near-tie selector spikes drift to colder scales, so
  uniform eigenvector regularity is neither assumed nor presently credible.

The same-policy defect audit found genuine recurrent split/merge dynamics, not
an annealed artifact. Its natural carry/policy quotient nevertheless refines
to essentially the full Jacobian, so it is a diagnostic rather than a compact
finite-state invariant. A selected mean-defect plus anti-concentration theorem
and the older expanding-window cones remain secondary endpoint routes.  A
bounded-history predictive-memory follow-up also failed its exact blocked
controls and is closed rather than promoted to an epsilon-machine claim. The
detailed evidence, counterexamples, and live kill tests are in the strategy
map and linked notes below.

None of these statements settles Collatz, positive density, divergence, or
nontrivial cycles. The predecessor result counts preimages of a fixed `a`; even
an `x^{1−ε}` lower bound is sublinear for each fixed `ε` and by itself gives no
positive-density conclusion.

## Headline results (with verification scope)

| Result | Status |
|---|---|
| Exact `k=19` KL threshold `γ₀=log₂(18783127/10⁷)=0.9094372617…` (all fixed `γ<γ₀`) | The SHA-pinned 2.9 GB sidecar passes all 387,420,489 exact inequalities. Lean commits through `76ec861` replace two false printed steps and prove the generic transfer to `π_a(X)≥X^γ` eventually for every eligible fixed target and every `γ<γ₀`. This is a mixed exact-Python/kernel-Lean chain; the large record is not one Lean-native theorem and a fresh clone is self-contained through `k=15`. See `experiments/kl/RESULT.md` and `experiments/kl/TERMINATION_AUDIT.md`. |
| Fully Lean-native `k=12` counting checkpoint | Commits `4c7fcc3`/`659dc81` kernel-reduce all 177,147 feasibility rows, pin the generator/source provenance, and prove `HasPredecessorExponent a (log₂(18064231/10^7))` for every eligible target. The audited build uses no `sorry`, `native_decide`, or project axiom. |
| Strict existential improvement and infinite feasible ladder | `78602d4` proves that every positive feasible point below two lifts to a strictly larger feasible parameter at the next level. `882a00e`/`9323f26` specialize this to `k=12` and produce an existential predecessor exponent strictly above the Lean-native decimal. The gain is non-numerical and may be exponentially small, so this is not `λ_∞=2`. |
| Coarse-minimum/defect package and conditional counting endpoint | `5a8727f`/`786c02e` prove coarse-minimum order and defect data processing; `ee37cd9`/`27b9e69` expose the exact rowwise mismatch and one-stage canonical frustration seam; `d4b328b` retains inherited supersolution slack. Commits `ca0a6e9`/`e2723e2` isolate the exact all-stage normalized and rowwise slack-gain premises. Exact selected `k=12,...,19` data obey `ε_(j+1)≥ε_j+(3/2)ε_j²`, while an exact feasible `k=3` counterexample rules out a cone-wide theorem. `38f1497` proves the conditional endpoint, `da029d4` composes it to literal almost-linear predecessor counting, and `4419b30` weakens uniform gain to divergent effective intermittent or checkpoint gain. The theorems still assume a positive exact fixed tower, all mass/defect side conditions, and the gain; the certificate records are feasible subeigenvectors, not instances of that tower. See `docs/notes/coarse-minimum-gap.md`. |
| Information-geometric selected defect | For each carry-aligned transport/branch fiber pair, the local hard slack is the zero-temperature order-θ Rényi separation rate of two residual-cost escorts, uniformly within `log(3)/β`; Lean commits `8c3e1df`--`9ff6d64` check the scalar, multiway, and literal-overlap forms. A `D_KL` projection onto the union of common-minimizer order cones has the exact zero set and satisfies `(3/4)J²≤I≤log(3)J`, but on `k=12,...,14` it is only `3.45%,3.18%,2.98%` of the quadratic target. An exact slowly rotating family has macroscopic fiber defect and vanishing information production, so a selected carry/branch rigidity theorem is still essential. See `docs/notes/information-geometric-defect.md`. |
| Uniform zero-temperature control and an exact soft-to-hard bridge | For `p=-β`, `F_min≤F_p≤3^(1/β)F_min`; for every fixed `p<1`, power-mean projection proves `ρ_(k-1,λ,p)≤ρ_(k,λ,p)≤s(λ)`, so the fixed-temperature limit exists. Lean commit `4419b30` checks the literal normalized ternary cold mean, replaces only the KL branch-fiber minimum, retains transport, and turns any positive soft subeigenpair `r*x≤F_β(x)` with `3^(1/β)<r` into exact hard feasibility and, along arbitrary witness levels tending to parameter two, almost-linear counting. It does not construct those subeigenvectors or prove fixed-temperature saturation. The two-copy carry audit also closes generic unweighted `L²` contraction; selected/on-code cancellation remains open. See `docs/notes/softmin-replica.md` and `docs/notes/softmin-pair-carry.md`. |
| Forward-orbit side-bush capacity | Along an injective Syracuse spine, the inverse basins attached at the odd-step side targets `b_j=6n_j+2` are pairwise disjoint. Lean commits `b47aa31`/`3577b8f` package the side-target identities, disjoint packing, explicit all-`X` KL lower bound, and normalized combined capacity inequality; the full audit and a separate SHA-pinned exact checker pass. The current numerical load is tiny, so this is a new full-proof interface, not a proof of divergence exclusion. See `docs/notes/side-bush-capacity.md`. |
| Critical base-`3/2` span capacity | The rational-base span is `σ(n)=H(n+1)-H(n)` for a bounded-displacement coordinate satisfying `H(ceil(3n/2))=(3/2)H(n)`. Exact all-level consequences include interval discrepancy at most one, `σ(2n)≥(2/3)K(3)`, and inverse-capacity ratio at least `2/3` (at least `4/3` in residue class two). An independently audited depth-96 checker passes. Explicit exponentially small spans and a telescoping cycle Jacobian kill scalar-Lyapunov and hyperbolicity proofs; only a long-range capacity anti-correlation route survives. See `docs/notes/rational-span-cocycle.md`. |

Other checked results include the exact oscillation identity, the annealed
critical coding and renewal algebra, local renormalization at `−1`, the
Diaconis–Fulman multiplication-carries spectrum, the Mahler/Cartier and
two-base exclusions, Antihydra rarity, exhaustive small-DFA exclusions, the
tree-product Collapse Lemma, and the solenoid Traceless Theorem. Their scopes
and artifacts are indexed below and in `docs/notes/`.

## Strategy and failure map

The chronological record is in [`docs/STRATEGY.md`](docs/STRATEGY.md), with
derivations and exact commands under [`docs/notes/`](docs/notes/).  The finite
KL counting foundation is complete.  The unportable 2.9 GB `k=19` sidecar is
an engineering caveat, not an unproved mathematical premise.

### Surviving proof programs

- **Exclude divergent orbits.**  Combine the exact side-bush packing with the
  critical base-`3/2` span capacity or a product-of-places boundary theorem.
  The missing assertion must control one feedback-selected arithmetic orbit,
  not almost every random affine product.
- **Exclude nontrivial cycles.**  Couple compatible closed walks in the
  ramified ternary refinement tower to the cycle-modulus exponential sums.
  A useful invariant must see more than `(K,L)`.
- **Reach the KL endpoint by hard-min pressure.**  Supply the positive exact
  selected tower and a structural intermittent/checkpoint gain whose effective
  sum diverges.  All downstream telescoping and counting transfer is checked.
- **Reach it by finite temperature.**  Prove fixed-temperature saturation or
  certify positive soft subeigenvectors with factor above `3^(1/beta)` along
  parameters tending to two.  The literal soft-to-hard consumer is checked.
- **Bypass selection entirely.**  Construct exact feasible witnesses at
  arbitrary cofinal levels with parameters tending to two.

The first two are full-Collatz programs.  The last three can at most prove
almost-linear predecessor counting and require a separate no-escape argument.

### Compact failure ledger

| Route | Calibrated verdict | Where to inspect |
|---|---|---|
| Printed KL advanced elimination | Invalid as stated: exact paths break the history-free deletion, nonempty-minimum, and split-invariant steps. The occurrence-aware replacement and counting transfer are kernel-checked, so the finite certificate consequence survives. | [Termination audit](experiments/kl/TERMINATION_AUDIT.md) |
| Printed KL equation (2.1) | False as an equality: `phi^7_2(1)=3` while `phi^14_2(0)=2`. A targetwise one-sided repair gives the required lower-bound direction and is checked in Lean. | [Exact obstruction](experiments/kl/verify_equation_2_1_obstruction.py) |
| Autonomous charged/projective contraction | Structurally closed for every tested admissible window: the `-1` co-spine supplies a marginal mode. This rules out the certificate class, not `lambda_infinity=2`. | [Kill tests](docs/notes/cl-killtests.md) |
| Uniform unweighted shell `L2` contraction | Closed by amenable almost-invariant modes and an exact expanding detail witness. Selected/on-code signed cancellation remains possible. | [Pair-carry note](docs/notes/softmin-pair-carry.md) |
| Generic local information coercivity | Closed: standard divergences have the wrong hard zero set, and a slowly rotating tie-wall family has macroscopic defect with vanishing production. A selected holonomy theorem remains open. | [Information defect](docs/notes/information-geometric-defect.md) |
| Natural finite defect automaton | Closed at the tested quotient: carry/policy refinement recovers essentially the full `k=12` Jacobian. | [Defect automaton](docs/notes/same-policy-defect-automaton.md) |
| Growing bounded-summary predictive memory | Negative at the exact `k=12` checkpoint: next-edge gain is exactly zero and every longer-history gain is negative under origin-digit blocked holdout. | [Exact diagnostic](experiments/kl/diagnose_active_path_memory.py) |
| Pointwise pressure split `U(21/50)` | Refuted on an exact `k=19` feasible record by ratio `0.542601...>0.42`. Rare violations leave mass-weighted or selected-critical statements open. | [Genealogy note](docs/notes/multiscale-genealogy.md) |
| Cone-wide coarse-minimum or entropy monotonicity | Refuted by exact positive feasible `k=3` counterexamples. Any endpoint theorem must retain selected critical or vanishing-slack structure. | [Coarse-minimum note](docs/notes/coarse-minimum-gap.md) |
| Fitted geometric localization envelopes | Closed as all-level critical/vanishing-slack laws by exact low-depth annealed floors. Polynomial or direct selected-family control remains open. | [Terminal statistics](docs/notes/terminal-defect-statistics.md) |
| Global collision growth implies local Pearson decay | False for an audited sparse product law; a separate exact detail mode also expands. Renewal plus positive defect support is insufficient without the nonlinear minimum coupling. | [Annealed coding](docs/notes/annealed-critical-coding.md) |
| Finite-place and finite-state full-proof certificates | Cycle finite-place tests collapse to existing Baker information; exhaustive regular divergence searches find none through eight base-2 or five base-3 states. These are scoped exclusions, not evidence of convergence. | [Cycle tests](experiments/cycles/README.md), [base 2](experiments/dfacert/README.md), [base 3](experiments/dfacert3/README.md) |
| Ordinary linear resolvent / one-certificate-away framing | Retracted. The KL threshold is nonlinear and no ordinary-pole counting bridge was supplied; the autonomous certificate sought earlier cannot exist in its proposed class. | [Analytic-combinatorics audit](docs/notes/analytic-combinatorics.md) |

Other negative probes—tree-product spectral gaps, tropical geometry proper,
ensemble continued-fraction thermodynamics, the first-circle solenoid boundary,
and the linear modular-knot invariant—remain documented in
[`docs/LANDSCAPE.md`](docs/LANDSCAPE.md) and their linked notes.  They should
not be revived on analogy alone.

### Formal boundary

[`CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md`](CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md)
and [`CLEAN_LEAN/AUDIT.md`](CLEAN_LEAN/AUDIT.md) are authoritative.  At the
pause, Lean checks the corrected finite counting chain, the native `k=12`
record, exact transport/Perron and coarse-minimum identities, side-bush
capacity, information-rate and holonomy interfaces, the intermittent hard-min
endpoint, and the literal soft-to-hard endpoint.  The full 8,784-job audit
reports only standard mathlib axioms and no project axiom, `sorry`, or
`admit`.

The standing frame is unchanged: `X^(1-epsilon)` predecessor counting would
be a substantial theorem, but not Collatz.  A full proof still needs both
no-divergence and no-nontrivial-cycle arguments.

## Status at the pause

Active exploration is paused at this checkpoint.  These bullets record the
last live seams and should not be read as background jobs still running.

- The exact iterated-minimum, translated-Doeblin, and `S_3` frustration views
  now isolate one missing amortized selected-pressure theorem. The local
  frustration lower bound clears the first-stage quadratic target on
  `k=12,...,15`, but only as finite exact data.  An application of spatial
  `5->2->8` holonomy would first need a theorem turning within-level mismatch
  into net gain across genuinely increasing precision checkpoints.
- The soft-min investigation found uniform zero-temperature control of values,
  a nonuniform near-tie boundary layer for selectors, and exact refinement
  monotonicity of the softened Perron radii. Their bounded limit exists; the
  stronger scalar target is to prove that it equals the annealed value.
  Floating Collatz--Wielandt diagnostics currently support this through `k=13`.
- The same-policy defect investigation is complete. It confirms real recurrent
  split/merge lineages, then rules out the natural bounded carry/policy quotient.
  The circuit probe is also complete at finite levels: the operator has a short
  output-linear uniform circuit, while selected policies at `k=12,...,15`
  defeat the tested OBDD, aligned-grammar, sparse-ANF, and tensor-train models.
  This is not a lower bound for unrestricted `poly(k)` coordinate circuits.
  The follow-up bounded-history predictive-memory probe also failed its exact
  blocked controls and is not a live lane.
- CLEAN_LEAN has closed the finite counting bridge, exact `k=12` import,
  transport/Perron identification, coarse-minimum order, strict feasible lift,
  the conditional quadratic telescope, the one-stage canonical frustration
  seam, inherited-slack bookkeeping, and the exact scalar/rowwise all-stage
  slack-gain interfaces. Commit `da029d4` closes the conditional composition
  from an exact positive fixed tower to literal almost-linear counting. Commit
  `174b16b` reduces nonlinear positive-eigenpair existence to a simplex fixed
  point; the pinned mathlib lacks Brouwer. Lean still does not construct the
  required fixed tower, prove the selected gain, localization, or a
  dimension-free endpoint rate.  Commit `4419b30` fully audits the weaker
  intermittent/checkpoint consumers and an independent literal soft-to-hard
  route.  The full build completed with 8,784 jobs and no project axiom,
  `sorry`, or `admit`; the reported headline axioms are only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Larger-record computation is deprioritized as a limit strategy. Scaling the
  Lean-native import beyond `k=12` remains an engineering task; the leading
  mathematical priority on restart is an all-level endpoint mechanism.

## Future directions

If the project resumes, the first two problems are the ones that could address
the full conjecture; the KL endpoint remains a substantial but strictly weaker
milestone.

1. **Turn capacity into a no-escape theorem.**  Combine the exact disjoint
   side-bush packing with the critical base-`3/2` span coordinate, and prove
   that one feedback-selected injective Syracuse spine cannot concentrate
   indefinitely on cells whose inverse capacity is summable.  The most
   ambitious candidate is a deterministic, product-of-places/adelic boundary
   statement.  A probabilistic theorem about typical rational affine products
   is not enough: the bridge must control one arithmetic orbit.
2. **Add a genuinely new obstruction to cycles.**  Relate compatible closed
   walks in the ramified ternary refinement tower to the cycle-modulus
   exponential sums.  The target must see more than `(K,L)` and beat the
   existing Baker/Steiner information; separate finite-level cycle counts,
   modular-knot length, and finite-place tests have already failed this test.
3. **Prove amortized selected pressure.**  For structurally chosen checkpoints
   `0=t_0<...<t_m`, prove
   `epsilon_(t_(i+1)) >= epsilon_(t_i)+a_i epsilon_(t_i)^2`, with `a_i>=0`
   and divergent `sum a_i/(1+a_i)`.  A plausible stronger statement is that
   each precision either produces quadratic slack or pays through a bounded
   tie-wall/second-gap potential.  The spatial `5->2->8` orbit must first be
   aggregated within a fixed precision; it is not itself a three-depth block.
   One must also supply the positive exact fixed tower/selection hypotheses
   that the current conditional endpoint consumes.

   A concrete literature-driven version is to Doob-transform the selected or
   softened active Jacobian and induce on branch-reset or defect/tie-wall
   states.  [Gouëzel](https://www.impan.pl/shop/publication/transaction/download/product/87253)
   and [Melbourne--Terhesiu](https://arxiv.org/abs/1008.4113) suggest a marked
   first-return equation for accumulated mismatch, while
   [Kombrink](https://arxiv.org/abs/1512.08351) and
   [Kesseböhmer--Kombrink](https://arxiv.org/abs/1604.08252) permit
   past-dependent or countable symbolic return words.  The literal neutral
   section `m=5 (mod 9)` has the pure-transport
   return `5->2->8->5`, so a marked return encounters both branch types while
   retaining the ramified sheet action.  Twist the return operator by
   carry/minimizer holonomy and ask whether compulsory charged returns produce
   a uniform reward.  The kill tests are
   selected-policy self-consistency, decaying cylinder variation, summable
   excursion weights, finite irreducibility/aperiodicity, and a spectral/reward
   bound uniform as `beta->infinity` and `lambda->2`.  The existing annealed
   run law is geometric, so the infinite-measure theorems do not apply
   directly; without those tests this would only repackage the annealed
   surrogate.
4. **Try the orthogonal soft-to-hard route.**  Prove fixed-temperature spectral
   saturation, or construct positive soft subeigenvectors whose factor beats
   `3^(1/beta)`.  Commit `4419b30` checks the exact branch-only soft operator,
   hard comparison, sparse-level feasibility transfer, and final counting
   consumer.  The surviving analytic input is finite-temperature saturation
   or certified soft subeigenvectors crossing that factor; selector regularity
   is not available, and the two-copy fallback is selected/on-code signed
   cancellation.
5. **Search for a cofinal exact feasible ansatz.**  Exact feasible witnesses at
   arbitrary levels with parameters tending to two bypass fixed-vector
   selection, Brouwer, tie walls, and the entire coarse-minimum pressure route.
   The tested OBDD, aligned grammar, sparse ANF, and tensor-train models failed,
   so a restart should demand a genuinely different symbolic coordinate
   representation rather than another fit to the same finite policies.
6. **Keep formal and engineering work attached to a live premise.**  The two
   downstream endpoint interfaces are now audited.  Formalize a new theorem
   only when it supplies one of their missing structural inputs, and develop a
   streamed representation only if higher certificate imports become
   necessary.  More finite levels or unrestricted local information
   inequalities are low priority unless they discriminate between the
   mechanisms above.

Do not restart the bounded predictive-memory, natural finite defect-automaton,
generic local information-coercivity, or uniform unweighted shell-`L2` lanes
without a new hypothesis that directly evades the recorded counterexamples.

## Verification discipline

Nothing is a result until: exact arithmetic or kernel-checked proof, plus
independent re-derivation (agent vs sol vs data) where feasible, plus
adversarial external review for anything load-bearing. The errata are public:
`SMELL.md` header, `fiber-geometry.md` v2. Corrections to date have come
from both directions (external review killed our Prop R; we killed a stale
preprint alarm and two prescribed-claim errors were corrected by our own
agents' proofs).

## Repository map

The main navigation links are in [Project guides](#project-guides).  For the
research record, see [`docs/STRATEGY.md`](docs/STRATEGY.md),
[`docs/LANDSCAPE.md`](docs/LANDSCAPE.md), [`docs/CRACKS.md`](docs/CRACKS.md),
[`docs/SMELL.md`](docs/SMELL.md),
[`docs/REVERSE-MINING.md`](docs/REVERSE-MINING.md), and
[`docs/CRYPTIDS.md`](docs/CRYPTIDS.md).  The Lean-facing snapshot and trust
ledger are [`CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md`](CLEAN_LEAN/MAIN_AGENT_LEAN_REVIEW.md)
and [`CLEAN_LEAN/AUDIT.md`](CLEAN_LEAN/AUDIT.md).  Data provenance is indexed
by [`DATA.md`](DATA.md), and literature by
[`papers/REFERENCES.md`](papers/REFERENCES.md).

## Credit and mathematical inspiration

*Per Simon's note above: credit belongs to the human mathematics community,
with apologies for the imperfect attribution below. Anything of value here is
their idea; the errors are ours.* Our approach is, honestly, an assembly of
existing lines of work; the closest ancestors, and what each contributes:

**The Kontorovich challenge and disproof frame.**
- **A. V. Kontorovich & Ya. G. Sinai, [“Structure Theorem for
  `(d,g,h)`-Maps”](https://arxiv.org/abs/math/0601622), Bull. Braz. Math. Soc.
  33 (2002), 213–224** — the exact arithmetic-progressions theorem for every
  finite valuation word and the density-level Brownian limit with drift
  `log(3/4)`.  The present compiler is a constructive specialization of their
  finite-word structure.
- **A. Kontorovich, [2019 thread on why the evidence for Collatz may be
  weak](https://x.com/AlexKontorovich/status/1172715174786228224)** — the
  hardware/software and “glider” challenge that sets the active research
  objective, including the proposed timing of widely separated bit packets
  using powers of `3` modulo powers of `2`.  The thread proposes a search
  philosophy, not a counterexample; an [archived full-thread
  rendering](https://threadreaderapp.com/thread/1172715174786228224.html)
  preserves posts 14--17 omitted from the prompt excerpt.
- **J. H. Conway, “Unpredictable Iterations” (1972)** — generalized
  Collatz-type maps can encode computation.  This motivates looking for
  structured programs while not transferring universality to the specific
  `3x+1` map.
- **Simon Dedeo** — suggested importing macro ideas from ultra-simple
  programming languages, targeting a possible 10,000-digit program, and—most
  importantly—not assuming spatial locality: a Collatz instruction may be a
  relation spread across the entire digit span.  Simon then proposed the
  “gap splash”: align sacrificial packets so collision carries erase the bad
  suffix and regenerate a delay line, then asked whether leaving a controlled
  overhang could absorb collision debris and renew the gap.  The exact
  three-bit-capped super-ether is the first recursive realization of that
  refinement, and the two-layer unit regenerator now isolates the general
  correction-word/carry identity.  Those proposals are the basis of the
  active dyadic--triadic, mixed-base, and two-rail bouncer searches.
- **L. Colussi, “The convergence classes of Collatz function” (2011)** — the
  exact rotated-repetend grammar for all finite stopping classes.  Its
  recursively generated order-10 background supplies an 11,846-digit
  structured test bed for a scale-changing defect.  The new unit repetend
  splash uses the same basic arithmetic resource in a different register:
  `(2^T C-s)/3^q` is a formula-generated sacrificial rail whose collision
  leaves a chosen marker and a clean gap.
- **L. De Mol, [“Tag systems and Collatz-like
  functions”](https://biblio.ugent.be/publication/436211/file/6812232.pdf)
  (2008)** and **E. Yolcu, S. Aaronson & M. J. H. Heule, [“An Automated
  Approach to the Collatz Conjecture”](https://arxiv.org/abs/2105.14697)
  (2023)** — respectively the three-symbol tag and 11-rule mixed-
  base presentations now being mined for formula bouncers.  These are exact
  encodings, not claims that the Collatz map itself is universal.
- **H. Bordihn, H. Fernau, M. Holzer, V. Manca & C. Martín-Vide,
  [“Iterated sequential transducers as language generating
  devices”](https://doi.org/10.1016/j.tcs.2006.07.059) (2006)** and
  **A. Pierce, [“Decision Problems on Iterated Length-Preserving
  Transducers”](https://www.cs.cmu.edu/afs/cs/user/mjs/ftp/thesis-program/2011/theses/pierce.pdf)
  (2011)** — supply the closest formal-language vocabulary for the new YAH
  macro quotient: repeated whole-word finite-state sweeps can generate rich
  languages, and even quite restricted iterated transducers can retain
  Turing-hard reachability.  This calibrates the hardware/software analogy;
  it does **not** transfer universality to the specific two-state Collatz
  quotient transducer.
- **J. C. M. Baeten & B. Luttik, [“The Queue Automaton
  Revisited”](https://arxiv.org/abs/2502.08345) (2025)** — revisits the
  classical Turing expressiveness of queue machines.  The YAH macro has the
  same head-consumption/remote-write spatial flavor but additionally rewrites
  the whole queue by arithmetic long division, so the comparison is a design
  guide rather than an equivalence theorem.
- **J. Cocke & M. Minsky, [“Universality of Tag Systems with
  `P=2`”](https://doi.org/10.1145/321203.321206) (1964)** — proves that
  deletion-two tag systems can simulate a Turing machine by encoding the two
  sides of its tape as binary stacks.  It does not say that De Mol's particular
  three-rule Collatz tag system, or the Collatz map, is universal.  Its remote
  append and two-stack moves are concrete compiler obligations for the
  separated-packet lane.
- **K. Morita, [“Universality of a Reversible Two-Counter
  Machine”](https://doi.org/10.1016/S0304-3975(96)00081-3) (1996)** — proves
  that reversibility does not prevent a two-counter machine from being
  universal.  This makes the charge bouncer's exact forward/reverse decoder a
  meaningful PL clue, but transfers no universality: its instruction set and
  arithmetic acceptance classes are far more constrained.  **A. Dudenhefner,
  [“Certified Decision Procedures for Two-Counter
  Machines”](https://doi.org/10.4230/LIPIcs.FSCD.2022.16) (2022)** is the
  relevant warning that decidability for reversible two-counter machines is
  instruction-set-sensitive; the present work must compile the actual
  increment/decrement/branch primitives, not argue from “two counters.”
- **T. Stérin & D. Woods, [“The Collatz process embeds a base conversion
  algorithm”](https://arxiv.org/abs/2007.06979) (2020)** — the exact
  quasi-cellular automaton with binary rows, ternary columns, and a nonlocal
  least-significant-bit bootstrap.  It supplies a spatial grid on which a
  diagonal defect or boundary glider can be posed exactly.
- **K. Mahler, [“An unsolved problem on the powers of
  `3/2`”](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/6416420BFE33A5DDC3DAB6EA358C2B0B/S1446788700005371a.pdf/an-unsolved-problem-on-the-powers-of-32.pdf)
  (1968)** — the original `Z`-number break-off algorithm repeatedly extracts
  a complete dyadic valuation and replaces it by a triadic factor.  The
  autonomous router's radix swap is a stricter factor-three-reserving cousin;
  no equivalence with `Z`-numbers is claimed.
- **S. Eliahou & J.-L. Verger-Gaugry, [“The number system in rational base
  `3/2` and the `3x+1` problem”](https://arxiv.org/abs/2504.13716) (2025)** —
  the rational-base tape where shortcut Collatz appends digit `1`, and a
  related saturated-word map appending `1` or `2` diverges.  We treat its
  missing “append `2`” as a compiler target, not as transferred divergence.
- **K. Väänänen & R. Wallisser, [“Zu einem Satz von Skolem über lineare
  Unabhängigkeit von Werten gewisser
  Thetareihen”](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0065/LOG_0016.pdf)
  (1989)** and
  **W. Zudilin, [“An elementary proof of the irrationality of Tschakaloff
  series”](https://arxiv.org/abs/math/0506086)
  (2005)** — the closest arithmetic literature for the exact partial-theta
  values forced by the standard two-rail schedule and by every constant-rate
  fixed-level unit clock, now also the determinant-four fixed-jump phase-up
  counter.  The full-source p-adic Väänänen--Wallisser theorem applies and
  rules out all three ansatz classes after their exact hypothesis audits;
  Zudilin's displayed real/complex hypothesis fails for the original
  standard-schedule parameters.
- **J.-P. Bézivin, [“Indépendance linéaire des valeurs des solutions
  transcendantes de certaines équations
  fonctionnelles”](https://gdz.sub.uni-goettingen.de/download/pdf/PPN365956996_0061/LOG_0012.pdf)
  (1988)** and [the 1990
  sequel](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/55/3)
  — the 1988 paper's p-adic theorem is a genuine stronger-looking neighbor,
  but it treats coefficients `p^(M(n))` for one prime.  The EC17 theta series
  has an unavoidable varying quadratic power of `3` in the denominator, so
  the theorem does not apply; the sequel is archimedean.  This is a
  source-checked closed shortcut, not a claim that no special theorem can
  handle the period-three linear form.
- **L. Koivula, O. Sankilampi & K. Väänänen, [“A linear independence measure
  for the values of Tschakaloff function and an
  application”](https://www.pphmj.com/article.php?act=art_download&art_id=409)
  (2006)** — gives a `v`-adic linear-independence theorem for the complete
  family `T_(q,d)(alpha_t*q^p)` with explicit height condition.  Our three
  period-three components are exactly its `d=3,D=1,H=1` family, but the
  condition fails by the already-certified separator
  `Gamma(3,0)<5/32<gamma`.  Thus this stronger packaging confirms rather than
  removes the period-three boundary.
- **M. Amou & K. Väänänen, [“Linear Independence of the Values of
  q-Hypergeometric Series and Related
  Functions”](https://doi.org/10.1007/s11139-005-1871-8) (2005)** — its
  qualitative theorem uses the full set of places where the rational
  parameter expands.  For the EC17 period-three parameter that set contains
  both the real and 2-adic places.  The theorem therefore does not exclude a
  relation present only in `Q_2`; this is a simultaneous-place mismatch, not
  a claim about the actual three-theta value.
- **M. Amou, T. Matala-aho & K. Väänänen, [“On Siegel--Shidlovskii's theory
  for q-difference equations”](https://doi.org/10.4064/aa127-4-2) (2007)**
  and **K. Väänänen, [“On Tschakaloff, q-exponential and related
  functions”](https://doi.org/10.1007/s11139-012-9375-9) (2013)** — the later
  paper's Theorem 4 does allow a non-archimedean place, but its cited 2007
  threshold misses uniformly in the three-value specialization.  Lean commit
  `92416b1` proves `B/A<13/12<3*log(3)/(4*log(2))` from exact ordered-field
  algebra and `2^13<3^9`.  These sufficient theorems do not close period
  three.
- **K. Väänänen, [“Algebraic independence of certain Mahler
  numbers”](https://arxiv.org/abs/1507.02510) (2015)** — covers Thue--Morse
  and related generating-function values at nonzero algebraic points in the
  ordinary complex open unit disk.  It does not by itself establish the
  needed statement for the bouncer's rational point in `Q_2`.
- **Y. Bugeaud, [“On the rational approximation to p-adic Thue--Morse
  numbers”](https://arxiv.org/abs/2110.01855) (2021)** — proves the relevant
  irrationality/approximation result for the standard signed Thue--Morse
  number evaluated at the prime `p`.  The bouncer reduction has a general
  rational argument `z=a_0a_1`, so no transfer is currently claimed.
- **T. Q. Wang, [“p-adic Transcendence and p-adic Transcendence Measures for
  the Values of Mahler Type
  Functions”](https://actamath.cjoe.ac.cn/Jwk_sxxb_en/EN/PDF/10.1007/s10114-005-0534-4)
  (2006)** — Theorem 1 is now visually source-audited.  For the geometric EC17
  series `G(z)=1+a*z*G(z^d)`, its parameters reduce to `rho=d`, theorem degree
  one, and `M0=d`, so the numerical hypothesis is `d<d^2`; the nonvanishing
  and 2-adic argument conditions are automatic.  Companion commit `1d3721a`
  kernel-checks the universal EC17-to-value bridge.  Companion commit
  `a6ce60a` later gives an elementary unconditional geometric no-go, so Wang
  plus Hadamard is now an independent value-theory audit rather than a
  soundness premise.  Neither result is a counterexample.
- **J.-C. Puchta, [“On Fabry's gap
  theorem”](https://www.dml.cz/bitstream/handle/10338.dmlcz/107844/ArchMathRetro_038-2002-4_7.pdf)
  (2002)** — states the classical Hadamard gap theorem used to show that the
  geometric EC17 Mahler function has the complex unit circle as a natural
  boundary.  Together with coefficient-field descent, this supplies Wang's
  function-transcendence premise; it says nothing by itself about an EC17
  orbit.
- **Y. Bilu & G. Hanrot, [“Solving Thue Equations of High
  Degree”](https://doi.org/10.1006/jnth.1996.0129) (1996)** — the algorithmic
  source behind PARI/GP's attack on the degree-23 power-quine survivor
  `3^15X^23-2^16Y^23=5`.  PARI/GP 2.15.4 returns no solutions and reports
  attached class number one.
- **The PARI Group, [PARI/GP `thue` and `thueinit`
  documentation](https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html#thue)**
  — specifies that `thue` enumerates every integral solution of the homogeneous
  form and that a flag-zero computation is unconditional when the attached
  tentative class number is one.  This is the explicit trust seam used to
  close the shortest perfect-power rail; it is not a Lean theorem.
- **K. F. Roth, [“Rational approximations to algebraic
  numbers”](https://doi.org/10.1112/S0025579300000644) (1955)** — proves that
  an irrational algebraic number has only finitely many reduced rational
  approximants at any fixed exponent greater than two.  The public-state
  23rd-power equation appears to force exponent 11 in each nonzero coefficient
  class.  Lean commit `07352a9` checks the elementary approximation,
  growth, residual-class, and exponent-11 interfaces.  Roth is still the
  external finiteness endpoint, and the sequence-level consumer is not yet a
  promoted result.
- **J. W. S. Cassels, [*Rational Quadratic
  Forms*](https://www.sciencedirect.com/science/article/pii/S0304020808704109)
  (Academic Press, 1978)** — the local--global, integral-lattice, and
  strong-approximation toolkit relevant to the new quadratic two-rail equation.
  The present audit uses only exact elementary identities, CRT, and one
  replayed rational point; no Hasse-principle or integral-representation
  theorem has yet been imported as a result.
- **J. H. Silverman, [*The Arithmetic of Dynamical
  Systems*](https://link.springer.com/book/10.1007/978-0-387-69904-2), GTM
  241 (Springer, 2007)** — supplies the arithmetic-dynamics vocabulary behind
  the new closure doctrine: orbits, conjugacy, invariant arithmetic sets, and
  families of algebraic self-maps.  No theorem from the book is being invoked
  to settle Collatz; the methodological point is that a counterexample
  construction needs an integer-preserving self-map on an invariant graph,
  not an accumulating list of points on successive transition varieties.
- **D. Barina, “Improved verification limit for the convergence of the
  Collatz conjecture” (2025)** — the `2^71` exhaustive frontier used to
  calibrate why another ordinary seed sweep is not the active attack.

**The direct spine of the counting result.**
- **I. Krasikov & J. C. Lagarias, "Bounds for the 3x+1 problem using
  difference inequalities," Acta Arith. 109 (2003) 237–258** (arXiv:math/0205002).
  The x^0.84 record and the LP/difference-inequality method we extend. Our
  entire counting line is *their method, run further and reinterpreted.*
- **[L. Collatz (1942)](https://eudml.org/doc/168987) and
  [H. Wielandt (1950)](https://doi.org/10.1007/BF02230720), the
  Collatz–Wielandt formula** — nonlinear
  spectral radius as inf–max of ratios. The lens under which the KL LP became
  a nonlinear eigenproblem (a genuine, if wry, namesake coincidence).
- **S. Gaubert & J. Gunawardena, "The Perron–Frobenius theorem for homogeneous,
  monotone functions," Trans. AMS 356 (2004)** — existence of the strictly
  positive nonlinear eigenvector; what discharges KL's (H_k) once the base map
  is seen as an odometer.
- **T. Bousch, "Le poisson n'a pas d'arêtes" (2000) and ergodic optimization
  (Jenkinson's survey, 2019)** — the maximizing-measure / zero-temperature
  view of the adversarial limit operator; the nearest *solved* cousin of our
  ℤ₃ transfer operator (optimization over a rotation/odometer). Our λ_∞
  dichotomy is an ergodic-optimization question in disguise.
- **A. A. Ahmadi, R. Jungers, P. Parrilo, M. Roozbehani (path-complete
  Lyapunov, 2014) and M. Philippe et al. (constrained joint spectral radius,
  2016)** — the certificate language. It enabled the structural no-go for
  autonomous charged/projective contraction; it is no longer a live endpoint
  route. Found independently via our keyword-blind search; the credit is theirs.

**Current endpoint inspirations — none selected for mentioning Collatz.**

- **A. Makur & J. Singh, [Doeblin Coefficients and Related
  Measures](https://arxiv.org/abs/2309.08475), and D. Lee, W. Lu, A. Makur &
  J. Singh, [Doeblin Curves](https://arxiv.org/abs/2606.19859)** supply the
  multiway-overlap and constrained-contraction language. Their generic theory
  is too weak here; renewal-min self-consistency is the project-specific input.
- **G. Litvinov, [Maslov
  dequantization](https://arxiv.org/abs/math/0507014); Y. Savas et al.,
  [entropy-regularized stochastic
  games](https://arxiv.org/abs/1907.11543); and J.-R. Chazottes & M. Hochman,
  [zero-temperature nonconvergence](https://arxiv.org/abs/0907.0081)** motivate
  the homogeneous soft-min family and warn that smooth finite-temperature
  selectors need not converge uniformly as temperature vanishes.
- **I. Csiszár, [I-divergence
  geometry](https://doi.org/10.1214/aop/1176996454), and J.-F. Bercher,
  [escort paths and Rényi
  divergence](https://arxiv.org/abs/1206.0561)** supply the information-
  projection and escort language.  The shared-minimizer order cone and the
  transport--branch cold-rate identity are derived here; neither source
  supplies the selected coercivity theorem.
- **S. Gouëzel, [correlation asymptotics from large
  deviations](https://www.impan.pl/shop/publication/transaction/download/product/87253),
  and I. Melbourne & D. Terhesiu, [operator renewal theory in infinite
  measure](https://arxiv.org/abs/1008.4113)** supply the first-return-operator
  equation, aperiodicity gate, and long-excursion estimates proposed for an
  induced selected-defect process.  Their regular-variation theorems do not
  directly fit the existing geometric annealed KL return law.
- **S. Kombrink, [dependent-interarrival renewal
  theorems](https://arxiv.org/abs/1512.08351), and M. Kesseböhmer & S.
  Kombrink, [complex Ruelle--Perron--Frobenius theory for infinite Markov
  shifts](https://arxiv.org/abs/1604.08252)** show how fading dependence on the
  symbolic past or countably many summable return words could replace the
  failed finite defect quotient.  The proposed holonomy twist and uniform
  hard-limit coercivity are new obligations, not consequences of those papers.
- **K. Schmidt, [amenability and strong
  ergodicity](https://doi.org/10.1017/S014338570000924X)** supplies the
  theorem behind the pair-carry no-go: an amenable ergodic carry action has
  almost-invariant modes.  This closes generic shell contraction while leaving
  selected/on-code signed cancellation open.
- **A. Bandeira, A. Singer & D. Spielman, [graph connection
  Laplacians](https://arxiv.org/abs/1204.3873), and C. Lange et al., [magnetic
  frustration inequalities](https://arxiv.org/abs/1502.06299)** provide the
  synchronization/frustration language. Their spectral theorems do not close
  the KL estimate because the abstract gain graph has flat sections.
- **M. Pivato, [defect-particle
  kinematics](https://arxiv.org/abs/math/0506417), and R. Paige & R. Tarjan,
  [partition refinement](https://doi.org/10.1137/0216062)** motivated the
  concrete same-policy propagation and quotient tests. This is inspiration and
  methodology, not a transferred cellular-automaton theorem.
- **R. Bryant, [ordered decision
  diagrams](https://doi.org/10.1109/TC.1986.1676819); I. Oseledets,
  [tensor trains](https://doi.org/10.1137/090752286); and Balle, Panangaden &
  Precup, [weighted-automaton
  minimization](https://arxiv.org/abs/1501.06841)** supply the restricted
  representation models used in the policy-circuit audit. Their machinery
  diagnoses exact finite complexity; it gives no unrestricted circuit lower
  bound.

**Full-proof thin connections — searched outward, not by Collatz keywords.**

- **Liu--Peyerimhoff--Vdovina on cyclic lifts and Dalfó--Fiol--Pavlíková--
  Širáň on factored lifts** provide the character/voltage language for the
  ramified three-sheet KL tower.  Exact checking confirms a quotient/detail
  decomposition with permutation transport and rank-one branch resets; it
  also refutes the stronger claim that KL is an ordinary weighted graph lift.
- **S. Brofferio, [the Poisson boundary of random rational
  affinities](https://arxiv.org/abs/math/0403198)** supplies a precise
  product-of-places object for the affine Collatz blocks.  Its random-walk
  theorem does not control a feedback-selected integer orbit; that missing
  atom/support bridge is the entire moonshot.
- **R. Lyons, R. Pemantle & Y. Peres, [size-biased branching
  spines](https://arxiv.org/abs/math/0404083)** inspired the deterministic
  side-bush cut.  Here it yields a literal disjoint-predecessor packing
  inequality, while also exposing why near-linear counts alone do not forbid
  exponential escape.
- **Akiyama--Marsault--Sakarovitch, [rational-base representation
  subtrees](https://arxiv.org/abs/1706.08266), and
  Morgenbesser--Steiner--Thuswaldner, [adelic rational-base
  tiles](https://arxiv.org/abs/1203.4919), with Akiyama--Frougny--Sakarovitch
  and Odlyzko--Wilf on the endpoint/Josephus coordinate**, supply the critical
  base-`3/2` span capacity.  Its stable even-cell gap and bounded interval
  discrepancy are exact; explicit small spans and neutral cycle Jacobians
  rule out the hoped scalar Lyapunov proof.
- **Akian--Gaubert--Walsh on the max-plus Martin boundary, Bond--Levine on
  abelian networks, and Danilenko--Lemańczyk on Maharam extensions** are the
  other three-way junctions retained by the atlas.  Each has a concrete kill
  test; none is promoted merely because the analogy is attractive.

**The forward-orbit / density tradition (context and the ceiling we press
toward).**
- **R. Terras (1976)** — density-1 finite stopping time; the elementary
  parity/congruence structure everything reuses.
- **T. Tao, "Almost all orbits of the Collatz map attain almost bounded
  values" (2019/2022)** (arXiv:1909.03562) — the a.e. result and the Fourier
  decay of Syracuse random variables; the 3-adic major-arc regime our
  exponential-sum atlas lands in, and the wall (a.e. vs every-n) we respect.
- **I. Krasikov (1989), Applegate–Lagarias (1995)** — the predecessor-tree
  and transfer-operator antecedents of the counting side.

**Structure theorems we proved are extensions of:**
- **P. Diaconis & J. Fulman, "Carries, shuffling, and an amazing matrix" /
  the multiplication-carries chain (2008–2012)** — our carries-spectrum
  theorem answers a spectral question they left open.
- **L. Berg & G. Meinardus (1994/95)** and **B. Adamczewski & J. Bell,
  Mahler-function rigidity (Ann. Sc. Norm. Pisa 2017)** — the Mahler-equation
  reformulation and the (2,3)-rigidity behind our bi-Mahler exclusion.
- **A. Cobham / A. Semenov** — the two-bases automatic-set rigidity behind the
  "no certificate in two bases" note.
- **K. Monks (2006)** — sufficient sets / arithmetic-progression reduction,
  used in the exclusion and Mahler notes.

**The frame (why this is hard, and the BB connection Simon came for).**
- **J. H. Conway, "Unpredictable iterations" (1972)** and **S. Kurtz & J. Simon
  (2007)** — undecidability / Π⁰₂-completeness of generalized Collatz; the
  invariant-rank ledger is Conway's unsettleability made quantitative.
- **P. Michel** (Busy-Beaver ↔ Collatz-like maps) and **S. Aaronson, "The Busy
  Beaver Frontier" (2020)** and **the bbchallenge collaboration** (BB(5)=47,176,870,
  Coq-verified; Antihydra and the cryptids) — the BB/Collatz bridge; our
  reverse-mining and Antihydra-rarity work sits on theirs.
- **C. Deninger** (foliated dynamical systems / solenoid Lefschetz program) —
  the frame for the Traceless Theorem on the (2,3)-solenoid.

**What our approach most resembles, in one line:** the Krasikov–Lagarias LP
method reread through nonlinear Perron–Frobenius and ergodic optimization, with
information contraction, zero-temperature smoothing, and exact formal and
computational audits used to expose the remaining selected-policy seam.

Full per-claim citations with URLs are inline in the `docs/notes/*` files and
`docs/LANDSCAPE.md`; the mirrored-PDF index is `papers/REFERENCES.md`.

# NEW_RESUME — Kontorovich counterexample-search handoff

Updated: 2026-07-23, about 12:46 EDT

### 12:46 EDT continuation -- KL pressure exposes an invariant EC1 component

There is no counterexample.  Do not continue the raw zero-preload scan: the
first million clock states contain 460 genuine one-step sources and no
two-step source, but this is only finite codimension evidence.  The exact
branch algebra is now

```text
P_m=8m+15, Q_m=6m+11,
2^P_m q'=3^Q_m q+delta_m,
delta_m=(3^(6m)W0-2^(8m-5)Z0)/473>0.
```

The disjoint target cylinders are an LSB-first variable-length code of
lengths `23,31,39,...`.  Its exact Kraft mass, generating function, and
pressure equation are

```text
sum_m 2^(-P_m)=1/(255*2^15),
A(x)=(1-x^8)/(1-x^8-x^23),
x^8+x^23=1,
d=-log_2(x)=0.07065929109419928758... .
```

Use this pressure cost for bounded falsification, not flat branch boxes.  It
does not exclude an ordinary ray: a natural seed is an exceptional
eventually-zero address, and dimension alone cannot decide its existence.

The stronger algebraic result is the invariant component `q=17r`.  Both
affine offsets divide by `17`:

```text
Zbar(r)=29073613+495976448r,
Wbar(r)=4911712+83790531r,
3^11 Zbar(r)+1=2^20 Wbar(r).
```

An accepted `n -> m` step becomes

```text
2^(8m+15)v'=3^(6n+11)v+1,  v,v'=2 mod3.
```

Modulo `17`,

```text
r'-14=6*(-2)^(m-1)*(r-1).
```

Therefore every accepted step in this component satisfies the universal
filter

```text
min(v17(u),v17(u'))=1.
```

Deep `17^2` core events are never adjacent and have upper density at most
one half.  This component is live: every finite branch pair remains
CRT-solvable, and the already-closed direct normalized-core-to-KL-edge tax
must not be retried.  The new worker/artifact are

```bash
python3 experiments/kontorovich/breakoff_ether_branch_pressure.py selftest
python3 experiments/kontorovich/breakoff_ether_branch_pressure.py verify \
  experiments/kontorovich/breakoff_ether_branch_pressure_audit.json
```

The artifact checks branches through `m=64`, 1,278 exact schedule cylinders
through 160 bits, and the higher 17-adic checksum clock through precision 12;
`counterexample:null`.

Companion commits through `8d59350` substantially sharpen the infinite gate:
for a prescribed branch schedule, eventual zero canonical carry is equivalent
to existence of a positive bare EC17 ray; packet color zero is reflected as
well as propagated; and a shifted bare ray promotes to the full self-writing
map iff every state lies on the exact affine `Z` rail.  Thus search can now
separate three exact tests: eventual-zero dyadic carry, color zero, and full
`473*2^20` rail membership.  A witness must pass all three.

### 12:02 EDT continuation -- the KL center yields one self-writing integer

There is no counterexample.  The rational ether center has now reduced the
complete packet transition to one deterministic nonnegative coordinate.  Put

```text
Z(q)=494251421+495976448*q,
W(q)= 83499104+ 83790531*q.
```

The constants satisfy the exact determinant identity

```text
3^11*Z(q)+17=2^20*W(q).                            (SW1)
```

For a genuine current packet, `v_3(Z)=6n` and `u=Z/3^(6n)` is the normalized
EC17 core.  If

```text
v_2(W)=8m-5,  h=W/2^(8m-5),
```

then the next packet coordinate must be

```text
q'=(729^m*h-494251421)/(473*2^20).                 (SW2)
```

It is accepted exactly when this is a nonnegative integer.  On acceptance,
`Z(q')=729^m*h`, so the binary delay `m` is written back as exactly `6m`
ternary zeros.  The unit is `1 mod 3` automatically after the first genuine
packet.  This is the sought self-writing mixed-radix controller: the branch
schedule is decoded from the payload rather than supplied externally.

The rational KL relation is exact.  With `Z=473R+4`,

```text
D(R)=(3^11*R+1221)/2^15,
E(R)=(729*R+4)/256,
R'=E^m(D(R)).                                      (SW3)
```

The literal boundary is `C=2^18*R+2215`; hence `E` is conjugate to
`C |-> (729C+881)/256` and the fixed center is the same `-881/473` found by
the KL tail chart.

For every fixed target branch `m`, CRT gives one complete family

```text
q=a_m+2^(8m+15)t,
q'=b_m+3^(6m+11)t.                                 (SW4)
```

The current ternary branch condition is coprime to this binary cylinder, so
every finite `n -> m` link still exists.  Therefore linked `r=2`, fixed-depth
tail synchronization, and the `473` resonance do not give an all-depth no-go.
Their constructive value is the one-state recurrence (SW1)--(SW2).

The checksum audit also corrects the semantic scope of the bare carry lane.
For `s=2^(8n-5)u`, define

```text
chi=s+291427 (mod 473).
```

Every EC17 step gives `chi'=316*chi`; genuine packets are exactly color zero
after the automatic `3^10` and outgoing `2^20` conditions.  Thus an eventual
zero-carry theorem constructs a bare EC17 ray, but it becomes a returning
glider only after one packet-valid/color-zero seed premise.  That premise then
propagates forever.

Every accepted self-writing step has `q'>q`, using
`3^(6m+11)>2^(8m+15)` for all `m>=1`.  The branch counter need not diverge,
but the public payload counter must grow strictly on any infinite execution.
Finite or ultimately periodic schedules remain excluded; the live object is
an aperiodic invariant thin set of (SW2) whose canonical dyadic residues
eventually stabilize to one natural seed.

The exact worker checks the universal identities, constructs target families
through `m=32`, and replays 4,096 linked packet transitions:

```bash
python3 experiments/kontorovich/breakoff_ether_self_writing_kl.py selftest
python3 experiments/kontorovich/breakoff_ether_self_writing_kl.py verify \
  experiments/kontorovich/breakoff_ether_self_writing_kl_audit.json
```

The artifact has `counterexample:null`.  The next theorem-driven target is an
exact invariant/recurrence for the accepted `q` values, not a wider seed scan.
Companion commit `7ca6d4f` has now kernel-checked (SW1), the reduction from
any supplied self-writing orbit to the exact EC17 balance, strict monotonicity
of `q`, and impossibility of an eventually periodic branch schedule.  It does
not assert that such an orbit exists.

### 11:28 EDT continuation -- linked tails collapse to one KL ether spine

There is no counterexample.  The correct packet-level KL chart is now exact.
For a free length-`n` packet

```text
K=R_n+2^(8n+15)q,
Z=2^35*K-358513857,
r=v_3(Z),
C+1=3*2^(r+1)*(Z/3^r),
```

the tail coefficient `2^(8n+50)` is a 3-adic unit, so free `q mod 3^d`
has the geometric valuation counts `2*3^(d-r-1)` plus one root cylinder.
Do not use this as a Haar model for one execution.  The glider tail and EC17
core are different coordinates:

```text
u=u_base(n)+473*2^20*3^10*q.
```

In particular `u=1 mod 3` is automatic and does not restrict `q mod 3`.

The linked transition theorem removes the free-tail distribution from the
coherent problem.  Exact cancellation gives

```text
473*3^10*Z=2^(8n+30)u-9591553,
9591553=17*(2^15+3^12).
```

If a branch `n` links to branch `m` by EC17, then

```text
2^(8m+30)u'-9591553
 =3^12*(2^15*3^(6n-1)u-17).
```

The bracket is a 3-adic unit for every `n>=1`.  Therefore every genuine
successor has `v_3(Z')=2` exactly.  Its true Collatz boundary satisfies

```text
473*C'+881=2^18*3^(6n)u,
v_3(473*C'+881)=6n.
```

Hence unbounded linked branches approach `-881/473` in `Q_3`.  More
strongly, for `d<=6n+1`, `q' mod 3^d` depends only on the target branch `m`,
not on the source core or the affine lift.  The artifact checks this through
depth 49 on 192 lifted links.

The linked router rail vector is

```text
[2,0,2,0,1,0]+[2,0]^(n-1),
```

so every post-initial macro has `(R2,R8,S)=(2n+4,4n+7,0)`, exactly
`6n+11` odd steps and `8n+15` halvings.  Each extra ether cell is the genuine
six-edge KL cycle

```text
F_E(x)=(729*x+881)/256,  x_*=-881/473,
```

with two class-2 and four class-8 chords.  At certified level 12, synchronized
macros `n=2..6` satisfy the exact factorization
`Dev(n)=Dev_base*Dev_E^n`; `Dev_E=2.973148268...`, one of its six lifts is
selected, and `Dev_E/W_E=1.217522341...`.  This is a finite-precision
subeigenvector statement, not a tower limit.

The separate exact worker `kl_rational_ether_cycle.py` reconstructs this
rational six-edge cycle from all stored certificate vectors `k=12..19`,
SHA-checking and memory-mapping the large sidecars.  Exact cross-products
prove that `Dev_E/W_E>1` at every level and decreases strictly as

```text
1.217522341, 1.164166565, 1.148289542, 1.113495646,
1.097093460, 1.076368695, 1.066265371, 1.051569573.
```

This finite trend says the ether spine is close to the KL critical policy;
it does not prove a limit.  The artifact has `finite_evidence_only:true`,
`limit_theorem:null`, and `counterexample:null`.

Reconstruct with

```bash
python3 experiments/kontorovich/breakoff_ether_glider_kl_tail_chart.py selftest
python3 experiments/kontorovich/breakoff_ether_glider_kl_tail_chart.py verify \
  experiments/kontorovich/breakoff_ether_glider_kl_tail_chart_audit.json
python3 experiments/kontorovich/kl_rational_ether_cycle.py verify \
  experiments/kontorovich/kl_rational_ether_cycle.json
```

The artifact has `counterexample:null`.  The fixed-depth KL-fiber question is
settled: there is no tail choice after synchronization.  The remaining task
is to construct one positive infinite EC17 chain and pass the ordinary
dyadic-address gate.  Existing Lean already proves that any such chain is an
outward escape; the witness is missing.

### 10:54 EDT continuation -- exact height gate, proper thin language, and the failed EC17/KL bridge

There is no counterexample.  Companion commit `73601f7` strengthens the
zero-carry theorem to the exact height equivalence

```text
ResiduesBounded(e)
  <-> EventuallyConstantResidue(e)
  <-> EventuallyZeroCarry(e)
  <-> exists m, Follows(e,m) and 0<=m(0).
```

The contrapositive `no_nonnegative_follows_of_unbounded_residues` is now the
preferred symbolic no-go interface.  A worker need not derive every carry:
after identifying its nested address with `initialResidue`, any exact
unbounded height lower bound excludes an ordinary initial integer.

The exact signed-controller worker
`experiments/kontorovich/kl_signed_thin_residue.py` searches only the proper
outward language in `c in [-96,-1]`, shadow depths `1..8`, and binary
precision 8.  The minimal prefix code is exactly

```text
1, 011, 001111, 010111,
p=21/32, q=1905/2048.
```

It checks 768 current modes, 246 outward modes, 168 admitted residues, and
41,328 literal growing reset transitions.  The depth-nine preloaded tree has
finite zero-lift runs; the strongest audited natural `M=138770` continues for
eight zero-lift blocks and then has no zero-lift code extension.  This is a
bounded diagnostic only.  The artifact has `counterexample:null` and leaves
the eventual-zero tail undecided.  Companion commit `1aa3e52` proves that no
periodic or ultimately periodic block schedule over these four outward words
can be a positive ordinary shortcut orbit.  The only live subcase is a
genuinely aperiodic path with bounded canonical residue height.

The direct period-three EC17-to-KL bridge is false.  Exact reduction of the
EC17 coefficient congruences gives

```text
m_(t+1)=4^(-4*Delta_t)*m_t (mod 3^d).
```

For period-three gain `K`, the boundary orbit has length
`3^(d-1-min(v_3(K),d-1))`; if `3` does not divide `K`, it is all of `Y_d`.
However, a phase pair `y=u*m` is a KL transport only in the exceptional
congruence `u=4`, and over a full odometer orbit it meets exactly one class-2
and one class-8 chord.  For `(-1,1,1)`, every phase has counts
`(transport,R2,R8,nonedge)=(0,1,1,7)` at `d=3` and `(0,1,1,25)` at `d=4`.

The affine-defect obstruction is stronger.  Every KL predecessor word with
`r` divided letters has `D>=3^r-2^r`.  A normalized EC17 core transition has
`r=6n+11>=17` and `D=34`, but
`3^17-2^17=129009091`.  Hence no single core transition is any KL word.
The exact reconstructive artifact is
`breakoff_ether_period3_kl_bridge_audit.json`; it records
`tax_ready:false` and `counterexample:null`.  This closes only the boundary
identification.  The actual packet compiler uses different ordinary Collatz
endpoints and remains eligible for a KL audit after its literal path is
expanded and sampled at successive `2 mod 3` states.

The correct finite packet bridge is now implemented in
`breakoff_ether_glider_kl_bridge.py`.  At ether lengths `1..6`, tail zero, and
the exactly reverified `k=12` KL certificate, it performs the full chain

```text
compiled breakoff macro
 -> linked literal accelerated-Collatz words
 -> every one-halving Syracuse state
 -> successive 2 mod 3 visits
 -> reversed genuine KL full-lift edges
 -> exact prescribed-lift potential inequalities.
```

The edge-count rows `(R2,R8,S)` are `(6,9,0),(8,13,0),(10,18,0),
(12,22,0),(14,25,0),(16,29,0)`.  Every macro has leading multiplier larger
than one, and every edge and telescoped product inequality passes in exact
rational arithmetic.  The artifact has `counterexample:null`.  This is the
valid way to use KL on the ether program; it remains finite and says nothing
yet about the macro tails forced by one infinite period-three execution.
Companion commit `82c01dd` proves the semantic classification universally:
the next `2 mod 3` visit occurs after one Syracuse step from an odd state and
two from an even state, and the reversed pair is respectively advanced,
transport, or retarded according to the exact parity class.  The finite
worker is therefore checking packet linkage and certificate tax, not merely
guessing the KL graph convention.

### 08:59 EDT continuation -- special-theta audit and KL-calibrated escape

There is no counterexample.  The period-three analytic lane now has a real
quadratic-order arithmetic feature, but not yet a retained product-formula
gain.  Companion commit `7aad758` proves that the complete `3*nu` Skolem root
set is one consecutive geometric `R`-grid and kernel-checks

```text
det V(alpha,...,alpha*R^(m-1))
 =alpha^choose(m,2)*R^choose(m,3)
  *product_(1<=d<m)(R^d-1)^(m-d).
```

For `m=3*nu`, the cleared numerator is divisible by both
`11^choose(m,2)` and `43^choose(m,2)`, with exact LTE ledger

```text
v_p(det gap numerator)
 =choose(m,2)*(1+v_p(K))+sum_(1<=d<m)(m-d)*v_p(d),
p=11,43.
```

Unlike the fixed `3 x 3` determinant, this is genuinely quadratic in `nu`.
It still does not prove independence: a primitive Cramer/adjugate vector is
expected to cancel the common cofactor factor through order
`choose(m-1,2)`, leaving only linear savings.  Commit `847027b` proves the
determinant-minus-cofactor multiplicity and subquadratic limit; the generic
cofactor alternation divisor for a particular Padé matrix remains the semantic
seam.  Do not claim a repaired threshold unless a factor survives in the final
primitive linear form.

The tempting scalar rewrite is also being closed honestly.  For

```text
u_n=s_0+s_1*R^n+s_2*R^(2n),
```

the coefficient sequence has the cubic recurrence with characteristic roots
`1,R,R^2`, and its `3 x 3` Hankel determinant is

```text
s_0*s_1*s_2*R^2*(R-1)^6*(R+1)^2>0.
```

Thus a scalar full-support relation still has minimal recurrence rank three;
one cannot import the friendlier one-value Tschakaloff threshold merely by
renaming three theta values as one scalar.  Companion commit `847027b`
kernel-checks this recurrence, the determinant identity, positivity for the
literal ray, and the converse excluding every recurrence of order at most
two.  The same commit proves the determinant-minus-cofactor multiplicity is
only linear and hence subquadratic; applying that no-go to a particular Padé
matrix still needs the generic cofactor alternation divisor.

At Simon's suggestion, the original Krasikov--Lagarias paper was reread as a
construction guide, with its faulty deletion proof and equation (2.1)
excluded.  A positive critical eigenvector calibrates every selected edge by

```text
lambda^w*c(target)<=c(source).
```

Multiplication around a cycle cancels `c`; every KL minimizing-policy cycle
has strictly negative total time shift.  The KL critical value is sustained
by branching entropy, not by one outward ray.  A non-minimal chord lift pays
`d=c_alt/c_min`, and every outward full-lift cycle must satisfy

```text
lambda^(sum w)<=product d.
```

Companion commit `9f307a9` kernel-checks QM127--129: generic calibrated
path/cycle telescoping, strict negativity of every KL selected-policy cycle,
the exact mixed-word budget, and the pure minus-one rail no-go.  Commit
`ddff8d7` adds QM130, eliminating arbitrary path endpoints at the cost of the
fixed-level potential condition number.  Commit `7aa7c0d` adds the selected
corollary: `cmax/cmin<=lambda^B` forces every selected path, of every length,
to have total shift at most `B`.  These give a theorem-driven search objective:
minimize exact KL deviation tax among autonomous
recharge/discharge programs, rather than enumerate seeds or follow the active
policy itself.  The existing `3^41<2^65` separator forces every outward mixed
word with class counts `(n8,n2,ns)` to satisfy
`24*n8>17*n2+82*ns`.

The distinguished positive-shift cycle is the 3-adic fixed point `-1`.
The new exact diagnostic SHA-checks all stored KL inputs at `k=12..19` and
proves by integer cross-products that

```text
c(-1)/minFiber(-1) > B8/SC_W
```

at every level.  The exact surplus ratios decrease monotonically from
`1.00491098975441` to `1.00029914602351`: finite evidence that the nonordinary
`-1` loop saturates the escape tax.  For the pathwise extension, the audit also
extracts the exact condition number of each certified feasible
subeigenvector; it increases from
`146.967160601293` to `2782.61599307298`.  Consequently the endpoint factor is
bounded along every fixed-level path but no precision-uniform margin is yet
available.  Companion commit `cc9f441` proves that matching the exceptional
spine at precision `3^k` forces `3^k<=n+1`; a fixed natural eventually leaves
that spine, while a growing diagonal can still chase it.  Its positive natural
rail is

```text
T^L(2^L*t-1)=3^L*t-1.
```

Splicing another pure rail subtracts its length from the finite payload
counter `v_2(t)`, so no fixed positive payload supports infinitely many such
discharges.  An actual escape must autonomously recharge that counter.  This
literal statement is kernel-checked in `9f307a9`; the exact finite artifact
has `counterexample:null`.

```text
KL minus-one artifact b6204c3964b880e3c5857114f7bcd112e2e1592ca3653ad79445ce470dc14577
```

The new source-audited map is
`docs/notes/kl-calibrated-escape.md`.  The next constructive object is not a
periodic residue cycle but a mixed recharge/discharge recurrence which (i)
beats the KL deviation tax, (ii) regenerates `v_2(m+1)`, and (iii) closes for
one ordinary positive payload rather than a fresh 3-adic address at every
generation.

### 09:25 EDT continuation -- the resource ledger collapses to one centered integer

There is still no counterexample.  Commits `408cb2c` and `814fb00` replace
the informal mixed-recharge picture by literal Syracuse semantics.  For the
advanced, retarded, and transport KL children, Lean proves the centered
balances

```text
3*(advancedChild+1)=2*(a+1),
3*(retardedChild+2)=4*(a+1),
transportChild+4=4*(a+1).
```

It also proves that if `r=v_2(n+1)`, then the next `r` sources are odd, their
states are exactly `3^j*2^(r-j)*t-1`, and the endpoint at `j=r` is even.
Thus recharge depth is exactly the next forced odd-burst length.  It cannot be
stored for later or routed independently.

The same algebra has a general moving negative-center form.  If the center is
`-h`, the three new centers are `-(2h+1)/3`, `-(4h+2)/3`, and `-4h`; the
centered distance changes only by factors `2/3`, `4/3`, and `4`.  Therefore
its `2,3`-primitive cofactor is invariant on every coherent controller
segment, and `2^b*3^k<=n+h` whenever that segment has dyadic depth `b` and
ternary address depth `k`.  Companion commit `35200ca` kernel-checks QM131:
the ternary valuation balances, `content23(z)|z`, its ordinary-height bound,
and primitive-core invariance for all three arbitrary moving-center branches.

The exact new worker calibrates the three supplied signed cycles through
`-1,-5,-17`.  Their KL center cycles and outward separators are

```text
1                              3 > 2
7 -> 10 -> 7                   3^2 > 2^3
25 -> 34 -> 136 -> 91 -> 61
   -> 82 -> 55 -> 37 -> 25     3^7 > 2^11.
```

At every certified level `k=12..19`, all exact deviation products exceed the
corresponding certified lower weight products.  The surplus sequences
decrease from `1.00491,1.14003,1.86455` to
`1.00030,1.06409,1.48130`; `-1` is exactly cheapest in every row.  This is
finite evidence from feasible subeigenvectors, not a critical-vector limit or
cycle classification.  Artifact SHA-256:
`f52afeca61dc4bd0683a2ab72e285377355e86edd5e52fec85e89a84ab534249`;
`counterexample:null`.

Two further exact obstruction interfaces are QM132--133.  If two signed
Syracuse orbits share `N` parity choices, subtracting their affine laws gives

```text
2^N*(T^N(x)-T^N(y))=3^O*(x-y),
```

so `2^N | x-y`: no distinct positive/negative ordinary pair can shadow
coherently forever, even with an aperiodic negative controller.  A reset is
therefore compulsory.  For ternary switching, every center step has
`h'<=4h`; a length-`L` connector matching a distinct target `g` modulo `3^k`
must satisfy `3^k<=4^L*h+g`.  Fixed-length switches cannot work at cofinal
precision.  Companion commit `616ace8` kernel-checks QM132 completely,
including a literal signed-Syracuse specialization and the infinite
same-itinerary uniqueness theorem.  QM133's connector inequality remains
pending companion Lean checking.

The adversarial review prevents two overclaims.  QM132 is the exact cost of a
finite shadow, not a local impossibility: commit `2fcddea` proves that the
first `N` parity bits agree exactly when the starts agree modulo `2^N`, and
constructs an explicit negative representative in every finite cylinder.
Finite signed shadowing at separately chosen depths is therefore automatic.
Likewise commit `2700d1e` proves that QM133 only excludes fixed-length
connectors between fixed/bounded centers.  Commit `aab22e7` adds its sharper
count form

```text
h' <= 4^nS*2^n2*h,
h'!=g and h'=g (mod 3^k) -> 3^k<=4^nS*2^n2*h+g.
```

Transport words of unbounded length can attain every fixed target precision,
so this is not a finite-alphabet no-go.

The revised live object is an aperiodic **self-writing controller reset**.
Writing the reset state as `x_j=c_j+2^N_j*m_j`, exact subtraction gives the
new QM134 interface

```text
2^N_(j+1)*m_(j+1)=3^O_j*m_j+T^N_j(c_j)-c_(j+1).
```

Backward iteration selects one 2-adic payload; a counterexample requires it
to be a positive natural with every quotient positive, integral, and legal.
Eventually periodic coefficients reduce to a finite rational fixed-point
audit and are already closed; the live schedule must be genuinely aperiodic
and payload-written.  On the ternary side the exact word accumulators obey
`3^r*h'=A*h+B`, giving one connector congruence rather than an undirected
search.  Commit `aab22e7` kernel-checks the complete QM134 accumulator,
connector iff, and exact reset recurrence, with positivity/integrality/
legality kept as explicit construction obligations.

The finite ternary obligations are now completely classified.  Commits
`8c20163`/`54eb749` prove that `A=2^scaleBits(w)`, so a fixed word and target
select exactly one input class and any additional dyadic class is
CRT-compatible.  Commit `961c692` proves the stronger equivalence, for every
word with `r>0` divided letters,

```text
LegalWord(w,h) <-> A*h+B = 3^r (mod 3^(r+1)).
```

For every target center `g=1 (mod 3)` and `k>=1`, Lean constructs a positive
legal input reaching `g mod 3^k` and proves uniqueness modulo `3^(k+r)`.
Therefore finite controller legality, finite ternary targeting, and finite
mixed CRT hits are automatic.  The live seam is no longer “find a legal
connector”: it is make the dyadic and ternary inverse-limit cylinders come
from one fixed positive ordinary payload while the real KL size cocycle stays
outward.

Commits `2acceaa`, `d8d8337`, `2963a8d`, `ca8dc5c`, and `18b8c93` formalize the
dyadic inverse-limit side.  For reset
instructions `(N,O,delta)`, the accumulator

```text
(S,P,D)->(S+N,P+O,3^O*D+2^S*delta)
```

satisfies `2^S*m_end=3^P*m_start+D`; the corresponding initial class exists
and is unique modulo `2^S`.  The stronger terminal theorem proves that this
one congruence is equivalent to existence of every intermediate integer
quotient, and an affine cylinder shift makes every payload in any finite
program strictly positive.  Thus finite reset integrality and positivity are
automatic too.  For an infinite instruction stream with
unbounded cumulative `S`, any two ordinary integer payload chains have the
same initial payload.  Thus individual reset lengths need not grow, but their
cumulative written precision does, and it selects at most one ordinary
candidate.  The canonical representatives are nested and nondecreasing, and
an ordinary nonnegative chain with unbounded cumulative precision makes them
eventually equal to its initial payload.  The exact new carry digit satisfies

```text
r_(J+1)=r_J+2^S_J*q_J,  q_J<2^N_J,
q_J=0 <-> 2^N_J divides 3^O_J*z_J+delta_J,
```

where `z_J` is the canonical finite endpoint.  Lean proves the exact
infinite equivalence, without an unboundedness hypothesis:

```text
EventuallyZeroCarry(e)
  <-> exists m, Follows(e,m) and 0<=m(0).
```

Thus nonzero carries arbitrarily late exclude every nonnegative ordinary
chain, while a zero tail constructs one.  Strict positivity of every later
quotient and outward real growth remain separate construction obligations.

Commit `302ce3b` adds a deliberately abstract finite covering-dispatcher
consumer: if a supplied residue table already certifies every affine reset,
threshold preservation, positivity, and strict reset-state growth, Lean
constructs its infinite growing configuration orbit.  It has no
signed-Syracuse semantic bridge and cannot assert a Collatz counterexample.
Moreover a total semantic cover by outward next-controller cylinders should
pull back to the already closed Two-Kraft complete-code obstruction; that
affine-preimage reduction is currently a proposed bridge, not a new checked
no-go.  The live construction target remains a proper invariant thin
language.

Finally, the three-cycle audit is finite calibration only.  The certificates
are not a coherent critical tower, the `-17` surplus `1.4813` is not “near
equality,” and individual `-5` edge deviations alternate across levels.  Any
future renormalization theorem must control cycle products, not a named edge.
Commit `e15c6f0` proves the safe fixed-level consequence
`W<=product d_i<=M^q`: an outward `q`-chord cycle forces some nontrivial
projective fiber defect without selecting which edge carries it.
Pure seed widening, fixed negative controllers, and treating
height/precision/battery as independent counters no longer attack the seam.

### 07:20 EDT continuation — exact consecutive construction carries

There is no counterexample.  Period-three search is now centered on exact
adjacent-cycle compatibility rather than deeper fixed-depth clocks.  For the
canonical residue `r_q` at the sharp budget `U(q)`, write

```text
2^m(q)*y_q=3^Q(q)*r_q+D(q),
p(q)=U(q)-m(q)>0,
r_(q+1)-y_q=2^p(q)*C_q.
```

An eventual exact-zero tail `C_q=0` supplies consecutive literal three-step
EC17 factors.  Companion commit `daae4a8` proves non-circular residue
reduction/splitting from bare `backwardEval` and kernel-checks that any
compatible positive chain of three-step factors glues to an infinite EC17
orbit.  Commit `40835c0` checks the strict defect bound and abstract balanced
carry equivalence, `5769c85` checks the long-block last-carry theorem, and
`122680b` supplies the canonical upper-block range bounds.  Commit `f79192e`
then proves the displayed three-step identities, translates zero carry to the
exact `ComposedReplayFactor`, and constructs an infinite positive EC17 orbit
from any eventual zero-carry tail.  Commit `4516a03` promotes the endpoint to
the project's literal period-three `Ray`, and `fff0dec` kernel-checks the
canonical range gate by which a full worker congruence forces equality of the
two upper blocks.  Commit `732da20` instantiates that result at the worker's
actual `floor(log2(3^Q))` precision.  The construction implication and
finite-row gate are fully kernel-checked; there is simply no finite hit to
instantiate them.

The exact consecutive-cycle worker covers all 71 positive `[-1,1]^3`
schedules, starts through eight, and every `q=14..256` (17,253 rows).  Every
row checks the compact and stepwise equations, coverage, future low-bit
compatibility, and independent reverse predecessor congruence; 284 checkpoint
residues plus every anomaly use a second series evaluator.  Results:

```text
exact zero carries                                      0
full 3^Q predecessor divisibilities                     0
rows with |C|<3^Q                                  16,870
zero-forcing exponent-gate rows                     8,339
positive / negative carries                   8,748 / 8,505
maximum observed v3(C)                                  8
counterexample                                        null
```

The exact gate is `2^(U(q+1)-p(q))<=3^Q(q)`.  Together with
`D(q)<3^Q(q)`, it upgrades full predecessor divisibility to `C_q=0`; none of
the 8,339 finite gate rows has the divisibility.  Commits
`fff0dec`/`732da20` prove the gate with both canonical representative bounds
explicit and at the exact logarithmic precision.  This does not rule out a
later zero tail.

The balanced construction precision

```text
P_(q+1)=P_q-m(q)+floor(log2(3^Q(q)))
```

forces `|C_q|<3^Q(q)` on every row, so its full congruence is equivalent to
one exact three-step link.  Commit `4fe60a7` adds the independently verified
artifact over 1,136 paths (`h=1..16`), all 71 schedules, and `q=14..60`:
53,392 rows, zero hits, maximum run zero, `counterexample:null`.  Misses do
not exclude a ray because this is a construction precision, not the upper
budget.

Commit `a457222` adds an exact signed 2-adic rational reconstruction audit at
2,048 and 4,096 bits for all 71 `q=0` values.  With
`|numerator|,denominator<=2^512` and odd positive denominator, every uniqueness
gate passes and both residue evaluators agree; there are zero single-precision
or repeated rational candidates.  This is a finite height exclusion only.

Companion commits `2cad6e1`/`b518d2b`/`a2e940e` give the theorem-driven
analytic endpoint.  Any literal period-three ray's completed backward series
is exactly `1` plus three paper-normalized 2-adic theta values; independence of
those four values excludes the ray.  The theta count in the relevant 1989
sufficient bound is three, not four, but the required threshold inequality
still fails in the strict reverse direction.  The paper's inverse-parameter
normalization and functional equation are now pinned.  A live analytic lane
must improve the independence estimate for these three special geometric
arguments or use extra EC17 structure; merely completing the known proof will
not work.

The exact long-block identity closes deeper diagonal clocks as a construction
lane: modulo `3^d`, later ternary factors kill every carry except the final
consecutive carry; exact long-block zero can also be signed cancellation.
Only extend exact consecutive hits, balanced full-congruence hits, or a
symbolic theorem controlling the canonical representatives.  Do not widen
fixed-depth phase scans.

```text
consecutive-cycle artifact 18e65eb08d8d9960cacd88868779d17fdcca8f6912c97530c76fd91c851b951e
consecutive-cycle worker   bb7f53a312a6e7a7362c08743b962a17c516e9a13a250f5bfd6fe04d7640cfed
balanced-carry artifact    6a619989230c623cecdc8c10b8fb963c1f395568a1e5867d0e0186031cef9187
rational artifact          356994f129961e385b0dd6b0423d8ea96c96411c15a19ce501559c1d315bab93
```

A fresh 8,794-target `lake build` and `Audit.lean` pass at `f79192e`; the new
declarations use only the standard audited axioms.  The earlier failure was a
transient race while the companion was actively rewriting
`EtherCounterBareGlue.lean`, not a committed regression.  Akdeniz independently
rebuilt the consecutive-cycle artifact with 30 workers; the detached R23 PARI
service remains healthy.  PSC is idle because these are CPU big-integer
recurrences.

### 06:28 EDT continuation — fixed-depth clocks and canonical carries

There is no counterexample.  Companion commit `a9ed874` kernel-checks the
fixed-depth hierarchy: for every `d`, a hypothetical period-three ray
eventually satisfies the predecessor condition modulo `3^d`, whose required
coefficient has period dividing `3^(d-1)` in `q`; cofinally many failures in
one fixed window exclude the ray.  QM118 in the same commit is the guardrail:
one sufficiently wide appended binary block can hit any chosen fixed-depth
class.  Do not infer rationality, automaticity, or cofinal mismatch merely
from the periodic target.

The exact dense Akdeniz audit covers all 71 positive `[-1,1]^3` schedules,
starts through eight, and every `q=5..256` (17,892 rows):

```text
mod 3:    6,025 matches / 11,867 failures;  0 schedules have a no-match phase
mod 9:    2,014 matches / 15,878 failures;  0 schedules have a no-match phase
mod 27:     635 matches / 17,257 failures; 69 schedules have a no-match phase
mod 81:     217 matches / 17,675 failures; 71 schedules have a no-match phase
mod 243:     76 matches / 17,816 failures; 71 schedules have a no-match phase
counterexample: null
```

Thus mod 27 is the first discriminating finite window, not a cofinal theorem.
The two mod-27 exceptions are `(0,1,1)` from branch 8 and `(1,1,0)` from
branch 6; both lift to clean no-match cells modulo 81.

Commits `40f4265`/`2e8010c` formalize the canonical same-cycle extension carry

```text
carry_D(q)=r_(U(q)+D) // 2^U(q)
```

and prove that every ray makes it eventually zero, for arbitrary covered
`D(q)`.  The dense 24-bit artifact finds the first extension bit nonzero in
8,869/17,892 rows and some bit among the first 18 nonzero in every row.  The
longest observed zero run is 17 bits at `(0,1,0)`, branch 3, `q=167`; the next
is 16 bits at `(0,0,1)`, branch 4, `q=31`.  These are finite statistics only.

For the strongest mod-27 cell `(1,1,0)`, start 8, compose nine cycles at
source `q=0 mod 9`:

```text
2^(432q+4221)*y_q=3^(324q+3051)*r_q+D9(q),
y_q=13 (mod 27).
```

For `q>=99`, `p=U(q)-(432q+4221)>0` and the exact signed carry

```text
r_(q+9)-y_q=2^p*C_q
```

satisfies `r_(q+9)=13 mod27 <-> C_q=0 mod27`.  The new artifact checks all
17 sources `99,108,...,243`; their `C_q mod27` values are

```text
14,11,5,24,16,3,22,23,12,3,6,19,13,17,18,14,5.
```

Companion commit `6b96f89` kernel-checks the nine-cycle reduction, including
signed carries.  Commit `6f05ff5` kernel-checks the analogous 27-cycle/mod-81
budget and carry interfaces for both lower-depth exceptions.  Neither asserts
the missing universal nondivisibility premise.  Exact research-side block
composition shows why consecutive fixed-depth clock blocks do not provide a
naive induction: the huge ternary factor annihilates the earlier carry modulo
`3^d`, and a new terminal carry replaces it.  The live proof targets are
direct cofinal carry nondivisibility, a moving-depth invariant, or a sharper
three-theta arithmetic theorem.

```text
fixed-depth artifact    c4c93e5db3320803e8f434441bd555601f3ab439638a9b0a82c02adbac91c512
extension-carry artifact f05b656c0297a9af416f28f4da5df34d081a281636cf45f3379ae6dc90239978
nine-cycle artifact     c8358802829067b98fac11d7cc798de5d914cc59f79c219625fce2052fa537c3
```

The fixed-depth and 24-bit extension artifacts have both been independently
reconstructed on Akdeniz with 30 workers; the nine-cycle artifact was rebuilt
and verified locally.  A full 8,792-target Lean build and `Audit.lean` pass.
PSC remains unused because the workload is exact big-integer CPU arithmetic.
The detached R23 PARI service is still healthy and incomplete.

### 05:45 EDT continuation — eventual zero lift and the one-trit hinge

There is no counterexample.  Companion commit `5a3413a` proves the sharper
separator `3^971<2^1539`, the tight 971st-power core bound, and the exact gap

```text
971*G0(q)-306*G1(q)=q*(6*B+33+9*K*(q-1)),

G0=q*(462*B+2235+K*(693*q-3141)),
G1=q*(1466*B+7092+K*(2199*q-9967)).
```

With `U=ceil(G0/306)` and `V=ceil(G1/971)`, the gap eventually forces
`core(3q)<2^U`.  Hence every hypothetical period-three ray eventually has
normalized CRT lift exactly zero.  QM116 also strengthens every exact replay
or raw-congruence failure at precision `P` to the finite bound `P-V<L0`.

Commits `78a6d05` and `43cdba7` remove the CRT candidate from the decisive
endpoint.  If `r_q` is the canonical future residue modulo `2^U`, a ray must
eventually satisfy

```text
2^(8*branch(3q)+15)*r_q
  =17 (mod 3^(6*branch(3q-1)+11)).
```

Commit `d9398a8` proves the one-trit consequence `r_q=1 mod 3` and a direct
no-ray consumer for arbitrarily late violations.  This is the preferred live
target: prove, for every positive period-three schedule,

```text
forall Q, exists q>=Q, r_q % 3 != 1.
```

The exact Akdeniz dyadic artifacts cover all nine positive-gain words in
`[-1,1]^3`, all 71 positive starts through eight, and
`q=5,8,16,...,512` (568 rows each).  Every normalized residue and every CRT
candidate fails replay; every raw `U`-bit residue misses the full predecessor
class; 350/568 already miss `1 mod 3`.  The weakest replay, CRT, normalized-
gap, and padded-gap initial-core bounds are respectively 1,057, 3,084, 9,
and 1,065 bits.  Every artifact says `counterexample:null`; all have been
independently reconstructed.

```text
normalized margin artifact  2c51f510e4b86f0fafae489df8ad54749eb78e4aadf70511dcf5b0bcd073b720
normalized CRT artifact     f0754083c04d5912b7719f6f7c72455905d7eb23d265efde2eeb9b5d612da20c
tight raw-residue artifact  c964e93d7290832cb61f3beac17892b148b8319096411865e07c9dbb46c2832a
```

Do not infer cofinality from the dyadic rows.  A research-side exact-algebra
derivation, not yet kernel-checked, says that the binary mass from `q` to
`2q` already exceeds `U(q)`, so the terminal residue at `2q` is completely
erased modulo `2^U`.  Treat this as guidance against a dyadic induction until
formalized.  The missing theorem appears to require control of the canonical
reduction carry (equivalently the next Hensel digit of the finite three-theta
defect), not just the low-bit recurrence.

The independent analytic audit also closes one tempting overreach.  For any
fixed ternary depth and any periodic target clock, sufficiently large binary
precision gaps allow each next block to be chosen to hit that clock while the
resulting 2-adic number remains nonrational.  Thus eventual fixed-depth
matching does not generically imply rationality or automaticity.  The live
proof must exploit the EC17/three-theta coupling across cycle indices.  The
finite extension lemma has been sent to the companion as QM118; until its
reply, treat the infinite countermodel as a research-side guardrail.

### 04:55 EDT continuation — normalized residue and CRT no-ray consumers

There is no counterexample.  Companion commit `a6619c5` proves the exact
residual-width identity

```text
665*(E_upper+306) = 306*E_lower + W,
W=203490*(L0+1)+q*(307230*(B-3)+51)+9*K*q*(q-1).
```

The scaled terminal bit length lies strictly between `306*E_lower` and that
value plus `W`.  Its leading uncertainty is only `K*q^2/22610` bits.

Companion commit `52cd3e1` formalizes QM100--QM107.  Put

```text
A(q)=q*(462*B+2235+K*(693*q-3141)),
U(q)=(A(q)+305)/306,
L0=Nat.log 2 (core(0))+1.
```

Then `bits(core(3q))<=L0+U(q)`.  A future-forced residue at precision
`P=U(q)+R` has normalized margin at most `L0`; if the canonical residue fails
the prescribed replay, then `R<L0`.  Lean packages both cofinal consumers:
unbounded exact margins or replay failures at unbounded paddings exclude the
period-three `Ray`.  Finite rows do not establish either premise.

The stronger normalized CRT endpoint takes binary precision exactly `U(q)`
and combines it with the immediate predecessor residue modulo
`3^(6*n_previous+11)`.  A canonical CRT representative satisfying the two
congruences and strict product range, but failing the required replay, forces

```text
6*n_previous+11 < L0.
```

Because positive cycle gain makes `n_previous` unbounded with `q`, cofinal
failed CRT rows exclude the schedule.  This is the preferred worker target:
no guessed padding and no real logarithms.

Companion commit `44c43b0` closes the replay-certificate seam.  An
under-divisible numerator is an immediate failure.  An over-divisible
numerator has an even quotient and needs one further hypothetical transition
before it contradicts the forced odd core.  The Python workers now emit the
failure kind, exact replay length, certified prefix length, and a SHA-256 of
the reconstructed core list; their verifiers reconstruct everything.

A stable local `lake build` passes all 8,790 targets.  The Akdeniz run now
uses the theorem-relevant dyadic subsequence
`q=5,8,16,...,512`, not a dense interval, over all positive schedules with
increments in `[-1,1]` and starts `1..8`.  It is still finite evidence.  PSC
is idle because these arbitrary-precision modular inversions are a CPU task,
not a useful GPU kernel.

### 04:08 EDT continuation — period-three cores must carry quadratic bits

There is no counterexample.  Companion commit `2d016ab` strengthens the
universal slowdown theorem to an explicit finite horizon.  From every time
`K`, a positive EC17 execution has a branch-ceiling step in

```text
K <= t < K + Nat.log 2 (core(K)+1) + 1,
328*n_(t+1) < 390*n_t+141.
```

Companion commits `17de520`, `6aeb427`, and `3ebdb72` establish the new
period-three resource invariant.  If `G>0` is the cycle gain, then for every
`q>=5`,

```text
2^(q*(435+G*(84*q-412))) < core(3*q)^41,

(q*(435+G*(84*q-412)))/41
  < Nat.log 2 (core(3*q)) + 1.
```

Lean also refutes every eventual affine upper bound on this bit length and
constructs a violating cycle explicitly from the cutoff and affine
coefficients.  The branch counter itself is only linear in `q`; the ordinary
core must carry quadratically many bits.  This is the precise answer to the
resource question and a search-design theorem, not a counterexample.  Do not
enumerate bounded raw cores as the main period-three state space; use
normalized residues/theta data or another compressed representation that can
carry the forced quadratic growth.

The source audit has closed two further sufficient-theorem shortcuts:

1. Amou--Väänänen (2005) gives linear independence with respect to the full
   set of expanding places.  The EC17 parameter expands at both the real and
   2-adic places.  Its real series value is not the positive ordinary core,
   so this simultaneous-place theorem does not exclude the Q2-only relation.
2. Väänänen (2013), Theorem 4, is genuinely non-archimedean, but its cited
   Amou--Matala-aho--Väänänen (2007) criterion has an explicit auxiliary
   threshold.  Commit `92416b1` kernel-checks for every `0<delta<1,rho>0`
   in the three-value specialization that

   ```text
   B/A < 13/12 < 3*log(3)/(4*log(2)).
   ```

   The second strict inequality is proved from the exact separator
   `2^13<3^9`.  Hence the 2007/2013 sufficient condition misses the EC17
   parameter uniformly.

A fresh stable `cd KontoroC && lake build` passes all 8,790 targets.  The
earlier namespace error was a build race against a newly committed dependency,
not a committed Lean defect.  The current dirty
`experiments/kontorovich/unit_charge_morphic_audit.json` fails reconstruction
from its checked-in verifier; preserve it but do not cite it.  Akdeniz was
useful for retrieving the 2005, 2007, and 2013 primary PDFs.  PSC is idle:
there is still no theorem-guided GPU target worth running.

The live period-three hinge is unchanged in kind but much narrower in form:
prove the exact three-theta Q2 linear form nonordinary, reduce it to fewer
values, or prove a cofinal nonstabilization theorem for its exact residue
bits.  Finite CRT widening alone remains a lower-bound exercise.

Companion commit `e385967` makes the narrowing quantitative and nearly
optimal.  With `B=n_0+n_1+n_2`, `G=cycleGain`, and
`L0=Nat.log 2 (core(0))+1`, every `q>=5` satisfies

```text
2^(q*(7869+G*(1506*q-6826))) < core(3*q)^665,

core(3*q)^306 <
  2^(306*L0+q*(462*B+2235+G*(693*q-3141))).
```

The two leading bit coefficients are
`(1506/665)G=2.264661654...G` and
`(693/306)G=2.264705882...G`.  The proof uses the exact adjacent separators
`2^1054<3^665` and `3^306<2^485`; the upper initial contribution is `L0`, not
the numerical core.  This creates a principled shifted-window target.  Define

```text
A(q)=q*(462*B+2235+G*(693*q-3141)),
U(q)=ceil(A(q)/306).
```

The upper theorem gives `bits(core(3q))<=L0+U(q)`.  Compute the future-forced
residue `r(q,P)` modulo `2^P` at `P=U(q)+R`.  If

```text
margin(q,R)=bits(r(q,P))-U(q)=R-leadingZeroBits(r(q,P))
```

exceeds `L0`, the actual core is too small to represent that residue, a
contradiction.  Hence any ray must satisfy `L0>=margin(q,R)`; cofinally
unbounded exact margins exclude the schedule.  This is the next formal Lean
request and exact worker design.  It converts computation into certified
lower bounds on one fixed initial bit length and, in the unbounded case, a
universal no-ray theorem.  Do not claim the implication until CLEAN_LEAN has
checked its off-by-one and shifted-prefix details.

### 03:23 EDT continuation — unconditional geometric closure and sharp schedule budget

There is no counterexample.  Companion commit `a6ce60a` proves the elementary
QM84--QM87 route in `EtherCounterGeometricMahler.lean` and exposes its stronger
schedule-independent core.  For every positive EC17 execution, the weighted
defects contract by more than a factor of 15 and every finite accumulated
defect is below one.  Exact finite backward unrolling therefore gives

```text
core(0) <= P_N*core(N) < core(0)+1,
P_N=prod_(t<N) 2^(8*n_(t+1)+15)/3^(6*n_t+11).
```

For `n_t=n0*d^t`, `d>=2`, every backward coefficient is larger than two.
Taking `N=core(0)+1` gives a finite contradiction.  Thus every geometric EC17
schedule is now unconditionally impossible, both for the abstract ray and the
literal `TernaryCoreOrbit`.  Wang/Hadamard and the Mahler identities remain a
valid independent value-theory audit, but are no longer on the no-orbit
soundness path.

Companion commit `26cacdb` completes the sharper search-facing QM89 endpoint.
For `S_N=sum_(i<N)n_i` and every `N>0`, any positive EC17 execution satisfies

```text
328*n_N < 62*S_N + 328*n_0 + 100*N + 41*core(0).
```

Lean proves the exact closed product, the telescoping identity for the two
branch sums, and the inequality from `3^41<2^65` plus the universal product
budget.  The history coefficient is `62/328≈0.1890`.  Use this as a necessary
prefix prune before generating a forced core.  It excludes geometric growth,
but a positive-mean period-three increment word grows only linearly and is not
closed by this ceiling.

Companion commit `007c252` adds the local recurrence form.  For every starting
time `K`, a positive EC17 survivor has some `t>=K` with

```text
2^(8*n_(t+1)+15) <= 2*3^(6*n_t+11).
```

Equivalently, the backward multiplier is at most two at arbitrarily late
steps.  An eventual policy that makes every step more than two-expanding is
therefore impossible.  This is a cheap online prune and the sharp answer to
the resource-growth question: the combined public register escapes, but the
branch counter itself must undergo infinitely many compensating slowdowns.

Companion commit `eb06dcb` converts the same statement to the direct exact
integer threshold

```text
exists t>=K, 328*n_(t+1) < 390*n_t+141.
```

Thus the next/current branch ratio must return arbitrarily late below the
asymptotic value `390/328≈1.1891`, up to the displayed additive constant.
This is the simplest search-facing adversarial check for a nonlinear
dispatcher.

A fresh local `lake build` and full `Audit.lean` pass.  The new audited
endpoints depend only on standard `propext`, `Classical.choice`, and
`Quot.sound`.  The period-three target remains the arithmetic one: obtain a
special fixed-linear-form theorem for its exact three theta values, reduce the
combination to fewer values, or prove cofinally unbounded exact CRT/residue
failures.  Do not widen the finite box without one of those structural inputs.
The 1991 Väänänen--Wallisser paper and the 2011 p-adic dimension paper have
relevant abstracts/previews but no fully source-audited theorem in hand; do
not cite them as crossing the three-slot boundary.

Akdeniz's detached degree-23 exact PARI job (PID 3284717) is still active after
about 17 hours at essentially one full core and has not printed `R23_DONE`.
PSC remains idle because there is no theorem-guided GPU target.

### 02:54 EDT continuation — geometric bridge lands; CRT sharpens period three

There is no counterexample.  Companion commit `1d3721a` completes
QM78--QM81 in `EtherCounterGeometricMahler.lean`.  For every `n0>0,d>=2`,
Lean now proves the geometric exponent identities, finite EC17 backward
unrolling, 2-adic terminal vanishing, Mahler functional equation, and

```text
u0=-(17/3^(6*n0+11))*G(2^(8*n0*d)/3^(6*n0*d)).
```

It also attaches the endpoint to the literal `TernaryCoreOrbit` interface and
proves that `IsPadicIrrational` of the value excludes the orbit.  This makes
the geometric family a kernel-checked conditional no-go; Wang/Hadamard remain
explicit published analytic inputs rather than Lean proofs.

The companion requested the primary statement of Wang Theorem 1.  The journal
PDF is now recovered: definitions are on printed p. 187 (PDF p. 1), Theorem 1
on printed p. 188 (PDF p. 2).  `docs/FOR_CLEAN_LEAN.md` now records the full
hypotheses and literal substitution

```text
p=2, rho=d, N=1, Q0=a*z, Q1=1-u,
g=a*z, m0=1, M0=d.
```

It also replaces the shorthand scalar-descent claim by the correct finite
homogeneous-linear-system argument.  Companion commit `12236bb` separately
bridges the literal 1989 Väänänen--Wallisser linear-independence conclusion to
the project's `IsPadicIrrational` consumer.

A stronger exact finite period-three restriction now uses both sides of
EC17.  From the immediate predecessor branch `n`, reduction modulo its full
ternary coefficient gives

```text
u_next=17*2^(-(8*n_next+15)) (mod 3^(6*n+11)).
```

The infinite prescribed future fixes the same core modulo `2^P`; CRT fixes
one representative modulo `2^P*3^(6*n+11)`.  The new worker/artifact

```text
experiments/kontorovich/breakoff_ether_period3_crt_sieve.py
experiments/kontorovich/breakoff_ether_period3_crt_sieve_audit.json
verifier 8ac1eea9e627d7277c83d5a12b422f94a5cf6963c3f40ee32382a0c6c5885916
artifact 4706196c2ba7f5eb5edb78ae9936349674e62d1e5239a63e8b5558ff97b17b40
```

recomputes the same 2,340 words and 72,156 positive schedules at `P=4096`.
Every least CRT representative fails after 7--47 transitions.  The exact
rowwise successor-core lower bound is now
`2^4096*3^(6*n_previous+11)`, uniformly `>=2^4096*3^17`.  This is still finite
and does not provide the cofinally unbounded precision family needed for a
universal no-orbit theorem.  QM82--QM83 request the cheap Lean modular/CRT
wrapper.

The primary 2006 Koivula--Sankilampi--Väänänen theorem packages the three
period-three values exactly as one `d=3` family, but its sufficient height
condition fails:

```text
6*log(3)/(8*log(2)) > (1+sqrt(37))/6.
```

Thus it reproduces the same narrow boundary rather than closing period three.
The attempted extension of Bézivin's Borel--Dwork proof also fails honestly:
the normalized auxiliary coefficients grow superexponentially at the complex
place unless the 2-adic relation also holds complex-analytically.  Do not
claim that route.

### 02:34 EDT continuation — rational period-three closure and a geometric Mahler target

Companion commits `d0faf96` and `82198ac` complete the homogeneous rational
extension of QM69--QM72.  For a reduced univariate denominator `D`, the cleared
scaled equation gives `D(rz)|D(z)`.  Equal degree and `r>1` force `D` to be a
monomial.  Substitution and least/greatest support then contradict the
quadratic forcing.  Thus no homogeneous rational period-three potential
`x^-1 f(y/x)` exists.  The arbitrary nonhomogeneous bivariate rational case and
an accidental rational value of the three theta sums at one orbit remain open.

The next theorem-driven nonlinear schedule is

```text
n_t=n0*d^t,  n0>=1, d>=2.
```

For EC17 put

```text
e_j=(d^j-1)/(d-1),
a=2^15/3^11,
z=2^(8*n0*d)/3^(6*n0*d),
G(z)=sum_(j>=0) a^j*z^e_j.
```

Exact backward algebra gives the proposed universal endpoint

```text
u0=-17/3^(6*n0+11)*G(z),
G(z)=1+a*z*G(z^d).
```

The bounded artifact

```text
experiments/kontorovich/breakoff_ether_geometric_mahler.py
experiments/kontorovich/breakoff_ether_geometric_mahler_audit.json
verifier d22be4b977f9f6ba98d96b1426533634514237dc6ebfccfecd37b48f7f303e81
artifact 39ab4d6025729d2eced00cb8a4a331ba5640c41832cd05bc270c078823b85bbe
```

replays nine literal schedules through six transitions and checks 3,584
coefficient identities.  Wang's visually audited 2006 p-adic Theorem 1 applies
with `rho=d`, theorem degree one, and `M0=d`, so its size condition is simply
`d<d^2`.  Hadamard gaps plus scalar descent give the function-transcendence
premise.  QM78--QM81 in `docs/FOR_CLEAN_LEAN.md` request a kernel-checked
universal EC17-to-value bridge and irrationality consumer.  Until that lands,
this is a source-checked proposed conditional closure, not an all-parameter
machine-checked theorem.  It supplies no orbit and no counterexample.

Akdeniz's detached degree-23 exact Thue job remains active after roughly 16
CPU hours and has printed only its irreducibility/class-number header.  Do not
record a result unless `R23_DONE` appears.  PSC remains idle because this
Mahler work is symbolic rather than a useful GPU enumeration.

### 02:20 EDT continuation — finite coboundaries close; growth is automatic

Companion commit `1154476` completes QM67--QM68.  Using
`Finsupp ℤ ℚ` for one homogeneous Laurent slice, the least and greatest
support exponents give incompatible necessary forcing indices.  Slicing by
total degree extends this to every finite Laurent polynomial.  Therefore the
period-three defect has no finite Laurent/exponential-polynomial potential.
This does not exclude a non-Laurent rational function, an infinite series, or
an accidental rational theta value at one orbit.  The algebraic reduced-
denominator route to the rational extension is now in
`docs/FOR_CLEAN_LEAN.md`.

Companion commit `a732905` completes QM75--QM77.  Every legal normalized ether
step satisfies

```text
15*Y_t < Y_(t+1),
15^t*Y_0 <= Y_t.
```

Thus the branch and core counters can trade off, but their canonical combined
public register grows exponentially.  Any infinite legal ordinary execution
is automatically an outward escape.  Future constructive work should target
perpetual legality and ordinary-address regeneration, not a separate growth
heuristic.  No such execution or counterexample is known.

### 02:12 EDT continuation — infinite residue seam and literal period-three algebra

Companion commit `def4c52` completes QM62--QM65 and QM73--QM74.  The finite
least-residue theorem now has the exact unbounded-precision consumer: an
infinite cofinal family of exact prefix failures excludes one prescribed
ordinary schedule.  The current 4,096-bit artifact is still finite and does
not instantiate that endpoint.

The same commit composes three literal EC17 steps under an affine three-phase
branch law.  The cycle defect has exactly the monomials

```text
Y^(2q), (X*Y)^q, X^(2q),
```

with the phase coefficients requested in QM65.  This is the machine-checked
input for the finite-Laurent coboundary no-go in QM67--QM68, which remains in
progress.  The general derivative threshold is also formalized, and every
`sigma>=1` satisfies

```text
Gamma(3,sigma)<1/12<5/32<gamma.
```

Thus derivative order cannot rescue period three using the same 1989
sufficient theorem.  A sharper fixed-linear-form theorem or an infinite
residue nonstabilization argument is still required.

While starting the independent Hilfssatz layer, the companion found that the
round-188 Skolem root product was parsed with the subtraction outside the
product.  It corrected the definition and added factorwise root-vanishing
regressions.  The merged full `KontoroC` build and axiom audit pass.  This is
a semantic correction and proof progress, not a counterexample; no infinite
ordinary EC17 execution is known.

### 01:31 EDT continuation — exact period-three core lower bounds

The first constructive search beyond the period-two theta obstruction is an
ordinary-stabilization sieve on EC17, not a raw seed scan.  At precision `P`,
the infinite recurrence forces one residue `r_P mod 2^P`.  If an ordinary
core were below `2^P`, it would equal the least representative `r_P`; exact
forward failure of that integer therefore proves a `2^P` lower bound for the
prescribed schedule.

The new worker and Akdeniz artifact are

```text
experiments/kontorovich/breakoff_ether_period3_sieve.py
experiments/kontorovich/breakoff_ether_period3_sieve_audit.json
verifier 82ac3a9e463a95c573c4f8f30aa66eac420cf89bd85de40869a5e10fd2908d56
artifact bd7cf4b64a68c8146a6144c37d3a20098e2b84285a75bec2d2f393944f71848b
```

Akdeniz built and independently recomputed the exact box in about 17.5 wall
seconds per pass on 32 cores.  It covers all 2,340 genuine period-three words
with components in `-8..8` and positive cycle sum, all positive schedules
starting at branches `1..32`, and 4,096 bits of precision: 72,156 schedules
total.  Every least representative fails after 7--47 EC17 steps, so the
generic residue lemma would give `u_0>=2^4096` throughout the box.  The
largest leading-zero run was only 16 bits; no stabilization anomaly appeared.

QM57--QM59 ask the companion to kernel-check the generic residue/lower-bound
consumer.  This is a finite lower bound, not a no-orbit theorem and not a
counterexample.  Scaling the same box has diminishing conceptual value; the
priority remains either a stronger three-value `Q_2` independence theorem or
a special EC17 coboundary/modular identity that closes or isolates a
period-three program.

Companion commit `11eaba0` now completes QM53--QM56.  It works directly with
the literal EC17 recurrence, proves the even/odd theta split and terminal
vanishing, and exposes the exact two-value external independence seam.
Accepting Väänänen--Wallisser (1989), every positive-mean period-two increment
tail is impossible.  The same commit starts an independent formalization of
the paper and proves its theta functional equation; the Skolem--Hermite
linear-independence proof remains unfinished.

### 01:22 EDT continuation — periodic increments expose a period-three boundary

Companion commit `2150534` divides out the exactly forced factor of three
after the first successful ether step.  In positive branch coordinates the
public state now satisfies

```text
2^(8n_(t+1)+15)u_(t+1)=3^(6n_t+11)u_t+17,
u_(t+1)=1 (mod 3).
```

This is the preferred search state.  For a repeated integer increment word
`d_0,...,d_(L-1)` with positive cycle sum `K`, the exact research worker

```text
experiments/kontorovich/breakoff_ether_periodic_theta.py
experiments/kontorovich/breakoff_ether_periodic_theta_audit.json
verifier e0c29f74b3c4b34513309f056428a4767faa9d30e860177be9a570b8689e65cc
artifact 2d1e80094f494776f6a6fb3338a41403e806695db34b8feffab98ce391962f68
```

splits the backward series into `L` theta values.  It compiles 15 literal
public schedules through nine core transitions, including within-cycle
down-steps; checks every finite rational and 2-adic identity; and audits 624
theta coefficients.  Companion commit `11eaba0` now kernel-checks the
universal period-two algebra and exact external-theorem seam.

The external theorem's exact size bound passes for period two but fails
already at period three:

```text
gamma<1/6<Gamma(2,0),
Gamma(3,0)<5/32<gamma.
```

So, conditional on the cited theorem, all eventual positive-mean increment
words of length at most two close; length three is the smallest
theorem-escape target.  A failed sufficient inequality is not a witness.  The
constructive search should use EC17 and test period-three increment programs
for additional modular/coboundary obstructions before attempting broader
payload-dependent controllers.

### 01:09 EDT continuation — fixed-rate ether counters close by partial theta

Two new companion theorems sharply constrain the honest zero-tail search.
Commit `1c449e6` proves that every ordinary source eventually has zero
canonical extension digits; commit `bf8b7c2` proves that no infinite positive
ether orbit has an eventually periodic branch tail.  A finite controller and
an infinite preloaded source are both dead.  The missing controller must use
genuinely unbounded public state to emit a genuinely aperiodic schedule.

The simplest unbounded schedule, `n_t=n_0+k*t`, is now conditionally closed by

```text
experiments/kontorovich/breakoff_ether_linear_theta.py
experiments/kontorovich/breakoff_ether_linear_theta_audit.json
verifier 1a53504df1091e65054c5647b6ef59ff2ed04f4ca58840604de277469821b7a5
artifact 9190bf6ea1a85d3bffc81c9f066a3af8e96529fc75267b147096c3e2c2491dc2
```

The exact odd-part recurrence is

```text
2^(8n_(t+1)+15)h_(t+1)=3^(6n_t+11)h_t+51.
```

For every `n_0,k>=1`, backward unrolling gives a single partial-theta
candidate at paper parameters

```text
q=3^(6k)/2^(8k),
alpha=2^(8n_0+15)/3^(6n_0+11).
```

The artifact checks 16 finite schedules through eight transitions, 4,096
coefficient conversions, and the elementary Väänänen--Wallisser hypotheses
uniformly.  Accepting the same inspected external 1989 theorem used for the
unit bank, every candidate is irrational in `Q_2` and hence nonordinary.  The
theorem is cited, not reproved.  Nonlinear/payload-dependent counters and
bounded aperiodic branch schedules remain open.

### 00:53 EDT continuation — finite zero-tail transition, not a counter write

The live ether-counter pivot now has an exact artifact:

```text
experiments/kontorovich/breakoff_ether_dynamics.py
experiments/kontorovich/breakoff_ether_dynamics_audit.json
worker   f5c93af8af44fd7f789feaa92dd738d253c9a8e0d916a0040a29c947855f7497
artifact a2b0eeddb2667c0eb74305405585f479e2a861923cb01a7fc117c9c13a14395f
```

For every linked branch pair it proves coefficientwise

```text
q=a_(n,m)+2^(8m+15)t,
q'=b_(n,m)+3^(6n+11)t.
```

The default audit checks all 25,600 pairs in `1..160`, two tail members each,
then exhausts `160^3=4,096,000` canonical triple prefixes for a zero-address
extension into branch one.  The unique hit is

```text
115 -> 59 -> 9 -> 1,
address widths 487,87,23,
last address digit 0.
```

Adversarial audit corrects the interpretation: the initial tail bitlength is
`574=487+87`, so the zero 23-bit digit begins exactly after the natural's last
nonzero bit.  It is ordinary padding, not independently written storage.  The
three successor edges have expanding tail slopes with floor log-scale excesses
`624,491,80`, but numeric scale growth is not information regeneration.  The
positive public register has 463 decimal digits.  Exact
replay covers four public steps, 192 linked affine members, and 384 literal
gate macros.  It then halts at a register with `v2=2`.  `counterexample=null`.

Do not treat the hit as evidence of infinity.  Every ordinary accepted tail
has eventually zero canonical address digits.  The actual criterion is an
infinite public branch itinerary whose digits are eventually all zero,
equivalently a nonhalting orbit of the deterministic tail-zero/current-offset
dynamics.  This witness enters that regime once and immediately halts.

### 00:45 EDT continuation — fixed-lasso chart tower closed

`experiments/kontorovich/yah_chart_clock.py` now certifies a third
restorative edge.  On `w=249+256z`, the second-edge register has
`T=221 mod 256`; five macros with heads `01021` and carries
`[0],[1,1],[1],[1,1],[1,1]` return to a seven-trit reservoir, gain two cells,
and write `256*U=3^7*T+1`.  The output is again a two-adic isometry and
`U(z) mod 2=z mod 2`.

The normalized leading scale starts at `269001/262144` and obeys
`rho'=3rho/2` on head zero and `rho'=3rho/4` on heads one/two.  Its abstract
head word begins `01020210102101020210` and is not eventually periodic.  Do
not call this an infinite actual YAH itinerary: the finite correction has
only been separated from head boundaries for the five new phases.  The exact
segment identity

```text
3^J/2^S = 3^(J-M) * rho_end/rho_start
```

shows that every positive-space edge has slope greater than `3/2`; the
proposed nonexpanding-positive-space escape is closed.

The more decisive theorem is companion QM42: every current chart edge only
restricts a lasso parameter as `t_n=a_n+2^(k_n)t_(n+1)`, `k_n>0`, and any
ordinary natural tower of this form is eventually zero.  The third block's
possible reblocking was checked separately.  Its 19-layer carry action is

```text
f(r)=(262145*r+449133) mod 2^19,
f^2(r)=r+111834 mod 2^19,  v2(111834)=1,
```

so every carry state has full period `2^19`; the nominal block is one whole
cycle and writes no repetition-counter bits.  The all-depth LCG hypotheses are
checked through layer 24 and cycles are exhausted through 18.  QM45/QM46 ask
the companion to formalize the universal full-period/reblocking statement;
until then, keep that generalization separate from the kernel-checked QM42.

The current exact hashes are:

```text
worker   6cd98e32a22c47432d5d22d31a551afed0c5175f9abd094b7cea36385191d8ab
artifact 2c55cec21f81b563f181803a26ef5dc7489e13c668317af17438ace6220a29ab
```

Companion commit `9021e86` contains the Lean proofs of the third arithmetic
edge, abstract chart clock/slope identity, and lasso-tower drain theorem.  A
local `lake build KontoroC` passes.  Do not edit or stage the companion's
`KontoroC/` or `CLEAN_LEAN/` files; its untracked `KontoroC/Scratch.lean` is
also out of scope.

The live lane is no longer a fourth fixed lasso restriction.  Analyze the
autonomous public `breakoff_ether_counter.py` map, or another contextual YAH
pipeline, for an opcode which genuinely rewrites its surviving payload.  A
transition from branch `n` to branch `m` has exact tail form

```text
q=a_(n,m)+2^(8m+15)t,
q'=b_(n,m)+3^(6n+11)t.
```

Unlike a pure lasso pop, the odd multiplier can generate more binary
information than the next gate consumes.  Search for a symbolic invariant or
canonical tail-zero regeneration in this affine successor graph; do not
resume broad raw-seed searches.  No counterexample or infinite execution is
known.

### 20:53 EDT continuation

The shutdown bursts are now certified by
`experiments/kontorovich/yah_returned_burst.py` and its audit artifact through
`g=4`, using straight-line blocks rather than explicit blocks up to
268,435,456 trits.  The exact rows are `a_g=3,27,411,2971` modulo
`8,64,512,4096`, with head words `01,0102,010202,01020210`, gains `+g`, and
reservoirs `7+3g`.  Literal regressions independently replay `g=1,2`.

Do not extrapolate the head word: both `(01)^g` and `01(02)^(g-1)` fail in
the checked window.  The companion's returned-register isometry proves the
all-depth roots form a compatible nonordinary 2-adic tower, not an ordinary
source.

The requested collision edge has since been found on `u=35 mod 2048`.
Seven macros `0102021` with carries
`[1],[1,1],[0],[1,1],[1],[1,1],[1,1]` return to head zero and reservoir seven,
gain three cells, and write `2048*T=3^10*R+8`.  The artifact includes an exact
whole-cylinder SLP certificate and a 2,317,094-trit literal replay.  This is a
second affine edge but not a chart cycle.  Simple periodic alternation with
the first edge has composite ratio `3^16/2^19>1` and falls under companion
commit `2037f54`'s periodic affine no-go.  Next decode the new endpoint and
look specifically for nonperiodic control or a nonexpanding composite.  No
closure or counterexample is claimed.

Repository: `/Users/simon/Desktop/COLLATZ`

## CURRENT OVERRIDE — read this before the older detail below

The old 11:25 snapshot remains useful history, but the research target has
moved decisively from isolated quadratic/Thue transitions to **semantic
closure**.  Start with `git log --oneline -10`, the top README Diary entry,
and `docs/notes/kontorovich-closure-principles.md`.

The five current design laws are: conserve literal Collatz semantics across
every abstraction; allow only public/canonical state; regenerate every spent
delimiter; construct an endomorphism before collecting points; and demand
control of the next opcode rather than mere outward scale.  Opcode chaining
is useful only as a decoder-compatible semantic action, not a naked matrix
collision.

### New fundamental target: a thin trapping language

For a positive valuation word `w`, let `n=w.length` and `S=sum(w)`.  The two
weights

```text
p(w)=2^(-S),       q(w)=3^n/4^S
```

are both Kraft weights because their one-letter masses sum to one.  Every
outward word has `q(w)>p(w)`.  Therefore a prefix-complete valuation decoder
cannot be outward on every leaf: completeness would give `sum p=1`, while the
second Kraft inequality gives `sum q<=1`.  Quantitatively, a prefix family
whose every macro has slope at least `lambda>1` has ordinary mass at most
`1/lambda`; after `N` closed generations, at most `lambda^(-N)`.

Lean commit `da9fa59` constructs explicit self-delimiting binary and
four-letter compilers, derives both Kraft inequalities from finite
prefix-freeness, and proves the full finite contradiction and quantitative
mass bound.  The countably infinite prefix-free bridge still uses an abstract
`tsum` interface.  Earlier commit `29c1d22` also proves the direct handoff
progression and closes every everywhere-defined one-register total-affine
handoff gauge: positive binary precision forces arbitrarily large powers of
two to divide one fixed positive initial slope.

The constructive target is now a finite **thin-trap certificate** over
`CompleteSplashState.next`: a public predicate `L`, explicit ordinary seed,
and public successor which preserves `L` and is strictly outward.  Commit
`298f5a3` now kernel-checks the complete wrapper: it iterates the proof-carrying
subtype, constructs `InfiniteCanonicalSplashOrbit`, and concludes false
Collatz.  The endpoint is therefore ready; the missing object is the explicit
seed and closed predicate.

The most principled parallel presentation is the 11-rule mixed-base string
system of Yolcu--Aaronson--Heule.  Their Theorem 3.17 says global termination
is equivalent to Collatz.  The new exact worker/artifact are

```text
experiments/kontorovich/yah_context_loop.py
experiments/kontorovich/yah_context_loop_audit.json
```

They check literal and morphic pumping certificates, replay the published
`12 -> ... -> 1` trace, classify all 3,125 letter maps and all 9,765,625
uniform width-two maps, and exhaust the 513,916-state induced graph through
length eight.  It is acyclic across 694,458 edges but contains a 299-rewrite
delay `834 -> 1079`; no reproduction certificate is present.  Worker hash:
`fd3bb7aff3922d4c5f8a927166deed462c557d2216302ac66e0d52efc04c89ab`;
artifact hash:
`6056acc0571af5199aebbe98fff34fe43ec512a5a71b00c4ed087e816c2aac2b`.

Commit `1b3459d` kernel-checks the generic literal and productive morphic
pumping constructions; `b733caa` pins the exact seven-symbol, 11-rule carrier.
Commit `9ca4360` universally collapses proper whole-word context growth between
canonical endpoints.  Commit `2d50381` closes every uniform marker-fixed
digit morphism, and `bfe12f0` removes the common-width premise: identity is the
only productive nonerasing marker-fixed independent digit-word morphism.
Do not widen the literal or letter-morphism searches.  The live YAH target is
a delimiter-changing or context-dependent/multi-block *internal* template.

The first such internal opcode is now exact.  Digit complement
`bin0<->bin1`, `tri0<->tri2` fixes `tri1` and permutes the six A-rules.  For a
digit buffer with affine pair `(s,t)`, the complement's terminal defect is
`s-t>=1`; saturated buffers attain one and execute

```text
bin1 tri2^n . ->+ tri2^(n+1) .
/ tri0^k tri2^n . ->+ / tri1^(k-1) tri2^(n+1) .
```

The worker/artifact are

```text
experiments/kontorovich/yah_carry_opcode.py
experiments/kontorovich/yah_carry_opcode_audit.json
```

They check 488,281 buffers through length eight and literally replay 1,443 run
macros; all 1,056 transfer cases with `1<=k<=32,0<=n<=32` have one dynamic
step, satisfy `2*y=3*x+1`, and grow.  Worker hash:
`bcf2549d767db12be3e769eca9d9e7f3fa2a89768367cbd5a78c2e2f675f675c`;
artifact hash:
`2f1fa472db827f5eeec746d31c993dd1806a7ea9510b4ad4055c5850ad11d9b8`.

This is not closure.  It spends one left `tri0` token and phase-changes the
rest.  The exact constructive target is a contextual recharge from the
`tri1` phase back to a nonexhausted `tri0` block, with the branch selected by
the incremented right counter.  Do not replace this equation by a wider word
or seed search.  Commit `0365c72` independently kernel-checks the carry defect
and all displayed run/transfer identities at arbitrary lengths.

The more fundamental quotient is now explicit.  One complete left-boundary
macro consumes a ternary head and applies one or two sweeps of a two-state
base-three quotient transducer to the entire suffix:

```text
M(0v)=Q_1(v),
M(1v)=Q_0(Q_0(v)),
M(2v)=Q_0(Q_1(v)).
```

Every odd sweep deposits a terminal `2`, so

```text
len(M(w))-len(w)=number_of_odd_sweeps-1.
```

A head zero never grows.  A head one/two grows by one exactly when the
canonical value is `3 mod 4`; that residue is the alternating signed checksum
of all trits.  This is Simon's nonlocal instruction principle in exact form.
The first chained opcodes convert a contiguous zero/one reservoir into
alternating combs rather than merely destroying it.

Commits `1a88c3e` and `b1dd87a` kernel-check this entire fundamental
interface: literal queue-macro traces, length charge, quotient semantics,
mod-four growth type, and alternating checksum.  Commit `64bccb8` proves an
ordinary natural cannot execute a growing macro forever, since every such
step has `4*(N'+1)=9*(N+1)`.

The independent worker/artifact are

```text
experiments/kontorovich/yah_queue_macro.py
experiments/kontorovich/yah_queue_macro_audit.json
```

They compare the quotient transducer with literal YAH replay on all 88,572
nonempty ternary words through length ten and replay 16,769 structured
run/comb cases through coordinate 64.  Worker hash:
`dd31ba052f11102ad0b9cc6dc13278c0254c8366ddb39f5b01c96a519b305745`;
artifact hash:
`865cf4fffcc00fbfbf722dae309a32056b2d140da31e77f78751c12c652f3f09`.

The exact target is now a finite cycle of contextual comb/packet *types* with
positive total space charge and a checksum-enabled successor.  A fixed-time
return on a simple family `A*3^n+B` cannot shift `n` positively, because
coefficient comparison would require `2^L*3^d=3^O`.  The closure clock must
therefore grow with a public counter or use a genuinely mixed scale.

The newest exact type is `P(s,q)=2 (0012)^s (01)^q`.  Its head-two macro is a
four-phase block compiler: both blocks advance phase by one modulo four;
`0012` emits `0210,1112,2022,0001`, `01` emits `02,11,21,00`, and the terminal
suffix is `1,2,22,empty` at phases `0,1,2,3`.  Thus it grows exactly when
`s+q=2 mod 4`.  This is a real chained distributed opcode, but the output
alphabet does not yet return to the packet alphabet.

Use the dyadic battery

```text
B(w)=2*len(w)+v2(N(w)+1).
```

Every growing macro conserves it: one new cell spends exactly two valuation
units.  Neutral/shrinking macros are the only recharge sites.  The worker now
checks their exact battery changes at every bounded word; the possible gains
are `v2(D+1)-3`, `v2(D+3)-4`, `v2(3D+2)-3`, or `v2(D+1)-2` in the four
nontrivial head/residue cases.  Commits `e293f7d` and `22ce54d` independently
kernel-check the complete ledger, packet value, and all four phase-recharge
formulas.  Commit `8bed065` proves that deeper recharge addresses cannot
eventually stabilize to one fixed ordinary packet coordinate.

There is now a stronger constructive primitive.  For target gain `G>=1`, put
`K=4G+1` and choose the unique phase-one address

```text
41*9^q+15=0 mod 2^(K+5),      q mod 2^(K+2).
```

The neutral packet `2(01)^q` writes `v2(N+1)>=K`.  A maximal subsequent
all-odd macro prefix contains at least `K-1` shortcut steps; canonical ternary
scale forces it to gain at least `G` cells.  The free lift survives as

```text
A_K(t)=3*(41*9^(q0+2^(K+2)t)+15)/2^(K+5),
v2(A_K(t)-A_K(u))=v2(t-u).
```

Thus recharge supplies arbitrarily large finite workspace and a lossless
2-adic address register.  It also emits a spatial resource: the normalized
defect has exact `v3=2`, so after `J` safe odd steps the endpoint word has
exactly `J+2` trailing `2` trits.  The exact worker/artifact are

```text
experiments/kontorovich/yah_recharge_amplifier.py
experiments/kontorovich/yah_recharge_amplifier_audit.json
```

They construct 32 symbolic targets, exhaust all 1,024 ten-bit lift values for
four targets, and queue-replay guaranteed gains one through four through a
369,187-trit packet.  Worker hash:
`6100b2c33f35f26e0fc7874c7981829f9733a234c60576739e1fc6fa41637a75`;
artifact hash:
`3969fab7fc0b5ed38972afc7b3ed6a9cabfcb4ae1447b27db4093afb8aa54c3d`.
The all-parameter scale, LTE, and reservoir schemas are in
`docs/FOR_CLEAN_LEAN.md` as QM14--QM19.  Commit `67eabe3` already
kernel-checks the generic scale core: `J>=4G` plus the exact all-odd defect
balance forces at least `G` new cells.  The dynamic maximal-prefix wrapper
remains open; commits `1a69d5b`, `6b5e34c`, and `0b8179a` now kernel-check
the LTE isometry, exact triadic valuation, and literal trailing-reservoir
theorem.  The remaining closure obligation is exact: a forward finite type
must decode `A_K(t)` into the next packet address without an external lift.

The first decoder instruction is exact at `K=5`.  Write

```text
q=17+128t,
R(t)=(41*9^q+15)/(3*2^10).
```

Four queue macros map `2(01)^q` to an exact lasso `U V^t Z` with generated
lengths `(31,256,6)` and defect `3^7R(t)`.  The block size is
`256=ord_(2^10)(3)`.  The next head-zero macro reads the least significant
register bit, since `R(t)=t mod 2`:

```text
R=2r:    3^7R-1 -> 3^8r-1,
R=2r+1:  3^7R-1 -> (3^7(2r+1)-1)/2.
```

Thus zero shifts the register and extends the clean reservoir from seven to
eight twos; one consumes the reservoir and changes chart.  At word level the
256-trit block flips carry and splits into exact 512-trit successor blocks for
`t=2s` and `t=2s+1`.  The worker/artifact are

```text
experiments/kontorovich/yah_lift_decoder.py
experiments/kontorovich/yah_lift_decoder_audit.json
```

They construct the all-parameter finite-state lasso certificate and replay
all 65 parameters through `t=64`.  Worker hash:
`db4b19a53c40e7d7c5b250b71e938741ed9b1ee68d3a11248f416b17c9f8ca10`;
artifact hash:
`7ca77895ea65644857c920835fecbba5b35520416867b04960b2e4ff0d1b01a5`.
The all-length request is QM20--QM25 in `docs/FOR_CLEAN_LEAN.md`.  The next
edge investigated was the bit-one chart's return to recharge with a newly
written unbounded register.

That edge now exists on the exact cylinder

```text
t=91+256u,  q=11665+32768u.
```

The incoming register is `R=151 (mod 256)`, so the bit-one collision is
followed by a neutral recharge and writes

```text
Rnext=(3^6R+1)/2^8.
```

Three more safe macros spend five odd shortcut steps and return to head zero
with exactly seven trailing twos.  Across the five-macro restorative opcode,
the word gains one cell.  The six all-parameter lassos all have a 65,536-trit
repeated block, with shapes

```text
(23327,65536,6), (23326,65536,6), (23325,65536,7),
(23324,65536,8), (23323,65536,10), (23322,65536,12).
```

The worker/artifact are

```text
experiments/kontorovich/yah_restorative_decoder.py
experiments/kontorovich/yah_restorative_decoder_audit.json
```

They construct the all-parameter finite-state stages and independently replay
`u=0,...,4`.  Worker hash:
`2f8e835e100a5041b17a07db8fd86b92aa0e5a549fa06f08d7963ddcce5d54ba`;
artifact hash:
`2346f0b87c15d8a7c336be2b7f5dbcb2003c58bc2435d88344715ff27054638a`.
The exact request is QM26--QM30.  This is the first complete
`read -> collide -> recharge -> reproduce` edge, but not closure.  The return
block is new, and companion commit `f96e621` proves its register lies strictly
between consecutive original decoder registers.  Therefore it cannot be
reindexed into the old chart.  The live goal is now a **finite recurrent chart
graph**, not deeper restriction down an infinite externally selected tower.
Companion commit `0da1058` additionally closes an eventual tail consisting
only of this same update.  With `C=473R+1`, the recurrence becomes
`256C'=729C`, forcing `256^n | C(0)` for every `n`.  A recurrent component
must therefore contain at least two genuinely different chart edge maps.

Immediately before shutdown, an in-memory generic lasso brancher explored
the returned chart exactly through four macros.  It found:

```text
u=3 mod 8:
  heads 0,1; carries [1],[1,1]; net +1;
  return head 0, trailing-two reservoir 10, D' = 27D/8;

u=27 mod 64:
  heads 0,1,0,2; carries [1],[1,1],[1],[1,1]; net +2;
  return head 0, trailing-two reservoir 13, D' = 729D/64.
```

The generated lasso blocks had lengths 524,288 and 4,194,304.  The search was
interrupted at depth four before explicit strings exploded further.  These
are exact observations from finite-state composition, but there is not yet a
worker/artifact, so keep them out of the headline table until certified.  They
are nested all-odd charge-spending bursts, not closure; `64bccb8` forbids an
infinite all-growing tail.  The next implementation should use compressed
straight-line blocks or just their two-state transition algebra to derive the
general residue/reservoir law without materializing `2^k*65536` trits.  Then
seek a collision with the restorative opcode that creates a *different*
recharge affine map.

### Canonical arithmetic compiler, with corrected scope

For a normalized boundary,

```text
y=D^m w-1,
A^h(C^m w-1)=B^h(D^m' w'-1),
```

Lean commit `5a9324b` proves unique public coordinates and exact equivalence
with the **arithmetic** `ChargeBouncerStep` surrogate.  Commits
`36d6633`/`afecb2c` expose the separate semantic obligation.  Do not call PC3
alone a Collatz compiler.

The crucial correction is that neither normalized `y` nor the hierarchy
field named `ordinary_start` is the odd Collatz state.  The latter is the
breakoff coordinate `k`; the true state is
`router_breakoff.literal_step(k).collatz_start`.  Lean round 115 therefore
uses edgewise encoded growth, not a false global monotone encoder.

### New exact semantic regression

The complete bounded descent is now in

```text
experiments/kontorovich/unit_charge_semantic_compiler.py
experiments/kontorovich/unit_charge_semantic_compiler_audit.json
```

It composes

```text
charge(N) -> unit[N,1]
unit(N)   -> glider[1,2,1^N]
glider(N) -> breakoff gates [E,H,E^N]
```

and takes the literal valuation words from the final router.  The default
artifact covers all 54 members with `m,h,m'<=3`, expands 756 gliders and 4,968
breakoff macros, emits 14,057 accelerated instructions, and independently
replays every `v2(3*x+1)` and endpoint.  All tested literal endpoints agree
and grow.  Worker SHA-256:
`4c8c73605b9d809919fb50a839f8c504a4cbca8f483a43b97a9ea3acacb84f30`;
artifact SHA-256:
`8311baf98156759a3a7d3cb8e898deb240afab01ad435efdb46143c01da9b17c`.
This is bounded regression, not the universal theorem or an infinite ray.

The intermediate level-two packet encoding is exactly

```text
k=5841333965851681082096808370372608*K
  -76096151213931339145826796194905,
```

but this is the breakoff `k`, not the Collatz state; the final router rail
length varies.

### First exact opcode conjugacy: resonant phase gliders

The determinant-four identities expose a nontrivial relation which survives
the equal-short-product no-gos:

```text
(m,h,m') -> (m+2622k,h-391k,m'+2618k).
```

This preserves public-tail `P,Q` but slips the source/target phase by `4k`.
For two parallel branches, an affine public-tail conjugacy `E(t)=s*t+c`
exists when

```text
gcd(kappa_a,3^Q-2^P) | kappa_b.
```

The exact worker/artifact are

```text
experiments/kontorovich/unit_charge_resonant_conjugacy.py
experiments/kontorovich/unit_charge_resonant_conjugacy_audit.json
```

They construct the first phase-down pair
`(1,392,1)->(2623,1,2619)` and phase-up pair
`(1,392,5)->(2623,1,2623)`, with 21,330-digit integral slopes/intercepts,
coefficientwise cylinder checks, and eight arithmetic bouncer replays.
Worker hash:
`70666b9ff3a47436a3fd45003af37b631c7c592b913ee94201f0fdc24deb362c`;
artifact hash:
`e3db4d58871f3a8b0493969405ad4f29ca1e2f4e988eda0038eb578f78a333b1`.

This is an exact glider *cell*, not closure.  Successive phase-dependent
embeddings do not yet telescope, and a fixed periodic bounce is obstructed.
Read
`docs/notes/kontorovich-resonant-phase-glider.md`.  The next constructive
question is whether the surviving tail can choose and regenerate its own
jump size/direction.

The fixed-`k=1` up family is more endogenous than “prescribed word” suggests:

```text
U(m)=(m,392,m+4).
```

Since `m=v2(y+1)/23` is public, this is an autonomous one-counter policy.  It
already passes the causal-decoder gate and evades the finite-state/periodic
no-go by using unbounded public phase.  It nevertheless fails: commit
`466e381` identifies the unique `Q_2` cofactor candidate coefficientwise with

```text
f_(3^(68k)/2^(92k))
  (2^(23m0+154h)/3^(17m0+114h)),  h=391k+1,
```

for every fixed `k>=1`, and bridges a linked public-step ray to that
recurrence.  The inspected main theorem of Väänänen--Wallisser (1989), pp.
200--201, makes this value irrational; that published theorem is the explicit
external seam.  Thus every fixed positive phase-up jump is closed.  The live
phase language must vary `k` or direction from public payload infinitely
often and make its forced 2-adic debris series telescope or otherwise become
an integer.

The general design principle is now **rationality engineering**.  Every
opcode chain forces one convergent `Q_2` series for its initial cofactor.  A
constructive chain should make its local debris a public coboundary so the
series telescopes; a finite prefix search without such an identity is not a
closure attack.

The periodic extension has a corrected, sharply limited scope.  Commits
`f2efee4`/`772a6e8` split a repeated positive jump word into one theta residue
class per period position and connect the flattened PC4 series to the finite
sum in `Q_2`, with summability, nonzero scales, and pairwise argument
separation checked.  Commit `8b3d9f5` kernel-checks the period-dependent size
bounds from Väänänen--Wallisser: the hypothesis succeeds at `L=2,3`, but
`Gamma(4,0)<1/8<gamma`.  The formalizer retracted its initial all-period
claim.  Accepting the external theorem closes periods one through three;
period four is only the first escape from this theorem and no such ray is
known.

There is a more fundamental current lead.  A research derivation sent through
`docs/FOR_CLEAN_LEAN.md` rewrites every public step as

```text
w-3^(-17m)
  = (2^(154h+23m')/3^(114h+17m))*(w'-2^(-23m')).
```

Thus all forward cells, including phase-up and phase-down, have the same
ternary-entry/binary-exit type.  Every internal boundary pays the strictly
negative chart mismatch `3^(-17m)-2^(-23m)`, which is exactly the normalized
negative defect polynomial `-H_m`.  A multi-cell word cannot be a clean bare
chart adapter merely because its phase returns.  Lean commit `772a6e8` now
proves this one-step identity, its arbitrary finite-word expansion, strict
negativity, and the no-clean-adapter consequence.  The constructive target is
an additional public correction rail or resonant affine intercept which
converts the binary exit chart back to the ternary entry chart.

A second exact research derivation is even cheaper.  The resonant parallel
charts start `2622k` apart and end `2618k` apart.  Chaining them forces
`1311*k_(i+1)=1309*k_i`, hence `1311^N|k_0` after `N` cells.  No positive
finite `k_0` can feed an infinite ladder made only of the present conjugacy
cells.  Commit `772a6e8` proves the finite divisibility law and infinite
no-go.  The missing opcode is now specified as a phase booster with inverse
separation expansion, combined with the binary-to-ternary correction rail.

There is now a constructive word-level response.  Define

```text
W_r=[(r,h0,L-r),(L-r,h1,r+d)].
```

Consecutive words have boundary phase differences `(+d,-d,+d)`: their charts
cross internally and recover their separation.  Their total gains are
independent of `r`, namely

```text
Q=114*(h0+h1)+17*L,
P=154*(h0+h1)+23*(L+d).
```

The new exact worker/artifact

```text
experiments/kontorovich/unit_charge_phase_swap_conjugacy.py
experiments/kontorovich/unit_charge_phase_swap_conjugacy_audit.json
```

construct the smallest line `1->3->2`, `2->2->3`, `3->1->4`.  Both adjacent
composite pairs have `P=423,Q=296`, gcd-one positive integral affine
conjugacies and exact nested source/target cylinder checks.  Worker hash
`4352e4d7a6637e4e8407c28c916a63dc84ac966e66ebd28839cbf3e09af90f9b`;
artifact hash
`1dcd6feacc137fc04db60de43d3ea70bab1253220e2708bbed4ce5af05acd5ab`.
The artifact also proves that, for both squares, the conjugacy-selected next
input strictly outruns the current output in constant and slope.  Hence they
are parallel embeddings, not a bounded orbit glider.  Lean commit `3a6d285`
kernel-checks this for both concrete embeddings.

The version-two artifact also constructs the *different* direct handoff
lattices

```text
u=u0+2^423*t,       v=v0+3^296*t
```

between both adjacent word-rays and replays two members of each.  These are
fresh dyadic address selections, not conjugacies or reproduction.  This
exposes the fundamental renormalization principle: a finite opcode chain is
again a binary-reader/ternary-writer macro and does not solve its own ordinary
address.

Lean commit `a05ca2e` proves the general signed-area law, the concrete phase
totals, the remaining negative typed tax, and the exact correction-rail iff.
Commit `cc09f1b` adds that any nonnegative correction rail across the smallest
macros strictly grows because `2^423/3^296<1`.  A new request in
`docs/FOR_CLEAN_LEAN.md` supplied the complementary affine-gauge no-go:
coefficientwise handoff forces
`3^Q_i*s_i=2^P_(i+1)*s_(i+1)*a_i`, so a total affine one-register controller
strictly spends dyadic slope at every step; commit `29c1d22` now checks the
full accumulated divisibility theorem.  The constructive target is now a
nonlinear decoded stack operation or multi-rail address rotation, followed by
a public `L->L'` turnaround.

### Companion Lean state and next tasks

At this update, the newest pushed formalizer checkpoints are:

- `737e8de`: constant `(m,h)` schedules impossible, including after a finite
  transient;
- `f1ba1c8`: genuinely alternating period-two schedules impossible;
- `2be4a95`: finite breakoff runs compile to literal legal Collatz words;
- `76d60d8`: arbitrary linked breakoff-gate lists compose semantically;
- `e8585c4`: every fixed finite bouncer-opcode period is impossible, including
  after a transient;
- `cda9bd3`/`a458267`/`904c1de`: arbitrary finite `E,H,E^N` gliders compile
  to literal growing words and their dyadic witnesses are eliminated;
- `6619b49`: the one-cell packet family has exact universal breakoff input
  and output boundaries, completing that base glider's endpoint theorem;
- `a16883c`/`d452c59`/`f33fa00`/`466e381`: resonant conjugacy, the dependent
  ordinary-tail criterion, the fixed-jump `Q_2` candidate, and its exact
  partial-theta/public-step identification;
- `f2efee4`/`8b3d9f5`: periodic-jump theta residue algebra and the exact
  `L=2,3` success/`L=4` failure boundary for the external theorem's size
  hypothesis;
- `772a6e8`: completed flattened periodic `Q_2` splitter, universal typed
  chart-tax/no-clean-adapter theorem, and the resonant-separation divisibility
  no-go;
- `3a6d285`: generic and both concrete no-handoff theorems for the advertised
  phase-swap conjugacy embeddings;
- `cc09f1b`: positive TI3 correction rails strictly accumulate debt, with the
  exact `2^423/3^296<1` phase-swap specialization;
- `29c1d22`: direct handoff progressions, the total-affine dyadic-slope no-go,
  both exact Kraft letter sums, and the abstract two-Kraft core;
- `da9fa59`: both finite Kraft bounds derived from prefix-freeness and the
  complete finite outward-code contradiction;
- `298f5a3`: complete canonical thin-trap iteration and literal Collatz
  refutation endpoint;
- `ef1b888`: generic marker/flank boundary collapse for proper outer context
  loops; the concrete per-rule YAH bridge remains open;
- `b4a48a6`: the `w>=3` uniform-block value/size endpoint; the rewriting
  forced-shape bridge remains open;
- `1b3459d`: generic literal-context and full productive morphic-context
  gliders construct infinite chunked rewrite derivations;
- `b733caa`: exact YAH symbols/rules, context closure, marker-count
  preservation, and concrete-carrier specializations of both glider endpoints;
- `442826d`: actual YAH traces feed the boundary-collapse theorem once the
  certificate supplies the two flank equalities;
- `2d50381`: the forced-shape/value proof closes every uniform marker-fixed
  digit morphism of width at least three; exact Python covers widths one/two;
- `9ca4360`: canonical start/end words make every proper whole-word outer
  context collapse without separately supplied flank data;
- `bfe12f0`: identity is the unique productive nonerasing marker-fixed
  digit-word morphism, with no common image-width premise;
- `0365c72`: the carry defect and CR2--CR4 run/two-counter traces are exact
  all-length theorems over the pinned carrier;
- `f81ff21`: CR4 directly satisfies `2*endpoint=3*source+1` and is strictly
  outward for every pair of run lengths;
- `1a88c3e`: the general two-state quotient sweep, all three QM1 macro traces,
  and the exact QM2 space-charge laws are kernel-checked;
- `b1dd87a`: quotient semantics, the QM3 residue/growth table, and QM4's
  global alternating checksum are kernel-checked;
- `64bccb8`: every perpetual all-growing queue-macro orbit on ordinary
  naturals is impossible via `4*(N'+1)=9*(N+1)`;
- `99d3405`: fixed-clock positive exponent shifts on a simple ternary
  exponential family are impossible by two/three prime separation;
- `db13d82`: an `r`-macro all-growth burst forces `4^r | N+1` and has the
  exact iterated defect identity;
- `b794b2f`: the first packet `2(0012)^s(01)^q` never maps directly to another
  packet of that family; a second type must restore the head.
- `288fb09`: the dyadic battery `2*length+v2(N+1)` is exactly conserved by
  every growing queue macro at arbitrary word length.
- `e293f7d`: all six head/residue battery laws and the packet value backbone
  are kernel-checked.
- `22ce54d`: the complete four-phase packet recharge table is kernel-checked.
- `8bed065`: ever-deeper recharge addresses cannot stabilize to one fixed
  ordinary packet coordinate.
- `67eabe3`: any canonical all-odd defect segment of `J>=4G` steps gains at
  least `G` ternary cells; the packet-to-segment wrapper remains separate.
- `1a69d5b`: the normalized lift register is a kernel-checked 2-adic isometry.
- `6b5e34c`: its exact triadic reservoir valuation is kernel-checked.
- `0b8179a`: triadic defect valuation equals the literal trailing-two count,
  giving the typed reservoir theorem.
- `d801643`: queue prefix/suffix causality limits one-macro backwrite to the
  carry channel, and a positive register cannot eventually only bit-pop.
- `24b2dd5`: QM20/QM21/QM23 and the generic fixed/flipping-lasso induction
  engine are kernel-checked; the concrete four-stage QM22 instantiation is
  still separate.
- `f96e621`: the restorative output register lies strictly between consecutive
  original decoder registers and is therefore a genuinely disjoint chart.
- `0da1058`: no positive ordinary register can eventually repeat only the
  restorative affine update; a recurrent component needs multiple edge maps.

Never edit or stage its live `KontoroC/*` files.  Continue to send exact
formulas only through `docs/FOR_CLEAN_LEAN.md` and poll
`CLEAN_LEAN/FOR_FABLE.md`.

The best immediate research tasks are:

1. poll the companion's QM26--QM30 restorative response; decoder arithmetic,
   generic lasso induction, and original-chart separation are complete;
2. give the returned 65,536-trit chart its own symbolic decoder and test
   whether finitely many generated chart types close to a recurrent component;
3. search for a public invariant predicate on `CompleteSplashState.next`, not
   a deeper finite orbit or another direct CRT handoff;
4. treat nonlinear stack rewriting or multi-rail address rotation as the
   required operation; total one-register affine rails spend their dyadic
   slope and are closed;
5. reject new searches unless success would give a public self-map, a finite
   semantic rewrite, or a whole ansatz-class obstruction.

The detached Akdeniz 1,198-digit Thue solve remains active with class number
one and no completion line.  The Ganesha nonuniform-morphism workers are no
longer running; only shards 4 and 12 completed.  Leave them stopped unless a
new theorem-shaped hypothesis supplies a discriminating search target.  These
are scoped falsifiers, not the main closure strategy.  PSC is idle.

No counterexample or infinite orbit is known.

Start from the latest `origin/main`; do not trust the hash printed in an old
handoff.  At this handoff the newest independent Lean checkpoints are
`07352a9` (Roth bridge), `34e166b` (hidden register), `2743350`
(quadratic closure/mod-eight obstruction), and `90c9b6c` (accepted-step QN2
bridge); main-worker commit `f31a74d` adds their executable artifacts and
public map.  Run
`git log --oneline -10` first rather than trusting a copied hash.

## Mission

The active goal is deliberately adversarial: **try to disprove the Collatz
conjecture** by constructing an exact nontrivial positive cycle or a positive
ordinary seed with a certified infinite orbit.  The working metaphor is Alex
Kontorovich's: Collatz is hardware, the seed is software, and a counterexample
may be a highly nonlocal program with thousands of digits.  The target is a
self-reproducing symbolic mechanism, not a larger ordinary seed sweep.

No counterexample or infinite orbit is known at this pause.

## Read first

1. `AGENTS.md`, then this file.
2. The top of `README.md`, especially the newest Diary entry, **The
   Kontorovich Challenge**, **KC Strategy and failure map**, and **KC Headline
   results**.
3. `NEW_RESUME_LEAN.md` for the independent formalizer's exact theorem map and
   next Roth task.
4. The tail of `CLEAN_LEAN/FOR_FABLE.md` (Lean to research) and
   `docs/FOR_CLEAN_LEAN.md` (research to Lean).
5. `experiments/kontorovich/README.md` and the particular worker before using
   an artifact.

`HANDOFF.md` and `RESUME.md` are valuable history but predate the
Kontorovich pivot; the living README and this file take precedence.

## Non-negotiable workflow

- Nothing is a result until it has an exact replay artifact, a kernel-checked
  Lean theorem, or an exhaustive search with explicit bounds.  A cited
  external theorem must have its hypothesis/application seam stated plainly.
- Update the timestamped README **Diary about hourly**, including failures and
  next actions.  Keep its short entries linked to the KC strategy, failure,
  and headline maps.
- Commit and push every substantive coherent update.  End every commit with

  ```text
  Co-authored-by: OpenAI Codex <codex@openai.com>
  ```

- Never edit or stage `CLEAN_LEAN/*`.  The independent formalizer also owns
  its current `KontoroC/*` work, including the untracked
  `KontoroC/KontoroC/ChargeStatePowerRoth.lean`.  Send requests only through
  `docs/FOR_CLEAN_LEAN.md`; read replies in `CLEAN_LEAN/FOR_FABLE.md`.
- This is a shared dirty worktree.  Inspect `git status` before every stage.
  In particular, do **not** stage
  `experiments/kontorovich/unit_charge_morphic_audit.json`; another process
  owns its changing content.
- Do not revive a closed lane without a new hypothesis which evades its exact
  obstruction.
- Published ordinary-seed verification is already beyond `2^71`.  Compute is
  for exact symbolic falsifiers, certificates, or compiler searches—not a
  replacement for thinking about reproduction.

## Executive mathematical state

### 1. The shortest payload-power quine is closed

For the fixed-form charge bouncer, set

```text
A=3^114, B=2^154, C=3^17, D=2^23,
F=(A-B)/5.
```

The payload type `u=F*r^23` is a literal address-reproduction attempt.  Lean
commit `5fbacf5` proves that any accepted shortest-recharge (`h=1`)
transition would solve

```text
3^15 X^23 - 2^16 Y^23 = 5.
```

PARI/GP 2.15.4 checked the polynomial irreducible, reported attached class
number one, and returned the complete empty Thue solution list.  Under PARI's
documented class-number-one algorithm this is unconditional external-PARI
scope, not a Lean proof.  Do not rerun this lane.

### 2. The uncorrected `h=23` payload rail is one global Thue equation

At the first determinant-four resonance,

```text
A^23=3^4 C^154,
B^23=D^154,
G23=(A^23-B^23)/F=5*Phi_23(A,B).
```

Lean commits `4c56925`/`f61f569` include exact finite residue checks at
`277,599,829,1151`.  Every uncorrected single-rail transition must have

```text
m=9 (mod 23),
3^15 X^23-Y^23=G23.                              (R23)
```

`G23` has 1,198 decimal digits.  The global PARI solve is running detached on
Akdeniz; see **Remote jobs**.  A negative result closes only this uncorrected
single rail.  A correction packet or multi-rail splash changes the equation.

The reproducible input is
`experiments/kontorovich/unit_charge_power_resonance_thue.gp`.

### 3. A true public-state type reproduces, but its simplest class fails

Encode the public bouncer state itself as `y=s^23`.  If a transition begins
and ends in this type, ternary readback forces `h=23*ell`, and its odd
collision quotient is `t^23`.  The exact transition is

```text
C^m*(s^23+1)=D^m*(1+(B^ell*t)^23),               (GSPQ)
y'=(A^ell*t)^23.
```

This is genuine closure: the output data type is the input data type, without
preloading a fresh CRT word.

Lean commit `4c56925` proves the coefficient class `m=0 (mod 23)` impossible
for `ell=1`; arbitrary positive `ell` is the same theorem with
`t'=B^(ell-1)t`.  The 2-adic input register makes `s` too large for the
discrete gap between two 23rd-power packets.

Commit `f61f569` kernel-checks the 23-class norm reduction.  Commit `9f00894`
keeps the information a free local sieve discards.  With

```text
s+1       = 2^(23m) w,
B^ell*t+1 = 3^(17m) v,
Q(x)      = (x^23+1)/(x+1),
```

the transition gives

```text
w Q(s)=v Q(B^ell*t).
```

Lean proves `gcd(x+1,Q(x))` has no prime divisor except 23.  After cancelling
the forced fixed-register factor `F` from both valuation quotients, their
residual quotients agree modulo `F`.  The new exact audit below shows that the
lift stops being equality after the first digit and becomes a writable,
nonlinear instruction register.

Exact companion:

```bash
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_state_power_quine.py selftest
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_state_power_quine.py verify \
  experiments/kontorovich/unit_charge_state_power_quine_audit.json
```

At handoff the verifier SHA-256 is
`aa4749e1b3a51cb04b080a9b1ed79226e5abcbbf33c77004eba273f8ae020d9d` and
the artifact SHA-256 is
`8a297e55a7691a8c611ecb1daba7abc0e841b405050fbc90fe9f91c7c3e90a08`.

### 4. The hidden `F`-register is writable, not a second obstruction

With exact quotients

```text
s+1=D^m F w,                  B^ell*t+1=C^m F v,
s'+1=D^m' F w',              s'=A^ell*t,
```

Taylor expansion of `Q(-1+u)` and exact Hensel lifting give

```text
v=w+11F(C^m-D^m)w^2                         (mod F^2),
B D^m' w'=B C^m w-5ell                      (mod F).
```

All coefficients are units modulo `F`.  Therefore, for every input digit,
desired output digit, and positive `m,m'`, one recharge class `ell (mod F)`
writes that target.  The least positive representative can have 54 decimal
digits.  The second output digit is an explicit nonlinear quadratic in the
input digit and `ell`.

`unit_charge_hidden_register.py` reconstructs the cofactor Taylor polynomial,
lifts collision balance uniquely through `F^3`, checks the first and second
closed formulas, synthesizes five unrelated writes, and uses CRT to prove that
the visible register alone does not force `F^2`.  This is exact but only a
necessary `F`-adic transducer.  The selected `ell` has not yet been coupled to
the exact 2-adic collision valuation of a positive transition.
Lean commit `34e166b` independently proves the universal carry, geometric
output, first-digit divisibility, and unique recharge-class theorems.

```bash
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_hidden_register.py selftest
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_hidden_register.py verify \
  experiments/kontorovich/unit_charge_hidden_register_audit.json
```

Verifier SHA-256:
`58c35526dfdba88268f1821b9a439db54bb2f3242ba3674e1603e35c8494ba19`.
Artifact SHA-256:
`e04f1c829e28fe4621507755cc7f0b6dfbf59f920f02baf961e87f042ddc7f08`.

### 5. A quadratic two-rail type reproduces automatically

The first corrected lower-degree type is

```text
N_d(x,u)=x^2+d*u^2.
```

It is closed under every recharge because

```text
B^h N_d(t,v)=N_d(2^(77h)t,2^(77h)v),
A^h N_d(t,v)=N_d(3^(57h)t,3^(57h)v).
```

The naive `d=1` sum-of-two-squares type is universally impossible: accepted
states and collision quotients are `7 (mod 8)`.  The exact worker instead uses

```text
d_hw=13(C-D)=5*13*19*1271069=1569770215=7 (mod 8).
```

This ramifies every non-ternary prime forced by the public register.  CRT
constructs independent legal inputs for `m=1,2,5` and independent norm
quotients whose scaled outputs have `m'=1,3,5`.  A PARI-discovered homogeneous
integer vector, replayed exactly by Python, has nonzero last coordinate and
therefore supplies a rational point on the `m=h=1` affine collision quadric.

The live coupling equation is

```text
C^m*(x^2+d*u^2+1)=D^m*(1+B^h*(t^2+d*v^2)).
```

No paired integral solution or transition is claimed.  A one-dimensional ray
specialization reduced to a generalized Pell equation; its smallest PARI
solve did not finish promptly and was stopped.  Use the full three-parameter
quadric and hidden register rather than sinking compute into that ray.
Lean commit `2743350` independently proves automatic recharge closure and the
complete accepted-semantics obstruction for `d=1`.
Commit `90c9b6c` proves the exact forward bridge from an already accepted
typed step to QN2 and its regenerated output coordinates; it deliberately does
not turn a free quadric point into a bouncer step.

```bash
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_quadratic_norm.py selftest
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_quadratic_norm.py verify \
  experiments/kontorovich/unit_charge_quadratic_norm_audit.json
```

Verifier SHA-256:
`8dddae25c33895e948bff98b94361e32fb0586abf1263797a98184b4c0340e57`.
Artifact SHA-256:
`bb04d5fb5d05ce6c5e22765d00029430e626aabaf7c5970b12867ebca465c9b5`.

### 6. The Roth route is strong but not yet promoted

For `a=floor(17m/23)`, `e=17m mod 23`, `U=3^a`,
`X=Us`, and `Y=2^m B^ell t`, GSPQ gives

```text
Y^23-3^e X^23=C^m-D^m>0.
```

For nonzero `e`, put `alpha=3^(e/23)`.  Difference-of-powers factorization
appears to give

```text
0 < Y/X-alpha < alpha/s^23.
```

The input valuation gives `U<s`, hence the reduced denominator `q` of `Y/X`
obeys `q<=X<s^2`.  Since `s>alpha`, every such transition is eventually an
exponent-11 rational approximation to one of 22 fixed algebraic irrational
numbers.  The output root is strictly larger than `s`.  Roth's theorem would
therefore imply only finitely many transitions in each class and no infinite
run wholly inside this pure type.

This is **not yet a promoted global result**.  Lean commit `07352a9`
kernel-checks the exact normalization, real inequality, strict root growth,
residual-class bookkeeping, and exponent-11 conversion past `alpha<s`.  The
remaining seams are the reduced-rational sequence consumer, infinitely many
distinct approximants in one nonzero class, and Roth's external finiteness
theorem.  Roth must remain external, never a project axiom.

### 7. Constructive lesson and next escape

The pure 23rd-power type is probably too rigid precisely because it keeps
approximating one member of a finite algebraic target set.  A counterexample
compiler should now try one of:

- a corrected sum of two or more remote power packets whose carry term
  regenerates (Simon's “splash the gap”);
- a type-switching rail with genuinely unbounded algebraic state, not a finite
  set that pigeonhole reduces to Roth;
- the hardware-matched quadratic norm rail, coupled integrally to the writable
  hidden-`F` register and the 2-adic opcode;
- a fixed-level autonomous bouncer program compiled from valuation quotients,
  rather than another infinitely nested 2-adic address.

Do not merely solve more fixed small Thue equations.  Use their obstructions
to reverse-engineer which correction term changes the norm target while still
reproducing its own description.

## Remote jobs and infrastructure

Always recheck external state; PIDs can change.

### Akdeniz: keep only detached `R23`

Login:

```bash
ssh akdeniz.lan.cmu.edu
```

The only Collatz job which should remain is a user-systemd service launched at
10:17 EDT on 2026-07-22:

```bash
systemctl --user --no-pager --full status kc-r23.service
cat /home/simon/kc-r23.out
```

The output should begin with

```text
BEGIN_R23 PARI=[2, 15, 4] RHS_DIGITS=1198 IRREDUCIBLE=1
CLASS=1 REG=1289649122765.2898428133760724828888404
```

Do not treat it as finished until `R23_DONE` appears.  If it returns, copy the
complete log into a new repo audit transcript, check `IRREDUCIBLE=1` and
`CLASS=1`, inspect every reported solution by exact substitution, then update
README scope.  If the service vanished without `R23_DONE`, relaunch from the
tracked GP file with a detached service; do not silently cite the partial log.

The old higher-recharge batch and the bounded 22-class SPQ batch were
intentionally stopped at this handoff.  The Roth direction superseded the
latter; the former was stuck on a narrow single-rail family.

Akdeniz has 32 CPU cores and one GPU; passwordless sudo is available.  It is
appropriate for PARI and CPU jobs.

### Ganesha: partial morphic search stopped; leave it stopped

Login:

```bash
ssh ganesha.lan.cmu.edu
```

Work directory:

```text
/home/simon/kontorovich-run-20260721
```

Twenty-four deterministic shards were intended to search all nonempty binary morphisms with
image length at most 7, valuation codings `1..4`, depth at most 14, expanded
word length at most 16,384, seed-word length at most 1,024, and 100,000 exact
continuation steps.  Only shards 4 and 12 finished, both with zero nontrivial
cycles; the other workers are no longer running.  Do not cite this as an
exhaustive result, and do not restart it merely to widen a bounded morphic
search.  The two-Kraft/thin-trap program is now the primary lane.

Check with

```bash
pgrep -af search_nonuniform.py
ls -lh /home/simon/kontorovich-run-20260721/shards
```

If a later theorem-shaped reason justifies completing it and all 24 files
eventually exist:

```bash
cd /home/simon/kontorovich-run-20260721
python3 merge_nonuniform.py --expect-shards 24 \
  --output nonuniform_results.json shards/shard-*.json
```

Only a successful merge proves exhaustive coverage.  Copy the merged artifact
back to `experiments/kontorovich/`, run the local verifier/merge again if
practical, update the bounded scope in README, then commit.  A negative result
does not change the `2^71` verification frontier.

### PSC: GPU allocation only

Login:

```bash
ssh sdedeo@bridges2.psc.edu
```

The allocation ledger showed only **Bridges 2 GPU**, approximately 2,220 of
3,528 service units remaining through 2027-04-08; there is no CPU allocation.
Do not submit serial PARI/GP there.  PSC is reserved for a genuinely
CUDA-parallel exact subproblem.  File transfers must use
`data.bridges2.psc.edu`, never the login node.

## Lean collaboration

The formalizer resumed from `NEW_RESUME_LEAN.md` and pushed rounds 100--103.
Its current package is `KontoroC`, not a new edit inside `CLEAN_LEAN`:

```bash
cd KontoroC
lake build
lake env lean KontoroC/Audit.lean
```

The main research driver must not edit its files.  Put a complete theorem
request, proof sketch, assumptions, and scope warning into
`docs/FOR_CLEAN_LEAN.md`; then poll `CLEAN_LEAN/FOR_FABLE.md`.  The Roth,
hidden-`F`, quadratic/mod-8, and accepted-step QN2 requests are complete in
`07352a9`, `34e166b`, `2743350`, and `90c9b6c`.  Formalizer-owned files are
currently dirty with the concrete YAH flank and forced-shape work;
inspect status and never edit or stage those files.

The latest full formal build reported only standard mathlib logical axioms
(`propext`, `Classical.choice`, `Quot.sound`) for these results, no project
axiom, `sorry`, or `admit`.  Rebuild before citing a new theorem.

## Local verification and commit hygiene

Before staging:

```bash
git status --short
git diff --check
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_hidden_register.py selftest
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_hidden_register.py verify \
  experiments/kontorovich/unit_charge_hidden_register_audit.json
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_quadratic_norm.py selftest
PYTHONPATH=experiments/kontorovich \
  python3 experiments/kontorovich/unit_charge_quadratic_norm.py verify \
  experiments/kontorovich/unit_charge_quadratic_norm_audit.json
```

Stage explicit paths only.  Preserve the unrelated changing morphic artifact.
After a coherent commit, `git push origin main` and add the commit to the next
Diary entry.

## Best next actions

1. Poll the companion for QM45/QM46 after commit `9021e86`.  Do not stage or
   edit its Lean files; local `lake build KontoroC` already passes.
2. Use the certified ether successor law to formulate the deterministic
   tail-zero/current-offset state map and seek a nonhalting invariant ray.
   The `115->59->9->1` path is a halting regression, not a self-write seed.
3. Skip arithmetic branch growth `n_t=n_0+kt`: the partial-theta obstruction
   closes it conditionally on the cited theorem.  Search nonlinear
   payload-dependent counters or bounded genuinely aperiodic branch schedules.
4. Seek a contextual YAH block operator only if it depends on a surviving
   public payload or repetition index.  QM42 closes another fixed lasso pop.
5. Poll the detached R23 service without blocking the contextual search; leave
   the incomplete Ganesha morphic batch stopped.

The central calibration is unchanged: a spectacular finite path, a 10,000-
digit compiled seed, or a fresh CRT word at every generation is not a
counterexample.  Closure, ordinary-integer realization, and certified
nontermination must arrive together.

# NEW_RESUME — Kontorovich counterexample-search handoff

Updated: 2026-07-22, about 14:37 EDT

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

This is currently a research derivation with a locally compiling, uncommitted
companion draft in `KontoroC/KontoroC/TwoKraftObstruction.lean`.  That draft
checks the two geometric sums, leafwise comparison, and abstract
finite/countable contradictions.  The generic prefix-tree-to-Kraft theorem is
still an explicit interface.  Do not call it a pushed Lean checkpoint until
the companion commits it.

The constructive target is now a finite **thin-trap certificate** over
`CompleteSplashState.next`: a public predicate `L`, explicit ordinary seed,
and public successor which preserves `L` and is strictly outward.  A precise
wrapper request is at the tail of `docs/FOR_CLEAN_LEAN.md`.  This would produce
an `InfiniteCanonicalSplashOrbit` by iteration and hence use the existing
literal refutation theorem without preloading an infinite itinerary.

The most principled parallel presentation is the 11-rule mixed-base string
system of Yolcu--Aaronson--Heule.  Their Theorem 3.17 says global termination
is equivalent to Collatz.  A finite contextual self-embedding or cyclic
template rewrite would therefore be a genuine reproduction certificate.  Do
not search blindly yet: first specify a small exact checker for a parametric
rewrite/pumping certificate, and distinguish it from De Mol's tag encoding,
where an arbitrary nonhalting word need not be reachable from unary Collatz
input.

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
`docs/FOR_CLEAN_LEAN.md` asks for the complementary affine-gauge no-go:
coefficientwise handoff forces
`3^Q_i*s_i=2^P_(i+1)*s_(i+1)*a_i`, so a total affine one-register controller
strictly spends dyadic slope at every step.  The constructive target is now a
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
- the formalizer is now lifting only the upper charge/unit/level-two layers.

Never edit or stage its live `KontoroC/*` files.  Continue to send exact
formulas only through `docs/FOR_CLEAN_LEAN.md` and poll
`CLEAN_LEAN/FOR_FABLE.md`.

The best immediate research tasks are:

1. poll for the companion's two-Kraft and thin-trap commits, then promote only
   their precise checked scope;
2. define a finite parametric pumping/self-embedding certificate for the
   Yolcu--Aaronson--Heule rewrite system before launching a search;
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
currently dirty with the two-Kraft and finite-prefix-solvability work; inspect
status and never edit or stage those files.

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

1. Poll the detached R23 service, but do not block creative work on it; leave
   the incomplete Ganesha morphic batch stopped.
2. Finish the two-Kraft prefix-tree interface and thin-trap wrapper with the
   companion, preserving the exact distinction between a checked logical core
   and a concrete code theorem.
3. Specify and implement an exact finite checker for a contextual pumping
   certificate in the Yolcu--Aaronson--Heule 11-rule mixed-base system.
4. Seek a symbolic invariant `L` for the canonical splash map whose successor
   writes its own next address; do not promote long finite traces.
5. Keep Simon's spatial metaphor: the invariant should explain how a payload
   rail and sacrificial/catcher rail regenerate both the gap and the next
   correction packet.

The central calibration is unchanged: a spectacular finite path, a 10,000-
digit compiled seed, or a fresh CRT word at every generation is not a
counterexample.  Closure, ordinary-integer realization, and certified
nontermination must arrive together.

# NEW_RESUME — Kontorovich counterexample-search handoff

Paused: 2026-07-22, about 11:25 EDT

Repository: `/Users/simon/Desktop/COLLATZ`

Start from the latest `origin/main`; do not trust the hash printed in an old
handoff.  At this handoff the newest independent Lean checkpoints are
`07352a9` (Roth bridge), `34e166b` (hidden register), `2743350`
(quadratic closure/mod-eight obstruction), and `90c9b6c` (accepted-step QN2
bridge); the following main-worker
checkpoint adds their executable artifacts and public map.  Run
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

### Ganesha: leave the exact non-uniform morphic search running

Login:

```bash
ssh ganesha.lan.cmu.edu
```

Work directory:

```text
/home/simon/kontorovich-run-20260721
```

Twenty-four deterministic shards search all nonempty binary morphisms with
image length at most 7, valuation codings `1..4`, depth at most 14, expanded
word length at most 16,384, seed-word length at most 1,024, and 100,000 exact
continuation steps.  At handoff shards 4 and 12 had finished, both with zero
nontrivial cycles; 22 PPID-1 workers were still running.  They are detached and
survive this Codex instance.

Check with

```bash
pgrep -af search_nonuniform.py
ls -lh /home/simon/kontorovich-run-20260721/shards
```

When all 24 files exist:

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
`07352a9`, `34e166b`, `2743350`, and `90c9b6c`.  No formalizer-owned file is
dirty at this handoff; still inspect status and never stage its future edits.

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

1. Poll the detached R23 service and the Ganesha shard count; do not block
   creative work on them.
2. Attack the full integral quadratic collision equation, not the timed-out
   rank-one Pell ray.  Parameterize from the exact rational point, impose the
   2-adic opcode and public register by CRT/strong approximation, and demand
   literal `bouncer_step` replay for every candidate.
3. Couple the quadratic coordinates to the writable hidden instruction:
   recharge `ell` must simultaneously select `w' (mod F)` and be the exact
   collision valuation.  Seek a symbolic family in which one coordinate pair
   computes the next pair, not separately chosen endpoint witnesses.
4. The inexpensive Lean spines are complete.  Ask for more formalization only
   after the integral coupling attack produces a universal statement; keep
   the Roth external theorem and sequence-consumer seams explicit.
5. Keep Simon's spatial metaphor: interpret the two norm coordinates as the
   payload and sacrificial/catcher rails, and require the collision to
   regenerate both the gap and its next correction packet.

The central calibration is unchanged: a spectacular finite path, a 10,000-
digit compiled seed, or a fresh CRT word at every generation is not a
counterexample.  Closure, ordinary-integer realization, and certified
nontermination must arrive together.

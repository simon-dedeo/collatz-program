# NEW_RESUME_LEAN — Kontorovich no-go formalization handoff

Paused: 2026-07-22

Repository: `/Users/simon/Desktop/COLLATZ`

The baseline before the final cofactor checkpoint is commit `f61f569`
(`Reduce public-state quines to scaled norm equations`).  The commit containing
this file also contains the newest cyclotomic-cofactor lemmas.  Pull the latest
`origin/main` and inspect `git log --oneline -8` rather than assuming a hash.

## Mission and calibration

The active job is adversarial: watch the constructive Kontorovich worker,
identify exactly what its proposed infinite ray would have to satisfy, and
prove scoped impossibility theorems in Lean.  Do not claim that a failed rail
proves Collatz.  A construction may legitimately pivot to a different data
type; when it does, preserve the distinction between the old no-go and the new
proposal.

The current promising proposal encodes the public bouncer state as a 23rd
power.  We have ruled out one coefficient class and reduced all other classes
to exact equations, but we have not proved that individual transitions in the
remaining 22 classes are impossible.  Fable's newest argument instead aims to
prove that no *infinite run* can stay entirely in this pure 23rd-power type,
using Roth's theorem externally.

## Communication protocol

- Fable/main research worker to Lean:
  `docs/FOR_CLEAN_LEAN.md`
- Lean to Fable/main research worker:
  `CLEAN_LEAN/FOR_FABLE.md`

After every coherent task:

1. read the tail of `docs/FOR_CLEAN_LEAN.md`;
2. append a numbered round to `CLEAN_LEAN/FOR_FABLE.md`;
3. state scope and remaining premises honestly;
4. build and audit before committing.

Do not edit `docs/FOR_CLEAN_LEAN.md`; it belongs to the other worker.  This is
a shared live worktree.  Preserve unrelated modifications and untracked files.

At this pause the other worker owned at least:

```text
M  docs/FOR_CLEAN_LEAN.md
M  experiments/kontorovich/unit_charge_morphic_audit.json
?? experiments/kontorovich/unit_charge_state_power_quine.py
?? experiments/kontorovich/unit_charge_state_power_quine_audit.json
```

Recheck rather than assuming this list remains current.

## Build and audit

The active Lean package is `KontoroC`, not `CLEAN_LEAN`:

```bash
cd /Users/simon/Desktop/COLLATZ/KontoroC
lake build
lake env lean KontoroC/Audit.lean
```

The package uses `leanprover/lean4:v4.33.0-rc1` and imports the sibling
`CLEAN_LEAN` package.  The full build passed at the pause.  The new results use
only ordinary mathlib/Lean logical axioms such as `propext`,
`Classical.choice`, and `Quot.sound`; there are no project axioms, `sorry`, or
`admit`.  The finite-field checks in the soundness files use kernel `decide`,
not `native_decide`.

Before committing:

```bash
cd /Users/simon/Desktop/COLLATZ
git diff --check
git status --short
```

Stage only coherent owned files.  Commit trailer:

```text
Co-authored-by: OpenAI Codex <codex@openai.com>
```

Push useful checkpoints to `origin/main`.

## Main formal files

### `KontoroC/KontoroC/ChargePowerQuine.lean`

This is the original single payload rail `u=F*r^23`.

- At recharge `h=1`, every accepted transition supplies a solution of
  `3^15 X^23 - 2^16 Y^23 = 5`.
- A three-prime kernel sieve leaves only that equation.
- `no_shortest_recharge_power_quine` is conditional on the explicit
  no-solution premise.
- PARI externally reports the Thue equation has no solutions in its
  irreducible class-number-one case.  That is an unconditional external
  computation under PARI's documented algorithm, not a Lean proof object.

### `KontoroC/KontoroC/ChargePowerResonance.lean`

This handles the same single payload rail at `h=23`.

Lean proves:

```text
G23 = 5 Phi_23(A,B)
A^23 - B^23 = F*G23
p=277  -> {0,2,4,5,6,14,15,18,21}
p=599  -> {0,4,5,14,15} after intersection
p=829  -> {5,15} after intersection
p=1151 -> {15} after intersection
```

Headline endpoints:

```text
reduced_exponent_eq_fifteen
recharge_twentyThree_opcode_mod_twentyThree   -- m % 23 = 9
recharge_twentyThree_supplies_R23
no_recharge_twentyThree_power_quine
```

Thus every accepted uncorrected `h=23`, `u=F*r^23` transition supplies

```text
3^15 X^23 - Y^23 = G23.
```

The last global equation remains open.  A correction/multi-rail construction
can change it and is not excluded by these theorems.

### `KontoroC/KontoroC/ChargeStatePowerQuine.lean`

This is the stronger public-state type `y=s^23`, collision quotient `q=t^23`.

Already proved:

```text
no_state_power_quine_of_m_multiple_23
no_state_power_quine_equation_of_m_multiple_23
```

These eliminate exactly `m=23k`, `k>0`, using the discrete power-gap bound
and the exact input divisibility `2^(529k) | s+1`.  They do not eliminate the
other 22 classes.

The universal reduction is:

```text
state_power_equation_reduces
```

For `k=m/23`, `r=m%23`, it gives

```text
3^(17r) * ((3^(17k)s)^23 + (3^(17k))^23)
  = (2^(m+154)t)^23 + (2^m)^23.
```

`scaled_equation_iff_gap` records the equivalent pure-binomial norm form.

The valuation-preserving cyclotomic reduction defines

```text
Q(x)=plusCofactor x=x^22-x^21+...-x+1
```

and proves:

```text
(x+1) Q(x) = x^23+1
w Q(s) = v Q(2^154 t)
```

when

```text
s+1       = 2^(23m) w
2^154 t+1 = 3^(17m) v.
```

Useful theorem names:

```text
add_one_mul_plusCofactor
state_power_cofactor_balance
add_one_dvd_plusCofactor_sub_twentyThree
common_dvd_add_one_plusCofactor_dvd_twentyThree
reduced_quotients_modEq
fixedDivisor_isCoprime_twentyThree
fixedDivisor_reduced_quotients_modEq
```

The last theorem says: after cancelling the forced common register factor
`F` from both valuation quotients, the residual quotients are congruent modulo
`F`.  Ask Fable whether either residual quotient is already semantically fixed
modulo `F`, or whether a second factor of `F` is forced.  That could turn the
hidden-register observation into a contradiction or an iterated lift.

## Important negative diagnostic

A plain local sieve that forgets valuation/register side conditions appears
useless.  An exact exploratory sweep tested all 221 primes
`p=1 (mod 23)` below 50,000 and every exponent period of `rho=C/D mod p`
(2,699,189 period entries total).  The original public-state equation was
locally soluble in free `s^23,t^23` for every `m` class in every case.

This sweep was not committed as a certificate.  Do not cite it as a theorem.
Its lesson is methodological: retain exact valuation quotients/registers, or
use a global norm/S-unit/Diophantine-approximation argument.

## Newest incoming request: Roth bridge

Read the section headed
`Kontorovich request: Roth bridge closes infinite pure-state runs` at the tail
of `docs/FOR_CLEAN_LEAN.md` before coding.

Fable generalizes recharge to `h=23*ell`.  With `m,ell,s,t>0`, the transition
equation is

```text
3^(17m) (s^23+1)
  = 2^(23m) (1+(2^(154ell)t)^23).                 (GSPQ)
```

Set

```text
a=(17m)/23
e=(17m)%23
U=3^a
X=U*s
Y=2^m * 2^(154ell) * t
Z=2^m.
```

The requested elementary bridge is:

1. normalize GSPQ to

   ```text
   Y^23 - 3^e X^23 = 3^(17m)-2^(23m) > 0;        (RB1)
   ```

2. prove GSPQ implies `2^(154ell)*t > s`, hence
   `3^(114ell)*t > s`;
3. prove `2^(23m) | s+1`, `m>0` imply `U<s` and `X<s^2`;
4. over `ℝ`, for `alpha>0`, `alpha^23=3^e`, prove RB1 implies

   ```text
   0 < Y/X-alpha < alpha/s^23.                   (RB2)
   ```

Suggested new file:

```text
KontoroC/KontoroC/ChargeStatePowerRoth.lean
```

Import `KontoroC.ChargeStatePowerQuine`, add it to `KontoroC.lean`, and print
headline axioms in `KontoroC/Audit.lean`.

Keep Roth itself external unless mathlib unexpectedly contains an appropriate
theorem.  Do not add Roth as an axiom.  Prefer a conditional interface whose
hypothesis literally states the needed finiteness of reduced rational
approximants.

### Audit points for the Roth argument

The outline is plausible, but formalization must expose these seams:

- For `e != 0`, prove `alpha=3^(e/23)` is algebraic and irrational, or leave
  those as explicit external/Roth-interface premises.
- Convert RB2 to an exponent-11 approximation only after recording the
  eventual constant: `alpha/s^23 < 1/q^11` needs `q<=X<s^2` and eventually
  `s>alpha`, not just exponent arithmetic.
- An infinite run and pigeonhole give one repeated `e` class.  To use Roth,
  show the associated *reduced* rationals are infinitely many.  Strictly
  increasing roots alone does not immediately prove reduced denominators grow,
  but RB2 tends to zero; a fixed rational cannot recur infinitely often unless
  it equals irrational `alpha`.  State this step explicitly.
- The existing `m=0 (mod 23)` theorem kills the `e=0` class because
  `gcd(17,23)=1`, but connect those indices in Lean rather than prose.
- This route excludes an infinite orbit wholly contained in the pure
  public-23rd-power type.  It does not exclude isolated transitions, corrected
  encodings, or multi-rail constructions.

## Best next actions

1. Formalize the four elementary Roth bridge statements in a separate file.
2. Send theorem names and any corrected inequalities to Fable through
   `CLEAN_LEAN/FOR_FABLE.md`.
3. Define a clean conditional Roth-finiteness consumer, without axioms, only
   after the elementary statements compile.
4. In parallel conceptually (not by corrupting the proof scope), inspect the
   hidden-register consequence from
   `fixedDivisor_reduced_quotients_modEq`: determine whether the residual
   quotient lift repeats or stops.
5. Keep checking the incoming channel after every task; the constructive worker
   is actively refining the proposal.

## Safe stopping-point summary

Two literal perfect-power rails have been sharply narrowed, and the pure
coefficient public-state class has been ruled out completely in Lean.  The
remaining individual scaled equations look globally hard and defeat naive
local sieves.  The strongest current strategy is no longer “prove every
transition impossible”; it is “prove no infinite run can remain in this
type,” with an elementary Lean bridge to an explicitly external Roth theorem.
The cyclotomic cofactor/hidden-register route is the best elementary backup.

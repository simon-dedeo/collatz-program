# Condensed sets and the ordinary holonomy boundary

**Status (2026-07-29).** Condensed mathematics supplies a useful standard
language for the ordinary/profinite seam, but not a compactness proof of
Collatz.  The first consequence of taking that language seriously is negative
and kernel-checked: every complete component-holonomy bar has unbounded binary
cylinder width, and no finite family of collision shadows can be complete.
See
`KontoroC/KontoroC/ComponentHolonomyCondensedBoundary.lean`.

The background reference is Peter Scholze's
[Lectures on Condensed Mathematics](https://arxiv.org/abs/2605.03658),
reporting joint work with Dustin Clausen.  Nothing below imports a condensed
library into Lean; the checked theorems are the elementary set-level content
needed before that machinery could add anything.

## 1. The useful dictionary

A topological space `X` determines a condensed set by testing it on profinite
sets `S`:

```text
S |-> Continuous(S,X).
```

For this program the important distinction is

```text
ordinary integers       Z_disc
                           |
                           v
2-adic completion       Z_2.
```

A compatible tower of residues is a point of `Z_2`.  It is an ordinary
integer only when it lies in the image of the discrete object `Z_disc`; a
positive ordinary integer additionally satisfies an Archimedean sign
condition.  Thus the fully honest ambient object is adelic, for example the
diagonal inside `R x Z_2` (and `R x Z_2 x Z_3` when the odd multiplier is
retained).  Condensed sets preserve this distinction instead of identifying a
dense discrete subgroup with its completion.

This is exactly the seam met twice in the repo:

1. an infinite Hensel construction can converge to a nonordinary `2`-adic
   source;
2. a holonomy bar must cover the discrete positive naturals, not merely have
   full Haar measure or a large open subset in `Z_2`.

At the abelian level, the obstruction to ordinary realization can be placed
in the condensed quotient

```text
Q_ord = Z_2 / Z_disc.
```

The existing theorem that retroactive tail digits are eventually zero exactly
when the natural representatives stabilize is an explicit coordinate
description of the zero class.  Condensed language is the coordinate-free
version; it does not make a nonzero class vanish.

## 2. A bar is an infinite cover of a discrete locus

Each collision shadow is one clopen binary cylinder in `Z_2`.  A complete bar
asks for the pullback of the union of those cylinders to cover every discrete
ordinary point `n>1`.  Categorically, the intended statement is an
epimorphism onto the discrete ordinary locus, not a finite open cover of a
compact space.

Lean now checks the elementary ind-finite form.  If `BarsThrough shadow B`
means that all ordinary `2 <= n <= B` are covered, then

```text
OrdinaryHolonomyBar shadow
  <-> for every B, BarsThrough shadow B.
```

This is deliberately not compactness: the target is the increasing union of
finite discrete stages.

## 3. The mandatory boundary singularity at `1`

No valid collision shadow covers `1`, because its descent theorem would
produce a positive natural strictly below `1`.  But

```text
n_W = 1 + 2^W
```

is an ordinary positive integer greater than `1` and converges to `1` in
`Z_2`.  A cylinder of width at most `W` cannot distinguish `n_W` from `1`.
Consequently Lean proves

```text
OrdinaryHolonomyBar shadow
  -> for every W, some covering shadow has width > W,
```

and therefore

```text
no family indexed by a finite type is an OrdinaryHolonomyBar.
```

This adds a second distinguished boundary point to the earlier picture:

- `-1 = 111..._2` is the nonordinary all-one ray that a contraction theorem
  may leave untouched;
- `1` is the ordinary component minimum, and barred points accumulate at it
  through `1+2^W`.

A proof must separate every one of those points from `1` at a later finite
stage.  No bounded-state, bounded-width, or finite-subcover argument can do
that.

## 4. Where condensed methods might genuinely help

There are two non-cosmetic uses.

### 4.1 Derived inverse-limit obstruction

The construction side repeatedly produces compatible finite solutions whose
limit is only profinite.  A standard home for the defect is a quotient or a
derived inverse-limit class.  A useful theorem would identify the
retroactive-carry sequence with a canonical class in a condensed/solid
complex and prove that the literal Collatz transition annihilates that class
only when its digits are eventually zero.  This would replace the current
coordinate-by-coordinate ordinary-root audit with a functorial obstruction
that survives changes of compiler coordinates.

This is plausible infrastructure, not a proof: the relevant complex and its
exactness theorem have not been constructed.

### 4.2 A sheaf of local descent witnesses

Collision shadows restrict and pull back along clopen charts.  They can
therefore be organized as a presheaf of descent witnesses on the profinite
binary tree.  The desired productive-bar theorem becomes:

```text
every section over an ordinary finite stage extends, after finite refinement,
to a local descent witness.
```

If the shadow-production rules formed an exact or acyclic condensed complex,
local existence could imply the required stagewise epimorphism.  But
condensed descent cannot manufacture the missing production law: odd
pullback consumes a factor of `3` in the source gap, and a new arithmetic rule
must replenish it.  That is still the multiplier-specific heart of the
problem.

## 5. Research verdict

Condensed sets are useful here as a **truth-preserving interface**:

- they put ordinary, `2`-adic, `3`-adic, and Archimedean data in one standard
  local/global language;
- they expose the exact quotient in which a merely profinite construction
  fails;
- they formulate a complete holonomy bar as an infinite stagewise
  epimorphism;
- they prevent an invalid compactness or finite-subcover argument.

They are not yet a termination engine.  The next mathematical theorem remains
an unbounded-width shadow-production rule.  The condensed formulation says
precisely what such a rule must prove and where its obstruction class lives;
the arithmetic of `3x+1`, rather than the categorical formalism, must make the
class vanish.

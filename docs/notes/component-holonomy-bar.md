# The component-holonomy bar

**Status (2026-07-29).** The reduction in this note is kernel-checked in
`KontoroC/KontoroC/ComponentHolonomyBar.lean`. It does not prove Collatz. It
turns the missing theorem into a sharply specified infinite symbolic object:
a productive family of affine collision shadows barring every eventually-zero
binary ray except the integer `1`.

## 1. Stop following the orbit

Let `x ~ y` mean that the two Syracuse trajectories eventually merge, and call
`m` a component minimum when `m>0` and every positive `x~m` satisfies `m<=x`.
Every positive component has such an `m` by well-ordering. Therefore Collatz
is equivalent to the assertion that the only component minimum is `1`.

Suppose two legal affine routes collide:

```text
T^i(2^w k+r-d) = T^j(2^w k+r),       0<d<r<2^w.       (HB1)
```

Every integer `n=r mod 2^w` is the right sibling in this collision and has the
strictly smaller positive component mate `n-d`. Consequently no component
minimum lies in that binary cylinder. The Lean structure `CollisionShadow`
records exactly `(w,r,d,i,j)` and the symbolic all-`k` identity;
`CollisionShadow.descent` proves the conclusion without search or asymptotics.

The first checked shadows are

```text
5   mod 8:     n-1 ~ n,
99  mod 256:   n-1 ~ n,
101 mod 256:   n-3 ~ n.                              (HB2)
```

They follow from the two- and five-way collision fibers already proved in
`CollatzComponentHolonomy.lean`.

The first composition law is also checked.  If both sources of a shadow lie
in residue `2 mod 3`, take their odd predecessors and restrict the old affine
tail to one class modulo three.  A width-`w` shadow becomes a width-`w+1`
shadow, and its source gap changes by `d -> 2d/3`.  Applying this
`oddPullback` to `101 mod 256` generates

```text
67 mod 512:    n-2 ~ n.                              (HB2a)
```

This is generated algebraically rather than discovered as a new atlas row.

## 2. The proposed reason for termination

Positive natural numbers are the eventually-zero rays of the binary prefix
tree. The 2-adic fixed point `-1` is the all-one ray. Earlier contraction
programs repeatedly found a marginal `-1` mode and tried to suppress it by an
average or scalar potential. The holonomy-bar proposal allows that mode to
survive:

> **Holonomy-bar target.** Construct collision shadows whose right cylinders
> meet every eventually-zero binary ray representing an integer `n>1`. The
> all-one ray may be the unique infinite unbarred end.

This is enough. Lean proves `merge_one_of_ordinaryHolonomyBar`: if a family of
checked shadows covers every ordinary `n>1`, then the least point `m` of the
component of any positive `n` is covered; its smaller sibling contradicts
minimality; hence `m=1` and `n~1`.

This is a new possible mathematical reason for termination:

```text
ordinary termination
  = well-foundedness of component order
  + a collision bar on eventually-zero binary ends,

while the exceptional noncontracting point
  = the nonordinary all-one end -1.                         (HB3)
```

Measure is not enough. A prefix-free shadow family of Kraft mass one may still
miss exceptional ordinary rays. The required assertion is a **productive
bar**: given a finite prefix with a zero above its last one, a finite symbolic
procedure must eventually emit a collision shadow covering that ordinary
continuation. Its running time may grow with the last one. No uniform
finite-state or fixed-depth theorem is being assumed.

## 3. How to build the bar

At width `w`, each residue has an exact affine chart

```text
T^w(2^w k+r) = 3^a k+c_r,
```

where `a` and `c_r` come from its legal parity word. Equal chart pairs give
collision shadows; routes of different lengths may collide as well. The
construction problem is not to enumerate more isolated pairs. It is to prove
a recursive shadow-production rule of the form

```text
surviving prefix u0v
   -> a right-sibling collision below some finite extension of u0v,

surviving prefix 1^w
   -> 1^(w+1).                                           (HB4)
```

Only the second alternative may persist forever. The zero in the first line
is the ordinary boundary datum: it is the first bit at which a positive
integer separates from `-1`.

The likely state is not the residue alone. It should retain the affine offset
difference between two parity charts and the exact powers of `2` and `3` in
their common linear part. Composition may then be finite in syntax while
carrying an unbounded integer offset register, outside the already-closed
finite-state-potential lane.

There are two plausible proof engines.

1. **Carry induction.** Adding the right sibling changes a finite suffix of
   the parity word. Prove that the first zero above the suffix supplies a
   carry-termination point at which two affine offsets differ by the required
   power of three. The existing 2-, 3-, and 5-way fibers are the first carry
   identities.
2. **Two-base rigidity.** Let `S_w` be the survivor prefixes after all
   generated shadows of width at most `w` are removed. Binary refinement gives
   a 2-Mahler/automatic recursion. Equality of affine targets groups the same
   prefixes by powers of three. If that grouping can be promoted to a genuine
   3-Mahler recursion for the same regular survivor series, standard `x2/x3`
   rigidity forces rational/eventually periodic structure. Existing
   fixed-affine and finite-state no-go theorems would then leave only the
   singular homogeneous boundary `1^infinity`. The missing step is the
   3-Mahler recursion; it must not be inferred from one dyadic ray.

This places Mahler transcendence differently from the counterexample work. It
is not a payload intended to construct an orbit, but a rigidity theorem for
the *language of collision-shadow survivors*. A regular analytic survivor is
a wall; the singular boundary term is precisely `-1`.

## 4. The `5x+1` control

The formal minimum-and-shadow reduction works for any Collatz-like map, so it
cannot distinguish `3x+1` from `5x+1`. The distinction must enter the
production theorem (HB4). A parity-only or purely 2-adic proof of HB4 is
therefore invalid.

For `qx+1`, a length-`w` chart has linear part `q^a/2^w`; collision requires
equality of the odd-step counts and an offset difference divisible by the
corresponding power of `q`. Thus carry induction and survivor grouping depend
on powers of `3`, while the `5x+1` control substitutes powers of `5`. The
falsification test is exact:

- derive the shadow-production recurrence with `q` symbolic;
- identify the inequality or divisibility step true at `q=3`;
- verify that it fails at `q=5` before claiming a bar.

This forces the proof to couple binary prefix geometry to the Archimedean and
odd-prime multiplier, as the earlier descent audit requires.

## 5. Immediate theorem targets

The foundational interface is checked. The next non-numerical results are:

1. extend the checked odd-pullback composition into a complete finite grammar
   of common inverse-prefix operations;
2. a carry lemma producing a shadow when a surviving prefix first differs
   from `1^infinity`;
3. a well-founded measure on that carry construction;
4. the complete `OrdinaryHolonomyBar`, consumed directly by the checked
   full-Collatz theorem.

Until item 4 is proved, HB3 is a research mechanism, not a proof. Its value is
that the endpoint, exceptional mode, ordinary/2-adic distinction, and `5x+1`
falsification test are explicit in one theorem-shaped program.

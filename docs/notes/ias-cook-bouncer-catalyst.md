# Cook catalytic-memory audit of the bouncer

James Cook's IAS talk on catalytic memory is the strongest construction-side
complement to the Yap resource program.  A borrowed register is genuinely
catalytic only when the computation restores it exactly, allowing the same
unknown contents to be reused at every recursive call.  The bouncer's fixed
congruence register looks similar, but its free cylinder tail must be checked.

For one bouncer edge write

```text
input  = ib + is*t,
output = ob + os*t.
```

Linking this output to the next edge's input solves one linear Diophantine
equation.  The allowed incoming tails form one congruence class of index

```text
next_is / gcd(os,next_is).
```

Index one is the natural clean-reset condition: no new tail digits are
consumed.  An index above one means the next block requires a thinner address
cylinder, exactly the preloaded-tape behavior Cook's criterion is meant to
detect.

The bouncer strides make the obstruction symbolic.  If the shared defect
phase is `m`, the following background phase is `h'`, and its next defect
phase is `m''`, then

```text
v2(os)      = 23*m+1,
v2(next_is) = 23*m+154*h'+23*m''+1,

v2(link index) = 154*h'+23*m'' >= 177.
```

Thus every positive link restricts the incoming tail by an index divisible
by `2^177`; an `N`-block bouncer cylinder consumes at least `177*(N-1)`
dyadic tail bits.  This algebraic derivation is independent of the bounded
atlas but is still research-side rather than kernel-checked.

The exact worker additionally checks all 248,832 consecutive links with
`m,h,m'<=12`, using the full integer strides rather than valuations alone.
There are no clean links.  This closes the *natural affine-tail* catalyst
interpretation: the fixed congruence register is restored, but the ordinary
address catalyst is not.  It does not exclude a different nonlinear
coordinate with an independently proved fixed interface, and it does not
invalidate the backward atlas as a finite obstruction/precision dataset.

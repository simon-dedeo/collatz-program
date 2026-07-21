#!/usr/bin/env python3
"""Exact finite counterexample to entropy-increment monotonicity.

The promising selected k=12,...,19 exact feasible certificates, together with
the uncertified floating k=20 candidate, have decreasing digitwise entropy
deficits

    h_j = Ent(E[f | F_j]) - Ent(E[f | F_(j-1)]).

That pattern is not a consequence of KL feasibility alone.  This script
checks an explicit level-k=3 feasible vector at lambda=1001/1000 and proves
``h_2 > h_1`` using rational bounds only.

For alpha=log_2(3), the elementary inequalities 1<alpha<2 imply

    lambda^(alpha-2) > lambda^(-1),
    lambda^(alpha-1) > 1.

The verifier replaces the two irrational branch weights by the strict lower
bounds lambda^(-1) and 1.  Feasibility for this tighter rational system
therefore proves feasibility for the true KL operator.

For the entropy comparison, ``log x <= x-1`` gives
``D(p||u) <= chi^2(p,u)``, while ``log(1+x) > x/(1+x)`` gives
``log(9/8)>1/9``.  The resulting rational upper bound for h_1 is smaller than
the rational lower bound for h_2, so no floating transcendental comparison is
part of the proof.
"""

from __future__ import annotations

import math
from fractions import Fraction


K = 3
MODULUS = 3**K
COARSE_MODULUS = 3 ** (K - 1)
LAMBDA = Fraction(1001, 1000)
STATES = tuple(range(2, MODULUS, 3))
VALUES = (101, 100, 75, 101, 100, 75, 101, 100, 150)


def build_rows() -> list[tuple[int, int, tuple[int, int, int] | None]]:
    """Return transport index, branch class, and the exact three-fiber."""

    index = {state: i for i, state in enumerate(STATES)}
    rows: list[tuple[int, int, tuple[int, int, int] | None]] = []
    for state in STATES:
        transport = index[(4 * state) % MODULUS]
        branch = state % 9
        if branch == 2:
            coarse = ((4 * state - 2) // 3) % COARSE_MODULUS
        elif branch == 8:
            coarse = ((2 * state - 1) // 3) % COARSE_MODULUS
        else:
            if branch != 5:
                raise AssertionError("unexpected KL residue class")
            rows.append((transport, branch, None))
            continue
        fiber = tuple(
            index[coarse + digit * COARSE_MODULUS] for digit in range(3)
        )
        rows.append((transport, branch, fiber))
    return rows


def verify_tightened_feasibility() -> list[Fraction]:
    """Check ``c <= F(c)`` with W2=lambda^-1 and W8=1 exactly."""

    numerator = LAMBDA.numerator
    denominator = LAMBDA.denominator
    squared_numerator = numerator**2
    squared_denominator = denominator**2
    margins: list[Fraction] = []

    for i, (transport, branch, fiber) in enumerate(build_rows()):
        lhs = VALUES[i] * squared_numerator
        rhs = VALUES[transport] * squared_denominator
        if branch == 2:
            assert fiber is not None
            rhs += min(VALUES[index] for index in fiber) * numerator * denominator
        elif branch == 8:
            assert fiber is not None
            rhs += min(VALUES[index] for index in fiber) * squared_numerator
        elif branch != 5:
            raise AssertionError("unexpected branch")
        margin = Fraction(rhs - lhs, squared_numerator)
        if margin <= 0:
            raise AssertionError(
                f"state {STATES[i]} fails tightened feasibility by {-margin}"
            )
        margins.append(margin)
    return margins


def verify_entropy_reversal() -> tuple[Fraction, Fraction]:
    """Return rigorous ``h1`` upper and ``h2`` lower bounds."""

    digit_masses = tuple(
        sum(VALUES[digit + 3 * lift] for lift in range(3))
        for digit in range(3)
    )
    if digit_masses != (303, 300, 300) or sum(digit_masses) != 903:
        raise AssertionError("unexpected first-digit marginal")

    # For p=(303,300,300)/903 and u=(1/3,1/3,1/3),
    # KL(p||u) <= chi^2(p,u) = 3*sum_i (p_i-1/3)^2.
    probabilities = tuple(Fraction(mass, 903) for mass in digit_masses)
    uniform = Fraction(1, 3)
    h1_upper = 3 * sum((probability - uniform) ** 2 for probability in probabilities)

    # The first two fibers are uniform.  The last has conditional law
    # (1/4,1/4,1/2), KL divergence (1/2)log(9/8), and mass 300/903=100/301.
    # Since log(9/8)>1/9, h2 > (50/301)*(1/9).
    if (VALUES[2], VALUES[5], VALUES[8]) != (75, 75, 150):
        raise AssertionError("unexpected nonuniform terminal fiber")
    h2_lower = Fraction(50, 301 * 9)
    if not h2_lower > h1_upper:
        raise AssertionError("rational entropy bounds do not prove reversal")
    return h1_upper, h2_lower


def main() -> None:
    if len(STATES) != len(VALUES) or min(VALUES) <= 0:
        raise AssertionError("counterexample must be positive on every state")
    margins = verify_tightened_feasibility()
    h1_upper, h2_lower = verify_entropy_reversal()

    # Decimal renderings are orientation only; the proof above is rational.
    p = tuple(Fraction(mass, 903) for mass in (303, 300, 300))
    h1_decimal = sum(float(x) * math.log(3 * float(x)) for x in p)
    h2_decimal = (50 / 301) * math.log(9 / 8)
    print(
        "PASS: exact tightened KL feasibility at k=3, lambda=1001/1000, "
        f"minimum margin={min(margins)}"
    )
    print(
        "PASS: entropy increments reverse: "
        f"h1={h1_decimal:.12g} < {h1_upper} < {h2_lower} "
        f"< h2={h2_decimal:.12g}"
    )
    print("CONCLUSION: KL feasibility alone does not force entropy monotonicity")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact bounded audit of the targetwise KL base inequalities D1--D3.

For the accelerated Syracuse map

    T(n) = n/2                 if n is even,
           (3n+1)/2            if n is odd,

let P*_a(X) be the positive integers n <= X having a path to a all of
whose vertices are at most X.  If a is a nonperiodic point with
a == 2 (mod 3), put

    b = 4a,  c = (2a-1)/3.

The targetwise precursor of Krasikov--Lagarias Proposition 2.1 is the
exact disjoint partition

    P*_a(X) = {a, 2a} ⊎ P*_b(X) ⊎ P*_c(X),       X >= 4a.

At X = 2^y a and X' = 2^(y-1)(2a-1), y >= 2, it implies the
following bounds, including constants discarded in the homogeneous
base system:

  D1, a == 2 (mod 9): |P*_a(X)| >= 3 + |P*_(4a)(X)|
                                           + |P*_((4a-2)/3)(X')|;
  D2, a == 5 (mod 9): |P*_a(X)| >= 3 + |P*_(4a)(X)|;
  D3, a == 8 (mod 9): |P*_a(X)| >= 2 + |P*_(4a)(X)|
                                           + |P*_((2a-1)/3)(X')|.

This script exhaustively verifies the exact partition, all required
inclusions and disjointness statements, and the strengthened cardinality
bounds for every nonperiodic a < 500 with a == 2 (mod 3), at every integer
2 <= y <= 5.  It computes every predecessor set twice: once by scanning
forward orbits and independently by reverse-tree search in [1,X].

The periodic regression a=2, y=3 confirms why nonperiodicity is essential:
the two D1 child sets overlap and even the homogeneous inequality fails.
Only integer arithmetic is used.
"""

from functools import cache
from itertools import combinations


TARGET_LIMIT = 500
Y_MIN = 2
Y_MAX = 5


def syracuse(n: int) -> int:
    """One accelerated Collatz/Syracuse step on a positive integer."""

    assert n > 0
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


@cache
def forward_bounded_predecessors(target: int, bound: int) -> frozenset[int]:
    """Enumerate P* by independently scanning every forward orbit."""

    assert 1 <= target <= bound
    result: set[int] = set()
    for start in range(1, bound + 1):
        current = start
        seen: set[int] = set()
        while 1 <= current <= bound and current not in seen:
            if current == target:
                result.add(start)
                break
            seen.add(current)
            current = syracuse(current)
    return frozenset(result)


@cache
def reverse_bounded_predecessors(target: int, bound: int) -> frozenset[int]:
    """Enumerate P* by reverse search in the finite graph [1,bound]."""

    assert 1 <= target <= bound
    result = {target}
    frontier = [target]
    while frontier:
        current = frontier.pop()
        candidates = [2 * current]
        if current % 3 == 2:
            candidates.append((2 * current - 1) // 3)
        for predecessor in candidates:
            if 1 <= predecessor <= bound and predecessor not in result:
                assert syracuse(predecessor) == current
                result.add(predecessor)
                frontier.append(predecessor)
    return frozenset(result)


def checked_predecessors(target: int, bound: int) -> frozenset[int]:
    """Return P* after requiring the two independent enumerators to agree."""

    forward = forward_bounded_predecessors(target, bound)
    reverse = reverse_bounded_predecessors(target, bound)
    assert forward == reverse, (target, bound, forward ^ reverse)
    return forward


@cache
def is_periodic_point(n: int) -> bool:
    """Determine whether n itself belongs to its first repeated orbit cycle."""

    assert n > 0
    positions: dict[int, int] = {}
    orbit: list[int] = []
    current = n
    while current not in positions:
        positions[current] = len(orbit)
        orbit.append(current)
        current = syracuse(current)
    return n in orbit[positions[current] :]


def assert_pairwise_disjoint(*blocks: frozenset[int]) -> None:
    """Assert pairwise disjointness, reporting the first overlap exactly."""

    for left, right in combinations(blocks, 2):
        assert left.isdisjoint(right), left & right


def verify_nonperiodic_case(a: int, y: int) -> str:
    """Verify the exact partition and the applicable strengthened D-row."""

    assert 1 <= a < TARGET_LIMIT
    assert a % 3 == 2
    assert not is_periodic_point(a)
    assert Y_MIN <= y <= Y_MAX

    b = 4 * a
    c = (2 * a - 1) // 3
    d = 2 * c
    x = 2**y * a
    x_prime = 2 ** (y - 1) * (2 * a - 1)

    assert 3 * c == 2 * a - 1
    assert d == (4 * a - 2) // 3
    assert syracuse(c) == a
    assert syracuse(b) == 2 * a
    assert syracuse(syracuse(b)) == a
    assert x >= 4 * a
    assert x == 2 ** (y - 2) * b
    assert x_prime == x - 2 ** (y - 1)
    assert x_prime < x

    # These are the exact integer forms of the two displayed alpha-scale
    # identities, using 2^alpha = 3 rather than a floating approximation.
    assert x_prime == 2 ** (y - 2) * 3 * d
    assert x_prime == 2 ** (y - 1) * 3 * c

    # Periodicity would propagate from either child target to a.  Check the
    # contrapositive concretely throughout the exhaustive test range.
    assert not is_periodic_point(b)
    assert not is_periodic_point(c)

    p_a_x = checked_predecessors(a, x)
    p_b_x = checked_predecessors(b, x)
    p_c_x = checked_predecessors(c, x)
    roots = frozenset((a, 2 * a))

    # Exact reverse-tree partition by the last incoming edge to a.
    assert_pairwise_disjoint(roots, p_b_x, p_c_x)
    assert roots | p_b_x | p_c_x == p_a_x

    p_c_x_prime = checked_predecessors(c, x_prime)
    assert p_c_x_prime <= p_c_x

    if a % 9 == 2:
        # Here c == 1 (mod 3), so P*_c(X') splits exactly into c and
        # P*_(2c)(X').  The latter target is d=(4a-2)/3.
        assert c % 3 == 1
        assert not is_periodic_point(d)
        p_d_x_prime = checked_predecessors(d, x_prime)
        singleton_c = frozenset((c,))
        assert_pairwise_disjoint(singleton_c, p_d_x_prime)
        assert singleton_c | p_d_x_prime == p_c_x_prime

        # These four blocks are the actual injection behind strengthened D1.
        blocks = (roots, p_b_x, singleton_c, p_d_x_prime)
        assert_pairwise_disjoint(*blocks)
        assert frozenset().union(*blocks) <= p_a_x
        assert len(p_a_x) >= 3 + len(p_b_x) + len(p_d_x_prime)
        return "D1"

    if a % 9 == 5:
        # Retaining just c itself from the third root block gives the extra 1.
        assert c % 3 == 0
        singleton_c = frozenset((c,))
        blocks = (roots, p_b_x, singleton_c)
        assert_pairwise_disjoint(*blocks)
        assert frozenset().union(*blocks) <= p_a_x
        assert len(p_a_x) >= 3 + len(p_b_x)
        return "D2"

    assert a % 9 == 8
    assert c % 3 == 2
    # Cutoff monotonicity embeds the D3 c-branch at X' into its root block.
    blocks = (roots, p_b_x, p_c_x_prime)
    assert_pairwise_disjoint(*blocks)
    assert frozenset().union(*blocks) <= p_a_x
    assert len(p_a_x) >= 2 + len(p_b_x) + len(p_c_x_prime)
    return "D3"


def verify_periodic_regression() -> None:
    """Show exact failure of D1 when the periodic target a=2 is admitted."""

    a = 2
    y = 3
    b = 4 * a
    d = (4 * a - 2) // 3
    x = 2**y * a
    x_prime = 2 ** (y - 1) * (2 * a - 1)

    assert is_periodic_point(a)
    assert (a, y, x, x_prime, b, d) == (2, 3, 16, 12, 8, 2)

    p_a_x = checked_predecessors(a, x)
    p_b_x = checked_predecessors(b, x)
    p_d_x_prime = checked_predecessors(d, x_prime)
    overlap = p_b_x & p_d_x_prime

    assert len(p_a_x) == 10
    assert len(p_b_x) == 7
    assert len(p_d_x_prime) == 9
    assert overlap == frozenset((3, 5, 6, 8, 10, 12))
    assert len(p_a_x) < len(p_b_x) + len(p_d_x_prime)
    assert len(p_a_x) < 3 + len(p_b_x) + len(p_d_x_prime)


def main() -> None:
    row_counts = {"D1": 0, "D2": 0, "D3": 0}
    targets: set[int] = set()
    cases = 0

    for a in range(1, TARGET_LIMIT):
        if a % 3 != 2 or is_periodic_point(a):
            continue
        targets.add(a)
        for y in range(Y_MIN, Y_MAX + 1):
            row = verify_nonperiodic_case(a, y)
            row_counts[row] += 1
            cases += 1

    verify_periodic_regression()

    assert targets
    assert cases == len(targets) * (Y_MAX - Y_MIN + 1)
    assert sum(row_counts.values()) == cases
    print(
        "PASS: independent forward-orbit and reverse-tree enumerators agree "
        "on every tested predecessor set"
    )
    print(
        "PASS: exact disjoint root partition and strengthened D1--D3 bounds "
        f"for {len(targets)} nonperiodic targets a < {TARGET_LIMIT}, "
        f"a == 2 (mod 3), y={Y_MIN}..{Y_MAX} ({cases} target-scale cases)"
    )
    print(
        "PASS: residue-row case counts "
        f"D1={row_counts['D1']}, D2={row_counts['D2']}, "
        f"D3={row_counts['D3']}"
    )
    print(
        "PASS: a=2, y=3 regression has counts 10, 7, 9 and overlap "
        "{3, 5, 6, 8, 10, 12}; nonperiodicity is necessary"
    )
    print("SCOPE: exhaustive only for the stated finite target and scale range")


if __name__ == "__main__":
    main()

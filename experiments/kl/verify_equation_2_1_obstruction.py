#!/usr/bin/env python3
"""Exact obstruction to Krasikov--Lagarias equation (2.1).

The paper defines

    pi*_a(x) = #{n <= x : T^j(n)=a for some j, and the path stays <= x}

and phi_k^m(y) as the infimum of pi*_a(2^y a) over positive
nonperiodic targets a in residue class m modulo 3^k.  Printed equation (2.1)
claims phi_k^m(y) = phi_k^(2m)(y-1) when m == 1 (mod 3).

At k=2, m=7 (mod 9), y=1, the two sides are exactly 3 and 2.
The finite witness sets are enumerated directly.  The universal lower bounds
are checked as identities and inequalities between affine polynomials in the
nonnegative residue parameter q.
"""

from dataclasses import dataclass


def syracuse(n: int) -> int:
    assert n > 0
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def bounded_predecessors(target: int, bound: int) -> set[int]:
    """Enumerate pi* exactly on the finite directed graph [1,bound]."""

    assert 1 <= target <= bound
    result: set[int] = set()
    for start in range(1, bound + 1):
        seen: set[int] = set()
        current = start
        while 1 <= current <= bound and current not in seen:
            if current == target:
                result.add(start)
                break
            seen.add(current)
            current = syracuse(current)
    return result


def reverse_bounded_predecessors(target: int, bound: int) -> set[int]:
    """Independently enumerate pi* by reverse search inside [1,bound]."""

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
    return result


def is_periodic_point(n: int) -> bool:
    """Decide whether n itself lies on its eventually reached finite cycle."""

    positions: dict[int, int] = {}
    orbit: list[int] = []
    current = n
    while current not in positions:
        positions[current] = len(orbit)
        orbit.append(current)
        current = syracuse(current)
    cycle = orbit[positions[current] :]
    return n in cycle


@dataclass(frozen=True)
class Affine:
    """The exact affine integer polynomial q_coeff*q + constant."""

    q_coeff: int
    constant: int

    def __add__(self, other: "Affine") -> "Affine":
        return Affine(
            self.q_coeff + other.q_coeff, self.constant + other.constant
        )

    def __sub__(self, other: "Affine") -> "Affine":
        return Affine(
            self.q_coeff - other.q_coeff, self.constant - other.constant
        )

    def scale(self, factor: int) -> "Affine":
        return Affine(factor * self.q_coeff, factor * self.constant)

    def exact_div(self, divisor: int) -> "Affine":
        assert self.q_coeff % divisor == 0
        assert self.constant % divisor == 0
        return Affine(self.q_coeff // divisor, self.constant // divisor)

    def positive_for_nonnegative_q(self) -> bool:
        return self.q_coeff >= 0 and self.constant > 0

    def odd_for_every_q(self) -> bool:
        return self.q_coeff % 2 == 0 and self.constant % 2 == 1


ONE = Affine(0, 1)


def verify_parametric_lower_bounds() -> None:
    """Check the forced distinct predecessors for every q >= 0 exactly."""

    # Every a == 7 (mod 9) has these three bounded predecessors at x=2a:
    # a (zero steps), 2a -> a, and (4a-1)/3 -> 2a -> a.
    a = Affine(9, 7)
    two_a = a.scale(2)
    odd_predecessor_of_two_a = (a.scale(4) - ONE).exact_div(3)
    assert a.constant % 9 == 7 and a.q_coeff % 9 == 0
    assert odd_predecessor_of_two_a.odd_for_every_q()
    assert (odd_predecessor_of_two_a - a).positive_for_nonnegative_q()
    assert (two_a - odd_predecessor_of_two_a).positive_for_nonnegative_q()
    assert (odd_predecessor_of_two_a.scale(3) + ONE).exact_div(2) == two_a
    assert two_a.exact_div(2) == a

    # Every b == 5 (mod 9) has at least b and (2b-1)/3 -> b at x=b.
    b = Affine(9, 5)
    odd_predecessor_of_b = (b.scale(2) - ONE).exact_div(3)
    assert b.constant % 9 == 5 and b.q_coeff % 9 == 0
    assert odd_predecessor_of_b.positive_for_nonnegative_q()
    assert odd_predecessor_of_b.odd_for_every_q()
    assert (b - odd_predecessor_of_b).positive_for_nonnegative_q()
    assert (odd_predecessor_of_b.scale(3) + ONE).exact_div(2) == b


def main() -> None:
    verify_parametric_lower_bounds()

    left_target = 7
    right_target = 14  # 14 == 2*7 == 5 (mod 9)
    assert left_target % 9 == 7
    assert right_target % 9 == 5
    assert not is_periodic_point(left_target)
    assert not is_periodic_point(right_target)

    left = bounded_predecessors(left_target, 2 * left_target)
    right = bounded_predecessors(right_target, right_target)
    left_reverse = reverse_bounded_predecessors(
        left_target, 2 * left_target
    )
    right_reverse = reverse_bounded_predecessors(right_target, right_target)
    assert left_reverse == left
    assert right_reverse == right
    assert left == {7, 9, 14}
    assert right == {9, 14}

    # Parametric lower bounds plus these admissible witnesses identify the
    # infima, not merely one pair of target counts.
    phi_7_at_1 = len(left)
    phi_5_at_0 = len(right)
    assert phi_7_at_1 == 3
    assert phi_5_at_0 == 2
    assert phi_7_at_1 != phi_5_at_0

    print("PASS: every a == 7 (mod 9) forces three paths below 2a")
    print("PASS: pi*_7(14) has exactly {7, 9, 14}")
    print("PASS: every b == 5 (mod 9) forces two paths below b")
    print("PASS: pi*_14(14) has exactly {9, 14}")
    print("PASS: independent forward-orbit and reverse-tree enumerators agree")
    print("VERDICT: phi_2^7(1)=3 but phi_2^(2*7)(0)=2")
    print(
        "AUDITED CORRECTION (not checked here): "
        "phi_k^m(y) >= 1 + phi_k^(2m)(y-1) for y >= 1"
    )
    print("SCOPE: the printed equality fails, but the needed transfer direction survives")


if __name__ == "__main__":
    main()

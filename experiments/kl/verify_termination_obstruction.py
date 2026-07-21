#!/usr/bin/env python3
"""Exact finite obstruction to the printed proof of KL Theorem 3.1.

This checks one legal k=5 elimination path using only integer arithmetic.  It
does not claim that the elimination process fails to terminate.  It invalidates
the paper's deletion-rule derivation of equation (3.2) and directly falsifies
the following history-free subtree-isomorphism step.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Shift:
    """The exact real shift constant + alpha_coeff * log_2(3)."""

    constant: int
    alpha_coeff: int

    def __add__(self, other: "Shift") -> "Shift":
        return Shift(
            self.constant + other.constant,
            self.alpha_coeff + other.alpha_coeff,
        )

    def __sub__(self, other: "Shift") -> "Shift":
        return Shift(
            self.constant - other.constant,
            self.alpha_coeff - other.alpha_coeff,
        )


TRANSPORT = Shift(-2, 0)
RETARDED = Shift(-2, 1)
ADVANCED = Shift(-1, 1)


def sign(shift: Shift) -> int:
    """Sign of a+b*log_2(3), by comparing 2^a 3^b with 1 exactly."""

    numerator = 1
    denominator = 1
    if shift.constant >= 0:
        numerator *= 2**shift.constant
    else:
        denominator *= 2 ** (-shift.constant)
    if shift.alpha_coeff >= 0:
        numerator *= 3**shift.alpha_coeff
    else:
        denominator *= 3 ** (-shift.alpha_coeff)
    return (numerator > denominator) - (numerator < denominator)


def transport(m: int, modulus: int) -> int:
    return (4 * m) % modulus


def branch_lifts(m: int, k: int, kind: str) -> list[int]:
    coarse_modulus = 3 ** (k - 1)
    modulus = 3**k
    if kind == "B2":
        assert m % 9 == 2
        coarse = ((4 * m - 2) // 3) % coarse_modulus
    elif kind == "B8":
        assert m % 9 == 8
        coarse = ((2 * m - 1) // 3) % coarse_modulus
    else:
        raise ValueError(kind)
    return [(coarse + j * coarse_modulus) % modulus for j in range(3)]


def main() -> None:
    k = 5
    modulus = 3**k
    root = 188
    certificate = [
        ("B8", 206),
        ("B8", 137),
        ("B2", 182),
        ("B2", 161),
        ("B8", 107),
        ("B8", 71),
        ("B8", 47),
        ("T", 188),
    ]
    expected_shifts = [
        Shift(-1, 1),
        Shift(-2, 2),
        Shift(-4, 3),
        Shift(-6, 4),
        Shift(-7, 5),
        Shift(-8, 6),
        Shift(-9, 7),
        Shift(-11, 7),
    ]

    state = root
    shift = Shift(0, 0)
    # Principal ancestors on this path, including the root.
    history: list[tuple[int, Shift]] = [(root, shift)]

    for index, ((kind, target), expected) in enumerate(
        zip(certificate, expected_shifts, strict=True), start=1
    ):
        if kind == "T":
            assert target == transport(state, modulus)
            increment = TRANSPORT
            deletion_tested = False
        else:
            assert target in branch_lifts(state, k, kind)
            increment = RETARDED if kind == "B2" else ADVANCED
            deletion_tested = True

        new_shift = shift + increment
        assert new_shift == expected
        assert sign(new_shift) >= 0

        repeated_lower_ancestor = any(
            old_state == target and sign(new_shift - old_shift) > 0
            for old_state, old_shift in history
        )
        if deletion_tested:
            # Every first-pass branch destination is new, so its leaf survives.
            assert not repeated_lower_ancestor
        elif index == len(certificate):
            # The repeated root survives only because transport children are not
            # among the new three-lift leaves to which the deletion rule applies.
            assert repeated_lower_ancestor

        state = target
        shift = new_shift
        history.append((state, shift))

    assert state == root
    assert sign(shift) > 0
    assert 3**7 > 2**11

    # Re-expanding the returned root does not reproduce its original subtree:
    # the repeated B8 child 206 is now deleted against its earlier occurrence.
    repeated_child = 206
    assert repeated_child in branch_lifts(root, k, "B8")
    repeated_child_shift = shift + ADVANCED
    old_child_shift = next(s for m, s in history if m == repeated_child)
    assert old_child_shift == Shift(-1, 1)
    assert repeated_child_shift == Shift(-12, 8)
    assert sign(repeated_child_shift) >= 0
    assert sign(repeated_child_shift - old_child_shift) > 0

    print("PASS: exact k=5 path survives and returns to residue 188")
    print("      old shift = (0,0); new shift = (-11,7) > 0")
    print("      because 3^7 = 2187 > 2048 = 2^11")
    print("PASS: re-expanded B8 child 206 is then deletion-eligible")
    print("VERDICT: the derivation of KL (3.2) and the history-free subtree step fail")
    print("SCOPE: this is not a nontermination cycle and does not refute Theorem 3.1")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact obstruction to KL's claimed nonempty three-lift minimum.

The printed deletion rule removes every new nonnegative branch leaf that has
an earlier same-residue principal ancestor at a strictly smaller shift.  This
checker follows one legal k=5 history, verifies that every chosen branch leaf
survives that rule, and then verifies that the next advanced split makes all
three new alternatives deletion-eligible.

This does not prove nontermination.  It shows that the literal algorithm can
reach the case the paper says cannot occur, so a repaired construction must
replace the empty-minimum semantics.  The current research candidate compiles
only complete occurrence-aware policies and assigns no policy to a marked leaf.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Shift:
    """Exact value ``constant + alpha_coeff * log_2(3)``."""

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
    """Compare ``constant + alpha_coeff*log_2(3)`` with zero exactly."""

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


def transport(state: int, modulus: int) -> int:
    return (4 * state) % modulus


def branch_lifts(state: int, k: int, kind: str) -> list[int]:
    coarse_modulus = 3 ** (k - 1)
    modulus = 3**k
    if kind == "B2":
        assert state % 9 == 2
        coarse = ((4 * state - 2) // 3) % coarse_modulus
    elif kind == "B8":
        assert state % 9 == 8
        coarse = ((2 * state - 1) // 3) % coarse_modulus
    else:
        raise ValueError(kind)
    return [(coarse + j * coarse_modulus) % modulus for j in range(3)]


def deletion_blockers(
    history: list[tuple[int, Shift]], target: int, target_shift: Shift
) -> list[tuple[int, Shift]]:
    return [
        (state, shift)
        for state, shift in history
        if state == target and sign(target_shift - shift) > 0
    ]


def update_minimum(
    minima: dict[int, Shift], state: int, shift: Shift
) -> dict[int, Shift]:
    updated = minima.copy()
    old = updated.get(state)
    if old is None or sign(shift - old) < 0:
        updated[state] = shift
    return updated


def compressed_children(
    k: int, state: int, shift: Shift, minima: dict[int, Shift]
) -> list[tuple[int, Shift, dict[int, Shift]]]:
    """Legal expandable children; residue minima are sufficient history."""

    modulus = 3**k
    children: list[tuple[int, Shift, dict[int, Shift]]] = []

    transport_state = transport(state, modulus)
    transport_shift = shift + TRANSPORT
    if sign(transport_shift) >= 0:
        children.append(
            (
                transport_state,
                transport_shift,
                update_minimum(minima, transport_state, transport_shift),
            )
        )

    kind = "B2" if state % 9 == 2 else "B8" if state % 9 == 8 else None
    if kind is not None:
        increment = RETARDED if kind == "B2" else ADVANCED
        branch_shift = shift + increment
        if sign(branch_shift) >= 0:
            for target in branch_lifts(state, k, kind):
                old = minima.get(target)
                if old is not None and sign(branch_shift - old) > 0:
                    continue
                children.append(
                    (
                        target,
                        branch_shift,
                        update_minimum(minima, target, branch_shift),
                    )
                )
    return children


def all_three_eligible(
    k: int, state: int, shift: Shift, minima: dict[int, Shift]
) -> bool:
    kind = "B2" if state % 9 == 2 else "B8" if state % 9 == 8 else None
    if kind is None:
        return False
    increment = RETARDED if kind == "B2" else ADVANCED
    child_shift = shift + increment
    if sign(child_shift) < 0:
        return False
    return all(
        target in minima and sign(child_shift - minima[target]) > 0
        for target in branch_lifts(state, k, kind)
    )


def first_all_three_depth(k: int, depth_limit: int | None = None) -> int | None:
    """Exact BFS over the sufficient compressed-history state."""

    modulus = 3**k
    frontier = [
        (root, Shift(0, 0), {root: Shift(0, 0)})
        for root in range(8, modulus, 9)
    ]
    depth = 0
    while frontier and (depth_limit is None or depth <= depth_limit):
        if any(all_three_eligible(k, *config) for config in frontier):
            return depth
        next_frontier: dict[
            tuple[int, Shift, tuple[tuple[int, Shift], ...]],
            tuple[int, Shift, dict[int, Shift]],
        ] = {}
        for config in frontier:
            for child in compressed_children(k, *config):
                key = (child[0], child[1], tuple(sorted(child[2].items())))
                next_frontier.setdefault(key, child)
        frontier = list(next_frontier.values())
        depth += 1
    return None


def main() -> None:
    k = 5
    modulus = 3**k
    root = 161
    # (kind, lift index or None for transport, destination, exact shift)
    certificate = [
        ("B8", 1, 107, Shift(-1, 1)),
        ("B8", 1, 152, Shift(-2, 2)),
        ("B8", 2, 182, Shift(-3, 3)),
        ("B2", 0, 80, Shift(-5, 4)),
        ("B8", 1, 134, Shift(-6, 5)),
        ("B8", 1, 89, Shift(-7, 6)),
        ("B8", 0, 59, Shift(-8, 7)),
        ("T", None, 236, Shift(-10, 7)),
        ("B2", 1, 152, Shift(-12, 8)),
        ("B8", 2, 182, Shift(-13, 9)),
        ("B2", 2, 242, Shift(-15, 10)),
    ]

    state = root
    shift = Shift(0, 0)
    history = [(state, shift)]

    for index, (kind, lift, target, expected_shift) in enumerate(
        certificate, start=1
    ):
        if kind == "T":
            assert lift is None
            assert target == transport(state, modulus)
            increment = TRANSPORT
        else:
            assert lift is not None
            assert target == branch_lifts(state, k, kind)[lift]
            increment = RETARDED if kind == "B2" else ADVANCED

        shift = shift + increment
        assert shift == expected_shift
        assert sign(shift) >= 0
        if kind != "T":
            # The chosen branch leaf really survives every earlier ancestor.
            assert not deletion_blockers(history, target, shift), index

        state = target
        history.append((state, shift))

    assert state == 242
    assert shift == Shift(-15, 10)
    assert state % 9 == 8

    child_shift = shift + ADVANCED
    assert child_shift == Shift(-16, 11)
    assert sign(child_shift) > 0
    targets = branch_lifts(state, k, "B8")
    assert targets == [80, 161, 242]
    blockers = {
        target: deletion_blockers(history, target, child_shift)
        for target in targets
    }
    assert all(blockers[target] for target in targets)

    # Exhaustive bounded check: lower levels terminate without this event, and
    # no k=5 event occurs before the 11-edge certificate above.
    for lower_k in range(2, 5):
        assert first_all_three_depth(lower_k) is None
    assert first_all_three_depth(5, depth_limit=11) == 11

    print(f"PASS: all {len(certificate)} chosen steps form a legal k=5 history")
    print("PASS: splitting residue 242 creates targets 80, 161, 242")
    print("      at common positive shift (-16,11)")
    for target in targets:
        earlier = ", ".join(
            f"({old.constant},{old.alpha_coeff})" for _, old in blockers[target]
        )
        print(f"      target {target}: earlier lower shift(s) {earlier}")
    print("VERDICT: the literal deletion rule makes all three alternatives eligible")
    print("PASS: no such event at k=2..4, or at k=5 before depth 11")
    print("SCOPE: this invalidates the claimed nonempty-minimum invariant, not termination")


if __name__ == "__main__":
    main()

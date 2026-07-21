#!/usr/bin/env python3
"""Bounded exact audit of the conditional strict-lift mechanism.

For a level-``k`` vector ``c``, let ``L c`` copy its value to all three
highest-digit lifts at level ``k+1``.  The concrete KL lift calculation is

    F_(k+1)(L c) - L(F_k c)
      = w_beta * (c_(selected old lift) - min(old fiber)) >= 0

on a branch row of type ``beta`` and is zero on a neutral row.  The
transport coefficient cancels identically.  Summed over all fine rows, the
coefficients of both ``w_2`` and ``w_8`` are the old total fiber excess

    E(c) = sum_r (sum_j c_(r,j) - 3 min_j c_(r,j)).

This standard-library checker keeps the three operator weights symbolic and
verifies those identities on deterministic positive integer vectors for
``k=2,...,8``.  It also checks the local target permutations, the global
type-2/type-8 target bijections, and the fact that fine transport is one full
cycle.

As a separate bounded regression, integer weights ``(1,1,1)`` demonstrate
the superadditive orbit-averaging lemma: a nonzero subeigenvector slack is
propagated around the full transport cycle, and averaging the first full
orbit of iterates produces a componentwise strict subeigenvector.

This is a bounded audit of the finite combinatorial core of an all-level
research proof.  It does not prove that a critical parameter is attained,
construct a positive critical eigenvector, quantify a dimension-free lift,
or prove strict monotonicity of the critical parameters.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias


TRANSPORT = 0
BRANCH_2 = 2
NEUTRAL = 5
BRANCH_8 = 8

# A symbolic value means tau * transport + w_2 * retarded + w_8 * advanced.
Symbolic: TypeAlias = tuple[int, int, int]
Vector: TypeAlias = tuple[int, ...]


@dataclass(frozen=True)
class System:
    k: int
    states: tuple[int, ...]
    transport: tuple[int, ...]
    branch: tuple[int, ...]
    target: tuple[int, ...]
    fibers: tuple[tuple[int, int, int], ...]

    @property
    def size(self) -> int:
        return len(self.states)

    @property
    def coarse_size(self) -> int:
        return self.size // 3


def build_system(k: int) -> System:
    """Construct the exact residue-index form of the level-k KL system."""

    if k < 2:
        raise ValueError("the finite KL system starts at level two")
    modulus = 3**k
    coarse_modulus = 3 ** (k - 1)
    states = tuple(range(2, modulus, 3))
    index = {state: position for position, state in enumerate(states)}
    transport: list[int] = []
    branches: list[int] = []
    targets: list[int] = []
    fibers: list[tuple[int, int, int]] = []

    for state in states:
        transport.append(index[(4 * state) % modulus])
        branch = state % 9
        branches.append(branch)
        if branch == BRANCH_2:
            coarse = ((4 * state - 2) // 3) % coarse_modulus
        elif branch == BRANCH_8:
            coarse = ((2 * state - 1) // 3) % coarse_modulus
        elif branch == NEUTRAL:
            targets.append(-1)
            fibers.append((-1, -1, -1))
            continue
        else:
            raise AssertionError("unexpected residue outside 2+3 Z/3^k Z")

        if coarse % 3 != 2:
            raise AssertionError("branch target left the KL state class")
        target = (coarse - 2) // 3
        targets.append(target)
        fibers.append(
            tuple(target + digit * (len(states) // 3) for digit in range(3))
        )

    return System(
        k=k,
        states=states,
        transport=tuple(transport),
        branch=tuple(branches),
        target=tuple(targets),
        fibers=tuple(fibers),
    )


def deterministic_vector(system: System, salt: int) -> Vector:
    """A reproducible positive integer vector with no random dependency."""

    word = (0x9E3779B9 ^ (system.k << 16) ^ salt) & 0xFFFFFFFF
    values: list[int] = []
    for position in range(system.size):
        word = (
            1_664_525 * word
            + 1_013_904_223
            + (position + 1) * (2 * salt + system.k + 1)
        ) & 0xFFFFFFFF
        mixed = word ^ (word >> 11) ^ ((position + 3) * (salt + 17))
        values.append(1 + mixed % 1009)
    return tuple(values)


def lift(vector: Vector) -> Vector:
    """Copy a coarse value to the three new highest-digit lifts."""

    return vector + vector + vector


def fiber_min(system: System, vector: Vector, row: int) -> int:
    if system.branch[row] == NEUTRAL:
        raise ValueError("neutral rows have no branch fiber")
    return min(vector[source] for source in system.fibers[row])


def apply_symbolic(system: System, vector: Vector) -> tuple[Symbolic, ...]:
    """Apply the KL operator while retaining independent weight symbols."""

    if len(vector) != system.size:
        raise ValueError("vector has the wrong state count")
    output: list[Symbolic] = []
    for row, branch in enumerate(system.branch):
        transported = vector[system.transport[row]]
        if branch == BRANCH_2:
            output.append((transported, fiber_min(system, vector, row), 0))
        elif branch == NEUTRAL:
            output.append((transported, 0, 0))
        elif branch == BRANCH_8:
            output.append((transported, 0, fiber_min(system, vector, row)))
        else:
            raise AssertionError("unknown branch")
    return tuple(output)


def apply_unit_weights(system: System, vector: Vector) -> Vector:
    """Apply the operator with exact integer weights tau=w_2=w_8=1."""

    symbolic = apply_symbolic(system, vector)
    return tuple(sum(coefficients) for coefficients in symbolic)


def symbolic_sub(left: Symbolic, right: Symbolic) -> Symbolic:
    return tuple(a - b for a, b in zip(left, right, strict=True))


def symbolic_add(left: Symbolic, right: Symbolic) -> Symbolic:
    return tuple(a + b for a, b in zip(left, right, strict=True))


def vector_add(left: Vector, right: Vector) -> Vector:
    return tuple(a + b for a, b in zip(left, right, strict=True))


def vector_sub(left: Vector, right: Vector) -> Vector:
    return tuple(a - b for a, b in zip(left, right, strict=True))


def verify_transport_cycle(system: System) -> None:
    """Check that transport is one cycle containing every state."""

    seen: set[int] = set()
    row = 0
    while row not in seen:
        seen.add(row)
        row = system.transport[row]
    if row != 0 or len(seen) != system.size:
        raise AssertionError(f"level-{system.k} transport is not one full cycle")
    if set(system.transport) != set(range(system.size)):
        raise AssertionError("transport is not a permutation")


def verify_branch_bijections(system: System) -> None:
    """Each branch class must target every coarse state exactly once."""

    expected = list(range(system.coarse_size))
    for branch in (BRANCH_2, BRANCH_8):
        targets = sorted(
            system.target[row]
            for row, row_branch in enumerate(system.branch)
            if row_branch == branch
        )
        if targets != expected:
            raise AssertionError(
                f"level-{system.k} branch-{branch} target map is not bijective"
            )


def total_fiber_excess(system: System, vector: Vector) -> int:
    """Return sum over fibers of sum(children)-3*min(children)."""

    excess = 0
    for target in range(system.coarse_size):
        values = tuple(
            vector[target + digit * system.coarse_size] for digit in range(3)
        )
        excess += sum(values) - 3 * min(values)
    return excess


def verify_one_lift(old: System, vector: Vector) -> int:
    """Verify every coefficient of the old-to-fine lift identity."""

    fine = build_system(old.k + 1)
    if fine.size != 3 * old.size:
        raise AssertionError("successive state counts are not in ratio three")
    lifted = lift(vector)
    old_output = apply_symbolic(old, vector)
    fine_output = apply_symbolic(fine, lifted)
    coefficient_totals = (0, 0, 0)

    for old_row, branch in enumerate(old.branch):
        fine_rows = tuple(old_row + digit * old.size for digit in range(3))
        if any(fine.branch[row] != branch for row in fine_rows):
            raise AssertionError("lifting changed the low branch digit")

        if branch == NEUTRAL:
            for row in fine_rows:
                difference = symbolic_sub(fine_output[row], old_output[old_row])
                if difference != (0, 0, 0):
                    raise AssertionError("neutral lift produced symbolic slack")
            continue

        old_sources = old.fibers[old_row]
        selected_sources: list[int] = []
        old_minimum = min(vector[source] for source in old_sources)
        for row in fine_rows:
            projected_sources = tuple(
                source % old.size for source in fine.fibers[row]
            )
            if len(set(projected_sources)) != 1:
                raise AssertionError("a new target fiber does not project to one old lift")
            lifted_fiber_values = tuple(lifted[source] for source in fine.fibers[row])
            if len(set(lifted_fiber_values)) != 1:
                raise AssertionError("a copied vector is not constant on a new fiber")
            selected = projected_sources[0]
            selected_sources.append(selected)
            gap = vector[selected] - old_minimum
            expected = (0, gap, 0) if branch == BRANCH_2 else (0, 0, gap)
            difference = symbolic_sub(fine_output[row], old_output[old_row])
            if difference != expected or min(difference) < 0:
                raise AssertionError("fine lift has the wrong symbolic branch slack")
            coefficient_totals = symbolic_add(coefficient_totals, difference)

        if sorted(selected_sources) != sorted(old_sources):
            raise AssertionError("fine target lifts do not permute the old fiber")

    excess = total_fiber_excess(old, vector)
    if excess <= 0:
        raise AssertionError("deterministic regression vector has zero fiber excess")
    if coefficient_totals != (0, excess, excess):
        raise AssertionError(
            "branch coefficient sums are not one copy of total fiber excess"
        )
    return excess


def verify_symbolic_superadditivity(system: System, left: Vector, right: Vector) -> None:
    """Check F(left+right) >= F(left)+F(right) for each weight symbol."""

    combined = apply_symbolic(system, vector_add(left, right))
    separate_left = apply_symbolic(system, left)
    separate_right = apply_symbolic(system, right)
    for total, first, second in zip(
        combined, separate_left, separate_right, strict=True
    ):
        difference = symbolic_sub(total, symbolic_add(first, second))
        if min(difference) < 0 or difference[TRANSPORT] != 0:
            raise AssertionError("symbolic operator is not superadditive")


def verify_lift_identities(first_k: int = 2, last_k: int = 8) -> None:
    vector_count = 0
    for k in range(first_k, last_k + 1):
        old = build_system(k)
        fine = build_system(k + 1)
        verify_transport_cycle(old)
        verify_transport_cycle(fine)
        verify_branch_bijections(old)
        verify_branch_bijections(fine)
        vectors = tuple(deterministic_vector(old, salt) for salt in (3, 17, 41))
        for vector in vectors:
            verify_one_lift(old, vector)
            vector_count += 1
        verify_symbolic_superadditivity(old, vectors[0], vectors[1])

    print(
        "PASS: symbolic strict-lift identity and nonnegative coefficient gaps "
        f"for {vector_count} deterministic vectors, k={first_k},...,{last_k}"
    )
    print(
        "PASS: type-2/type-8 target bijections, fine target permutations, "
        "and branch totals (0,E,E)"
    )
    print(
        "PASS: symbolic superadditivity and one-full-cycle transport through "
        f"fine level {last_k + 1}"
    )


def verify_orbit_averaging(first_k: int = 2, last_k: int = 7) -> None:
    """Bounded exact demonstration of the superadditive averaging argument."""

    for k in range(first_k, last_k + 1):
        system = build_system(k)
        verify_transport_cycle(system)
        start = tuple(1 for _ in range(system.size))
        first_image = apply_unit_weights(system, start)
        slack = vector_sub(first_image, start)
        if min(slack) < 0 or max(slack) == 0:
            raise AssertionError("unit-weight seed does not have nonzero slack")

        iterate = start
        slack_iterate = slack
        transport_slack = slack
        accumulated_slack = tuple(0 for _ in range(system.size))
        accumulated_transport_slack = tuple(0 for _ in range(system.size))
        orbit_average = tuple(0 for _ in range(system.size))

        for _ in range(system.size):
            orbit_average = vector_add(orbit_average, iterate)
            accumulated_slack = vector_add(accumulated_slack, slack_iterate)
            accumulated_transport_slack = vector_add(
                accumulated_transport_slack, transport_slack
            )
            if any(
                a < b for a, b in zip(slack_iterate, transport_slack, strict=True)
            ):
                raise AssertionError("branch terms violated the transport-only bound")
            next_iterate = apply_unit_weights(system, iterate)
            lower_bound = vector_add(start, accumulated_slack)
            if any(a < b for a, b in zip(next_iterate, lower_bound, strict=True)):
                raise AssertionError("iterated superadditive slack bound failed")
            iterate = next_iterate
            slack_iterate = apply_unit_weights(system, slack_iterate)
            transport_slack = tuple(
                transport_slack[system.transport[row]]
                for row in range(system.size)
            )

        if min(accumulated_transport_slack) <= 0:
            raise AssertionError("one transport cycle did not visit the initial slack")
        if any(
            a < b
            for a, b in zip(
                accumulated_slack, accumulated_transport_slack, strict=True
            )
        ):
            raise AssertionError("accumulated slack missed its transport lower bound")
        if min(accumulated_slack) <= 0:
            raise AssertionError("a full transport orbit did not spread the slack")
        final_gap = vector_sub(iterate, start)
        if any(a < b for a, b in zip(final_gap, accumulated_slack, strict=True)):
            raise AssertionError("full-orbit iterate gap is too small")

        averaged_image = apply_unit_weights(system, orbit_average)
        averaged_gap = vector_sub(averaged_image, orbit_average)
        if min(averaged_gap) <= 0:
            raise AssertionError("orbit averaging did not make the slack strict")
        if any(a < b for a, b in zip(averaged_gap, final_gap, strict=True)):
            raise AssertionError("orbit-average gap missed the telescoping bound")

    print(
        "PASS: exact unit-weight superadditive orbit averaging turns one "
        f"nonzero slack into a strict slack for k={first_k},...,{last_k}"
    )


def main() -> None:
    verify_lift_identities()
    verify_orbit_averaging()
    print(
        "CONCLUSION: bounded exact audit supports the conditional strict-lift "
        "mechanism; attainment and all-level strict monotonicity remain outside "
        "this checker"
    )


if __name__ == "__main__":
    main()

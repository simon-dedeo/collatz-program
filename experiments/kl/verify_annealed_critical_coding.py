#!/usr/bin/env python3
"""Exact finite audit of the critical coding of the lambda=2 annealed law.

The column-stochastic annealed KL operator at lambda=2 is the random IFS on
``Y = 2 + 3 Z_3`` with maps

    g0(x) = x/4,             probability 1/4,
    g2(x) = (3x+2)/4,       probability 1/4,
    g8(x) = (3x+1)/2,       probability 1/2.

Resolving the initial string of ``g0`` maps gives one contracting block for
every integer ``e>=1``:

    p_e = 2^-e,
    H_e(x) = (3x+b_e)/2^e,  b_e = 1 (e odd), 2 (e even).

Every block consumes exactly one ternary digit.  If ``r_j`` is the stationary
law modulo ``3^(j+1)`` and

    Q_j = 3^j sum_x r_j(x)^2,

then separating equal and unequal first blocks gives the exact renewal

    Q_j - Q_(j-1) = (2/7) N r_(j-1)^T P_j r_(j-1),
    N = 3^(j-1),

where ``P_j`` is a symmetric doubly stochastic alignment kernel.  The factor
``2/7`` is the Haar-uniform benchmark increment, not a proved limiting slope.

This standard-library verifier checks induced affine instances through
``e=82``, the exact infinite geometric-series constants, the level-2 and
level-3 Perron records, and the alignment-kernel/renewal identity through
depth four.  It checks the sparse product-measure finite core through depth
256, an exact expanding direction for the normalized annealed detail-shell
operator, the sharp ternary Pearson/minimum-defect factorization, and an
exhaustive rational grid of probability fibers through denominator 60.  The
displayed all-level product conclusion is part of the audited research proof,
not an exhaustive computation.

The all-level affine and row-sum proofs are short quotient arguments recorded
in ``docs/notes/annealed-critical-coding.md``.  The missing result is a
local-limit estimate for the special affine alignment kernels; this script
does not claim that estimate or an asymptotic formula for ``Q_j``.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from typing import TypeAlias


Affine: TypeAlias = tuple[Fraction, Fraction]
Quadratic: TypeAlias = tuple[Fraction, Fraction]

FIRST_FREE_DIGIT = {
    2: Fraction(8, 21),
    5: Fraction(2, 21),
    8: Fraction(11, 21),
}
LEVEL_3_NUMERATORS = (9632, 4316, 5240, 6392, 2408, 17246, 17264, 1598, 23285)
LEVEL_3_DENOMINATOR = 87381
EXPECTED_Q = {
    1: Fraction(9, 7),
    2: Fraction(106203, 67963),
    3: Fraction(3975642477956869005, 2159281421340253987),
    4: Fraction(
        11345545190566365739217637538744781170044234926750959695731787,
        5350418720142111510029542161258891403960563152740894082816203,
    ),
}
ANNEALED_TRANSITIONS = (
    (Fraction(1, 4), 1, 0, 4),
    (Fraction(1, 4), 3, 2, 4),
    (Fraction(1, 2), 3, 1, 2),
)


def compose(outer: Affine, inner: Affine) -> Affine:
    """Return ``outer(inner(x))`` for affine rational maps."""

    outer_slope, outer_offset = outer
    inner_slope, inner_offset = inner
    return (
        outer_slope * inner_slope,
        outer_slope * inner_offset + outer_offset,
    )


def affine_power(function: Affine, exponent: int) -> Affine:
    result = (Fraction(1), Fraction(0))
    for _ in range(exponent):
        result = compose(function, result)
    return result


def block_offset(e: int) -> int:
    if e < 1:
        raise ValueError("block lengths are positive")
    return 1 if e % 2 else 2


def block_map(e: int) -> Affine:
    denominator = 2**e
    return Fraction(3, denominator), Fraction(block_offset(e), denominator)


def verify_induced_blocks(last_transport_run: int = 40) -> None:
    g0 = (Fraction(1, 4), Fraction(0))
    g2 = (Fraction(3, 4), Fraction(1, 2))
    g8 = (Fraction(3, 2), Fraction(1, 2))

    for run in range(last_transport_run + 1):
        transport = affine_power(g0, run)
        odd_e = 2 * run + 1
        even_e = 2 * run + 2
        if compose(transport, g8) != block_map(odd_e):
            raise AssertionError(f"odd induced block failed at run={run}")
        if compose(transport, g2) != block_map(even_e):
            raise AssertionError(f"even induced block failed at run={run}")

    # Exact infinite geometric-series evaluations.
    total_probability = Fraction(1, 2) / (1 - Fraction(1, 2))
    mean_block_length = Fraction(1, 2) / (1 - Fraction(1, 2)) ** 2
    collision_probability = Fraction(1, 4) / (1 - Fraction(1, 4))
    if total_probability != 1 or mean_block_length != 2:
        raise AssertionError("block probability or mean is wrong")
    if collision_probability != Fraction(1, 3):
        raise AssertionError("Renyi-2 block probability is not critical")
    for q in range(2, 9):
        moment = Fraction(1, 2**q) / (1 - Fraction(1, 2**q))
        if moment != Fraction(1, 2**q - 1):
            raise AssertionError(f"Renyi moment identity failed at q={q}")

    print(
        "PASS: induced-block affine regressions through "
        f"e={2 * last_transport_run + 2} for "
        "p_e=2^-e, H_e(x)=(3x+b_e)/2^e"
    )
    print(
        "PASS: E[E]=2, Shannon block entropy=2 log(2)=log(4), "
        "sum_e p_e^2=1/3"
    )


def periodic_weight(residue: int, period: int) -> Fraction:
    """Mass of positive ``e == residue (mod period)``, with 1<=residue<=period."""

    if not 1 <= residue <= period:
        raise ValueError("canonical positive residue required")
    return Fraction(1, 2**residue) / (1 - Fraction(1, 2**period))


def verify_first_free_digit() -> None:
    if pow(2, 6, 9) != 1:
        raise AssertionError("six is not a period modulo nine")
    masses: defaultdict[int, Fraction] = defaultdict(Fraction)
    for e in range(1, 7):
        modulus = 9
        image = (
            (6 + block_offset(e))
            * pow(pow(2, e, modulus), -1, modulus)
        ) % modulus
        masses[image] += periodic_weight(e, 6)

    if dict(masses) != FIRST_FREE_DIGIT:
        raise AssertionError(f"wrong first free digit law: {dict(masses)}")
    squared_mass = sum(value * value for value in masses.values())
    if squared_mass != Fraction(3, 7):
        raise AssertionError("wrong first-digit collision probability")
    cross_mass = squared_mass - Fraction(1, 3)
    if cross_mass != Fraction(2, 21):
        raise AssertionError("wrong unequal-block first-digit mass")

    print("PASS: first free digit law on residues (2,5,8) is (8,2,11)/21")
    print(
        "PASS: unequal-block same-digit mass=2/21; "
        "Haar-uniform benchmark increment=2/7"
    )


def image_distribution(x: int, depth: int) -> dict[int, Fraction]:
    """Law of ``H_E(x) mod 3^(depth+1)`` with ``x mod 3^depth`` fixed.

    The order of two modulo ``3^(depth+1)`` is ``2*3^depth``.  Parity, and
    hence ``b_e``, is preserved by this even period, so one exact finite sum
    represents all positive block lengths.
    """

    if depth < 1:
        raise ValueError("depth must be positive")
    input_modulus = 3**depth
    output_modulus = 3 ** (depth + 1)
    if x % 3 != 2 or not 0 <= x < input_modulus:
        raise ValueError("x is not the canonical representative in 2+3 Z_3")

    period = 2 * 3**depth
    if period % 2 or pow(2, period, output_modulus) != 1:
        raise AssertionError("claimed block-map period is invalid")
    distribution: defaultdict[int, Fraction] = defaultdict(Fraction)
    for e in range(1, period + 1):
        inverse = pow(pow(2, e, output_modulus), -1, output_modulus)
        image = ((3 * x + block_offset(e)) * inverse) % output_modulus
        if image % 3 != 2:
            raise AssertionError("an induced map left 2+3 Z_3")
        distribution[image] += periodic_weight(e, period)
    if sum(distribution.values()) != 1:
        raise AssertionError("finite periodic block law is not normalized")
    return dict(distribution)


def apply_annealed_law(
    law: dict[int, Fraction], modulus: int
) -> dict[int, Fraction]:
    """Apply the original three-map annealed IFS to a finite quotient law."""

    output = {state: Fraction(0) for state in range(2, modulus, 3)}
    if set(law) != set(output):
        raise ValueError("law has the wrong finite quotient state space")
    for source, mass in law.items():
        for probability, slope, offset, denominator in ANNEALED_TRANSITIONS:
            image = (
                (slope * source + offset)
                * pow(denominator, -1, modulus)
            ) % modulus
            output[image] += probability * mass
    return output


def next_marginal(
    previous: dict[int, Fraction], depth: int
) -> tuple[dict[int, Fraction], dict[int, dict[int, Fraction]]]:
    expected_states = tuple(range(2, 3**depth, 3))
    if tuple(sorted(previous)) != expected_states:
        raise ValueError(f"wrong parent state space at depth {depth}")

    image_laws = {x: image_distribution(x, depth) for x in previous}
    result: defaultdict[int, Fraction] = defaultdict(Fraction)
    for x, parent_mass in previous.items():
        for image, block_mass in image_laws[x].items():
            result[image] += parent_mass * block_mass

    if sum(result.values()) != 1:
        raise AssertionError("next marginal is not normalized")
    if tuple(sorted(result)) != tuple(range(2, 3 ** (depth + 1), 3)):
        raise AssertionError("next marginal does not have full support")
    projected: defaultdict[int, Fraction] = defaultdict(Fraction)
    for image, mass in result.items():
        projected[image % (3**depth)] += mass
    if dict(projected) != previous:
        raise AssertionError("stationary marginals are not projective")
    if apply_annealed_law(dict(result), 3 ** (depth + 1)) != dict(result):
        raise AssertionError("induced marginal is not fixed by the original IFS")
    return dict(result), image_laws


def dot(left: dict[int, Fraction], right: dict[int, Fraction]) -> Fraction:
    if len(left) > len(right):
        left, right = right, left
    return sum(value * right.get(key, 0) for key, value in left.items())


def alignment_kernel(
    states: tuple[int, ...],
    image_laws: dict[int, dict[int, Fraction]],
) -> tuple[tuple[Fraction, ...], ...]:
    """Return the unequal-first-block collision kernel ``B_j``.

    The full dot product includes identical block lengths.  Such a pair
    collides exactly when its two parent states agree, and its total mass is
    ``sum_e p_e^2=1/3``; subtracting that diagonal gives ``B_j``.
    """

    rows: list[tuple[Fraction, ...]] = []
    for x in states:
        row = tuple(
            dot(image_laws[x], image_laws[y])
            - (Fraction(1, 3) if x == y else 0)
            for y in states
        )
        if any(entry < 0 for entry in row):
            raise AssertionError("alignment kernel has a negative entry")
        if sum(row) != Fraction(2, 21):
            raise AssertionError("alignment-kernel row sum is not 2/21")
        rows.append(row)

    matrix = tuple(rows)
    if matrix != tuple(zip(*matrix)):
        raise AssertionError("alignment kernel is not symmetric")
    for column in zip(*matrix):
        if sum(column) != Fraction(2, 21):
            raise AssertionError("alignment-kernel column sum is not 2/21")
    return matrix


def collision(marginal: dict[int, Fraction]) -> Fraction:
    return sum(mass * mass for mass in marginal.values())


def verify_collision_renewal(last_depth: int = 4) -> None:
    marginal = {2: Fraction(1)}
    previous_q = Fraction(1)
    for depth in range(1, last_depth + 1):
        states = tuple(sorted(marginal))
        next_law, image_laws = next_marginal(marginal, depth)
        kernel = alignment_kernel(states, image_laws)

        off_diagonal = sum(
            marginal[x] * kernel[row][column] * marginal[y]
            for row, x in enumerate(states)
            for column, y in enumerate(states)
        )
        current_collision = collision(next_law)
        if current_collision != Fraction(1, 3) * collision(marginal) + off_diagonal:
            raise AssertionError(f"collision renewal failed at depth {depth}")

        current_q = 3**depth * current_collision
        increment = current_q - previous_q
        normalized_kernel_pairing = (
            len(states)
            * Fraction(21, 2)
            * off_diagonal
        )
        if increment != Fraction(2, 7) * normalized_kernel_pairing:
            raise AssertionError(f"stochastic-kernel formula failed at depth {depth}")
        if not 0 <= increment <= Fraction(2, 7) * previous_q:
            raise AssertionError(f"stochasticity bound failed at depth {depth}")
        if depth in EXPECTED_Q and current_q != EXPECTED_Q[depth]:
            raise AssertionError(f"Q regression changed at depth {depth}")

        if depth == 1 and next_law != FIRST_FREE_DIGIT:
            raise AssertionError("depth-one marginal changed")
        if depth == 2:
            expected = tuple(
                Fraction(numerator, LEVEL_3_DENOMINATOR)
                for numerator in LEVEL_3_NUMERATORS
            )
            if tuple(next_law[x] for x in sorted(next_law)) != expected:
                raise AssertionError("depth-two marginal changed")
            if increment != Fraction(18822, 67963):
                raise AssertionError("depth-two Q increment changed")

        print(
            f"PASS: depth {depth}: Q={float(current_q):.12f}, "
            f"increment={float(increment):.12f}, "
            f"Haar multiplier={float(normalized_kernel_pairing):.12f}"
        )
        marginal = next_law
        previous_q = current_q


def qadd(left: Quadratic, right: Quadratic) -> Quadratic:
    return left[0] + right[0], left[1] + right[1]


def qmul(left: Quadratic, right: Quadratic) -> Quadratic:
    # Pairs encode a+b*sqrt(2).
    return (
        left[0] * right[0] + 2 * left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def qpositive(value: Quadratic) -> bool:
    """Decide positivity of ``a+b*sqrt(2)`` using exact rational squares."""

    rational, radical = value
    if radical == 0:
        return rational > 0
    if radical > 0:
        return rational >= 0 or 2 * radical**2 > rational**2
    return rational > 0 and rational**2 > 2 * radical**2


def verify_global_energy_no_go(last_depth: int = 256) -> None:
    """Check the sparse product-law obstruction to a local-Pearson inference."""

    active_digit = (
        (Fraction(1, 3), Fraction(-1, 6)),
        (Fraction(1, 3), Fraction(-1, 6)),
        (Fraction(1, 3), Fraction(1, 3)),
    )
    total = (Fraction(0), Fraction(0))
    squared = (Fraction(0), Fraction(0))
    for probability in active_digit:
        total = qadd(total, probability)
        squared = qadd(squared, qmul(probability, probability))
    pearson = qadd(
        (3 * squared[0], 3 * squared[1]),
        (Fraction(-1), Fraction(0)),
    )
    if total != (Fraction(1), Fraction(0)):
        raise AssertionError("quadratic active digit is not normalized")
    if not all(qpositive(probability) for probability in active_digit):
        raise AssertionError("quadratic active digit is not positive")
    if squared != (Fraction(2, 3), Fraction(0)):
        raise AssertionError("quadratic active digit has wrong collision")
    if pearson != (Fraction(1), Fraction(0)):
        raise AssertionError("quadratic active digit has Pearson energy != 1")

    active_count = 0
    for depth in range(1, last_depth + 1):
        if depth & (depth - 1) == 0:
            active_count += 1
            local_pearson = 1
        else:
            local_pearson = 0
        global_q = 2**active_count
        if not depth <= global_q <= 2 * depth:
            raise AssertionError("sparse product global energy is not Theta(depth)")
        if depth & (depth - 1) == 0 and local_pearson != 1:
            raise AssertionError("active local Pearson energy changed")

    print(
        f"PASS: sparse product finite core through depth {last_depth} has linear Q_j "
        "but Pearson energy 1 at each tested power-of-two depth"
    )


def verify_terminal_pearson_bounds(last_denominator: int = 60) -> None:
    """Check the sharp polynomial identities and an exact probability grid."""

    # Coefficient order is (a^2, a*x, x^2).  For deviations
    # (-a,x,a-x), chi=3*sum(deviation^2).
    chi_coefficients = (Fraction(6), Fraction(-6), Fraction(6))
    lower_gap = (
        chi_coefficients[0] - Fraction(9, 2),
        chi_coefficients[1],
        chi_coefficients[2],
    )
    six_shifted_square = (Fraction(3, 2), Fraction(-6), Fraction(6))
    upper_gap = (
        Fraction(18) - chi_coefficients[0],
        -chi_coefficients[1],
        -chi_coefficients[2],
    )
    six_factored_interval = (Fraction(12), Fraction(6), Fraction(-6))
    if lower_gap != six_shifted_square:
        raise AssertionError("lower Pearson factorization failed")
    if upper_gap != six_factored_interval:
        raise AssertionError("upper Pearson factorization failed")

    for denominator in range(1, last_denominator + 1):
        for first in range(denominator + 1):
            for second in range(denominator - first + 1):
                third = denominator - first - second
                probabilities = tuple(
                    Fraction(value, denominator)
                    for value in (first, second, third)
                )
                defect = Fraction(1, 3) - min(probabilities)
                pearson = 3 * sum(
                    (probability - Fraction(1, 3)) ** 2
                    for probability in probabilities
                )
                if not (
                    Fraction(9, 2) * defect**2
                    <= pearson
                    <= 18 * defect**2
                    <= 6 * defect
                ):
                    raise AssertionError(
                        "terminal Pearson bound failed for "
                        f"{probabilities}"
                    )
    print(
        "PASS: sharp terminal bounds "
        "(9/2)a^2<=chi(p)<=18a^2<=6a"
    )


def trace_level_three(vector: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    if len(vector) != 9:
        raise ValueError("level-three vectors have nine coordinates")
    return tuple(
        vector[index] + vector[index + 3] + vector[index + 6]
        for index in range(3)
    )


def lift_level_two(vector: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    if len(vector) != 3:
        raise ValueError("level-two vectors have three coordinates")
    return tuple(value / 3 for _ in range(3) for value in vector)


def apply_level_three_annealed(
    vector: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    """Apply the lambda=2 annealed matrix, built columnwise from its IFS."""

    states = tuple(range(2, 27, 3))
    if len(vector) != len(states):
        raise ValueError("level-three vector has the wrong dimension")
    output = apply_annealed_law(dict(zip(states, vector)), 27)
    return tuple(output[state] for state in states)


def transport_level_three(
    vector: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    states = tuple(range(2, 27, 3))
    coordinate = {state: index for index, state in enumerate(states)}
    return tuple(vector[coordinate[(4 * state) % 27]] for state in states)


def verify_detail_shell_expansion() -> None:
    """Refute uniform scalar normalized L2 contraction at the first fine level."""

    for coarse_index in range(3):
        for first_lift, second_lift in ((0, 1), (1, 2)):
            basis = [Fraction(0) for _ in range(9)]
            basis[coarse_index + 3 * first_lift] = 1
            basis[coarse_index + 3 * second_lift] = -1
            basis_vector = tuple(basis)
            if trace_level_three(basis_vector) != (0, 0, 0):
                raise AssertionError("claimed detail basis is not trace zero")
            if apply_level_three_annealed(basis_vector) != tuple(
                value / 4 for value in transport_level_three(basis_vector)
            ):
                raise AssertionError("A restricted to ker(T) is not U/4")

    transport_test = tuple(Fraction(index) for index in range(9))
    transported = transport_test
    for _ in range(9):
        transported = transport_level_three(transported)
    if transported != transport_test:
        raise AssertionError("level-three transport does not have order nine")

    coarse = (Fraction(1), Fraction(1), Fraction(-2))
    lifted = lift_level_two(coarse)
    annealed = apply_level_three_annealed(lifted)
    coarse_trace = trace_level_three(annealed)
    uniform_trace = lift_level_two(coarse_trace)
    detail_source = tuple(
        value - coarse_value
        for value, coarse_value in zip(annealed, uniform_trace)
    )
    expected_source = tuple(
        Fraction(value, 4) for value in (1, 0, 2, 1, 0, 2, -2, 0, -4)
    )
    if detail_source != expected_source:
        raise AssertionError("Pi A L z regression changed")

    detail = tuple(
        Fraction(value, 1387)
        for value in (504, -258, 629, 528, 126, 725, -1032, 132, -1354)
    )
    transported = transport_level_three(detail)
    if tuple(
        value - transported_value / 4
        for value, transported_value in zip(detail, transported)
    ) != detail_source:
        raise AssertionError("(I-U/4) K_detail z = Pi A L z failed")
    if trace_level_three(detail) != (0, 0, 0):
        raise AssertionError("detail output is not trace zero")

    input_norm = sum(value * value for value in coarse)
    output_norm = sum(value * value for value in detail)
    normalized_ratio = 3 * output_norm / input_norm
    if input_norm != 6 or output_norm != Fraction(3210, 1387):
        raise AssertionError("detail-shell squared-norm regression changed")
    if normalized_ratio != Fraction(1605, 1387) or normalized_ratio <= 1:
        raise AssertionError("exact normalized detail energy is not expanding")
    print(
        "PASS: normalized annealed squared-L2 detail energy ratio="
        "1605/1387 on z=(1,1,-2) at k=3"
    )


def main() -> None:
    verify_induced_blocks()
    verify_first_free_digit()
    verify_collision_renewal()
    verify_global_energy_no_go()
    verify_terminal_pearson_bounds()
    verify_detail_shell_expansion()
    print(
        "CONCLUSION: exact finite core passes for the audited Renyi-2-critical "
        "coding; a pair-carry local-limit theorem is still required"
    )


if __name__ == "__main__":
    main()

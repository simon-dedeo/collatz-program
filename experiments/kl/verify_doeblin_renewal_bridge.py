#!/usr/bin/env python3
"""Exact bounded audit of the renewal/Doeblin dictionary.

For a probability vector ``x`` on a cyclic group of order ``3*n``, let ``U``
translate by the order-three subgroup generator ``n``.  The normalized KL
terminal excess is exactly

    epsilon(x) = 1 - sum_r min_{d=0,1,2} (U^d x)_r,

the complementary three-way Doeblin (common-overlap) coefficient of the
three translated laws.

The general-lambda critical renewal has the form

    c = K_tau J_a q,
    K_tau = (1-tau) (I-tau*S)^(-1),

where ``S x[p] = x[4*p+2]`` is a cyclic permutation and ``J_a`` mixes the
two mass-preserving branch injections.  This checker verifies exactly that
``S`` commutes with ``U``, that the two injections intertwine ``U`` with
the first and second powers of the coarse translation, and consequently

    rho({U^d K_tau J_a q}) <= rho({U^d J_a q}) = epsilon(q).

On a fine quotient of order ``3*n``, the checker also verifies the sharp
unconstrained translated-family curve

    rho({U^d K_tau x}) <= gamma_n rho({U^d x}),
    gamma_n = 1 - 3*tau^(2*n)/(1+tau^n+tau^(2*n)).

Equality holds for every prescribed input defect after mixing a point mass
with a translation-invariant law.  Thus the generic strict gain is only
exponentially small in ``n``.  This is a finite exact core for the all-level
algebraic proof; it does not prove the conjectural quadratic improvement
needed for the KL endpoint.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence


Vector = tuple[Fraction, ...]


def normalize(values: Iterable[int]) -> Vector:
    vector = tuple(Fraction(value) for value in values)
    if not vector or min(vector) <= 0:
        raise ValueError("normalization requires a nonempty positive vector")
    total = sum(vector)
    return tuple(value / total for value in vector)


def translate(vector: Vector, shift: int) -> Vector:
    size = len(vector)
    return tuple(vector[(position + shift) % size] for position in range(size))


def transport(vector: Vector) -> Vector:
    """Apply the KL transport permutation in residue-index coordinates."""

    size = len(vector)
    return tuple(vector[(4 * position + 2) % size] for position in range(size))


def inject_two(vector: Vector) -> Vector:
    """Mass-preserving injection into rows m=2 (mod 9)."""

    size = len(vector)
    output = [Fraction(0) for _ in range(3 * size)]
    for position in range(size):
        output[3 * position] = vector[(4 * position) % size]
    return tuple(output)


def inject_eight(vector: Vector) -> Vector:
    """Mass-preserving injection into rows m=8 (mod 9)."""

    size = len(vector)
    output = [Fraction(0) for _ in range(3 * size)]
    for position in range(size):
        output[3 * position + 2] = vector[(2 * position + 1) % size]
    return tuple(output)


def add_scaled(
    first: Vector, first_weight: Fraction, second: Vector, second_weight: Fraction
) -> Vector:
    if len(first) != len(second):
        raise ValueError("vector sizes differ")
    return tuple(
        first_weight * left + second_weight * right
        for left, right in zip(first, second, strict=True)
    )


def branch_mixture(vector: Vector, two_mass: Fraction) -> Vector:
    if not 0 <= two_mass <= 1:
        raise ValueError("branch mass is outside the probability interval")
    return add_scaled(
        inject_two(vector), two_mass, inject_eight(vector), 1 - two_mass
    )


def green_channel(vector: Vector, tau: Fraction) -> Vector:
    """Apply the exact finite-quotient geometric transport resolvent."""

    if not 0 < tau < 1:
        raise ValueError("tau must lie strictly between zero and one")
    size = len(vector)
    accumulated = [Fraction(0) for _ in range(size)]
    iterate = vector
    weight = Fraction(1)
    for _ in range(size):
        for position, value in enumerate(iterate):
            accumulated[position] += weight * value
        iterate = transport(iterate)
        weight *= tau
    if iterate != vector:
        raise AssertionError("transport did not close after the quotient size")
    factor = (1 - tau) / (1 - tau**size)
    output = tuple(factor * value for value in accumulated)
    if sum(output) != sum(vector):
        raise AssertionError("the Green channel did not preserve mass")
    return output


def common_overlap(family: Sequence[Vector]) -> Fraction:
    if not family or any(len(vector) != len(family[0]) for vector in family):
        raise ValueError("overlap requires a nonempty equal-sized family")
    return sum(
        min(vector[position] for vector in family)
        for position in range(len(family[0]))
    )


def translated_family(vector: Vector) -> tuple[Vector, Vector, Vector]:
    if len(vector) % 3 != 0:
        raise ValueError("translated family requires order divisible by three")
    generator = len(vector) // 3
    return tuple(translate(vector, digit * generator) for digit in range(3))


def complementary_doeblin(vector: Vector) -> Fraction:
    if sum(vector) != 1:
        raise ValueError("Doeblin input must be a probability vector")
    return 1 - common_overlap(translated_family(vector))


def terminal_excess(vector: Vector) -> Fraction:
    """Return 1-3 times the total fiber minimum."""

    if len(vector) % 3 != 0 or sum(vector) != 1:
        raise ValueError("terminal excess requires a ternary probability vector")
    third = len(vector) // 3
    minimum_sum = sum(
        min(vector[index + digit * third] for digit in range(3))
        for index in range(third)
    )
    return 1 - 3 * minimum_sum


def minimum_profile(vector: Vector) -> Vector:
    if len(vector) % 3 != 0:
        raise ValueError("minimum profile requires ternary length")
    third = len(vector) // 3
    return tuple(
        min(vector[index + digit * third] for digit in range(3))
        for index in range(third)
    )


def uniform_lift(vector: Vector) -> Vector:
    return vector + vector + vector


def verify_common_component(vector: Vector) -> None:
    """Check that the translated common part is the lifted fiber minimum."""

    family = translated_family(vector)
    common = tuple(
        min(member[position] for member in family)
        for position in range(len(vector))
    )
    profile = minimum_profile(vector)
    if common != uniform_lift(profile):
        raise AssertionError("translated common component is not the lifted minimum")
    overlap = sum(common)
    if overlap != 1 - terminal_excess(vector):
        raise AssertionError("common-component mass has the wrong normalization")
    normalized_profile = tuple(value / sum(profile) for value in profile)
    normalized_common = tuple(value / overlap for value in common)
    expected = tuple(value / 3 for value in uniform_lift(normalized_profile))
    if normalized_common != expected:
        raise AssertionError("normalized common component has the wrong quotient law")


def deterministic_probability(level: int, salt: int) -> Vector:
    size = 3 ** (level - 2)
    values = (
        1 + ((position + 1) * (17 + 2 * salt) + 11 * level + salt**2) % 97
        for position in range(size)
    )
    return normalize(values)


def verify_one(
    level: int, vector: Vector, tau: Fraction, two_mass: Fraction
) -> tuple[Fraction, Fraction]:
    coarse_size = len(vector)
    fine_size = 3 * coarse_size
    fine_generator = fine_size // 3
    coarse_generator = coarse_size // 3

    if level < 3 or coarse_size != 3 ** (level - 2):
        raise AssertionError("unexpected level/vector pairing")
    if sum(inject_two(vector)) != 1 or sum(inject_eight(vector)) != 1:
        raise AssertionError("branch injection failed to preserve mass")

    # The fine high-digit translation acts as U and U^2 on the two branch
    # injections.  These are the carry permutations behind the dictionary.
    for digit in range(3):
        if translate(inject_two(vector), digit * fine_generator) != inject_two(
            translate(vector, digit * coarse_generator)
        ):
            raise AssertionError("type-two injection has the wrong intertwining")
        if translate(inject_eight(vector), digit * fine_generator) != inject_eight(
            translate(vector, ((2 * digit) % 3) * coarse_generator)
        ):
            raise AssertionError("type-eight injection has the wrong intertwining")

    seed = branch_mixture(vector, two_mass)
    seed_family = translated_family(seed)
    for digit, member in enumerate(seed_family):
        expected = add_scaled(
            inject_two(translate(vector, digit * coarse_generator)),
            two_mass,
            inject_eight(
                translate(vector, ((2 * digit) % 3) * coarse_generator)
            ),
            1 - two_mass,
        )
        if member != expected:
            raise AssertionError("mixed branch family has the wrong translate law")

    input_defect = 1 - common_overlap(seed_family)
    if input_defect != terminal_excess(vector):
        raise AssertionError("branch injection changed the translated defect")

    output = green_channel(seed, tau)
    output_family = translated_family(output)
    for digit, member in enumerate(output_family):
        translated_seed = seed_family[digit]
        if member != green_channel(translated_seed, tau):
            raise AssertionError("Green channel failed to commute with translation")
    output_defect = 1 - common_overlap(output_family)
    if output_defect != terminal_excess(output):
        raise AssertionError("output Doeblin defect is not terminal excess")
    eta = 3 * tau ** (2 * coarse_size) / (
        1 + tau**coarse_size + tau ** (2 * coarse_size)
    )
    gamma = 1 - eta
    if output_defect > gamma * input_defect:
        raise AssertionError("sharp translated-family contraction failed")

    verify_common_component(vector)
    verify_common_component(output)
    return input_defect, output_defect


def verify_sharp_curve(level: int, tau: Fraction) -> None:
    """Check the exact generic curve and its equality calibration."""

    fine_size = 3 ** (level - 1)
    orbit_size = fine_size // 3

    # On the KL residue-index cycle, high-digit translation is S^(2*n).
    for position in range(fine_size):
        image = position
        for _ in range(2 * orbit_size):
            image = (4 * image + 2) % fine_size
        if image != (position + orbit_size) % fine_size:
            raise AssertionError("high-digit translation is not S^(2*n)")

    point = tuple(
        Fraction(position == 0) for position in range(fine_size)
    )
    kernel_column = green_channel(point, tau)
    eta = common_overlap(translated_family(kernel_column))
    expected_eta = 3 * tau ** (2 * orbit_size) / (
        1 + tau**orbit_size + tau ** (2 * orbit_size)
    )
    if eta != expected_eta:
        raise AssertionError("geometric-kernel common overlap is wrong")
    gamma = 1 - eta

    for salt in (5, 23):
        vector = normalize(
            1
            + ((position + 3) * (29 + salt) + 7 * position**2 + salt**2) % 101
            for position in range(fine_size)
        )
        if complementary_doeblin(green_channel(vector, tau)) > (
            gamma * complementary_doeblin(vector)
        ):
            raise AssertionError("generic translated-family bound failed")

    # These mixtures attain the curve at every t; the three translated point
    # masses are disjoint, while the uniform component is U-invariant.
    uniform = Fraction(1, fine_size)
    for defect in (Fraction(1, 11), Fraction(2, 5), Fraction(1)):
        vector = tuple(
            (1 - defect) * uniform + defect * value for value in point
        )
        if complementary_doeblin(vector) != defect:
            raise AssertionError("sharpness input has the wrong defect")
        output = green_channel(vector, tau)
        if complementary_doeblin(output) != gamma * defect:
            raise AssertionError("sharpness family does not attain gamma*t")


def main() -> None:
    cases = 0
    strict_cases = 0
    for level in range(3, 7):
        for salt in (2, 19):
            vector = deterministic_probability(level, salt)
            for tau, two_mass in (
                (Fraction(1, 4), Fraction(1, 3)),
                (Fraction(4, 13), Fraction(7, 11)),
            ):
                input_defect, output_defect = verify_one(
                    level, vector, tau, two_mass
                )
                cases += 1
                strict_cases += output_defect < input_defect

    curve_cases = 0
    for level in range(3, 7):
        for tau in (Fraction(1, 4), Fraction(4, 13)):
            verify_sharp_curve(level, tau)
            curve_cases += 1

    if strict_cases != cases:
        raise AssertionError("bounded regression unexpectedly lost strict contraction")
    print(
        "PASS: exact translated-overlap/terminal-excess identity, branch "
        f"intertwining, and renewal data processing in {cases} bounded cases"
    )
    print(
        "PASS: normalized common component equals the uniform lift of the "
        "normalized fiber-minimum profile"
    )
    print(
        "PASS: sharp generic curve gamma_n*t, with "
        "gamma_n=1-3*tau^(2n)/(1+tau^n+tau^(2n)), in "
        f"{curve_cases} bounded quotient/parameter cases"
    )
    print(
        "SCOPE: the generic strict gain is exponentially small in quotient "
        "size; no quadratic constrained curve or KL endpoint theorem is asserted"
    )


if __name__ == "__main__":
    main()

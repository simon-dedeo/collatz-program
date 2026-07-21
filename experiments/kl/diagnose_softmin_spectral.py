#!/usr/bin/env python3
"""Fixed-temperature structural gates and floating KL spectral diagnostic.

At level ``k``, replace every ternary fiber minimum in the KL operator by

    M_p(z) = ((z_0**p + z_1**p + z_2**p) / 3)**(1/p),  p < 0.

The script applies normalized nonlinear power iteration and stops only when
the floating Collatz--Wielandt bracket

    min_i F(c)_i / c_i <= rho(F) <= max_i F(c)_i / c_i

has the requested logarithmic width.  The positive transport cycle supplies
the positive Perron eigenpair needed for this finite-dimensional comparison.

The script first runs small exact-rational gates for the harmonic-mean
projection inequality, its tangent dual, and finite-horizon annealed identity.
The spectral computations are IEEE-754 diagnostics.  Their displayed brackets
measure iteration convergence but are not interval-arithmetic or exact
certificates.  In particular, the script does not prove convergence as ``k``
tends to infinity.  Its default run tests the fixed-temperature annealing
conjecture at ``lambda=1.9``, levels 2 through 13, and powers -1, -2, -4, and
-8.
"""

from __future__ import annotations

import argparse
import math
from collections.abc import Callable
from fractions import Fraction

import numpy as np


ALPHA = math.log2(3.0)
DEFAULT_POWERS = (-1.0, -2.0, -4.0, -8.0)


def exact_harmonic_mean(values: list[Fraction]) -> Fraction:
    return Fraction(len(values), 1) / sum(Fraction(1, value) for value in values)


def exact_arithmetic_mean(values: list[Fraction]) -> Fraction:
    return sum(values) / len(values)


def exact_apply_operator(
    vector: list[Fraction],
    level: int,
    mean: Callable[[list[Fraction]], Fraction],
) -> list[Fraction]:
    """Apply a structurally identical KL operator with rational test weights."""

    modulus = 3**level
    coarse_modulus = 3 ** (level - 1)
    states = list(range(2, modulus, 3))
    positions = {state: index for index, state in enumerate(states)}
    tau = Fraction(7, 19)
    weight_two = Fraction(11, 17)
    weight_eight = Fraction(13, 17)
    result: list[Fraction] = []
    for state in states:
        value = tau * vector[positions[(4 * state) % modulus]]
        if state % 9 == 2:
            target = ((4 * state - 2) // 3) % coarse_modulus
            fiber = [
                vector[positions[target + digit * coarse_modulus]]
                for digit in range(3)
            ]
            value += weight_two * mean(fiber)
        elif state % 9 == 8:
            target = ((2 * state - 1) // 3) % coarse_modulus
            fiber = [
                vector[positions[target + digit * coarse_modulus]]
                for digit in range(3)
            ]
            value += weight_eight * mean(fiber)
        result.append(value)
    return result


def exact_project(vector: list[Fraction]) -> list[Fraction]:
    coarse_count = len(vector) // 3
    return [
        exact_harmonic_mean(
            [vector[parent + digit * coarse_count] for digit in range(3)]
        )
        for parent in range(coarse_count)
    ]


def run_exact_structural_gates() -> None:
    """Check bounded exact cores of the research derivations in section 6."""

    test_triples = [
        [Fraction(1), Fraction(2), Fraction(7)],
        [Fraction(3), Fraction(11), Fraction(5)],
        [Fraction(17), Fraction(4), Fraction(29)],
    ]
    policies = [
        [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)],
        [Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)],
        [Fraction(7, 10), Fraction(1, 5), Fraction(1, 10)],
    ]
    for triple in test_triples:
        harmonic = exact_harmonic_mean(triple)
        tangent = [harmonic**2 / (3 * value**2) for value in triple]
        if sum(a * value for a, value in zip(tangent, triple)) != harmonic:
            raise AssertionError("harmonic tangent does not attain the dual mean")
        for policy in policies:
            coefficients = [3 * probability**2 for probability in policy]
            if sum(a * value for a, value in zip(coefficients, triple)) < harmonic:
                raise AssertionError("reverse-Holder support inequality failed")

    for level in range(3, 7):
        vector = [
            Fraction((17 * index * index + 13 * index + 5) % 97 + 1)
            for index in range(3 ** (level - 1))
        ]
        projected_image = exact_project(
            exact_apply_operator(vector, level, exact_harmonic_mean)
        )
        image_of_projection = exact_apply_operator(
            exact_project(vector), level - 1, exact_harmonic_mean
        )
        if any(
            left < right
            for left, right in zip(projected_image, image_of_projection)
        ):
            raise AssertionError("power-mean projection inequality failed")

    for level in range(3, 8):
        harmonic = [Fraction(1) for _ in range(3 ** (level - 1))]
        arithmetic = harmonic.copy()
        for _ in range(1, level):
            harmonic = exact_apply_operator(
                harmonic, level, exact_harmonic_mean
            )
            arithmetic = exact_apply_operator(
                arithmetic, level, exact_arithmetic_mean
            )
            if harmonic != arithmetic:
                raise AssertionError("finite-horizon annealed identity failed")

    print(
        "EXACT GATES: harmonic dual/projection through k=6 and "
        "finite-horizon identity through k=7 passed"
    )


def parse_levels(specification: str) -> tuple[int, ...]:
    levels: set[int] = set()
    for piece in specification.split(","):
        piece = piece.strip()
        if not piece:
            continue
        if "-" in piece:
            first_text, last_text = piece.split("-", 1)
            levels.update(range(int(first_text), int(last_text) + 1))
        else:
            levels.add(int(piece))
    result = tuple(sorted(levels))
    if not result or result[0] < 2:
        raise ValueError("levels must be integers at least 2")
    return result


def parse_powers(specification: str) -> tuple[float, ...]:
    powers = tuple(float(piece) for piece in specification.split(","))
    if not powers or any(not math.isfinite(power) or power >= 0 for power in powers):
        raise ValueError("powers must be finite and strictly negative")
    return powers


def build_operator_indices(
    level: int,
) -> tuple[
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    int,
]:
    modulus = 3**level
    states = np.arange(2, modulus, 3, dtype=np.int64)
    state_count = len(states)
    coarse_modulus = 3 ** (level - 1)
    coarse_count = state_count // 3

    transport = ((4 * states) % modulus - 2) // 3
    rows_two = np.flatnonzero(states % 9 == 2)
    rows_eight = np.flatnonzero(states % 9 == 8)

    target_two = ((4 * states[rows_two] - 2) // 3) % coarse_modulus
    target_eight = ((2 * states[rows_eight] - 1) // 3) % coarse_modulus
    base_two = (target_two - 2) // 3
    base_eight = (target_eight - 2) // 3
    digit_offsets = coarse_count * np.arange(3, dtype=np.int64)
    fibers_two = base_two[:, None] + digit_offsets[None, :]
    fibers_eight = base_eight[:, None] + digit_offsets[None, :]

    if (
        np.any(transport < 0)
        or np.any(transport >= state_count)
        or np.any(fibers_two < 0)
        or np.any(fibers_two >= state_count)
        or np.any(fibers_eight < 0)
        or np.any(fibers_eight >= state_count)
    ):
        raise AssertionError("closed residue-index formulas left the state space")

    return (
        transport,
        rows_two,
        rows_eight,
        fibers_two,
        fibers_eight,
        state_count,
    )


def negative_power_mean(values: np.ndarray, power: float) -> np.ndarray:
    scaled_logs = power * np.log(values)
    peak = np.max(scaled_logs, axis=1)
    log_mean = peak + np.log(
        np.mean(np.exp(scaled_logs - peak[:, None]), axis=1)
    )
    return np.exp(log_mean / power)


def apply_operator(
    vector: np.ndarray,
    indices: tuple[
        np.ndarray,
        np.ndarray,
        np.ndarray,
        np.ndarray,
        np.ndarray,
        int,
    ],
    lambda_value: float,
    power: float,
) -> np.ndarray:
    transport, rows_two, rows_eight, fibers_two, fibers_eight, _ = indices
    result = lambda_value**-2 * vector[transport]
    result[rows_two] += lambda_value ** (ALPHA - 2) * negative_power_mean(
        vector[fibers_two], power
    )
    result[rows_eight] += lambda_value ** (ALPHA - 1) * negative_power_mean(
        vector[fibers_eight], power
    )
    return result


def spectral_bracket(
    indices: tuple[
        np.ndarray,
        np.ndarray,
        np.ndarray,
        np.ndarray,
        np.ndarray,
        int,
    ],
    lambda_value: float,
    power: float,
    maximum_iterations: int,
    cw_log_tolerance: float,
) -> tuple[float, float, float, int]:
    vector = np.ones(indices[-1], dtype=np.float64)
    lower = 0.0
    upper = math.inf
    for iteration in range(1, maximum_iterations + 1):
        image = apply_operator(vector, indices, lambda_value, power)
        if not np.all(np.isfinite(image)) or np.any(image <= 0.0):
            raise FloatingPointError("operator image is not finite and positive")
        ratios = image / vector
        lower = float(np.min(ratios))
        upper = float(np.max(ratios))
        if not 0.0 < lower <= upper:
            raise FloatingPointError("invalid Collatz--Wielandt bracket")
        if math.log(upper / lower) <= cw_log_tolerance:
            estimate = math.sqrt(lower * upper)
            return estimate, lower, upper, iteration
        vector = image / upper
    raise RuntimeError(
        f"power iteration did not reach log CW width {cw_log_tolerance:g}; "
        f"last bracket [{lower:.17g}, {upper:.17g}]"
    )


def main() -> None:
    run_exact_structural_gates()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", default="2-13")
    parser.add_argument(
        "--powers", default=",".join(str(power) for power in DEFAULT_POWERS)
    )
    parser.add_argument("--lambda-value", type=float, default=1.9)
    parser.add_argument("--maximum-iterations", type=int, default=10_000)
    parser.add_argument("--cw-log-tolerance", type=float, default=1e-11)
    args = parser.parse_args()

    levels = parse_levels(args.levels)
    powers = parse_powers(args.powers)
    if not math.isfinite(args.lambda_value) or args.lambda_value <= 0.0:
        parser.error("--lambda-value must be finite and positive")
    if args.maximum_iterations <= 0:
        parser.error("--maximum-iterations must be positive")
    if not 0.0 < args.cw_log_tolerance < 1.0:
        parser.error("--cw-log-tolerance must lie in (0,1)")

    annealed = args.lambda_value**-2 + (
        args.lambda_value ** (ALPHA - 2)
        + args.lambda_value ** (ALPHA - 1)
    ) / 3.0
    print(
        f"lambda={args.lambda_value:.12g}  annealed_s={annealed:.12f}  "
        f"CW_log_tolerance={args.cw_log_tolerance:g}"
    )
    print("  k    states      p       rho_mid          cw_lower          cw_upper    iterations       s-rho")
    for level in levels:
        indices = build_operator_indices(level)
        for power in powers:
            estimate, lower, upper, iterations = spectral_bracket(
                indices,
                args.lambda_value,
                power,
                args.maximum_iterations,
                args.cw_log_tolerance,
            )
            print(
                f"{level:3d} {indices[-1]:9d} {power:7.2f}  "
                f"{estimate:14.10f}  {lower:14.10f}  {upper:14.10f}  "
                f"{iterations:10d}  {annealed-estimate:11.8f}"
            )
    print()
    print(
        "SCOPE: bounded structural gates use exact rationals; spectral values "
        "use floating nonlinear power iteration and floating Collatz--Wielandt "
        "brackets, with no interval or all-level claim"
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact bounded gates and floating diagnostics for soft-min pair carries.

The exact part uses the rational structural channel ``a=b2=b8=1/3``.  It
checks the induced countable block law on complete finite periods, constructs
the full unequal-word affine alignment kernel, verifies collision and
martingale-shell identities, and certifies a genuinely subcritical diagonal
coefficient whose full two-copy response expands an exact detail-shell mode.

The floating part uses the physical KL weights at a requested ``lambda`` and
reports the signed shell correlations of the actual annealed stationary law.
Those values are diagnostics, not interval bounds or asymptotic claims.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from fractions import Fraction

import numpy as np


ALPHA = math.log2(3.0)


@dataclass(frozen=True)
class RationalChannel:
    transport: Fraction
    branch_two: Fraction
    branch_eight: Fraction

    def __post_init__(self) -> None:
        if min(self.transport, self.branch_two, self.branch_eight) <= 0:
            raise ValueError("channel weights must be positive")
        if self.transport + self.branch_two + self.branch_eight != 1:
            raise ValueError("channel weights must sum to one")


def block_weight(
    exponent: int,
    transport: Fraction,
    branch_two: Fraction,
    branch_eight: Fraction,
) -> Fraction:
    if exponent <= 0:
        raise ValueError("block exponent must be positive")
    if exponent % 2:
        return branch_eight * transport ** ((exponent - 1) // 2)
    return branch_two * transport ** ((exponent - 2) // 2)


def aggregated_block_weights(
    step: int, channel: RationalChannel
) -> list[Fraction]:
    """Aggregate the infinite block law over its exact quotient period."""

    period = 2 * 3**step
    cycle_weight = channel.transport ** (period // 2)
    weights = [
        block_weight(
            exponent,
            channel.transport,
            channel.branch_two,
            channel.branch_eight,
        )
        / (1 - cycle_weight)
        for exponent in range(1, period + 1)
    ]
    if sum(weights) != 1:
        raise AssertionError("aggregated block law is not a probability law")
    return weights


def block_output(parent: int, exponent: int, output_modulus: int) -> int:
    offset = 1 if exponent % 2 else 2
    inverse_power = pow(pow(2, exponent, output_modulus), -1, output_modulus)
    output = ((3 * parent + offset) * inverse_power) % output_modulus
    if output % 3 != 2:
        raise AssertionError("block map left the KL state class")
    return output


def channel_scalars(
    channel: RationalChannel,
) -> tuple[Fraction, tuple[Fraction, Fraction, Fraction], Fraction]:
    a = channel.transport
    b2 = channel.branch_two
    b8 = channel.branch_eight
    diagonal = (b2 * b2 + b8 * b8) / (1 - a * a)
    first_two = (b2 + b8 * a) / (1 - a**3)
    first_five = a * first_two
    first_eight = (b8 + b2 * a * a) / (1 - a**3)
    first_digits = (first_two, first_five, first_eight)
    if sum(first_digits) != 1:
        raise AssertionError("first-digit masses do not sum to one")
    off_diagonal = sum(value * value for value in first_digits) - diagonal
    if off_diagonal <= 0:
        raise AssertionError("off-diagonal collision mass is not positive")
    return diagonal, first_digits, off_diagonal


def exact_marginals(
    maximum_depth: int, channel: RationalChannel
) -> list[list[Fraction]]:
    marginals: list[list[Fraction]] = [[Fraction(1)]]
    for step in range(1, maximum_depth + 1):
        weights = aggregated_block_weights(step, channel)
        output_modulus = 3 ** (step + 1)
        parent_count = 3 ** (step - 1)
        output = [Fraction(0) for _ in range(3**step)]
        for parent_index, parent_mass in enumerate(marginals[-1]):
            parent = 2 + 3 * parent_index
            for exponent, weight in enumerate(weights, start=1):
                child = block_output(parent, exponent, output_modulus)
                output[(child - 2) // 3] += parent_mass * weight
        if len(marginals[-1]) != parent_count or sum(output) != 1:
            raise AssertionError("invalid induced marginal")
        marginals.append(output)
    return marginals


def exact_alignment_kernel(
    step: int, channel: RationalChannel
) -> tuple[list[list[Fraction]], Fraction, Fraction]:
    """Return P_step, equal-word mass D, and unequal-word mass beta."""

    weights = aggregated_block_weights(step, channel)
    parent_count = 3 ** (step - 1)
    output_count = 3**step
    output_modulus = 3 ** (step + 1)
    distributions = [
        [Fraction(0) for _ in range(output_count)]
        for _ in range(parent_count)
    ]
    for parent_index in range(parent_count):
        parent = 2 + 3 * parent_index
        for exponent, weight in enumerate(weights, start=1):
            child = block_output(parent, exponent, output_modulus)
            distributions[parent_index][(child - 2) // 3] += weight

    diagonal, _, off_diagonal = channel_scalars(channel)
    kernel: list[list[Fraction]] = []
    for left in range(parent_count):
        row: list[Fraction] = []
        for right in range(parent_count):
            total = sum(
                distributions[left][output] * distributions[right][output]
                for output in range(output_count)
            )
            if left == right:
                total -= diagonal
            row.append(total / off_diagonal)
        kernel.append(row)

    for left, row in enumerate(kernel):
        if sum(row) != 1:
            raise AssertionError("alignment-kernel row is not stochastic")
        for right in range(parent_count):
            if kernel[left][right] != kernel[right][left]:
                raise AssertionError("alignment kernel is not symmetric")
    return kernel, diagonal, off_diagonal


def quadratic_form(
    vector: list[Fraction], matrix: list[list[Fraction]]
) -> Fraction:
    return sum(
        vector[left] * matrix[left][right] * vector[right]
        for left in range(len(vector))
        for right in range(len(vector))
    )


def normalized_energy(probabilities: list[Fraction]) -> Fraction:
    return len(probabilities) * sum(value * value for value in probabilities)


def compose_affine(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    return (
        left[0] * right[0],
        left[0] * right[1] + left[1],
    )


def inverse_affine(
    transformation: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    return (
        1 / transformation[0],
        -transformation[1] / transformation[0],
    )


def run_exact_gates() -> None:
    channel = RationalChannel(Fraction(1, 3), Fraction(1, 3), Fraction(1, 3))
    diagonal, first_digits, off_diagonal = channel_scalars(channel)
    if diagonal != Fraction(1, 4):
        raise AssertionError("unexpected equal-word collision mass")
    if first_digits != (Fraction(6, 13), Fraction(2, 13), Fraction(5, 13)):
        raise AssertionError("unexpected first-digit law")
    if off_diagonal != Fraction(7, 52):
        raise AssertionError("unexpected unequal-word collision mass")

    # General two-state Green normalization at this rational parameter.
    a = channel.transport
    b2 = channel.branch_two
    b8 = channel.branch_eight
    start_even = b2 * b2 / (1 - a * a)
    start_odd = b8 * b8 / (1 - a * a)
    edge_even_odd = (b8 / b2) * a
    edge_odd_even = (b2 / b8) * a * a
    two_step = a**3
    forward_mass = (
        start_even * (edge_even_odd + two_step)
        + start_odd * (edge_odd_even + two_step)
    ) / (1 - two_step)
    if 2 * forward_mass != off_diagonal:
        raise AssertionError("two-state Green mass does not match pair mass")

    transport_map = (Fraction(2), Fraction(1))
    long_map = (Fraction(32), Fraction(24))
    commutator = compose_affine(
        compose_affine(long_map, transport_map),
        inverse_affine(compose_affine(transport_map, long_map)),
    )
    if commutator != (Fraction(1), Fraction(7)):
        raise AssertionError("affine loop commutator is not translation by seven")

    marginals = exact_marginals(4, channel)
    energies = [normalized_energy(marginal) for marginal in marginals]
    increments = [Fraction(0)] + [
        energies[depth] - energies[depth - 1]
        for depth in range(1, len(energies))
    ]
    kappa = 3 * diagonal
    eta = 3 * off_diagonal

    for step in range(1, 5):
        kernel, checked_diagonal, checked_off_diagonal = exact_alignment_kernel(
            step, channel
        )
        if (checked_diagonal, checked_off_diagonal) != (
            diagonal,
            off_diagonal,
        ):
            raise AssertionError("kernel scalar mismatch")
        parent = marginals[step - 1]
        parent_count = len(parent)
        carry = parent_count * quadratic_form(parent, kernel)
        if energies[step] != kappa * energies[step - 1] + eta * carry:
            raise AssertionError("two-copy collision renewal failed")

    for depth in range(1, 4):
        kernel, _, _ = exact_alignment_kernel(depth + 1, channel)
        density = [len(marginals[depth]) * value for value in marginals[depth]]
        coarse_density = [
            len(marginals[depth - 1]) * value
            for value in marginals[depth - 1]
        ]
        detail = [
            density[index] - coarse_density[index % len(coarse_density)]
            for index in range(len(density))
        ]
        correlation = quadratic_form(detail, kernel) / len(detail)
        expected = (increments[depth + 1] - kappa * increments[depth]) / eta
        if correlation != expected:
            raise AssertionError("martingale-shell correlation identity failed")

    # A pure conductor-two vector: every three-child fiber sums to zero.
    witness = [
        Fraction(value)
        for value in (1, 2, -10, -1, 3, -10, 0, -5, 20)
    ]
    for parent in range(3):
        if sum(witness[parent + digit * 3] for digit in range(3)) != 0:
            raise AssertionError("expansion witness is not a pure detail shell")
    kernel, _, _ = exact_alignment_kernel(3, channel)
    rayleigh = quadratic_form(witness, kernel) / sum(
        value * value for value in witness
    )
    response = kappa + eta * rayleigh
    expected_response = Fraction(6_272_085_579, 6_199_042_768)
    if response != expected_response or response <= 1:
        raise AssertionError("subcritical pair-carry expansion witness failed")

    print(
        "EXACT GATES: block/pair kernels through depth 4, shell identities "
        "through depth 3, and subcritical detail expansion passed"
    )
    print(
        f"  rational channel: kappa={kappa}, eta={eta}, "
        f"detail_response={response}"
    )


def build_operator_indices(
    level: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, int]:
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
    offsets = coarse_count * np.arange(3, dtype=np.int64)
    fibers_two = base_two[:, None] + offsets[None, :]
    fibers_eight = base_eight[:, None] + offsets[None, :]
    return transport, rows_two, rows_eight, fibers_two, fibers_eight, state_count


def physical_channel(lambda_value: float) -> tuple[float, float, float, float]:
    annealed = lambda_value**-2 + (
        lambda_value ** (ALPHA - 2) + lambda_value ** (ALPHA - 1)
    ) / 3.0
    transport = lambda_value**-2 / annealed
    branch_two = lambda_value ** (ALPHA - 2) / (3.0 * annealed)
    branch_eight = lambda_value ** (ALPHA - 1) / (3.0 * annealed)
    return annealed, transport, branch_two, branch_eight


def floating_marginal(
    depth: int,
    lambda_value: float,
    tolerance: float,
    maximum_iterations: int,
) -> tuple[np.ndarray, float]:
    if depth == 0:
        return np.ones(1), 0.0
    indices = build_operator_indices(depth + 1)
    transport, rows_two, rows_eight, fibers_two, fibers_eight, state_count = indices
    annealed, _, _, _ = physical_channel(lambda_value)
    vector = np.full(state_count, 1.0 / state_count)
    residual = math.inf
    for _ in range(maximum_iterations):
        image = lambda_value**-2 * vector[transport]
        image[rows_two] += lambda_value ** (ALPHA - 2) * np.mean(
            vector[fibers_two], axis=1
        )
        image[rows_eight] += lambda_value ** (ALPHA - 1) * np.mean(
            vector[fibers_eight], axis=1
        )
        image /= annealed
        image /= np.sum(image)
        residual = state_count * float(np.max(np.abs(image - vector)))
        vector = image
        if residual <= tolerance:
            return vector, residual
    raise RuntimeError(
        f"annealed marginal at depth {depth} did not converge; residual={residual}"
    )


def first_shell_response(lambda_value: float) -> float:
    """Floating response of the fixed z=(1,1,-2) first-shell direction."""

    _, a, b2, b8 = physical_channel(lambda_value)
    period = 18
    weights = np.array(
        [
            (b8 * a ** ((exponent - 1) // 2) if exponent % 2 else
             b2 * a ** ((exponent - 2) // 2))
            / (1.0 - a**9)
            for exponent in range(1, period + 1)
        ]
    )
    distributions = np.zeros((3, 9))
    for parent_index in range(3):
        parent = 2 + 3 * parent_index
        for exponent, weight in enumerate(weights, start=1):
            child = block_output(parent, exponent, 27)
            distributions[parent_index, (child - 2) // 3] += weight
    diagonal = (b2 * b2 + b8 * b8) / (1.0 - a * a)
    first_two = (b2 + b8 * a) / (1.0 - a**3)
    first_five = a * first_two
    first_eight = (b8 + b2 * a * a) / (1.0 - a**3)
    off_diagonal = (
        first_two**2 + first_five**2 + first_eight**2 - diagonal
    )
    kernel = (
        distributions @ distributions.T - diagonal * np.eye(3)
    ) / off_diagonal
    witness = np.array([1.0, 1.0, -2.0])
    rayleigh = float(witness @ kernel @ witness / (witness @ witness))
    return 3.0 * diagonal + 3.0 * off_diagonal * rayleigh


def run_floating_dashboard(
    lambda_value: float,
    maximum_depth: int,
    tolerance: float,
    maximum_iterations: int,
) -> None:
    annealed, a, b2, b8 = physical_channel(lambda_value)
    diagonal = (b2 * b2 + b8 * b8) / (1.0 - a * a)
    first_two = (b2 + b8 * a) / (1.0 - a**3)
    first_five = a * first_two
    first_eight = (b8 + b2 * a * a) / (1.0 - a**3)
    off_diagonal = (
        first_two**2 + first_five**2 + first_eight**2 - diagonal
    )
    kappa = 3.0 * diagonal
    eta = 3.0 * off_diagonal
    threshold = (1.0 - kappa) / eta

    energies: list[float] = []
    residuals: list[float] = []
    for depth in range(maximum_depth + 1):
        marginal, residual = floating_marginal(
            depth, lambda_value, tolerance, maximum_iterations
        )
        energies.append(len(marginal) * float(marginal @ marginal))
        residuals.append(residual)
    increments = [math.nan] + [
        energies[depth] - energies[depth - 1]
        for depth in range(1, len(energies))
    ]

    print()
    print(
        f"FLOAT lambda={lambda_value:.12g} s={annealed:.12f} "
        f"kappa={kappa:.12f} eta={eta:.12f} "
        f"theta_critical={threshold:.12f}"
    )
    print(
        f"fixed first-shell response={first_shell_response(lambda_value):.12f}"
    )
    print("  n          Q_n        Delta_n   Delta_ratio       theta_n    residual")
    for depth in range(1, maximum_depth):
        ratio = increments[depth + 1] / increments[depth]
        theta = (ratio - kappa) / eta
        print(
            f"{depth:3d}  {energies[depth]:12.9f}  "
            f"{increments[depth]:12.9f}  {ratio:12.9f}  "
            f"{theta:12.9f}  {residuals[depth]:.3e}"
        )
    print(
        "SCOPE: exact gates use an abstract rational channel with the same "
        "affine block structure; physical-lambda stationary laws and shell "
        "correlations are floating diagnostics, not interval or asymptotic claims"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lambda-value", type=float, default=1.9)
    parser.add_argument("--maximum-depth", type=int, default=12)
    parser.add_argument("--tolerance", type=float, default=1e-12)
    parser.add_argument("--maximum-iterations", type=int, default=5_000)
    args = parser.parse_args()
    if not 1.0 < args.lambda_value <= 2.0:
        parser.error("--lambda-value must lie in (1,2]")
    if args.maximum_depth < 2:
        parser.error("--maximum-depth must be at least 2")
    if not 0.0 < args.tolerance < 1.0:
        parser.error("--tolerance must lie in (0,1)")
    if args.maximum_iterations <= 0:
        parser.error("--maximum-iterations must be positive")

    run_exact_gates()
    run_floating_dashboard(
        args.lambda_value,
        args.maximum_depth,
        args.tolerance,
        args.maximum_iterations,
    )


if __name__ == "__main__":
    main()

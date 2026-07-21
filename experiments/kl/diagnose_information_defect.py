#!/usr/bin/env python3
"""Information-geometric diagnostics for the selected KL fiber defect.

This script keeps three scopes separate.

* Exact bounded gates check the ternary carry indexing, the hard Jensen-gap
  identity, its shared-minimizer zero set, and a rational slowly rotating
  obstruction family.
* Exact reductions on the SHA-pinned portable k=12,13,14 certificate vectors
  reconstruct the hard local mismatch with integer arithmetic.
* Quantities involving logarithms, square roots, or Gibbs escorts are floating
  diagnostics on those exact inputs.  They are not interval certificates.

For a transport conditional triple p, a carry-aligned branch triple q, and
theta in (0,1), put

    J_theta(p,q) = min_i [theta (p_i-min p)
                          +(1-theta) (q_i-min q)].

If A and B are the two unnormalized row masses, the exact hard local KL-system
slack is (A+B) J_theta, theta=A/(A+B).  The diagnostic compares this quantity
with ordinary divergences, with forward D_KL projection onto the union of
shared-minimizer order cones, and with the order-theta Renyi escort rate

    R_beta=(1-theta) D_theta(P_beta || Q_beta)/beta,
    P_beta(i) proportional to exp(-beta (p_i-min p)),
    Q_beta(i) proportional to exp(-beta (q_i-min q)).

Algebra gives |R_beta-J_theta| <= log(3)/beta and R_beta -> J_theta.  At
theta=1/2 this is D_(1/2)/(2 beta), equivalently minus the logarithm of the
Hellinger affinity divided by beta.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np


HERE = Path(__file__).resolve().parent
BRANCH_2 = 2
NEUTRAL = 5
BRANCH_8 = 8

EXPECTED_MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
}

EXPECTED_REDUCTIONS = {
    12: (39_366, 26_448,
         772_423_864_681_596_547_189_456_501_972_885_013_539_027_640),
    13: (118_098, 79_282,
         2_234_900_867_728_090_992_035_322_634_418_498_268_573_545_536),
    14: (354_294, 237_189,
         6_531_852_270_199_133_814_291_567_659_656_285_337_188_903_364),
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(8 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def exact_sum(values: Iterable[np.integer]) -> int:
    return sum(map(int, values))


def branch_type(index: int) -> int:
    return (BRANCH_2, NEUTRAL, BRANCH_8)[index % 3]


def transport(index: int, size: int) -> int:
    return (4 * index + 2) % size


def branch_target(index: int, size: int) -> int:
    parent_size = size // 3
    kind = branch_type(index)
    if kind == BRANCH_2:
        return 4 * (index // 3) % parent_size
    if kind == BRANCH_8:
        return (2 * ((index - 2) // 3) + 1) % parent_size
    raise ValueError("neutral rows do not have a branch target")


def edge_signature(
    fine_level: int, coarse_row: int
) -> tuple[int, int, tuple[int, int, int]]:
    """Return transport fiber, branch fiber, and branch digit by source digit."""

    fine_size = 3 ** (fine_level - 1)
    coarse_size = fine_size // 3
    branch_size = coarse_size // 3
    transport_fiber = transport(coarse_row, coarse_size)
    branch_fiber = branch_target(coarse_row, coarse_size)
    signature = [-1, -1, -1]
    for lift_digit in range(3):
        fine_row = coarse_row + lift_digit * coarse_size
        fine_transport = transport(fine_row, fine_size)
        fine_branch = branch_target(fine_row, fine_size)
        source_digit = fine_transport // coarse_size
        target_digit = fine_branch // branch_size
        if fine_transport % coarse_size != transport_fiber:
            raise AssertionError("transport lift left its coarse fiber")
        if fine_branch % branch_size != branch_fiber:
            raise AssertionError("branch lift left its coarse fiber")
        if signature[source_digit] != -1:
            raise AssertionError("carry signature is not injective")
        signature[source_digit] = target_digit
    if sorted(signature) != [0, 1, 2]:
        raise AssertionError("carry signature is not a permutation")
    return transport_fiber, branch_fiber, tuple(signature)


def argmins(values: Sequence[Fraction | int | float]) -> set[int]:
    minimum = min(values)
    return {index for index, value in enumerate(values) if value == minimum}


def hard_jensen_gap(
    p: Sequence[Fraction], q: Sequence[Fraction], theta: Fraction
) -> Fraction:
    p_min = min(p)
    q_min = min(q)
    return min(
        theta * (p[index] - p_min)
        + (1 - theta) * (q[index] - q_min)
        for index in range(3)
    )


def verify_exact_local_gates() -> None:
    """Exhaust a small rational grid, including ties and carry permutations."""

    from itertools import permutations, product

    triples = tuple(product(range(1, 5), repeat=3))
    for left in triples:
        for right in triples:
            for signature in permutations(range(3)):
                aligned = tuple(right[signature[index]] for index in range(3))
                for a_weight, b_weight in ((1, 1), (2, 3), (5, 2)):
                    p_total = sum(left)
                    q_total = sum(aligned)
                    p = tuple(Fraction(value, p_total) for value in left)
                    q = tuple(Fraction(value, q_total) for value in aligned)
                    mass_a = Fraction(a_weight * p_total)
                    mass_b = Fraction(b_weight * q_total)
                    theta = mass_a / (mass_a + mass_b)
                    direct = min(
                        a_weight * (left[index] - min(left))
                        + b_weight * (aligned[index] - min(aligned))
                        for index in range(3)
                    )
                    normalized = (mass_a + mass_b) * hard_jensen_gap(p, q, theta)
                    if direct != normalized:
                        raise AssertionError("hard conditional Jensen identity failed")
                    common_minimum = bool(argmins(p) & argmins(q))
                    if (direct == 0) != common_minimum:
                        raise AssertionError("shared-minimizer zero set failed")


def rotating_family(length: int) -> list[tuple[Fraction, Fraction, Fraction]]:
    vertices = (
        (Fraction(1, 6), Fraction(1, 3), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 6), Fraction(1, 3)),
        (Fraction(1, 3), Fraction(1, 2), Fraction(1, 6)),
    )
    result: list[tuple[Fraction, Fraction, Fraction]] = []
    for segment in range(3):
        left = vertices[segment]
        right = vertices[(segment + 1) % 3]
        for step in range(length):
            result.append(tuple(
                (length - step) * left[index] / length
                + step * right[index] / length
                for index in range(3)
            ))
    return result


def verify_slow_rotation() -> None:
    """Check the exact long-cycle obstruction to a local coercivity theorem."""

    for length in (13, 49, 193):
        cycle = rotating_family(length)
        total_gap = Fraction(0)
        mismatches = 0
        terminal_defect = Fraction(0)
        raw_d_kl = 0.0
        cone_information = 0.0
        for index, p in enumerate(cycle):
            q = cycle[(index + 1) % len(cycle)]
            gap = hard_jensen_gap(p, q, Fraction(1, 2))
            total_gap += gap
            mismatches += int(argmins(p).isdisjoint(argmins(q)))
            terminal_defect += 1 - 3 * min(p)
            p_float = tuple(map(float, p))
            q_float = tuple(map(float, q))
            raw_d_kl += d_kl(p_float, q_float)
            cone_information += min(
                (d_kl_to_minimum_cone(p_float, label)
                 + d_kl_to_minimum_cone(q_float, label)) / 2
                for label in range(3)
            )
        if total_gap != Fraction(1, 4 * length):
            raise AssertionError("slow-rotation hard cost changed")
        if mismatches != 3:
            raise AssertionError("slow-rotation wall-crossing count changed")
        if terminal_defect / len(cycle) <= Fraction(1, 3):
            raise AssertionError("slow rotation lost its macroscopic fiber defect")
        print(
            f"  slow rotation L={length}: exact hard={total_gap}, "
            f"mean defect={float(terminal_defect / len(cycle)):.9f}; "
            f"floating L*D_KL={length * raw_d_kl:.9f}, "
            f"L^2*I_DKL={length * length * cone_information:.9f}"
        )

    # If the mesh hits all three tie walls exactly, every neighboring pair has
    # a common minimizer and the hard production vanishes identically.
    tied_cycle = rotating_family(48)
    if sum(
        (hard_jensen_gap(p, tied_cycle[(index + 1) % len(tied_cycle)], Fraction(1, 2))
         for index, p in enumerate(tied_cycle)),
        Fraction(0),
    ) != 0:
        raise AssertionError("tie-mediated rotation should have zero hard cost")


def parse_levels(specification: str) -> tuple[int, ...]:
    levels = tuple(sorted({int(piece.strip()) for piece in specification.split(",") if piece.strip()}))
    if not levels or any(level not in EXPECTED_MANIFEST_SHA256 for level in levels):
        raise ValueError("levels must be a nonempty subset of 12,13,14")
    return levels


def load_record(level: int) -> tuple[dict[str, object], np.ndarray]:
    path = HERE / f"cert_k{level}.json"
    actual_hash = sha256(path)
    if actual_hash != EXPECTED_MANIFEST_SHA256[level]:
        raise AssertionError(f"k={level} manifest hash changed: {actual_hash}")
    manifest = json.loads(path.read_text())
    raw = manifest.get("C")
    if not isinstance(raw, list):
        raise AssertionError("portable record no longer contains an inline vector")
    vector = np.asarray(raw, dtype=np.int64)
    if vector.shape != (3 ** (level - 1),) or np.any(vector <= 0):
        raise AssertionError("certificate vector has the wrong shape or positivity")
    return manifest, vector


def d_kl(first: Sequence[float], second: Sequence[float]) -> float:
    return sum(x * math.log(x / y) for x, y in zip(first, second) if x > 0)


def js_divergence(first: Sequence[float], second: Sequence[float]) -> float:
    middle = tuple((x + y) / 2 for x, y in zip(first, second))
    return (d_kl(first, middle) + d_kl(second, middle)) / 2


def hellinger_squared(first: Sequence[float], second: Sequence[float]) -> float:
    # Convention H^2=1-BC, where BC is the Hellinger/Bhattacharyya affinity.
    return 1 - sum(math.sqrt(x * y) for x, y in zip(first, second))


def d_kl_to_minimum_cone(p: Sequence[float], distinguished: int) -> float:
    """Forward D_KL projection onto {r_distinguished <= r_j for every j}.

    The three-coordinate I-projection is ordinary isotonic pooling: leave p
    alone if the declared label is already minimal; otherwise pool it with the
    smaller competing coordinate, and pool all three if that pair average
    still exceeds the last coordinate.
    """

    others = sorted(
        (index for index in range(3) if index != distinguished),
        key=p.__getitem__,
    )
    first, second = others
    if p[distinguished] <= p[first]:
        return 0.0
    pooled = (p[distinguished] + p[first]) / 2
    if pooled <= p[second]:
        return sum(
            p[index] * math.log(p[index] / pooled)
            for index in (distinguished, first)
            if p[index] > 0
        )
    return sum(value * math.log(3 * value) for value in p if value > 0)


def logsumexp(values: Sequence[float]) -> float:
    maximum = max(values)
    return maximum + math.log(sum(math.exp(value - maximum) for value in values))


def renyi_escort_rate(
    p: Sequence[float], q: Sequence[float], theta: float, beta: float
) -> float:
    p_min = min(p)
    q_min = min(q)
    x = tuple(value - p_min for value in p)
    y = tuple(value - q_min for value in q)
    mixture = tuple(theta * x_i + (1 - theta) * y_i for x_i, y_i in zip(x, y))
    log_z_x = logsumexp(tuple(-beta * value for value in x))
    log_z_y = logsumexp(tuple(-beta * value for value in y))
    log_z_mixture = logsumexp(tuple(-beta * value for value in mixture))
    return (-log_z_mixture + theta * log_z_x + (1 - theta) * log_z_y) / beta


def cold_power_escort(p: Sequence[float], beta: float) -> tuple[float, float, float]:
    logits = tuple(-beta * math.log(value) for value in p)
    normalizer = logsumexp(logits)
    return tuple(math.exp(value - normalizer) for value in logits)  # type: ignore[return-value]


def verify_record(level: int, betas: tuple[float, ...]) -> None:
    manifest, vector = load_record(level)
    fine_size = len(vector)
    coarse_size = fine_size // 3
    branch_size = coarse_size // 3
    children = vector.reshape(3, coarse_size)
    coarse = np.minimum(np.minimum(children[0], children[1]), children[2])
    coarse_children = coarse.reshape(3, branch_size)
    twice_coarse = np.minimum(
        np.minimum(coarse_children[0], coarse_children[1]), coarse_children[2]
    )

    lambda_numerator = int(manifest["A"])
    lambda_scale = int(manifest["SC_L"])
    weight_scale = int(manifest["SC_W"])
    lambda_square = lambda_numerator * lambda_numerator
    transport_numerator = lambda_scale * lambda_scale * weight_scale
    branch_numerators = {
        BRANCH_2: int(manifest["B2"]) * lambda_square,
        BRANCH_8: int(manifest["B8"]) * lambda_square,
    }
    tau = (lambda_scale / lambda_numerator) ** 2
    branch_weights = {
        BRANCH_2: int(manifest["B2"]) / weight_scale,
        BRANCH_8: int(manifest["B8"]) / weight_scale,
    }

    edge_count = 0
    mismatches = 0
    hard_numerator = 0
    hard_float = 0.0
    total_mass = 0.0
    projected_information = 0.0
    raw_forward = 0.0
    raw_reverse = 0.0
    raw_js = 0.0
    raw_hellinger = 0.0
    harmless_raw_forward = 0.0
    escort_rates = [0.0 for _ in betas]
    cold_js = {64.0: 0.0, 1024.0: 0.0}
    cold_hellinger = {64.0: 0.0, 1024.0: 0.0}
    mismatch_mass = 0.0

    for row in range(coarse_size):
        kind = branch_type(row)
        if kind == NEUTRAL:
            continue
        edge_count += 1
        transport_fiber, branch_fiber, signature = edge_signature(level, row)
        left = tuple(int(children[digit, transport_fiber]) for digit in range(3))
        right = tuple(
            int(coarse_children[signature[digit], branch_fiber])
            for digit in range(3)
        )
        left_min = min(left)
        right_min = min(right)
        branch_numerator = branch_numerators[kind]
        local_numerator = min(
            transport_numerator * (left[index] - left_min)
            + branch_numerator * (right[index] - right_min)
            for index in range(3)
        )
        hard_numerator += local_numerator

        p_total = sum(left)
        q_total = sum(right)
        p = tuple(value / p_total for value in left)
        q = tuple(value / q_total for value in right)
        mass_a = tau * p_total
        mass_b = branch_weights[kind] * q_total
        mass = mass_a + mass_b
        theta = mass_a / mass
        p_min = min(p)
        q_min = min(q)
        normalized_gap = min(
            theta * (p[index] - p_min) + (1 - theta) * (q[index] - q_min)
            for index in range(3)
        )
        local_float = mass * normalized_gap
        hard_float += local_float
        total_mass += mass

        mismatch = min(range(3), key=p.__getitem__) != min(range(3), key=q.__getitem__)
        mismatches += int(mismatch)
        mismatch_mass += mass * int(mismatch)

        projected = min(
            theta * d_kl_to_minimum_cone(p, index)
            + (1 - theta) * d_kl_to_minimum_cone(q, index)
            for index in range(3)
        )
        projected_information += mass * projected
        forward = d_kl(p, q)
        reverse = d_kl(q, p)
        raw_forward += mass * forward
        raw_reverse += mass * reverse
        raw_js += mass * js_divergence(p, q)
        raw_hellinger += mass * hellinger_squared(p, q)
        if local_numerator == 0:
            harmless_raw_forward += mass * forward

        for index, beta in enumerate(betas):
            escort_rates[index] += mass * renyi_escort_rate(p, q, theta, beta)

        for beta in cold_js:
            p_escort = cold_power_escort(p, beta)
            q_escort = cold_power_escort(q, beta)
            cold_js[beta] += mass * js_divergence(p_escort, q_escort) / math.log(2)
            cold_hellinger[beta] += mass * hellinger_squared(p_escort, q_escort)

    expected_edges, expected_mismatches, expected_hard = EXPECTED_REDUCTIONS[level]
    if (edge_count, mismatches, hard_numerator) != (
        expected_edges, expected_mismatches, expected_hard
    ):
        raise AssertionError("pinned exact information-defect reduction changed")
    hard_exact_float = hard_numerator / (lambda_square * weight_scale)
    if not math.isclose(hard_float, hard_exact_float, rel_tol=2e-12, abs_tol=0.0):
        raise AssertionError("floating conditional normalization changed the hard sum")

    total = exact_sum(vector)
    coarse_total = exact_sum(coarse)
    excess = total - 3 * coarse_total
    branch_sum_numerator = int(manifest["B2"]) + int(manifest["B8"])
    branch_sum = branch_sum_numerator / weight_scale
    epsilon = excess / total
    quadratic_target = branch_sum * coarse_total * epsilon * epsilon / 2
    exact_hard_target_ratio = Fraction(
        2 * hard_numerator * total * total,
        lambda_square * branch_sum_numerator * coarse_total * excess * excess,
    )

    print(
        f"PASS k={level}: exact edges={edge_count}, mismatches={mismatches}, "
        f"hard/target={float(exact_hard_target_ratio):.9f}"
    )
    print(
        "  floating raw divergence / target: "
        f"D_KL(p||q)={raw_forward / quadratic_target:.9f}, "
        f"D_KL(q||p)={raw_reverse / quadratic_target:.9f}, "
        f"Jeffreys={(raw_forward + raw_reverse) / quadratic_target:.9f}, "
        f"JS={raw_js / quadratic_target:.9f}, "
        f"Hellinger^2={raw_hellinger / quadratic_target:.9f}"
    )
    print(
        "  synchronizable-cone projection: "
        f"I_DKL/target={projected_information / quadratic_target:.9f}, "
        f"I_DKL/hard={projected_information / hard_float:.9f}; "
        f"raw-forward mass on hard-zero rows={harmless_raw_forward / raw_forward:.9f}"
    )
    print(
        "  Renyi escort-rate recovery of hard mismatch: "
        + ", ".join(
            f"beta={beta:g}: {value / hard_float:.9f}"
            for beta, value in zip(betas, escort_rates)
        )
    )
    print(
        "  actual power-mean escort label diagnostics (mass averages): "
        f"hard mismatch={mismatch_mass / total_mass:.9f}; "
        + ", ".join(
            f"beta={beta:g}: JS/log2={cold_js[beta] / total_mass:.9f}, "
            f"H^2={cold_hellinger[beta] / total_mass:.9f}"
            for beta in cold_js
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", default="12,13,14")
    parser.add_argument("--betas", default="64,1024,16384")
    arguments = parser.parse_args()
    levels = parse_levels(arguments.levels)
    betas = tuple(float(piece) for piece in arguments.betas.split(",") if piece.strip())
    if not betas or any(beta <= 0 for beta in betas):
        raise ValueError("betas must be positive")

    for level in range(4, 9):
        coarse_size = 3 ** (level - 2)
        for row in range(coarse_size):
            if branch_type(row) != NEUTRAL:
                edge_signature(level, row)
    print("PASS: exact carry permutations through level 8")
    verify_exact_local_gates()
    print("PASS: exhaustive exact hard Jensen identity and shared-minimizer zero set")
    verify_slow_rotation()
    print("PASS: exact rational slowly rotating obstruction family")
    for level in levels:
        verify_record(level, betas)
    print(
        "CONCLUSION: exact finite reductions pass; logarithmic divergence and "
        "escort rows are floating diagnostics, not asymptotic claims"
    )


if __name__ == "__main__":
    main()

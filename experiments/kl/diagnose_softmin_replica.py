#!/usr/bin/env python3
"""Finite soft-min / replica diagnostic on selected KL certificates.

For a positive ternary fiber ``x=(x_0,x_1,x_2)`` and inverse temperature
``beta>0``, use the homogeneous power mean

    M_beta(x) = ((x_0^-beta+x_1^-beta+x_2^-beta)/3)^(-1/beta).

This is the power mean of order ``-beta``.  The full interpolation is the
power-mean family of order ``p<=1``: ``p=1`` is the annealed fiber average and
``p -> -infinity`` is the strict minimum.  The cold parametrization above is
numerically convenient near the strict-min endpoint.

Writing ``g_i=log(x_i/min(x))`` and

    pi_i(beta) = exp(-beta*g_i) / sum_j exp(-beta*g_j),

two independent replicas drawn from ``pi`` agree with probability

    Q_beta = sum_i pi_i(beta)^2
           = Z_(2 beta) / Z_beta^2.

Thus ``1-Q_beta`` is the probability that two soft selectors disagree, and
``beta*(1-Q_beta)`` is the magnitude of the trace of the log-coordinate
selector Hessian.  It localizes near fibers whose two smallest coordinates
are nearly tied as beta grows.

The canonical temperature susceptibility (heat capacity) is the second
two-copy statistic

    C_beta = beta^2 Var_pi(g)
           = (beta^2/2) E_(I,J iid pi)[(g_I-g_J)^2].

It satisfies ``-d H(pi_beta)/d log(beta)=C_beta``.  The implementation checks
the variance and two-replica formulas independently in every streamed chunk.

The script streams the SHA-pinned exact feasible certificates and reports the
strict-min defect, its finite-temperature approximation, min-profile- and
parent-mass-weighted replica disagreement, the near-tie mass at log-gap
``<=1/beta``, and the common log-partition correction.  All transcendental
statistics are floating diagnostics over exact inputs.  They are not exact
certificates, not critical eigenvectors, and not an all-level theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import time

import numpy as np

import multiscale_genealogy as genealogy


HERE = Path(__file__).resolve().parent
EXPECTED_LEVELS = tuple(range(12, 20))
EXPECTED_MANIFEST_SHA256 = {
    12: "a6386bfc8d0410a3dd82a98d765690e53c620259e6b7c4a5359f150ce6d1459f",
    13: "32f22a8bfc6e7962443ce0da0fd28bdb5d2a56748e0ea832a9135a45391fc7b7",
    14: "08ac51b3f259798b9bf979388ec5f7f590c26025cc323ee331867d20d616285f",
    15: "fdf28dbd79aa50334e4f643e51232bebb46d32e6e18d40acd144101613c87ae1",
    16: "5e4aa8081659c0d33ce0b50a6c3a211d62c508fcccc602dd2b33fa07dede170e",
    17: "56cf23c9ea2e61006535a3a65f952136c671d8f770df37dbc647d0133c462183",
    18: "4c064a165c680f4eab05b58b1cd49ba27de37fa15c3b093ea70bda711b406a6f",
    19: "a37716cc508410ec6043ff153c2f2b2527b25b53220fa9827d79d3145f0641fb",
}
DEFAULT_BETAS = (1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0)


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
    if not result or any(level not in EXPECTED_LEVELS for level in result):
        raise ValueError("levels must be a nonempty subset of 12,...,19")
    return result


def parse_betas(specification: str) -> tuple[float, ...]:
    betas = tuple(sorted({float(piece) for piece in specification.split(",")}))
    if not betas or any(not math.isfinite(beta) or beta <= 0 for beta in betas):
        raise ValueError("inverse temperatures must be finite and positive")
    return betas


def self_check() -> None:
    fibers = np.asarray(
        [
            [1.0, 1.0, 1.0],
            [1.0, 2.0, 4.0],
            [3.0, 3.0, 12.0],
        ]
    )
    gaps = np.log(fibers / fibers.min(axis=1, keepdims=True))
    for beta in (0.5, 1.0, 7.0, 64.0):
        weights = np.exp(-beta * gaps)
        partition = weights.sum(axis=1)
        probabilities = weights / partition[:, None]
        collision = np.square(probabilities).sum(axis=1)
        replica_collision = np.exp(-2.0 * beta * gaps).sum(axis=1) / np.square(
            partition
        )
        if not np.allclose(collision, replica_collision, rtol=2e-15, atol=2e-15):
            raise AssertionError("two-replica collision identity failed")
        power_mean = np.power(np.mean(np.power(fibers, -beta), axis=1), -1 / beta)
        reconstructed = fibers.min(axis=1) * np.exp(
            (math.log(3.0) - np.log(partition)) / beta
        )
        if not np.allclose(power_mean, reconstructed, rtol=2e-15, atol=2e-15):
            raise AssertionError("stable power-mean reconstruction failed")
    if not np.allclose(collision[0], 1 / 3):
        raise AssertionError("three-way exact tie regression failed")


def manifest_sha_verified(level: int) -> None:
    path = HERE / f"cert_k{level}.json"
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != EXPECTED_MANIFEST_SHA256[level]:
        raise AssertionError(
            f"k={level} manifest hash mismatch: expected "
            f"{EXPECTED_MANIFEST_SHA256[level]}, got {actual}"
        )
    if int(json.loads(path.read_text())["k"]) != level:
        raise AssertionError(f"k={level} manifest level mismatch")


def analyze_level(
    level: int, betas: tuple[float, ...], chunk_size: int
) -> tuple[float, list[dict[str, float]]]:
    started = time.perf_counter()
    manifest_sha_verified(level)
    values, _source, _digest, hash_verified, _hash_kind = (
        genealogy.load_certificate(level, verify_sha=True)
    )
    if not hash_verified:
        raise AssertionError("certificate source was not SHA verified")

    parent_count = len(values) // 3
    total_mass = 0.0
    minimum_mass = 0.0
    exact_tie_minimum_mass = 0.0
    exact_tie_parent_mass = 0.0
    exact_tie_count = 0
    smallest_positive_log_gap = math.inf
    accumulators = {
        beta: {
            "soft_minimum_mass": 0.0,
            "minimum_disagreement": 0.0,
            "parent_disagreement": 0.0,
            "minimum_near_tie": 0.0,
            "parent_near_tie": 0.0,
            "minimum_log_partition": 0.0,
            "minimum_heat_capacity": 0.0,
            "minimum_collision_identity_error": 0.0,
            "minimum_heat_capacity_identity_error": 0.0,
        }
        for beta in betas
    }

    for start in range(0, parent_count, chunk_size):
        stop = min(start + chunk_size, parent_count)
        children_int = (
            values[start:stop],
            values[parent_count + start : parent_count + stop],
            values[2 * parent_count + start : 2 * parent_count + stop],
        )
        children_exact = np.stack(children_int, axis=1)
        exact_minima = children_exact.min(axis=1)
        exact_multiplicity = np.equal(
            children_exact, exact_minima[:, None]
        ).sum(axis=1)
        exact_tie = exact_multiplicity >= 2
        children = children_exact.astype(np.float64)
        parents = children.sum(axis=1)
        minima = children.min(axis=1)
        relative_excess = (children - minima[:, None]) / minima[:, None]
        gaps = np.log1p(relative_excess)
        second_gap = np.partition(gaps, 1, axis=1)[:, 1]
        positive_second_gaps = second_gap[second_gap > 0.0]
        if len(positive_second_gaps):
            smallest_positive_log_gap = min(
                smallest_positive_log_gap,
                float(positive_second_gaps.min()),
            )

        total_mass += float(parents.sum(dtype=np.float64))
        minimum_mass += float(minima.sum(dtype=np.float64))
        exact_tie_count += int(np.count_nonzero(exact_tie))
        exact_tie_minimum_mass += float(minima[exact_tie].sum(dtype=np.float64))
        exact_tie_parent_mass += float(parents[exact_tie].sum(dtype=np.float64))

        for beta in betas:
            weights = np.exp(-beta * gaps)
            partition = weights.sum(axis=1)
            probabilities = weights / partition[:, None]
            collision = np.square(probabilities).sum(axis=1)
            replica_collision = np.exp(-2.0 * beta * gaps).sum(axis=1) / np.square(
                partition
            )
            disagreement = 1.0 - collision
            mean_gap = np.sum(probabilities * gaps, axis=1)
            gap_variance = np.sum(
                probabilities * np.square(gaps - mean_gap[:, None]), axis=1
            )
            replica_gap_variance = (
                probabilities[:, 0]
                * probabilities[:, 1]
                * np.square(gaps[:, 0] - gaps[:, 1])
                + probabilities[:, 0]
                * probabilities[:, 2]
                * np.square(gaps[:, 0] - gaps[:, 2])
                + probabilities[:, 1]
                * probabilities[:, 2]
                * np.square(gaps[:, 1] - gaps[:, 2])
            )
            heat_capacity = beta * beta * gap_variance
            replica_heat_capacity = beta * beta * replica_gap_variance
            near_tie = second_gap <= 1.0 / beta
            soft_ratio = np.exp((math.log(3.0) - np.log(partition)) / beta)
            accumulator = accumulators[beta]
            accumulator["soft_minimum_mass"] += float(
                np.dot(minima, soft_ratio)
            )
            accumulator["minimum_disagreement"] += float(
                np.dot(minima, disagreement)
            )
            accumulator["parent_disagreement"] += float(
                np.dot(parents, disagreement)
            )
            accumulator["minimum_near_tie"] += float(minima[near_tie].sum())
            accumulator["parent_near_tie"] += float(parents[near_tie].sum())
            accumulator["minimum_log_partition"] += float(
                np.dot(minima, np.log(partition))
            )
            accumulator["minimum_heat_capacity"] += float(
                np.dot(minima, heat_capacity)
            )
            identity_error = float(np.max(np.abs(collision - replica_collision)))
            accumulator["minimum_collision_identity_error"] = max(
                accumulator["minimum_collision_identity_error"], identity_error
            )
            heat_capacity_identity_error = float(
                np.max(np.abs(heat_capacity - replica_heat_capacity))
            )
            accumulator["minimum_heat_capacity_identity_error"] = max(
                accumulator["minimum_heat_capacity_identity_error"],
                heat_capacity_identity_error,
            )

    epsilon_infinity = 1.0 - 3.0 * minimum_mass / total_mass
    if not 0.0 < epsilon_infinity < 1.0:
        raise AssertionError(f"k={level}: strict-min defect is outside (0,1)")

    rows: list[dict[str, float]] = []
    for beta in betas:
        accumulator = accumulators[beta]
        epsilon_beta = 1.0 - 3.0 * accumulator["soft_minimum_mass"] / total_mass
        if not -1e-12 <= epsilon_beta <= epsilon_infinity + 1e-12:
            raise AssertionError(f"k={level}, beta={beta}: power-mean order failed")
        minimum_disagreement = accumulator["minimum_disagreement"] / minimum_mass
        parent_disagreement = accumulator["parent_disagreement"] / total_mass
        minimum_near_tie = accumulator["minimum_near_tie"] / minimum_mass
        parent_near_tie = accumulator["parent_near_tie"] / total_mass
        minimum_log_partition = (
            accumulator["minimum_log_partition"] / minimum_mass
        )
        minimum_heat_capacity = (
            accumulator["minimum_heat_capacity"] / minimum_mass
        )
        heat_capacity_identity_error = accumulator[
            "minimum_heat_capacity_identity_error"
        ]
        if heat_capacity_identity_error > 2e-10:
            raise AssertionError(
                f"k={level}, beta={beta}: two-replica heat-capacity identity "
                f"error {heat_capacity_identity_error}"
            )
        rows.append(
            {
                "beta": beta,
                "epsilon_beta": max(0.0, epsilon_beta),
                "epsilon_recovered": max(0.0, epsilon_beta) / epsilon_infinity,
                "minimum_replica_disagreement": minimum_disagreement,
                "beta_minimum_replica_disagreement": beta
                * minimum_disagreement,
                "epsilon_beta_minimum_replica_disagreement": epsilon_infinity
                * beta
                * minimum_disagreement,
                "parent_replica_disagreement": parent_disagreement,
                "beta_parent_replica_disagreement": beta * parent_disagreement,
                "minimum_near_tie_mass": minimum_near_tie,
                "beta_minimum_near_tie_mass": beta * minimum_near_tie,
                "epsilon_beta_minimum_near_tie_mass": epsilon_infinity
                * beta
                * minimum_near_tie,
                "parent_near_tie_mass": parent_near_tie,
                "minimum_log_partition": minimum_log_partition,
                "beta_minimum_log_partition": beta * minimum_log_partition,
                "minimum_heat_capacity": minimum_heat_capacity,
                "collision_identity_error": accumulator[
                    "minimum_collision_identity_error"
                ],
                "heat_capacity_identity_error": heat_capacity_identity_error,
            }
        )

    exact_tie_minimum_fraction = exact_tie_minimum_mass / minimum_mass
    exact_tie_parent_fraction = exact_tie_parent_mass / total_mass
    elapsed = time.perf_counter() - started
    print(
        f"k={level}: eps_inf={epsilon_infinity:.10f}, "
        f"exact_tie_fibers={exact_tie_count}/{parent_count}, "
        f"tie_q_mass={exact_tie_minimum_fraction:.3e}, "
        f"tie_parent_mass={exact_tie_parent_fraction:.3e}, "
        f"min_log_gap={smallest_positive_log_gap:.3e}, {elapsed:.2f}s"
    )
    print(
        "  beta  eps/eps_inf  eps*beta*E_q[1-Q]  E_q[C_beta]  "
        "eps*beta*q(gap2<=1/beta)"
    )
    for row in rows:
        print(
            f"  {row['beta']:5.1f}  {row['epsilon_recovered']:11.7f}  "
            f"{row['epsilon_beta_minimum_replica_disagreement']:20.8f}  "
            f"{row['minimum_heat_capacity']:11.8f}  "
            f"{row['epsilon_beta_minimum_near_tie_mass']:25.8f}"
        )
    return epsilon_infinity, rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", default="12-19")
    parser.add_argument(
        "--betas", default=",".join(str(beta) for beta in DEFAULT_BETAS)
    )
    parser.add_argument("--chunk-size", type=int, default=1_000_000)
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")

    levels = parse_levels(args.levels)
    betas = parse_betas(args.betas)
    self_check()
    for level in levels:
        analyze_level(level, betas, args.chunk_size)
    print()
    print(
        "SCOPE: floating soft-min/replica diagnostics over SHA-pinned exact "
        "selected feasible records; no critical-eigenvector or all-level claim"
    )


if __name__ == "__main__":
    main()

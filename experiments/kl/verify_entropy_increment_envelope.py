#!/usr/bin/env python3
"""Audit digitwise entropy increments of the exact KL certificate densities.

For a level-k certificate ``C`` and its 3-adic genealogy masses, let
``f_(k,j)`` be the normalized density on the first ``j`` ternary digits.  The
entropy chain-rule increment (natural logarithms) is

    h_(k,j) = Ent(f_(k,j)) - Ent(f_(k,j-1))
            = E_parent D(p_children || uniform_3).

This script reconstructs all increments for the tracked inline manifests and
SHA-pinned exact sidecars at k=12,...,19.  Logarithms are evaluated in
binary64 from exact integer masses, so the resulting table is a floating
diagnostic over exact inputs, not a rational certificate.  A stable
nonnegative generalized-KL formula is used, and the chain-rule sum is checked
against a direct entropy calculation.

The available exact tower and the separately pinned floating k=20 candidate
were inspected before selecting the simple finite envelope

    h_(k,j) <= (1/5) (3/4)^j.                    (post-hoc)

Thus the check is a compact theorem target and a future falsifier, not an
all-level theorem.  If it held uniformly for a suitable all-level family,

    sum_(j>J) h_(k,j) <= (4/5) (3/4)^(J+1),

and conditional Pinsker would give uniform L1 approximation by fixed-depth
conditional expectations.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import numpy as np

import multiscale_genealogy as genealogy
from verify_martingale_increment_envelope import exact_nonnegative_sum


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "analysis_cache" / "entropy_increments_exact.csv"
EXPECTED_LEVELS = tuple(range(12, 20))
ENVELOPE_SCALE = 1.0 / 5.0
ENVELOPE_RATIO = 3.0 / 4.0
INT64_MAX = np.iinfo(np.int64).max
EXPECTED_TOTAL_ENTROPY = {
    12: 0.324539498972,
    13: 0.343076457098,
    14: 0.361601378782,
    15: 0.379537682362,
    16: 0.396851017153,
    17: 0.413556121234,
    18: 0.429380564938,
    19: 0.444583262625,
}


def coarsen(children: np.ndarray) -> np.ndarray:
    """Sum the three digit blocks, preserving exact integer arithmetic."""

    if len(children) % 3:
        raise ValueError("a 3-adic level must contain a multiple of three nodes")
    triples = children.reshape(3, -1)
    if children.dtype != object and int(children.max()) <= INT64_MAX // 3:
        return triples.sum(axis=0, dtype=np.int64)
    return triples.astype(object, copy=False).sum(axis=0)


def entropy_kernel(relative_deviation: np.ndarray) -> np.ndarray:
    """Return ``(1+z) log(1+z)-z`` accurately for ``z > -1``."""

    z = relative_deviation
    result = (1.0 + z) * np.log1p(z) - z
    small = np.abs(z) < 1.0e-4
    if np.any(small):
        x = z[small]
        # Sum z^n*(-1)^n/(n(n-1)), n=2,...,8.  The next term is below
        # 1.4e-38 in this branch, far beneath binary64 resolution here.
        result[small] = (
            x**2 / 2.0
            - x**3 / 6.0
            + x**4 / 12.0
            - x**5 / 20.0
            + x**6 / 30.0
            - x**7 / 42.0
            + x**8 / 56.0
        )
    return result


def generalized_kl_sum(
    children: np.ndarray,
    parents: np.ndarray,
    chunk_size: int,
) -> float:
    """Return ``sum child*log(3*child/parent)`` in stable KL form."""

    parent_count = len(parents)
    if len(children) != 3 * parent_count:
        raise ValueError("each entropy parent must have exactly three children")
    total = 0.0
    for digit in range(3):
        child_start = digit * parent_count
        for start in range(0, parent_count, chunk_size):
            end = min(parent_count, start + chunk_size)
            x = np.asarray(
                children[child_start + start : child_start + end],
                dtype=np.float64,
            )
            parent = np.asarray(parents[start:end], dtype=np.float64)
            relative_deviation = 3.0 * x / parent - 1.0
            terms = (parent / 3.0) * entropy_kernel(relative_deviation)
            minimum = float(terms.min(initial=0.0))
            if minimum < -1.0e-12 * max(1.0, float(parent.max())):
                raise AssertionError("stable KL kernel produced a negative term")
            total += float(np.sum(np.maximum(terms, 0.0), dtype=np.float64))
    return total


def direct_entropy(
    values: np.ndarray,
    total_mass: int,
    node_count: int,
    chunk_size: int,
) -> float:
    """Compute KL of the finest normalized masses from the uniform law."""

    uniform_mass = float(total_mass) / node_count
    total = 0.0
    for start in range(0, len(values), chunk_size):
        block = np.asarray(values[start : start + chunk_size], dtype=np.float64)
        relative_deviation = block / uniform_mass - 1.0
        terms = uniform_mass * entropy_kernel(relative_deviation)
        total += float(np.sum(np.maximum(terms, 0.0), dtype=np.float64))
    return total / float(total_mass)


def analyze_level(
    k: int,
    chunk_size: int,
    verify_sha: bool,
) -> tuple[list[dict[str, object]], float, float]:
    values, source, digest, hash_verified, hash_kind = (
        genealogy.load_certificate(k, verify_sha)
    )
    total_mass = exact_nonnegative_sum(values, chunk_size)
    entropy_direct = direct_entropy(values, total_mass, len(values), chunk_size)
    children = values
    rows: list[dict[str, object]] = []

    for parent_depth in range(k - 1, 0, -1):
        parents = coarsen(children)
        if exact_nonnegative_sum(parents, chunk_size) != total_mass:
            raise AssertionError(f"k={k}, depth={parent_depth}: mass changed")
        increment = generalized_kl_sum(
            children, parents, chunk_size
        ) / float(total_mass)
        envelope = ENVELOPE_SCALE * ENVELOPE_RATIO**parent_depth
        if increment > envelope * (1.0 + 5.0e-13):
            raise AssertionError(
                f"k={k}, depth={parent_depth}: {increment} > {envelope}"
            )
        rows.append({
            "k": k,
            "parent_depth": parent_depth,
            "child_depth": parent_depth + 1,
            "terminal_offset": k - 1 - parent_depth,
            "parent_node_count": len(parents),
            "child_node_count": len(children),
            "entropy_increment": f"{increment:.17g}",
            "envelope": f"{envelope:.17g}",
            "increment_over_envelope": f"{increment / envelope:.17g}",
            "envelope_slack": f"{envelope - increment:.17g}",
            "passes_envelope": increment <= envelope * (1.0 + 5.0e-13),
            "envelope_scope": "post_hoc_k12_through_float_k20",
            "logarithm": "natural",
            "arithmetic": "float64_log_on_exact_integer_masses",
            "source_kind": "exact_feasible_certificate",
            "source": source,
            "source_sha256": digest,
            "source_sha256_verified": hash_verified,
            "source_sha256_kind": hash_kind,
        })
        children = parents

    if len(children) != 1 or int(children[0]) != total_mass:
        raise AssertionError(f"k={k}: hierarchy did not reach the exact root")
    rows.sort(key=lambda row: int(row["parent_depth"]))
    entropy_chain = sum(float(row["entropy_increment"]) for row in rows)
    if abs(entropy_chain - entropy_direct) > 2.0e-13:
        raise AssertionError(
            f"k={k}: entropy chain mismatch {entropy_chain} != {entropy_direct}"
        )
    return rows, entropy_chain, entropy_direct


def verify_patterns(
    rows: list[dict[str, object]],
    totals: dict[int, float],
) -> None:
    expected_count = sum(k - 1 for k in EXPECTED_LEVELS)
    if len(rows) != expected_count:
        raise AssertionError(f"expected {expected_count} rows, got {len(rows)}")

    for k in EXPECTED_LEVELS:
        profile = [
            float(row["entropy_increment"])
            for row in rows
            if int(row["k"]) == k
        ]
        if not all(left > right for left, right in zip(profile, profile[1:])):
            raise AssertionError(f"k={k}: entropy increments are not decreasing")
        if abs(totals[k] - EXPECTED_TOTAL_ENTROPY[k]) > 5.0e-12:
            raise AssertionError(f"k={k}: total entropy regression changed")

    for parent_depth in range(1, 12):
        sequence = [
            float(row["entropy_increment"])
            for row in rows
            if int(row["parent_depth"]) == parent_depth
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            left < right for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"depth {parent_depth}: expected increasing level sequence"
            )

    for terminal_offset in range(11):
        sequence = [
            float(row["entropy_increment"])
            for row in rows
            if int(row["terminal_offset"]) == terminal_offset
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            right < left for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"offset {terminal_offset}: expected decreasing sequence"
            )

    worst = max(rows, key=lambda row: float(row["increment_over_envelope"]))
    print(
        "PASS: floating entropy diagnostic on exact inputs, "
        f"{len(rows)} rows, worst envelope ratio="
        f"{float(worst['increment_over_envelope']):.12g} at k/depth="
        f"{int(worst['k'])}/{int(worst['parent_depth'])}"
    )
    print(
        "PASS: within-level depth decrease, fixed-depth level increase, "
        "and fixed-terminal-offset decrease"
    )


def write_rows(path: Path, rows: list[dict[str, object]]) -> None:
    if not rows:
        raise ValueError(f"refusing to write empty table {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {path} ({len(rows)} rows)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--levels", nargs="+", type=int, default=list(EXPECTED_LEVELS)
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--chunk-size", type=int, default=1_000_000)
    parser.add_argument("--skip-sha", action="store_true")
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("require a positive chunk size")
    requested_levels = tuple(args.levels)
    if (
        not requested_levels
        or tuple(sorted(set(requested_levels))) != requested_levels
        or any(k not in EXPECTED_LEVELS for k in requested_levels)
    ):
        parser.error("levels must be an increasing subset of 12 through 19")
    full_regression = requested_levels == EXPECTED_LEVELS
    if not full_regression and args.output.resolve() == DEFAULT_OUTPUT.resolve():
        parser.error("subset runs require a nondefault --output path")

    rows: list[dict[str, object]] = []
    totals: dict[int, float] = {}
    for k in requested_levels:
        level_rows, entropy_chain, entropy_direct_value = analyze_level(
            k, args.chunk_size, not args.skip_sha
        )
        rows.extend(level_rows)
        totals[k] = entropy_chain
        print(
            f"PASS: k={k}, {len(level_rows)} increments, "
            f"total entropy={entropy_chain:.12g}, chain error="
            f"{abs(entropy_chain - entropy_direct_value):.3g}"
        )
    rows.sort(key=lambda row: (int(row["k"]), int(row["parent_depth"])))
    if full_regression:
        verify_patterns(rows, totals)
    else:
        print("NOTE: subset run skips full-tower trend regressions")
    write_rows(args.output, rows)


if __name__ == "__main__":
    main()

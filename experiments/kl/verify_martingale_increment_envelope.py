#!/usr/bin/env python3
"""Verify exact L1 martingale increments of the KL certificate densities.

For a level-k certificate ``C`` and its exact genealogy masses ``A_j``, let
``f_(k,j)`` be the normalized density on the first j ternary digits.  Thus the
atoms of ``f_(k,j)`` carry the masses ``A_(j+1)``.  The adjacent conditional-
expectation increment is exactly

    Delta_(k,j) = ||f_(k,j) - f_(k,j-1)||_1
                = sum_children |3 A_(j+1) - A_j| / (3 sum C).

This script reconstructs every increment for the tracked inline manifests and
SHA-pinned exact sidecars at k=12,...,19, then checks the post-hoc finite envelope

    Delta_(k,j) <= (1/2) (9/10)^j,              j >= 2.

The envelope was selected after inspecting the available finite tower.  It is
therefore a compact theorem target and a future falsifier, not evidence for an
all-level theorem.  If the same estimate held uniformly for an all-level
family of appropriate critical densities, martingale telescoping would give

    ||f_k - E[f_k | F_J]||_1
      <= sum_(j>J) Delta_(k,j) <= 5 (9/10)^(J+1),   J >= 1,

which implies relative L1 compactness and forces the moving terminal
increments to vanish.

All generated fractions and envelope comparisons are exact.  Binary64 is
used only to sum radix limbs that are individually and collectively below
2^53, and to render already exact fractions as decimals.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from pathlib import Path

import numpy as np

import multiscale_genealogy as genealogy


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = (
    HERE / "analysis_cache" / "martingale_increments_exact.csv"
)
EXPECTED_LEVELS = tuple(range(12, 20))
FIRST_ENVELOPE_DEPTH = 2
ENVELOPE_SCALE = Fraction(1, 2)
ENVELOPE_RATIO = Fraction(9, 10)
INT64_MAX = np.iinfo(np.int64).max
FLOAT_EXACT_INT = 2**53 - 1
RADIX = 2**20


def exact_nonnegative_sum(
    values: np.ndarray, chunk_size: int
) -> int:
    """Sum a nonnegative int64/object array exactly with bounded radix limbs."""

    if len(values) == 0:
        return 0
    if values.dtype == object:
        return sum(int(value) for value in values)
    if values.dtype != np.int64:
        raise TypeError(f"expected int64 or object values, got {values.dtype}")
    minimum = int(values.min())
    if minimum < 0:
        raise ValueError("exact_nonnegative_sum received a negative value")

    max_high_limb = max(1, int(values.max()) // RADIX)
    safe_chunk = min(
        chunk_size,
        FLOAT_EXACT_INT // max_high_limb,
        FLOAT_EXACT_INT // (RADIX - 1),
    )
    if safe_chunk <= 0:
        raise OverflowError("no binary64-exact radix chunk is available")

    total = 0
    for start in range(0, len(values), safe_chunk):
        block = values[start : start + safe_chunk]
        high = block // RADIX
        low = block - high * RADIX
        high_sum = float(np.sum(high, dtype=np.float64))
        low_sum = float(np.sum(low, dtype=np.float64))
        if not high_sum.is_integer() or not low_sum.is_integer():
            raise AssertionError("binary64 radix sum lost integrality")
        total += int(high_sum) * RADIX + int(low_sum)
    return total


def coarsen_and_increment_numerator(
    children: np.ndarray, chunk_size: int
) -> tuple[np.ndarray, int]:
    """Return exact parents and ``sum |3 child - parent|``."""

    if len(children) % 3:
        raise ValueError("a 3-adic level must contain a multiple of three nodes")
    triples = children.reshape(3, -1)
    if children.dtype != object and int(children.max()) <= INT64_MAX // 3:
        parents = triples.sum(axis=0, dtype=np.int64)
        numerator = 0
        for digit in range(3):
            deviations = np.abs(3 * triples[digit] - parents)
            numerator += exact_nonnegative_sum(deviations, chunk_size)
        return parents, numerator

    triples = triples.astype(object, copy=False)
    parents = triples.sum(axis=0)
    numerator = 0
    for digit in range(3):
        deviations = np.abs(3 * triples[digit] - parents)
        numerator += exact_nonnegative_sum(deviations, chunk_size)
    return parents, numerator


def fraction_fields(prefix: str, value: Fraction) -> dict[str, object]:
    return {
        f"{prefix}_num": value.numerator,
        f"{prefix}_den": value.denominator,
        f"{prefix}_decimal": f"{float(value):.12g}",
    }


def analyze_level(
    k: int, chunk_size: int, verify_sha: bool
) -> list[dict[str, object]]:
    values, source, digest, hash_verified, hash_kind = (
        genealogy.load_certificate(k, verify_sha)
    )
    total_mass = exact_nonnegative_sum(values, chunk_size)
    children = values
    rows: list[dict[str, object]] = []

    for parent_depth in range(k - 1, 0, -1):
        parents, deviation_sum = coarsen_and_increment_numerator(
            children, chunk_size
        )
        if exact_nonnegative_sum(parents, chunk_size) != total_mass:
            raise AssertionError(f"k={k}, depth={parent_depth}: mass changed")

        delta = Fraction(deviation_sum, 3 * total_mass)
        envelope = ENVELOPE_SCALE * ENVELOPE_RATIO**parent_depth
        applies = parent_depth >= FIRST_ENVELOPE_DEPTH
        passes = delta <= envelope
        if applies and not passes:
            raise AssertionError(
                f"k={k}, depth={parent_depth}: {delta} > {envelope}"
            )

        rows.append({
            "k": k,
            "parent_depth": parent_depth,
            "child_depth": parent_depth + 1,
            "terminal_offset": k - 1 - parent_depth,
            "parent_node_count": len(parents),
            "child_node_count": len(children),
            **fraction_fields("martingale_increment", delta),
            **fraction_fields("envelope", envelope),
            **fraction_fields("increment_over_envelope", delta / envelope),
            **fraction_fields("envelope_slack", envelope - delta),
            "envelope_applies": applies,
            "passes_envelope": passes,
            "envelope_scope": "post_hoc_k12_through_float_k20",
            "source_kind": "exact_feasible_certificate",
            "source": source,
            "source_sha256": digest,
            "source_sha256_verified": hash_verified,
            "source_sha256_kind": hash_kind,
        })
        children = parents

    if len(children) != 1 or int(children[0]) != total_mass:
        raise AssertionError(f"k={k}: hierarchy did not reach the exact root")
    return rows


def verify_patterns(rows: list[dict[str, object]]) -> None:
    def delta(row: dict[str, object]) -> Fraction:
        return Fraction(
            int(row["martingale_increment_num"]),
            int(row["martingale_increment_den"]),
        )

    expected_count = sum(k - 1 for k in EXPECTED_LEVELS)
    if len(rows) != expected_count:
        raise AssertionError(
            f"expected {expected_count} increment rows, got {len(rows)}"
        )

    for parent_depth in range(1, 12):
        sequence = [
            delta(row)
            for row in rows
            if int(row["parent_depth"]) == parent_depth
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            left < right for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"depth {parent_depth}: expected increasing level sequence"
            )

    for terminal_offset in range(5):
        sequence = [
            delta(row)
            for row in rows
            if int(row["terminal_offset"]) == terminal_offset
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            right < left for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"offset {terminal_offset}: expected decreasing sequence"
            )

    applicable = [row for row in rows if bool(row["envelope_applies"])]
    worst = max(
        applicable,
        key=lambda row: Fraction(
            int(row["increment_over_envelope_num"]),
            int(row["increment_over_envelope_den"]),
        ),
    )
    if (int(worst["k"]), int(worst["parent_depth"])) != (19, 2):
        raise AssertionError("exact envelope maximum location changed")
    print(
        "PASS: exact martingale envelope, "
        f"{len(applicable)} applicable/{len(rows)} total rows, "
        "worst ratio="
        f"{float(worst['increment_over_envelope_decimal']):.12g} "
        f"at k/depth={int(worst['k'])}/{int(worst['parent_depth'])}"
    )
    print("PASS: fixed-depth increase and fixed-terminal-offset decrease")


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
    for k in requested_levels:
        level_rows = analyze_level(k, args.chunk_size, not args.skip_sha)
        rows.extend(level_rows)
        terminal = level_rows[0]
        print(
            f"PASS: k={k}, {len(level_rows)} increments, terminal="
            f"{terminal['martingale_increment_decimal']}"
        )
    rows.sort(key=lambda row: (int(row["k"]), int(row["parent_depth"])))
    if full_regression:
        verify_patterns(rows)
    else:
        print("NOTE: subset run skips full-tower trend regressions")
    write_rows(args.output, rows)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Provisional floating k=20 holdout for the exact-data weighted cones.

This script applies the rational cone witnesses in
``verify_weighted_bin_cone.py`` to the local float64 vector
``eigvec_k20.npy``.  That 8.7 GiB sidecar is not an exact feasible certificate
and is intentionally not tracked by git.  Consequently this audit can falsify
numerical stability of a proposed cone, but it cannot certify or confirm an
exact k=20 statement.

The source SHA-256 is pinned.  Coarsening follows the same three-block 3-adic
indexing as ``multiscale_genealogy.py``.  Float64 is used throughout; threshold
gaps and mass-conservation errors are recorded, and floating point appears in
every substantive output column.  The default run peaks near 23 GB RSS.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
from fractions import Fraction
from pathlib import Path

import numpy as np

import verify_weighted_bin_cone as exact


HERE = Path(__file__).resolve().parent
DEFAULT_INPUT = HERE / "eigvec_k20.npy"
DEFAULT_CONE_OUTPUT = (
    HERE / "analysis_cache" / "float_k20_weighted_cone_rows.csv"
)
DEFAULT_RECURRENCE_OUTPUT = (
    HERE / "analysis_cache" / "float_k20_weighted_recurrence.csv"
)
EXPECTED_SHA256 = (
    "35fa2453500ce4dec5d8a504e7dc29acd8d4088d4d3ebdc366b2f8796fb91681"
)
K = 20
EXPECTED_SIZE = 3 ** (K - 1)


def sha256_file(path: Path, chunk_bytes: int = 8 << 20) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(chunk_bytes):
            digest.update(block)
    return digest.hexdigest()


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


def float_fields(prefix: str, value: float) -> dict[str, object]:
    return {prefix: f"{value:.17g}"}


def coarsen_and_classify(
    children: np.ndarray, chunk_size: int
) -> tuple[np.ndarray, np.ndarray, float]:
    if len(children) % 3:
        raise ValueError("a 3-adic level must contain a multiple of three nodes")
    triples = children.reshape(3, -1)
    parents = triples.sum(axis=0, dtype=np.float64)
    minima = triples.min(axis=0)
    score = triples.max(axis=0)
    score -= minima
    del minima
    score *= 3.0
    score /= parents

    categories = np.zeros(len(parents), dtype=np.uint8)
    minimum_gap = float("inf")
    for threshold in exact.THRESHOLDS:
        threshold_float = float(threshold)
        for start in range(0, len(score), chunk_size):
            end = min(len(score), start + chunk_size)
            block = score[start:end]
            categories[start:end] += block > threshold_float
            gap = float(np.min(np.abs(block - threshold_float)))
            minimum_gap = min(minimum_gap, gap)
    return parents, categories, minimum_gap


def transition_cells(
    parent_categories: np.ndarray,
    child_categories: np.ndarray,
    child_masses: np.ndarray,
    chunk_size: int,
) -> np.ndarray:
    parent_count = len(parent_categories)
    if len(child_categories) != 3 * parent_count:
        raise ValueError("each parent must have exactly three child nodes")
    cells = np.zeros(64, dtype=np.float64)
    for digit in range(3):
        child_start = digit * parent_count
        for start in range(0, parent_count, chunk_size):
            end = min(parent_count, start + chunk_size)
            child_slice = slice(child_start + start, child_start + end)
            codes = (
                parent_categories[start:end] * 8
                + child_categories[child_slice]
            )
            cells += np.bincount(
                codes, weights=child_masses[child_slice], minlength=64
            )
    return cells.reshape(8, 8)


def analyze_transition(
    parent_depth: int,
    cells: np.ndarray,
    total_mass: float,
    parent_gap: float,
    child_gap: float,
    source_name: str,
    source_sha256: str,
    source_sha256_verified: bool,
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    cone_rows: list[dict[str, object]] = []
    recurrence_rows: list[dict[str, object]] = []
    parent_masses = cells.sum(axis=1)
    child_masses = cells.sum(axis=0)
    conservation_error = abs(float(cells.sum()) - total_mass) / total_mass

    for spec in exact.CONE_SPECS:
        if parent_depth < spec.first_parent_depth:
            continue
        high = spec.first_high_bin
        weights = np.asarray([float(weight) for weight in spec.weights])
        rho = float(spec.rho)

        parent_potential = float(parent_masses[high:] @ weights / total_mass)
        persistent = float(
            (cells[high:, high:] * weights[np.newaxis, :]).sum()
            / total_mass
        )
        immigration = float(
            (cells[:high, high:] * weights[np.newaxis, :]).sum()
            / total_mass
        )
        child_potential = float(child_masses[high:] @ weights / total_mass)
        recurrence_error = abs(child_potential - persistent - immigration)

        recurrence_rows.append({
            "threshold": str(spec.threshold),
            "k": K,
            "parent_depth": parent_depth,
            "child_depth": parent_depth + 1,
            "terminal_offset": K - 2 - parent_depth,
            "first_parent_depth": spec.first_parent_depth,
            "weights": exact.weight_string(spec.weights),
            **float_fields("rho", rho),
            **float_fields("parent_potential", parent_potential),
            **float_fields("persistent_potential", persistent),
            **float_fields("immigration_potential", immigration),
            **float_fields("child_potential", child_potential),
            **float_fields(
                "realized_retention", persistent / parent_potential
            ),
            **float_fields("recurrence_absolute_error", recurrence_error),
            **float_fields("mass_relative_error", conservation_error),
            **float_fields("parent_minimum_threshold_gap", parent_gap),
            **float_fields("child_minimum_threshold_gap", child_gap),
            **float_fields("total_mass", total_mass),
            "source_kind": "uncertified_float_candidate",
            "source": source_name,
            "source_sha256": source_sha256,
            "source_sha256_verified": source_sha256_verified,
        })

        for parent_bin in range(high, 8):
            parent_mass = float(parent_masses[parent_bin])
            if parent_mass == 0.0:
                continue
            weighted_child = float(cells[parent_bin, high:] @ weights)
            weighted_parent = parent_mass * weights[parent_bin - high]
            ratio = weighted_child / weighted_parent
            cone_rows.append({
                "threshold": str(spec.threshold),
                "k": K,
                "parent_depth": parent_depth,
                "child_depth": parent_depth + 1,
                "parent_bin": parent_bin,
                "first_parent_depth": spec.first_parent_depth,
                "weights": exact.weight_string(spec.weights),
                **float_fields("rho", rho),
                **float_fields("parent_bin_mass", parent_mass),
                **float_fields("weighted_high_child_mass", weighted_child),
                **float_fields("weighted_parent_mass", weighted_parent),
                **float_fields("ratio", ratio),
                **float_fields("ratio_minus_rho", ratio - rho),
                "passes": ratio <= rho,
                **float_fields("mass_relative_error", conservation_error),
                **float_fields("parent_minimum_threshold_gap", parent_gap),
                **float_fields("child_minimum_threshold_gap", child_gap),
                "source_kind": "uncertified_float_candidate",
                "source": source_name,
                "source_sha256": source_sha256,
                "source_sha256_verified": source_sha256_verified,
            })
    return cone_rows, recurrence_rows


def check_expected_summary(cone_rows: list[dict[str, object]]) -> None:
    expected = {
        "1/5": {
            "rows": 61,
            "matrices": 16,
            "violations": 2,
            "maximum": 0.9941725429887102,
            "location": (3, 7),
            "shifted_rows": 59,
            "shifted_matrices": 15,
            "shifted_maximum": 0.9763329303398277,
            "shifted_location": (4, 4),
        },
        "3/10": {
            "rows": 31,
            "matrices": 17,
            "violations": 1,
            "maximum": 0.8955761683443402,
            "location": (2, 7),
            "shifted_rows": 30,
            "shifted_matrices": 16,
            "shifted_maximum": 0.8332516990705758,
            "shifted_location": (3, 7),
        },
    }
    for threshold, target in expected.items():
        rows = [row for row in cone_rows if row["threshold"] == threshold]
        matrices = {(row["parent_depth"], row["child_depth"]) for row in rows}
        violations = [row for row in rows if not bool(row["passes"])]
        worst = max(rows, key=lambda row: float(row["ratio"]))
        maximum = float(worst["ratio"])
        location = (int(worst["parent_depth"]), int(worst["parent_bin"]))
        if len(rows) != target["rows"]:
            raise AssertionError(f"{threshold}: row count changed")
        if len(matrices) != target["matrices"]:
            raise AssertionError(f"{threshold}: matrix count changed")
        if len(violations) != target["violations"]:
            raise AssertionError(f"{threshold}: violation count changed")
        if abs(maximum - target["maximum"]) > 1e-12:
            raise AssertionError(f"{threshold}: maximum changed")
        if location != target["location"]:
            raise AssertionError(f"{threshold}: maximum location changed")

        shifted = [
            row
            for row in rows
            if int(row["parent_depth"]) >= int(row["first_parent_depth"]) + 1
        ]
        shifted_matrices = {
            (row["parent_depth"], row["child_depth"]) for row in shifted
        }
        shifted_worst = max(shifted, key=lambda row: float(row["ratio"]))
        shifted_maximum = float(shifted_worst["ratio"])
        shifted_location = (
            int(shifted_worst["parent_depth"]),
            int(shifted_worst["parent_bin"]),
        )
        if len(shifted) != target["shifted_rows"]:
            raise AssertionError(f"{threshold}: shifted row count changed")
        if len(shifted_matrices) != target["shifted_matrices"]:
            raise AssertionError(f"{threshold}: shifted matrix count changed")
        if abs(shifted_maximum - target["shifted_maximum"]) > 1e-12:
            raise AssertionError(f"{threshold}: shifted maximum changed")
        if shifted_location != target["shifted_location"]:
            raise AssertionError(f"{threshold}: shifted maximum location changed")
        rho = float(rows[0]["rho"])
        print(
            f"FLOAT FALSIFIER: t={threshold}, rows={len(rows)}, "
            f"violations={len(violations)}, max={maximum:.12g} at "
            f"depth/bin={location}; after one extra burn-in, "
            f"max={shifted_maximum:.12g} at depth/bin={shifted_location} "
            f"< rho={rho:.12g}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--cone-output", type=Path, default=DEFAULT_CONE_OUTPUT)
    parser.add_argument(
        "--recurrence-output", type=Path, default=DEFAULT_RECURRENCE_OUTPUT
    )
    parser.add_argument("--chunk-size", type=int, default=1_000_000)
    parser.add_argument("--skip-sha", action="store_true")
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("require a positive chunk size")

    digest = sha256_file(args.input)
    if not args.skip_sha and digest != EXPECTED_SHA256:
        raise ValueError(
            f"SHA-256 mismatch for {args.input}: expected {EXPECTED_SHA256}, "
            f"got {digest}"
        )
    values = np.load(args.input, mmap_mode="r")
    if values.shape != (EXPECTED_SIZE,) or values.dtype != np.float64:
        raise ValueError(
            f"expected float64 shape ({EXPECTED_SIZE},), got "
            f"{values.dtype} {values.shape}"
        )
    minimum = float(values.min())
    maximum = float(values.max())
    total_mass = float(values.sum(dtype=np.float64))
    if not np.isfinite([minimum, maximum, total_mass]).all() or minimum <= 0:
        raise ValueError("float candidate must be finite and strictly positive")
    print(
        f"source shape={values.shape}, min={minimum:.17g}, "
        f"max={maximum:.17g}, total={total_mass:.17g}"
    )

    all_cone_rows: list[dict[str, object]] = []
    all_recurrence_rows: list[dict[str, object]] = []
    finer_masses: np.ndarray | None = None
    finer_categories: np.ndarray | None = None
    finer_gap: float | None = None
    children: np.ndarray = values

    for depth in range(K - 1, 0, -1):
        node_masses, categories, gap = coarsen_and_classify(
            children, args.chunk_size
        )
        if finer_masses is not None:
            assert finer_categories is not None and finer_gap is not None
            cells = transition_cells(
                categories, finer_categories, finer_masses, args.chunk_size
            )
            cone_rows, recurrence_rows = analyze_transition(
                depth,
                cells,
                total_mass,
                gap,
                finer_gap,
                args.input.name,
                digest,
                not args.skip_sha,
            )
            all_cone_rows.extend(cone_rows)
            all_recurrence_rows.extend(recurrence_rows)
        finer_masses = node_masses
        finer_categories = categories
        finer_gap = gap
        children = node_masses

    if len(children) != 1:
        raise AssertionError("3-adic hierarchy did not coarsen to one root")
    root_relative_error = abs(float(children[0]) - total_mass) / total_mass
    print(f"root relative mass error={root_relative_error:.3g}")
    check_expected_summary(all_cone_rows)
    all_cone_rows.sort(
        key=lambda row: (
            exact.THRESHOLDS.index(Fraction(row["threshold"])),
            int(row["parent_depth"]),
            int(row["parent_bin"]),
        )
    )
    all_recurrence_rows.sort(
        key=lambda row: (
            exact.THRESHOLDS.index(Fraction(row["threshold"])),
            int(row["parent_depth"]),
        )
    )
    write_rows(args.cone_output, all_cone_rows)
    write_rows(args.recurrence_output, all_recurrence_rows)


if __name__ == "__main__":
    main()

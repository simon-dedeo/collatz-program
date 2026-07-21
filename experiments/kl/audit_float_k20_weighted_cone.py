#!/usr/bin/env python3
"""Provisional floating k=20 audit for the exact-data weighted cones.

This script applies the seven-threshold rational cone frontier and the original
preregistered ``t=1/5`` witness from ``verify_weighted_bin_cone.py`` to the
local float64 vector
``eigvec_k20.npy``.  That 8.7 GiB sidecar is not an exact feasible certificate
and is intentionally not tracked by git.  Consequently this audit can falsify
a proposed exact-data margin and provisionally test qualitative contraction,
but it cannot certify or confirm an exact k=20 statement.

The source SHA-256 is pinned.  Coarsening follows the same three-block 3-adic
indexing as ``multiscale_genealogy.py``.  Float64 is used throughout; threshold
gaps and mass-conservation errors are recorded, and floating point appears in
every substantive output column.  The default run peaks near 23 GB RSS.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
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
FLOAT_SPECS = exact.CONE_SPECS + exact.PREREGISTERED_CONE_SPECS


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

    for spec in FLOAT_SPECS:
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
            "spec_name": spec.name,
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
                "spec_name": spec.name,
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
                "contracts": ratio < 1.0,
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
        "frontier_t_1_20": (91, 13, 1, 0, 0.99514995432466358, (6, 2),
                             84, 12, 0.9919763645834655, (7, 7)),
        "frontier_t_1_10": (89, 16, 2, 0, 0.99975874832582279, (3, 7),
                             87, 15, 0.9995309724658249, (4, 4)),
        "frontier_t_3_20": (75, 16, 2, 0, 0.99738611814473221, (3, 7),
                             73, 15, 0.99490860633569156, (4, 4)),
        "frontier_t_1_5": (61, 16, 2, 0, 0.9938806602034661, (3, 7),
                            59, 15, 0.98026146188639796, (4, 4)),
        "frontier_t_1_4": (46, 16, 2, 0, 0.93382479353776293, (3, 7),
                            44, 15, 0.84778007179143022, (4, 7)),
        "frontier_t_3_10": (31, 17, 1, 0, 0.89557616834434017, (2, 7),
                             30, 16, 0.8332516990709159, (3, 7)),
        "frontier_t_2_5": (17, 17, 1, 0, 0.89557616834434017, (2, 7),
                            16, 16, 0.8332516990709159, (3, 7)),
        "preregistered_t_1_5": (
            61, 16, 2, 0, 0.99417254298871016, (3, 7),
            59, 15, 0.97633293034002711, (4, 4),
        ),
    }
    if set(expected) != {spec.name for spec in FLOAT_SPECS}:
        raise AssertionError("floating summary specs changed")

    for spec in FLOAT_SPECS:
        target = expected[spec.name]
        rows = [row for row in cone_rows if row["spec_name"] == spec.name]
        matrices = {(row["parent_depth"], row["child_depth"]) for row in rows}
        violations = [row for row in rows if not bool(row["passes"])]
        unit_violations = [row for row in rows if not bool(row["contracts"])]
        worst = max(rows, key=lambda row: float(row["ratio"]))
        maximum = float(worst["ratio"])
        location = (int(worst["parent_depth"]), int(worst["parent_bin"]))

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
        observed_discrete = (
            len(rows),
            len(matrices),
            len(violations),
            len(unit_violations),
            location,
            len(shifted),
            len(shifted_matrices),
            shifted_location,
        )
        expected_discrete = (
            target[0], target[1], target[2], target[3], target[5],
            target[6], target[7], target[9],
        )
        if observed_discrete != expected_discrete:
            raise AssertionError(
                f"{spec.name}: floating discrete summary changed: "
                f"{observed_discrete} != {expected_discrete}"
            )
        if abs(maximum - target[4]) > 1e-12:
            raise AssertionError(f"{spec.name}: floating maximum changed")
        if abs(shifted_maximum - target[8]) > 1e-12:
            raise AssertionError(
                f"{spec.name}: shifted floating maximum changed"
            )
        rho = float(rows[0]["rho"])
        print(
            f"FLOAT AUDIT: {spec.name}, rows/matrices="
            f"{len(rows)}/{len(matrices)}, rho violations="
            f"{len(violations)}, unit violations={len(unit_violations)}, "
            f"max={maximum:.12g} at depth/bin={location}; after one "
            f"extra burn-in, rows/matrices={len(shifted)}/"
            f"{len(shifted_matrices)}, "
            f"max={shifted_maximum:.12g} at depth/bin={shifted_location} "
            f"versus rho={rho:.12g}"
        )


def check_expected_immigration_summary(
    recurrence_rows: list[dict[str, object]],
) -> None:
    expected_k20 = {
        "frontier_t_1_20": (
            0.13436942114963304,
            0.11950714601259599,
            0.11812143706780046,
            0.10841316047888633,
            0.090004602862998315,
        ),
        "frontier_t_1_5": (
            0.0071675743321247256,
            0.014311721607429526,
            0.02852967703265695,
            0.050015499811874142,
            0.069178869534380127,
        ),
        "frontier_t_3_10": (
            0.00075581062316027565,
            0.0024510937749100945,
            0.0058329025414332273,
            0.012743697266712112,
            0.019261244488348244,
        ),
    }
    exact_k19 = {
        "frontier_t_1_20": (
            0.138297954298,
            0.117606935642,
            0.110456641856,
            0.0972237178444,
            0.0774336265414,
        ),
        "frontier_t_1_5": (
            0.00857462496819,
            0.0171791992247,
            0.0344159645883,
            0.0597948574014,
            0.0818344592235,
        ),
        "frontier_t_3_10": (
            0.000888976853819,
            0.00295249425926,
            0.00717137934039,
            0.0156453291614,
            0.0235595995234,
        ),
    }

    for spec_name, expected in expected_k20.items():
        rows = sorted(
            (row for row in recurrence_rows if row["spec_name"] == spec_name),
            key=lambda row: int(row["terminal_offset"]),
        )
        observed = tuple(
            float(row["immigration_potential"])
            for row in rows
            if int(row["terminal_offset"]) < 5
        )
        if len(observed) != 5 or any(
            abs(left - right) > 1e-12
            for left, right in zip(observed, expected)
        ):
            raise AssertionError(f"{spec_name}: k20 immigration changed")

        previous = exact_k19[spec_name]
        if spec_name == "frontier_t_1_20":
            if not all(observed[offset] > previous[offset] for offset in range(1, 5)):
                raise AssertionError("t=1/20 adverse immigration trend changed")
        elif not all(right < left for left, right in zip(previous, observed)):
            raise AssertionError(f"{spec_name}: favorable immigration trend changed")
    print("PASS: floating fixed-offset immigration trend regressions")


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
    check_expected_immigration_summary(all_recurrence_rows)
    all_cone_rows.sort(
        key=lambda row: (
            tuple(spec.name for spec in FLOAT_SPECS).index(row["spec_name"]),
            int(row["parent_depth"]),
            int(row["parent_bin"]),
        )
    )
    all_recurrence_rows.sort(
        key=lambda row: (
            tuple(spec.name for spec in FLOAT_SPECS).index(row["spec_name"]),
            int(row["parent_depth"]),
        )
    )
    write_rows(args.cone_output, all_cone_rows)
    write_rows(args.recurrence_output, all_recurrence_rows)


if __name__ == "__main__":
    main()

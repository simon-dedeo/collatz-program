#!/usr/bin/env python3
"""Exact within-vector 3-adic oscillation genealogy for KL certificates.

For a level-k certificate ``C[i]``, where the paper state is ``m=2+3*i``, let

    A_j(p) = sum { C[i] : i == p (mod 3^(j-1)) },   1 <= j <= k.

Thus ``A_k=C`` and every depth-j node has the three depth-(j+1) children
``p+d*3^(j-1)``, d=0,1,2.  Its exact normalized oscillation is

    omega_j(p) = 3 * (max_child A_(j+1) - min_child A_(j+1)) / A_j(p).

At j=k-1 this is the ordinary one-step fiber oscillation, and weighting a
node by A_j(p) gives exactly the mass measure used in Proposition R'.  The
script records exact rational tail masses at several thresholds and, between
successive depths, the identity

    M_(j+1)(t) = q_(k,j)(t,t') M_j(t') + E_(k,j)(t,t'),

where q is the fraction of high-parent mass retained in high children and E
is high-child mass immigrating from low parents.  This is a diagnostic
identity, not an asserted uniform recurrence theorem.

The coarser ``A_j`` are conditional aggregates inside one fixed feasible
vector.  They are not asserted to be KL eigenvectors or feasible vectors at a
lower KL level.

All classifications and reported mass totals are exact integers.  Large totals
are accumulated through radix limbs; binary64 ``bincount`` is used only where
an explicit below-2^53 bound makes the integer additions exact, and otherwise
only to render decimal columns.  The default inputs are the SHA-pinned exact
feasible subeigenvectors at k=12,...,19.  The in-memory hierarchy peaks near
16 GB at k=19; use ``--levels`` to run large levels separately on smaller
machines.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable

import numpy as np


HERE = Path(__file__).resolve().parent
DEFAULT_TAIL_OUTPUT = HERE / "analysis_cache" / "multiscale_tail_exact.csv"
DEFAULT_TRANSITION_OUTPUT = (
    HERE / "analysis_cache" / "multiscale_transitions_exact.csv"
)
DEFAULT_SUMMARY_OUTPUT = (
    HERE / "analysis_cache" / "multiscale_recurrence_summary.csv"
)
DEFAULT_THRESHOLDS = tuple(
    Fraction(x)
    for x in ("1/20", "1/10", "3/20", "1/5", "1/4", "3/10", "2/5")
)
INT64_MAX = np.iinfo(np.int64).max
FLOAT_EXACT_INT = 2**53 - 1
RADIX = 2**20


def sha256_file(path: Path, chunk_bytes: int = 8 << 20) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(chunk_bytes):
            digest.update(block)
    return digest.hexdigest()


def load_certificate(k: int, verify_sha: bool):
    manifest_path = HERE / f"cert_k{k}.json"
    manifest = json.loads(manifest_path.read_text())
    if manifest["k"] != k:
        raise ValueError(f"{manifest_path}: expected k={k}")

    if "C_file" in manifest:
        source_path = HERE / manifest["C_file"]
        if not source_path.exists():
            raise FileNotFoundError(
                f"missing local sidecar {source_path}; large exact arrays are "
                "intentionally not tracked by git"
            )
        expected_sha = manifest["C_sha256"]
        if verify_sha:
            actual_sha = sha256_file(source_path)
            if actual_sha != expected_sha:
                raise ValueError(
                    f"SHA-256 mismatch for {source_path}: expected "
                    f"{expected_sha}, got {actual_sha}"
                )
        hash_verified = verify_sha
        values = np.load(source_path, mmap_mode="r")
        source_name = source_path.name
        hash_kind = "array"
    else:
        values = np.asarray(manifest["C"], dtype=np.int64)
        expected_sha = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
        hash_verified = True
        source_name = manifest_path.name
        hash_kind = "manifest"

    expected_size = 3 ** (k - 1)
    if values.ndim != 1 or len(values) != expected_size:
        raise ValueError(
            f"{source_name}: expected {expected_size} coordinates, "
            f"got shape {values.shape}"
        )
    if values.dtype != np.int64:
        raise TypeError(f"{source_name}: expected int64, got {values.dtype}")
    if int(values.min()) <= 0:
        raise ValueError(f"{source_name}: coordinates must be positive")
    return values, source_name, expected_sha, hash_verified, hash_kind


def exact_exceeds(
    differences: np.ndarray, sums: np.ndarray, threshold: Fraction
) -> np.ndarray:
    """Return ``3*difference/sum > threshold`` without overflowing int64."""

    a, b = threshold.numerator, threshold.denominator
    multiplier = 3 * b
    if not (0 < a < multiplier):
        raise ValueError("oscillation thresholds must lie strictly between 0 and 3")

    if differences.dtype == object or sums.dtype == object:
        return np.fromiter(
            (
                multiplier * int(difference) > a * int(total)
                for difference, total in zip(differences, sums, strict=True)
            ),
            dtype=bool,
            count=len(sums),
        )

    # Write sum = multiplier*q+r.  The desired comparison becomes
    # multiplier*(difference-a*q) > a*r.  If the parenthesized integer is at
    # least a, the inequality is automatic because r<multiplier; only the
    # tiny range 0<z<a needs a multiplication.
    quotient = sums // multiplier
    remainder = sums % multiplier
    z = differences - a * quotient
    result = z >= a
    ambiguous = (z > 0) & (z < a)
    if np.any(ambiguous):
        result[ambiguous] = (
            multiplier * z[ambiguous] > a * remainder[ambiguous]
        )
    return result


def coarsen_and_classify(
    children: np.ndarray, thresholds: tuple[Fraction, ...]
) -> tuple[np.ndarray, np.ndarray]:
    """Sum triples into parents and classify their exact oscillations."""

    if len(children) % 3:
        raise ValueError("a 3-adic level must contain a multiple of three nodes")
    triples = children.reshape(3, -1)
    if children.dtype != object and int(children.max()) <= INT64_MAX // 3:
        parents = triples.sum(axis=0, dtype=np.int64)
        minima = triples.min(axis=0)
        maxima = triples.max(axis=0)
    else:
        triples = triples.astype(object, copy=False)
        parents = triples.sum(axis=0)
        minima = triples.min(axis=0)
        maxima = triples.max(axis=0)

    differences = maxima - minima
    categories = np.zeros(len(parents), dtype=np.uint8)
    for threshold in thresholds:
        categories += exact_exceeds(differences, parents, threshold)
    return parents, categories


def exact_histogram(
    categories: np.ndarray, weights: np.ndarray, category_count: int,
    chunk_size: int
) -> tuple[list[int], list[int]]:
    """Exact counts and weighted sums by category.

    For int64 weights, each number is split into base-2^20 limbs.  Chunk sizes
    are capped so every positive weighted ``bincount`` total is below 2^53;
    binary64 therefore represents and adds every integer exactly.  Chunk
    results are immediately converted back to Python integers.  Object arrays
    occur only after the hierarchy has become small and use direct Python sums.
    """

    if len(categories) != len(weights):
        raise ValueError("category and weight arrays must have equal length")
    if len(categories) and (
        int(categories.min()) < 0 or int(categories.max()) >= category_count
    ):
        raise ValueError("category lies outside the requested histogram range")
    counts = [0] * category_count
    masses = [0] * category_count
    if len(weights) == 0:
        return counts, masses

    if weights.dtype == object:
        for category, weight in zip(categories, weights, strict=True):
            index = int(category)
            counts[index] += 1
            masses[index] += int(weight)
        return counts, masses

    max_high_limb = max(1, int(weights.max()) // RADIX)
    safe_chunk = min(
        chunk_size,
        FLOAT_EXACT_INT // max_high_limb,
        FLOAT_EXACT_INT // (RADIX - 1),
    )
    if safe_chunk <= 0:
        raise OverflowError("no binary64-exact histogram chunk is available")

    for start in range(0, len(weights), safe_chunk):
        end = min(len(weights), start + safe_chunk)
        cats = np.asarray(categories[start:end], dtype=np.int64)
        vals = np.asarray(weights[start:end], dtype=np.int64)
        high = vals // RADIX
        low = vals - high * RADIX
        chunk_counts = np.bincount(cats, minlength=category_count)
        high_bins = np.bincount(
            cats, weights=high.astype(np.float64), minlength=category_count
        )
        low_bins = np.bincount(
            cats, weights=low.astype(np.float64), minlength=category_count
        )
        for index in range(category_count):
            high_value = float(high_bins[index])
            low_value = float(low_bins[index])
            if not high_value.is_integer() or not low_value.is_integer():
                raise AssertionError("binary64 limb histogram lost integrality")
            counts[index] += int(chunk_counts[index])
            masses[index] += int(high_value) * RADIX + int(low_value)
    return counts, masses


def transition_histogram(
    parent_categories: np.ndarray, child_categories: np.ndarray,
    child_masses: np.ndarray, category_count: int, chunk_size: int
) -> tuple[list[list[int]], list[list[int]]]:
    """Return exact parent-category by child-category count/mass matrices."""

    parent_count = len(parent_categories)
    if len(child_categories) != 3 * parent_count:
        raise ValueError("each genealogy parent must have exactly three children")
    count_matrix = [[0] * category_count for _ in range(category_count)]
    mass_matrix = [[0] * category_count for _ in range(category_count)]
    for digit in range(3):
        start, end = digit * parent_count, (digit + 1) * parent_count
        joint = (
            parent_categories.astype(np.int16) * category_count
            + child_categories[start:end].astype(np.int16)
        )
        counts, masses = exact_histogram(
            joint, child_masses[start:end], category_count**2, chunk_size
        )
        for code in range(category_count**2):
            parent_category, child_category = divmod(code, category_count)
            count_matrix[parent_category][child_category] += counts[code]
            mass_matrix[parent_category][child_category] += masses[code]
    return count_matrix, mass_matrix


def rational_fields(prefix: str, numerator: int, denominator: int) -> dict[str, object]:
    if denominator == 0:
        return {
            f"{prefix}_num": "",
            f"{prefix}_den": "",
            f"{prefix}_decimal": "",
        }
    ratio = Fraction(numerator, denominator)
    return {
        f"{prefix}_num": ratio.numerator,
        f"{prefix}_den": ratio.denominator,
        f"{prefix}_decimal": f"{float(ratio):.12g}",
    }


def source_fields(
    source: str, source_sha256: str, source_sha256_verified: bool,
    source_sha256_kind: str
) -> dict[str, object]:
    return {
        "source": source,
        "source_sha256": source_sha256,
        "source_sha256_verified": source_sha256_verified,
        "source_sha256_kind": source_sha256_kind,
    }


def analyze_level(
    k: int, thresholds: tuple[Fraction, ...], chunk_size: int,
    verify_sha: bool
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    values, source, digest, hash_verified, hash_kind = load_certificate(
        k, verify_sha
    )
    category_count = len(thresholds) + 1
    total_counts, total_masses = exact_histogram(
        np.zeros(len(values), dtype=np.uint8), values, 1, chunk_size
    )
    if total_counts != [len(values)]:
        raise AssertionError("exact total count failed")
    total_mass = total_masses[0]
    provenance = source_fields(source, digest, hash_verified, hash_kind)

    tail_rows: list[dict[str, object]] = []
    transition_rows: list[dict[str, object]] = []
    finer_masses: np.ndarray | None = None
    finer_categories: np.ndarray | None = None
    finer_depth: int | None = None
    children: np.ndarray = values

    for depth in range(k - 1, 0, -1):
        node_masses, categories = coarsen_and_classify(children, thresholds)
        counts_by_category, masses_by_category = exact_histogram(
            categories, node_masses, category_count, chunk_size
        )
        if sum(counts_by_category) != len(node_masses):
            raise AssertionError("oscillation categories do not partition nodes")
        if sum(masses_by_category) != total_mass:
            raise AssertionError("node masses do not partition certificate mass")

        for threshold_index, threshold in enumerate(thresholds):
            high_count = sum(counts_by_category[threshold_index + 1 :])
            high_mass = sum(masses_by_category[threshold_index + 1 :])
            row = {
                "k": k,
                "depth": depth,
                "coarsenings_from_finest": k - 1 - depth,
                "threshold": str(threshold),
                "threshold_num": threshold.numerator,
                "threshold_den": threshold.denominator,
                "node_count": len(node_masses),
                "high_node_count": high_count,
                "high_mass": high_mass,
                "total_mass": total_mass,
                **rational_fields("tail", high_mass, total_mass),
                **provenance,
            }
            tail_rows.append(row)

        if finer_masses is not None:
            assert finer_categories is not None and finer_depth == depth + 1
            count_matrix, mass_matrix = transition_histogram(
                categories, finer_categories, finer_masses,
                category_count, chunk_size
            )
            multiplicity_tables: list[tuple[list[list[int]], list[list[int]]]] = []
            parent_count = len(categories)
            for child_index in range(len(thresholds)):
                multiplicity = np.zeros(parent_count, dtype=np.uint8)
                for digit in range(3):
                    start, end = digit * parent_count, (digit + 1) * parent_count
                    multiplicity += (
                        finer_categories[start:end] >= child_index + 1
                    )
                joint = categories.astype(np.int16) * 4 + multiplicity
                multiplicity_counts, multiplicity_masses = exact_histogram(
                    joint, node_masses, category_count * 4, chunk_size
                )
                multiplicity_tables.append((
                    [
                        multiplicity_counts[4 * category : 4 * category + 4]
                        for category in range(category_count)
                    ],
                    [
                        multiplicity_masses[4 * category : 4 * category + 4]
                        for category in range(category_count)
                    ],
                ))
            for parent_index, parent_threshold in enumerate(thresholds):
                parent_high_count = sum(counts_by_category[parent_index + 1 :])
                parent_high_mass = sum(masses_by_category[parent_index + 1 :])
                for child_index, child_threshold in enumerate(thresholds):
                    multiplicity_counts, multiplicity_masses = (
                        multiplicity_tables[child_index]
                    )
                    high_parent_counts_by_multiplicity = [
                        sum(
                            multiplicity_counts[parent_category][multiplicity]
                            for parent_category in range(
                                parent_index + 1, category_count
                            )
                        )
                        for multiplicity in range(4)
                    ]
                    high_parent_masses_by_multiplicity = [
                        sum(
                            multiplicity_masses[parent_category][multiplicity]
                            for parent_category in range(
                                parent_index + 1, category_count
                            )
                        )
                        for multiplicity in range(4)
                    ]
                    if sum(high_parent_counts_by_multiplicity) != parent_high_count:
                        raise AssertionError("high-parent multiplicities lost nodes")
                    if sum(high_parent_masses_by_multiplicity) != parent_high_mass:
                        raise AssertionError("high-parent multiplicities lost mass")
                    persistent_count = sum(
                        count_matrix[parent_category][child_category]
                        for parent_category in range(parent_index + 1, category_count)
                        for child_category in range(child_index + 1, category_count)
                    )
                    immigration_count = sum(
                        count_matrix[parent_category][child_category]
                        for parent_category in range(parent_index + 1)
                        for child_category in range(child_index + 1, category_count)
                    )
                    persistent_mass = sum(
                        mass_matrix[parent_category][child_category]
                        for parent_category in range(parent_index + 1, category_count)
                        for child_category in range(child_index + 1, category_count)
                    )
                    immigration_mass = sum(
                        mass_matrix[parent_category][child_category]
                        for parent_category in range(parent_index + 1)
                        for child_category in range(child_index + 1, category_count)
                    )
                    child_high_count = persistent_count + immigration_count
                    child_high_mass = persistent_mass + immigration_mass
                    expected_persistent_count = sum(
                        multiplicity * high_parent_counts_by_multiplicity[multiplicity]
                        for multiplicity in range(4)
                    )
                    if persistent_count != expected_persistent_count:
                        raise AssertionError("high-child multiplicities lost edges")
                    expected_child_high_mass = sum(
                        sum(row[child_index + 1 :]) for row in mass_matrix
                    )
                    if child_high_mass != expected_child_high_mass:
                        raise AssertionError("persistent + immigration identity failed")
                    if persistent_mass > parent_high_mass:
                        raise AssertionError("retained child mass exceeds high-parent mass")

                    row = {
                        "k": k,
                        "parent_depth": depth,
                        "child_depth": depth + 1,
                        "coarsenings_from_finest_child": k - 2 - depth,
                        "parent_threshold": str(parent_threshold),
                        "parent_threshold_num": parent_threshold.numerator,
                        "parent_threshold_den": parent_threshold.denominator,
                        "child_threshold": str(child_threshold),
                        "child_threshold_num": child_threshold.numerator,
                        "child_threshold_den": child_threshold.denominator,
                        "parent_high_node_count": parent_high_count,
                        "child_high_node_count": child_high_count,
                        "persistent_high_child_count": persistent_count,
                        "immigration_high_child_count": immigration_count,
                        "parent_high_mass": parent_high_mass,
                        "child_high_mass": child_high_mass,
                        "persistent_high_child_mass": persistent_mass,
                        "immigration_high_child_mass": immigration_mass,
                        "escaped_from_high_parent_mass": (
                            parent_high_mass - persistent_mass
                        ),
                        "high_parent_high_child_count": persistent_count,
                        "high_parent_high_child_mass": persistent_mass,
                        "high_parent_low_child_count": (
                            3 * parent_high_count - persistent_count
                        ),
                        "high_parent_low_child_mass": (
                            parent_high_mass - persistent_mass
                        ),
                        "low_parent_high_child_count": immigration_count,
                        "low_parent_high_child_mass": immigration_mass,
                        "low_parent_low_child_count": (
                            len(finer_masses)
                            - 3 * parent_high_count
                            - immigration_count
                        ),
                        "low_parent_low_child_mass": (
                            total_mass - parent_high_mass - immigration_mass
                        ),
                        "high_parent_0_high_children_count": (
                            high_parent_counts_by_multiplicity[0]
                        ),
                        "high_parent_1_high_child_count": (
                            high_parent_counts_by_multiplicity[1]
                        ),
                        "high_parent_2_high_children_count": (
                            high_parent_counts_by_multiplicity[2]
                        ),
                        "high_parent_3_high_children_count": (
                            high_parent_counts_by_multiplicity[3]
                        ),
                        "high_parent_0_high_children_parent_mass": (
                            high_parent_masses_by_multiplicity[0]
                        ),
                        "high_parent_1_high_child_parent_mass": (
                            high_parent_masses_by_multiplicity[1]
                        ),
                        "high_parent_2_high_children_parent_mass": (
                            high_parent_masses_by_multiplicity[2]
                        ),
                        "high_parent_3_high_children_parent_mass": (
                            high_parent_masses_by_multiplicity[3]
                        ),
                        "pointwise_retention_one_witness_count": (
                            high_parent_counts_by_multiplicity[3]
                        ),
                        "total_mass": total_mass,
                        **rational_fields(
                            "retention", persistent_mass, parent_high_mass
                        ),
                        **rational_fields(
                            "closure", child_high_mass, parent_high_mass
                        ),
                        **rational_fields(
                            "immigration", immigration_mass, total_mass
                        ),
                        **rational_fields(
                            "ancestry", persistent_mass, child_high_mass
                        ),
                        **rational_fields(
                            "immigration_share", immigration_mass,
                            child_high_mass
                        ),
                        **rational_fields(
                            "parent_tail", parent_high_mass, total_mass
                        ),
                        **rational_fields(
                            "child_tail", child_high_mass, total_mass
                        ),
                        **provenance,
                    }
                    transition_rows.append(row)

        finer_masses = node_masses
        finer_categories = categories
        finer_depth = depth
        children = node_masses

    if len(children) != 1 or int(children[0]) != total_mass:
        raise AssertionError("3-adic hierarchy did not coarsen to exact total mass")
    print(
        f"k={k}: total_mass={total_mass}; tail rows={len(thresholds) * (k - 1)}, "
        f"transition rows={len(thresholds)**2 * (k - 2)}"
    )
    return tail_rows, transition_rows


def recurrence_summary(
    transition_rows: list[dict[str, object]], thresholds: tuple[Fraction, ...]
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for parent_threshold in thresholds:
        for child_threshold in thresholds:
            matching = [
                row for row in transition_rows
                if row["parent_threshold"] == str(parent_threshold)
                and row["child_threshold"] == str(child_threshold)
            ]
            offsets = sorted({
                int(row["coarsenings_from_finest_child"]) for row in matching
            })
            for offset in offsets:
                at_offset = [
                    row for row in matching
                    if int(row["coarsenings_from_finest_child"]) == offset
                ]
                q_rows = [
                    row for row in at_offset if row["retention_num"] != ""
                ]
                worst_retention = (
                    max(
                        q_rows,
                        key=lambda row: Fraction(
                            int(row["retention_num"]),
                            int(row["retention_den"]),
                        ),
                    )
                    if q_rows else None
                )
                worst_immigration = max(
                    at_offset,
                    key=lambda row: Fraction(
                        int(row["immigration_num"]), int(row["immigration_den"])
                    ),
                )
                latest = max(at_offset, key=lambda row: int(row["k"]))
                rows.append({
                    "parent_threshold": str(parent_threshold),
                    "child_threshold": str(child_threshold),
                    "coarsenings_from_finest_child": offset,
                    "levels_present": len(at_offset),
                    "levels_with_nonzero_parent_tail": len(q_rows),
                    "minimum_k": min(int(row["k"]) for row in at_offset),
                    "maximum_k": max(int(row["k"]) for row in at_offset),
                    "max_retention_k": (
                        worst_retention["k"] if worst_retention else ""
                    ),
                    "max_retention_parent_depth": (
                        worst_retention["parent_depth"] if worst_retention else ""
                    ),
                    "max_retention_num": (
                        worst_retention["retention_num"] if worst_retention else ""
                    ),
                    "max_retention_den": (
                        worst_retention["retention_den"] if worst_retention else ""
                    ),
                    "max_retention_decimal": (
                        worst_retention["retention_decimal"] if worst_retention else ""
                    ),
                    "max_immigration_k": worst_immigration["k"],
                    "max_immigration_parent_depth": worst_immigration["parent_depth"],
                    "max_immigration_num": worst_immigration["immigration_num"],
                    "max_immigration_den": worst_immigration["immigration_den"],
                    "max_immigration_decimal": worst_immigration["immigration_decimal"],
                    "latest_k": latest["k"],
                    "latest_parent_depth": latest["parent_depth"],
                    "latest_retention_num": latest["retention_num"],
                    "latest_retention_den": latest["retention_den"],
                    "latest_retention_decimal": latest["retention_decimal"],
                    "latest_closure_num": latest["closure_num"],
                    "latest_closure_den": latest["closure_den"],
                    "latest_closure_decimal": latest["closure_decimal"],
                    "latest_immigration_num": latest["immigration_num"],
                    "latest_immigration_den": latest["immigration_den"],
                    "latest_immigration_decimal": latest["immigration_decimal"],
                    "latest_ancestry_num": latest["ancestry_num"],
                    "latest_ancestry_den": latest["ancestry_den"],
                    "latest_ancestry_decimal": latest["ancestry_decimal"],
                    "latest_immigration_share_num": latest["immigration_share_num"],
                    "latest_immigration_share_den": latest["immigration_share_den"],
                    "latest_immigration_share_decimal": latest["immigration_share_decimal"],
                    "latest_parent_tail_num": latest["parent_tail_num"],
                    "latest_parent_tail_den": latest["parent_tail_den"],
                    "latest_parent_tail_decimal": latest["parent_tail_decimal"],
                    "latest_child_tail_num": latest["child_tail_num"],
                    "latest_child_tail_den": latest["child_tail_den"],
                    "latest_child_tail_decimal": latest["child_tail_decimal"],
                })
    return rows


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


def parse_thresholds(values: Iterable[str]) -> tuple[Fraction, ...]:
    thresholds = tuple(sorted(set(Fraction(value) for value in values)))
    if not thresholds or any(not (0 < threshold < 3) for threshold in thresholds):
        raise ValueError("require distinct rational thresholds strictly between 0 and 3")
    if len(thresholds) > 100:
        raise ValueError("at most 100 thresholds are supported")
    if any(
        threshold.numerator > 1_000_000 or threshold.denominator > 1_000_000
        for threshold in thresholds
    ):
        raise ValueError("threshold numerators and denominators must be <= 1000000")
    return thresholds


def self_test() -> None:
    values = np.asarray([5, 2, 7, 3, 11, 13, 17, 19, 23], dtype=np.int64)
    thresholds = (Fraction(1, 5), Fraction(2, 5))
    depth_two, categories_two = coarsen_and_classify(values, thresholds)
    assert list(map(int, depth_two)) == [25, 32, 43]
    # Independent scalar check of both threshold categories.
    expected_categories = []
    for column in range(3):
        triple = [int(values[column + digit * 3]) for digit in range(3)]
        difference, total = max(triple) - min(triple), sum(triple)
        expected_categories.append(
            sum(3 * threshold.denominator * difference
                > threshold.numerator * total for threshold in thresholds)
        )
    assert list(map(int, categories_two)) == expected_categories
    depth_one, categories_one = coarsen_and_classify(depth_two, thresholds)
    assert int(depth_one[0]) == int(values.sum()) == 100
    counts, masses = transition_histogram(
        categories_one, categories_two, depth_two, 3, 2
    )
    assert sum(map(sum, counts)) == 3
    assert sum(map(sum, masses)) == 100

    # Radix accumulation stays exact after the total exceeds signed int64.
    huge = np.asarray([INT64_MAX - 10, 20, 30], dtype=np.int64)
    huge_categories = np.asarray([0, 1, 1], dtype=np.uint8)
    huge_counts, huge_masses = exact_histogram(
        huge_categories, huge, 2, chunk_size=2
    )
    assert huge_counts == [1, 2]
    assert huge_masses == [INT64_MAX - 10, 50]
    assert sum(huge_masses) > INT64_MAX

    # Coarsening switches to Python integers before a triple can overflow.
    object_children = np.asarray([INT64_MAX // 2] * 3, dtype=object)
    object_parent, _ = coarsen_and_classify(object_children, thresholds)
    assert object_parent.dtype == object
    assert int(object_parent[0]) == 3 * (INT64_MAX // 2) > INT64_MAX

    # Strict threshold equality is low; moving the sum down by one is high.
    differences = np.asarray([1, 1], dtype=np.int64)
    sums = np.asarray([15, 14], dtype=np.int64)
    assert exact_exceeds(differences, sums, Fraction(1, 5)).tolist() == [
        False, True
    ]

    # Tail monotonicity is not a formal consequence of 3-adic coarsening.
    # Here A_2=(12,12,12), so the coarse tail is zero, while one depth-two
    # node has children (10,1,1), omega=9/4, and mass 12/36.
    counterexample = np.asarray(
        [10, 4, 4, 1, 4, 4, 1, 4, 4], dtype=np.int64
    )
    counter_depth_two, counter_categories_two = coarsen_and_classify(
        counterexample, (Fraction(1, 5),)
    )
    counter_depth_one, counter_categories_one = coarsen_and_classify(
        counter_depth_two, (Fraction(1, 5),)
    )
    assert counter_depth_two.tolist() == [12, 12, 12]
    assert counter_categories_two.tolist() == [1, 0, 0]
    assert counter_depth_one.tolist() == [36]
    assert counter_categories_one.tolist() == [0]
    print("PASS: exact hierarchy, transition, bigint, and boundary self-tests")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", nargs="+", type=int, default=range(12, 20))
    parser.add_argument(
        "--thresholds", nargs="+", default=[str(x) for x in DEFAULT_THRESHOLDS]
    )
    parser.add_argument("--chunk-size", type=int, default=1_000_000)
    parser.add_argument("--skip-sha", action="store_true")
    parser.add_argument("--tail-output", type=Path, default=DEFAULT_TAIL_OUTPUT)
    parser.add_argument(
        "--transition-output", type=Path, default=DEFAULT_TRANSITION_OUTPUT
    )
    parser.add_argument("--summary-output", type=Path, default=DEFAULT_SUMMARY_OUTPUT)
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("require a positive chunk-size")
    try:
        thresholds = parse_thresholds(args.thresholds)
    except (ValueError, ZeroDivisionError) as error:
        parser.error(str(error))

    self_test()
    tail_rows: list[dict[str, object]] = []
    transition_rows: list[dict[str, object]] = []
    for k in args.levels:
        level_tail, level_transitions = analyze_level(
            k, thresholds, args.chunk_size, not args.skip_sha
        )
        tail_rows.extend(level_tail)
        transition_rows.extend(level_transitions)
    tail_rows.sort(key=lambda row: (int(row["k"]), int(row["depth"]), Fraction(str(row["threshold"]))))
    transition_rows.sort(key=lambda row: (
        int(row["k"]), int(row["parent_depth"]),
        Fraction(str(row["parent_threshold"])),
        Fraction(str(row["child_threshold"])),
    ))
    write_rows(args.tail_output, tail_rows)
    write_rows(args.transition_output, transition_rows)
    write_rows(
        args.summary_output, recurrence_summary(transition_rows, thresholds)
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact audit of the top-window child/parent mass split U(sigma).

The combined pressure proposal models the four refinements of a base-4 top
window as four equally weighted children.  Its missing H1 hypothesis instead
requires a pointwise estimate

    M(q, D e) <= sigma * M(q, D).

``validate2.py`` measured this only for six-digit parents at k=15,16.  This
script measures the exact ratio at the window depth actually under discussion,
without loading or sorting a whole large certificate in memory.  The source
arrays are the SHA-pinned exact feasible vectors from ``experiments/kl``.

All mass aggregation and maximization use integers.  Floating point appears
only in the printed decimal rendering of the final exact fraction.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Iterable

import numpy as np

import combined as cb


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
KL = ROOT / "experiments" / "kl"
DEFAULT_OUTPUT = HERE / "csv" / "split_ratio_audit.csv"
INT64_MAX = np.iinfo(np.int64).max


def sha256_file(path: Path, chunk_bytes: int = 8 << 20) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(chunk_bytes):
            digest.update(block)
    return digest.hexdigest()


def load_certificate(k: int, verify_sha: bool):
    manifest_path = KL / f"cert_k{k}.json"
    manifest = json.loads(manifest_path.read_text())
    if manifest["k"] != k:
        raise ValueError(f"{manifest_path}: expected k={k}")

    if "C_file" in manifest:
        source_path = KL / manifest["C_file"]
        if not source_path.exists():
            raise FileNotFoundError(
                f"missing local sidecar {source_path}; large k=16..19 arrays "
                "are intentionally not tracked by git"
            )
        expected_sha = manifest["C_sha256"]
        if verify_sha:
            actual_sha = sha256_file(source_path)
            if actual_sha != expected_sha:
                raise ValueError(
                    f"SHA-256 mismatch for {source_path}: "
                    f"expected {expected_sha}, got {actual_sha}"
                )
        hash_verified = verify_sha
        values = np.load(source_path, mmap_mode="r")
        source_name = source_path.name
    else:
        values = np.asarray(manifest["C"], dtype=np.int64)
        expected_sha = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
        source_name = manifest_path.name
        hash_verified = True

    expected_size = 3 ** (k - 1)
    if values.ndim != 1 or len(values) != expected_size:
        raise ValueError(
            f"{source_name}: expected {expected_size} coordinates, "
            f"got shape {values.shape}"
        )
    if values.dtype != np.int64:
        raise TypeError(f"{source_name}: expected int64, got {values.dtype}")
    if int(values.min()) <= 0:
        raise ValueError(f"{source_name}: coordinate values must be positive")
    return values, source_name, expected_sha, hash_verified


def aggregate_at_depth(
    values: np.ndarray, k: int, depth: int, chunk_size: int
) -> tuple[np.ndarray, np.ndarray]:
    """Return exact mass/count arrays indexed by (q mod 27, top window).

    State index ``i`` is the paper residue ``m=2+3*i``.  The low-window ball
    index is ``i mod 9`` and the depth-``d`` top-window index is
    ``floor(m*4^d/3^k)``.  Within one low ball the latter is monotone, so each
    streamed chunk is reduced on its constant runs before accumulation.
    """

    width = 4**depth
    state_count = len(values)
    max_value = int(values.max())
    # A fixed low ball and top interval contains at most this many state
    # coordinates.  The two extra endpoint allowances make the bound safely
    # conservative for the affine m=2+3*i indexing.
    max_bin_count = (state_count + 9 * width - 1) // (9 * width) + 2
    if max_bin_count * max_value > INT64_MAX:
        raise OverflowError(
            "an exact aggregate might overflow int64; increase the minimum "
            "window depth or implement Python-integer bins"
        )

    mass = np.zeros((9, width), dtype=np.int64)
    counts = np.zeros((9, width), dtype=np.int64)
    modulus = 3**k
    largest_index_product = (2 + 3 * (state_count - 1)) * width
    if largest_index_product > INT64_MAX:
        raise OverflowError(
            "top-window index arithmetic would overflow int64; reduce the "
            "window depth or implement Python-integer indices"
        )

    for start in range(0, state_count, chunk_size):
        end = min(state_count, start + chunk_size)
        for ball in range(9):
            first = start + ((ball - start) % 9)
            if first >= end:
                continue
            indices = np.arange(first, end, 9, dtype=np.int64)
            chunk_values = np.asarray(values[first:end:9], dtype=np.int64)
            windows = ((2 + 3 * indices) * width) // modulus
            cuts = np.r_[0, np.flatnonzero(windows[1:] != windows[:-1]) + 1]
            run_mass = np.add.reduceat(chunk_values, cuts)
            run_counts = np.diff(np.r_[cuts, len(chunk_values)])
            targets = windows[cuts]
            mass[ball, targets] += run_mass
            counts[ball, targets] += run_counts

    if np.any(mass < 0):
        raise OverflowError("negative aggregate indicates int64 overflow")
    if int(counts.sum()) != state_count:
        raise AssertionError("top-window cells do not partition the coordinates")
    return mass, counts


def base4_digits(index: int, length: int) -> str:
    return "".join(
        str((index >> (2 * (length - 1 - position))) & 3)
        for position in range(length)
    )


@lru_cache(maxsize=None)
def uncovered_transport_mask(parent_depth: int) -> np.ndarray:
    """Mask source-uncovered/T-successor-uncovered child refinements."""

    width = 4**parent_depth
    mask = np.zeros((9, width, 4), dtype=bool)
    for ball in range(9):
        q = 2 + 3 * ball
        target_q = (4 * q) % 27
        for window_index in range(width):
            digits = tuple(map(int, base4_digits(window_index, parent_depth)))
            if cb.covered(q % 9, digits):
                continue
            for child_digit in range(4):
                target_digits = (
                    cb.shift_window(digits, child_digit) if digits else ()
                )
                mask[ball, window_index, child_digit] = not cb.covered(
                    target_q % 9, target_digits
                )
    return mask


def exact_max_split(
    mass: np.ndarray, counts: np.ndarray, k: int, parent_depth: int,
    source_name: str, source_sha256: str, source_sha256_verified: bool,
    scope: str
) -> dict[str, object]:
    """Find the global maximum by exact cross multiplication."""

    child_mass = mass.reshape(9 * 4**parent_depth, 4)
    child_counts = counts.reshape(9 * 4**parent_depth, 4)
    if scope == "all":
        eligible = None
    elif scope == "uncovered_T_uncovered":
        eligible = uncovered_transport_mask(parent_depth).reshape(-1, 4)
    else:
        raise ValueError(f"unknown scope {scope}")
    best_num, best_den = 0, 1
    best_parent, best_digit = 0, 0
    eligible_count = 0
    violations_21_over_50 = 0
    eligible_child_mass = 0
    violation_child_mass = 0

    for parent, row in enumerate(child_mass):
        values = tuple(map(int, row))
        denominator = sum(values)
        if denominator == 0:
            continue
        for digit, numerator in enumerate(values):
            if eligible is not None and not eligible[parent, digit]:
                continue
            eligible_count += 1
            eligible_child_mass += numerator
            if numerator * 50 > denominator * 21:
                violations_21_over_50 += 1
                violation_child_mass += numerator
            if numerator * best_den > best_num * denominator:
                best_num, best_den = numerator, denominator
                best_parent, best_digit = parent, digit

    if eligible_count == 0:
        raise AssertionError(f"scope {scope} has no eligible transitions")

    ball, window_index = divmod(best_parent, 4**parent_depth)
    count_row = tuple(map(int, child_counts[best_parent]))
    ratio = Fraction(best_num, best_den)
    violation_mass_ratio = Fraction(violation_child_mass, eligible_child_mass)
    digits = base4_digits(window_index, parent_depth)
    q = 2 + 3 * ball
    target_q = (4 * q) % 27
    parent_digits_tuple = tuple(map(int, digits))
    target_digits_tuple = (
        cb.shift_window(parent_digits_tuple, best_digit)
        if parent_digits_tuple else ()
    )
    target_digits = "".join(map(str, target_digits_tuple))

    return {
        "k": k,
        "parent_depth": parent_depth,
        "scope": scope,
        "sigma_num": ratio.numerator,
        "sigma_den": ratio.denominator,
        "sigma_decimal": f"{float(ratio):.12f}",
        "margin_50num_minus_21den": 50 * ratio.numerator - 21 * ratio.denominator,
        "ball_residue_q": q,
        "phase_mod9": q % 9,
        "parent_window_index": window_index,
        "parent_window_base4": digits,
        "child_digit": best_digit,
        "child_mass": best_num,
        "parent_mass": best_den,
        "child_coordinate_count": count_row[best_digit],
        "parent_coordinate_count": sum(count_row),
        "parent_window_covered": cb.covered(q % 9, tuple(map(int, digits))),
        "transport_target_q": target_q,
        "transport_target_window_base4": target_digits,
        "transport_target_uncovered": not cb.covered(
            target_q % 9, target_digits_tuple
        ),
        "eligible_transition_count": eligible_count,
        "violations_above_21_over_50": violations_21_over_50,
        "eligible_child_mass": eligible_child_mass,
        "violation_child_mass": violation_child_mass,
        "violation_mass_fraction": f"{float(violation_mass_ratio):.12g}",
        "source": source_name,
        "source_sha256": source_sha256,
        "source_sha256_verified": source_sha256_verified,
    }


def audit(
    levels: Iterable[int], min_depth: int, max_depth: int,
    chunk_size: int, verify_sha: bool
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for k in levels:
        values, source_name, source_sha256, source_sha256_verified = (
            load_certificate(k, verify_sha)
        )
        mass, counts = aggregate_at_depth(values, k, max_depth + 1, chunk_size)
        for depth in range(max_depth, min_depth - 1, -1):
            for scope in ("all", "uncovered_T_uncovered"):
                row = exact_max_split(
                    mass, counts, k, depth, source_name, source_sha256,
                    source_sha256_verified, scope
                )
                rows.append(row)
                print(
                    f"k={k} Lw={depth} scope={scope}: sigma_max="
                    f"{row['sigma_num']}/{row['sigma_den']}="
                    f"{row['sigma_decimal']} at q={row['ball_residue_q']}, "
                    f"D={row['parent_window_base4']}, e={row['child_digit']} "
                    f"({row['child_coordinate_count']}/"
                    f"{row['parent_coordinate_count']} coordinates); "
                    f">21/50: {row['violations_above_21_over_50']}/"
                    f"{row['eligible_transition_count']}"
                )
            if depth > min_depth:
                # The next shallower audit uses these parent cells as its
                # children.  The requested default range stays exactly within
                # int64; check every coarsening rather than relying on that.
                reshaped_mass = mass.reshape(9, 4**depth, 4)
                reshaped_counts = counts.reshape(9, 4**depth, 4)
                if int(reshaped_mass.max()) > INT64_MAX // 4:
                    raise OverflowError(
                        f"coarsening to depth {depth} might overflow int64"
                    )
                mass = reshaped_mass.sum(axis=2, dtype=np.int64)
                counts = reshaped_counts.sum(axis=2, dtype=np.int64)
                if np.any(mass < 0):
                    raise OverflowError(
                        f"coarsening to depth {depth} overflowed int64"
                    )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", nargs="+", type=int, default=range(15, 20))
    parser.add_argument("--min-depth", type=int, default=6)
    parser.add_argument("--max-depth", type=int, default=9)
    parser.add_argument("--chunk-size", type=int, default=24_000_000)
    parser.add_argument("--skip-sha", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    if not (0 <= args.min_depth <= args.max_depth):
        parser.error("require 0 <= min-depth <= max-depth")
    if args.chunk_size <= 0:
        parser.error("require a positive chunk-size")
    rows = audit(
        args.levels, args.min_depth, args.max_depth,
        args.chunk_size, not args.skip_sha
    )
    regression = next(
        (row for row in rows
         if row["k"] == 19 and row["parent_depth"] == 9
         and row["scope"] == "uncovered_T_uncovered"),
        None,
    )
    if regression is not None:
        expected = {
            "sigma_num": 1892575973641960,
            "sigma_den": 3487969866821777,
            "violations_above_21_over_50": 233,
            "margin_50num_minus_21den": 21381431478840683,
        }
        for field, value in expected.items():
            if regression[field] != value:
                raise AssertionError(
                    f"k=19 restricted depth-nine regression changed: "
                    f"{field}={regression[field]}, expected {value}"
                )
        print("PASS: exact k=19 restricted depth-nine regression")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()

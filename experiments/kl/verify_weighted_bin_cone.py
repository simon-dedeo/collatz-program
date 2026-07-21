#!/usr/bin/env python3
"""Verify exact finite weighted cones for the KL oscillation genealogy.

The input table stores cumulative high-parent/high-child masses for seven
oscillation thresholds.  Mobius differencing reconstructs the exact 8-by-8
mass matrix between oscillation bins at every observed genealogy transition.

For a target threshold with high-bin block Q, this script checks exact
rational inequalities

    Q_(k,j) w <= rho w

row by row after a fixed burn-in.  Here Q is conditional on the parent bin;
the check averages over all parents in that bin and is not a pointwise-parent
or all-vector operator statement.  It also records the exact recurrence

    V_(k,j+1) = persistent_(k,j) + immigration_(k,j)
                <= rho V_(k,j) + immigration_(k,j).

The cones were selected after inspecting k=12,...,19, so they are exact finite
certificates and future falsifiers, not independent evidence for an all-level
theorem.  The decisive missing statement is decay of weighted immigration for
each fixed terminal offset (and ultimately for thresholds tending to zero).

The verifier is standard-library only.  Floating point is used solely to
render already exact fractions as decimals.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFAULT_INPUT = HERE / "analysis_cache" / "multiscale_transitions_exact.csv"
DEFAULT_CONE_OUTPUT = (
    HERE / "analysis_cache" / "weighted_bin_cone_rows_exact.csv"
)
DEFAULT_RECURRENCE_OUTPUT = (
    HERE / "analysis_cache" / "weighted_bin_recurrence_exact.csv"
)
EXPECTED_INPUT_SHA256 = (
    "ea02b6b4b87b89a3938e4c8814c109d561d82535ab4bbd2afbef2691fd088161"
)
THRESHOLDS = tuple(
    Fraction(value)
    for value in ("1/20", "1/10", "3/20", "1/5", "1/4", "3/10", "2/5")
)
EXPECTED_LEVELS = tuple(range(12, 20))


@dataclass(frozen=True)
class ConeSpec:
    threshold: Fraction
    first_parent_depth: int
    weights: tuple[Fraction, ...]
    rho: Fraction
    expected_row_count: int
    expected_matrix_count: int
    expected_maximum: Fraction
    expected_maximum_location: tuple[int, int, int]

    @property
    def first_high_bin(self) -> int:
        return THRESHOLDS.index(self.threshold) + 1


CONE_SPECS = (
    ConeSpec(
        threshold=Fraction(1, 5),
        first_parent_depth=3,
        # Integer representative (62,69,50,68), normalized so min(w)=1.
        weights=(Fraction(31, 25), Fraction(69, 50), Fraction(1), Fraction(34, 25)),
        rho=Fraction(68, 69),
        expected_row_count=349,
        expected_matrix_count=92,
        expected_maximum=Fraction(68, 69),
        expected_maximum_location=(15, 4, 5),
    ),
    ConeSpec(
        threshold=Fraction(3, 10),
        first_parent_depth=2,
        weights=(Fraction(1), Fraction(1)),
        rho=Fraction(179, 200),
        expected_row_count=184,
        expected_matrix_count=100,
        expected_maximum=Fraction(
            4334815655959768610198, 4845180013388557558821
        ),
        expected_maximum_location=(19, 2, 7),
    ),
)


def sha256_file(path: Path, chunk_bytes: int = 8 << 20) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(chunk_bytes):
            digest.update(block)
    return digest.hexdigest()


def fraction_fields(prefix: str, value: Fraction) -> dict[str, object]:
    return {
        f"{prefix}_num": value.numerator,
        f"{prefix}_den": value.denominator,
        f"{prefix}_decimal": f"{float(value):.12g}",
    }


def weight_string(weights: tuple[Fraction, ...]) -> str:
    return ";".join(str(weight) for weight in weights)


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


def suffix_from_cells(cells: list[list[int]]) -> list[list[int]]:
    size = len(cells)
    if any(len(row) != size for row in cells):
        raise ValueError("cell matrix must be square")
    suffix = [[0] * (size + 1) for _ in range(size + 1)]
    for parent_bin in range(size - 1, -1, -1):
        for child_bin in range(size - 1, -1, -1):
            suffix[parent_bin][child_bin] = (
                cells[parent_bin][child_bin]
                + suffix[parent_bin + 1][child_bin]
                + suffix[parent_bin][child_bin + 1]
                - suffix[parent_bin + 1][child_bin + 1]
            )
    return suffix


def cells_from_suffix(suffix: list[list[int]]) -> list[list[int]]:
    size = len(suffix) - 1
    if size <= 0 or any(len(row) != size + 1 for row in suffix):
        raise ValueError("suffix matrix must be square with a zero boundary")
    if any(suffix[size]) or any(row[size] for row in suffix):
        raise ValueError("suffix matrix boundary must be zero")
    return [
        [
            suffix[parent_bin][child_bin]
            - suffix[parent_bin + 1][child_bin]
            - suffix[parent_bin][child_bin + 1]
            + suffix[parent_bin + 1][child_bin + 1]
            for child_bin in range(size)
        ]
        for parent_bin in range(size)
    ]


def self_test() -> None:
    cells = [[2, 3, 5], [7, 11, 13], [17, 19, 23]]
    suffix = suffix_from_cells(cells)
    assert cells_from_suffix(suffix) == cells
    assert suffix[0][0] == sum(map(sum, cells))
    print("PASS: exact Möbius reconstruction self-test")


def load_groups(
    path: Path, verify_sha: bool
) -> tuple[
    dict[tuple[int, int], dict[tuple[Fraction, Fraction], dict[str, str]]],
    str,
]:
    digest = sha256_file(path)
    if verify_sha and digest != EXPECTED_INPUT_SHA256:
        raise ValueError(
            f"SHA-256 mismatch for {path}: expected {EXPECTED_INPUT_SHA256}, "
            f"got {digest}"
        )

    groups: dict[
        tuple[int, int], dict[tuple[Fraction, Fraction], dict[str, str]]
    ] = {}
    with path.open(newline="") as handle:
        for row in csv.DictReader(handle):
            key = (int(row["k"]), int(row["parent_depth"]))
            pair = (
                Fraction(row["parent_threshold"]),
                Fraction(row["child_threshold"]),
            )
            group = groups.setdefault(key, {})
            if pair in group:
                raise ValueError(f"duplicate threshold pair {pair} at {key}")
            if int(row["child_depth"]) != key[1] + 1:
                raise ValueError(f"wrong child depth at {key}, {pair}")
            if row["source_sha256_verified"] != "True":
                raise ValueError(f"unverified source row at {key}, {pair}")
            group[pair] = row

    expected_keys = {
        (k, parent_depth)
        for k in EXPECTED_LEVELS
        for parent_depth in range(1, k - 1)
    }
    if set(groups) != expected_keys:
        missing = sorted(expected_keys - set(groups))
        extra = sorted(set(groups) - expected_keys)
        raise ValueError(f"transition keys differ: missing={missing}, extra={extra}")
    expected_pairs = {
        (parent_threshold, child_threshold)
        for parent_threshold in THRESHOLDS
        for child_threshold in THRESHOLDS
    }
    for key, group in groups.items():
        if set(group) != expected_pairs:
            raise ValueError(f"threshold grid differs at {key}")
    return groups, digest


def reconstruct_cells(
    key: tuple[int, int],
    group: dict[tuple[Fraction, Fraction], dict[str, str]],
) -> tuple[list[list[int]], int]:
    sample = next(iter(group.values()))
    total_mass = int(sample["total_mass"])
    if any(int(row["total_mass"]) != total_mass for row in group.values()):
        raise ValueError(f"inconsistent total mass at {key}")

    suffix = [[0] * 9 for _ in range(9)]
    suffix[0][0] = total_mass
    for parent_index, parent_threshold in enumerate(THRESHOLDS, start=1):
        row = group[(parent_threshold, THRESHOLDS[0])]
        suffix[parent_index][0] = int(row["parent_high_mass"])
    for child_index, child_threshold in enumerate(THRESHOLDS, start=1):
        row = group[(THRESHOLDS[0], child_threshold)]
        suffix[0][child_index] = int(row["child_high_mass"])
    for parent_index, parent_threshold in enumerate(THRESHOLDS, start=1):
        for child_index, child_threshold in enumerate(THRESHOLDS, start=1):
            row = group[(parent_threshold, child_threshold)]
            suffix[parent_index][child_index] = int(
                row["high_parent_high_child_mass"]
            )

    cells = cells_from_suffix(suffix)
    if min(map(min, cells)) < 0:
        raise ValueError(f"negative Mobius cell at {key}")
    if sum(map(sum, cells)) != total_mass:
        raise AssertionError(f"Mobius cells lose total mass at {key}")
    if suffix_from_cells(cells) != suffix:
        raise AssertionError(f"Mobius round trip failed at {key}")

    for parent_index, parent_threshold in enumerate(THRESHOLDS, start=1):
        for child_index, child_threshold in enumerate(THRESHOLDS, start=1):
            row = group[(parent_threshold, child_threshold)]
            parent_high = suffix[parent_index][0]
            child_high = suffix[0][child_index]
            high_high = suffix[parent_index][child_index]
            expected = {
                "parent_high_mass": parent_high,
                "child_high_mass": child_high,
                "high_parent_high_child_mass": high_high,
                "high_parent_low_child_mass": parent_high - high_high,
                "low_parent_high_child_mass": child_high - high_high,
                "low_parent_low_child_mass": (
                    total_mass - parent_high - child_high + high_high
                ),
            }
            for field, value in expected.items():
                if int(row[field]) != value:
                    raise AssertionError(f"{field} mismatch at {key}")
    return cells, total_mass


def verify_obstruction(
    matrices: dict[tuple[int, int], list[list[int]]]
) -> None:
    # At every observed depth-one transition, B7 maps entirely to B7.  Thus a
    # positive one-step cone beginning at the root must have rho >= 1.
    for k in EXPECTED_LEVELS:
        row = matrices[(k, 1)][7]
        if row[7] <= 0 or any(row[child_bin] for child_bin in range(7)):
            raise AssertionError(f"expected B7 self-loop is absent at k={k}")

    # A stronger exact obstruction rules out a common t=.2 cone beginning at
    # depth two.  The first row forces w5<w7 for rho<1; the second forces
    # w7<w5.  They need not be consecutive: a common cone must satisfy both.
    depth_two = matrices[(17, 2)][7]
    expected_depth_two = {
        5: 51502644182774780905,
        7: 427972643644712297522,
    }
    if {
        child_bin: mass
        for child_bin, mass in enumerate(depth_two)
        if mass
    } != expected_depth_two:
        raise AssertionError("k=17 depth-two B7 obstruction row changed")

    depth_four = matrices[(17, 4)][5]
    expected_depth_four = {7: 11131874291182481018}
    if {
        child_bin: mass
        for child_bin, mass in enumerate(depth_four)
        if mass
    } != expected_depth_four:
        raise AssertionError("k=17 depth-four B5 obstruction row changed")
    print("PASS: exact t=1/5 common-cone obstruction through depth two")


def verify_cones(
    groups: dict[tuple[int, int], dict[tuple[Fraction, Fraction], dict[str, str]]],
    matrices: dict[tuple[int, int], list[list[int]]],
    totals: dict[tuple[int, int], int],
    input_name: str,
    input_sha256: str,
    input_sha256_verified: bool,
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    cone_rows: list[dict[str, object]] = []
    recurrence_rows: list[dict[str, object]] = []

    for spec in CONE_SPECS:
        high = spec.first_high_bin
        if len(spec.weights) != 8 - high:
            raise AssertionError(f"wrong weight dimension for {spec.threshold}")
        if min(spec.weights) != 1:
            raise AssertionError("cone weights must be normalized to min(w)=1")

        observed_matrices = 0
        observed_rows = 0
        maximum = Fraction(-1)
        maximum_location: tuple[int, int, int] | None = None

        for key in sorted(matrices):
            k, parent_depth = key
            if parent_depth < spec.first_parent_depth:
                continue
            observed_matrices += 1
            cells = matrices[key]
            total_mass = totals[key]
            parent_masses = [sum(row) for row in cells]
            child_masses = [
                sum(cells[parent_bin][child_bin] for parent_bin in range(8))
                for child_bin in range(8)
            ]

            parent_potential = sum(
                Fraction(parent_masses[parent_bin], total_mass)
                * spec.weights[parent_bin - high]
                for parent_bin in range(high, 8)
            )
            persistent = sum(
                Fraction(cells[parent_bin][child_bin], total_mass)
                * spec.weights[child_bin - high]
                for parent_bin in range(high, 8)
                for child_bin in range(high, 8)
            )
            immigration = sum(
                Fraction(cells[parent_bin][child_bin], total_mass)
                * spec.weights[child_bin - high]
                for parent_bin in range(high)
                for child_bin in range(high, 8)
            )
            child_potential = sum(
                Fraction(child_masses[child_bin], total_mass)
                * spec.weights[child_bin - high]
                for child_bin in range(high, 8)
            )
            if child_potential != persistent + immigration:
                raise AssertionError(f"weighted recurrence failed at {key}")
            if persistent > spec.rho * parent_potential:
                raise AssertionError(f"aggregate cone failed at {key}")

            source_row = groups[key][(spec.threshold, spec.threshold)]
            parent_tail = Fraction(
                int(source_row["parent_tail_num"]),
                int(source_row["parent_tail_den"]),
            )
            child_tail = Fraction(
                int(source_row["child_tail_num"]),
                int(source_row["child_tail_den"]),
            )
            reconstructed_parent_tail = Fraction(
                sum(parent_masses[high:]), total_mass
            )
            reconstructed_child_tail = Fraction(
                sum(child_masses[high:]), total_mass
            )
            if parent_tail != reconstructed_parent_tail:
                raise AssertionError(f"parent tail mismatch at {key}")
            if child_tail != reconstructed_child_tail:
                raise AssertionError(f"child tail mismatch at {key}")
            if parent_potential < parent_tail or child_potential < child_tail:
                raise AssertionError(f"weighted potential does not dominate tail at {key}")

            recurrence_rows.append({
                "threshold": str(spec.threshold),
                "k": k,
                "parent_depth": parent_depth,
                "child_depth": parent_depth + 1,
                "terminal_offset": k - 2 - parent_depth,
                "first_parent_depth": spec.first_parent_depth,
                "weights": weight_string(spec.weights),
                **fraction_fields("rho", spec.rho),
                **fraction_fields("parent_tail", parent_tail),
                **fraction_fields("child_tail", child_tail),
                **fraction_fields("parent_potential", parent_potential),
                **fraction_fields("persistent_potential", persistent),
                **fraction_fields("immigration_potential", immigration),
                **fraction_fields("child_potential", child_potential),
                **fraction_fields(
                    "realized_retention",
                    persistent / parent_potential,
                ),
                "total_mass": total_mass,
                "selection_scope": "post_hoc_k12_19",
                "source": input_name,
                "source_sha256": input_sha256,
                "source_sha256_verified": input_sha256_verified,
            })

            for parent_bin in range(high, 8):
                parent_mass = parent_masses[parent_bin]
                if parent_mass == 0:
                    continue
                observed_rows += 1
                weighted_child = sum(
                    cells[parent_bin][child_bin]
                    * spec.weights[child_bin - high]
                    for child_bin in range(high, 8)
                )
                weighted_parent = (
                    parent_mass * spec.weights[parent_bin - high]
                )
                ratio = weighted_child / weighted_parent
                if ratio > spec.rho:
                    raise AssertionError(
                        f"cone row fails at k={k}, depth={parent_depth}, "
                        f"bin={parent_bin}: {ratio}>{spec.rho}"
                    )
                if ratio > maximum:
                    maximum = ratio
                    maximum_location = (k, parent_depth, parent_bin)
                cone_rows.append({
                    "threshold": str(spec.threshold),
                    "k": k,
                    "parent_depth": parent_depth,
                    "child_depth": parent_depth + 1,
                    "parent_bin": parent_bin,
                    "parent_bin_mass": parent_mass,
                    "first_parent_depth": spec.first_parent_depth,
                    "weights": weight_string(spec.weights),
                    **fraction_fields("parent_bin_weight", spec.weights[parent_bin - high]),
                    **fraction_fields("weighted_high_child_mass", weighted_child),
                    **fraction_fields("weighted_parent_mass", weighted_parent),
                    **fraction_fields("ratio", ratio),
                    **fraction_fields("rho", spec.rho),
                    **fraction_fields("rho_minus_ratio", spec.rho - ratio),
                    "selection_scope": "post_hoc_k12_19",
                    "source": input_name,
                    "source_sha256": input_sha256,
                    "source_sha256_verified": input_sha256_verified,
                })

        if observed_rows != spec.expected_row_count:
            raise AssertionError(
                f"{spec.threshold}: expected {spec.expected_row_count} rows, "
                f"got {observed_rows}"
            )
        if observed_matrices != spec.expected_matrix_count:
            raise AssertionError(
                f"{spec.threshold}: expected {spec.expected_matrix_count} matrices, "
                f"got {observed_matrices}"
            )
        if maximum != spec.expected_maximum:
            raise AssertionError(
                f"{spec.threshold}: expected max {spec.expected_maximum}, got {maximum}"
            )
        if maximum_location != spec.expected_maximum_location:
            raise AssertionError(
                f"{spec.threshold}: expected first max at "
                f"{spec.expected_maximum_location}, got {maximum_location}"
            )
        print(
            f"PASS: t={spec.threshold}, depth>={spec.first_parent_depth}, "
            f"{observed_rows} rows/{observed_matrices} matrices, "
            f"max={maximum}={float(maximum):.12g} <= "
            f"rho={spec.rho}"
        )
    return cone_rows, recurrence_rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--cone-output", type=Path, default=DEFAULT_CONE_OUTPUT)
    parser.add_argument(
        "--recurrence-output", type=Path, default=DEFAULT_RECURRENCE_OUTPUT
    )
    parser.add_argument("--skip-sha", action="store_true")
    args = parser.parse_args()

    self_test()
    groups, digest = load_groups(args.input, not args.skip_sha)
    matrices: dict[tuple[int, int], list[list[int]]] = {}
    totals: dict[tuple[int, int], int] = {}
    for key, group in groups.items():
        matrices[key], totals[key] = reconstruct_cells(key, group)
    print(f"PASS: reconstructed {len(matrices)} exact 8x8 mass matrices")

    verify_obstruction(matrices)
    cone_rows, recurrence_rows = verify_cones(
        groups, matrices, totals, args.input.name, digest, not args.skip_sha
    )
    write_rows(args.cone_output, cone_rows)
    write_rows(args.recurrence_output, recurrence_rows)


if __name__ == "__main__":
    main()

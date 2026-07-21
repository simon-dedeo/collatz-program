#!/usr/bin/env python3
"""Verify exact finite weighted cones for the KL oscillation genealogy.

The input table stores cumulative high-parent/high-child masses for seven
oscillation thresholds.  Mobius differencing reconstructs the exact 8-by-8
mass matrix between oscillation bins at every observed genealogy transition.

For every tracked target threshold with high-bin block Q, this script checks
exact rational inequalities

    Q_(k,j) w <= rho w

row by row after a fixed burn-in.  Here Q is conditional on the parent bin;
the check averages over all parents in that bin and is not a pointwise-parent
or all-vector operator statement.  It also records the exact recurrence

    V_(k,j+1) = persistent_(k,j) + immigration_(k,j)
                <= rho V_(k,j) + immigration_(k,j).

The minimal observed burn-in is exactly classified on this finite grid: direct
obstructions rule out every earlier start, and rational cones close every row
from the stated start onward.  The cones were selected after inspecting
k=12,...,19, so they are exact finite certificates and future falsifiers, not
independent evidence for an all-level theorem.  The decisive missing statement
is decay of weighted immigration for each fixed terminal offset (and ultimately
for thresholds tending to zero).

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
    name: str
    threshold: Fraction
    first_parent_depth: int
    weights: tuple[Fraction, ...]
    rho: Fraction
    expected_row_count: int
    expected_matrix_count: int
    expected_maximum: Fraction
    expected_maximum_location: tuple[int, int, int]
    lower_policy_locations: tuple[tuple[int, int, int], ...] = ()

    @property
    def first_high_bin(self) -> int:
        return THRESHOLDS.index(self.threshold) + 1


CONE_SPECS = (
    ConeSpec(
        name="frontier_t_1_20",
        threshold=Fraction(1, 20),
        first_parent_depth=6,
        weights=tuple(
            Fraction(value, 1_000_000_000)
            for value in (
                1_000_000_000,
                1_078_786_101,
                1_083_682_611,
                1_072_436_018,
                1_087_675_568,
                1_090_717_598,
                1_097_747_396,
            )
        ),
        rho=Fraction(
            25604305653308784707641489927,
            25747725810864661525426071486,
        ),
        expected_row_count=476,
        expected_matrix_count=68,
        expected_maximum=Fraction(
            25604305653308784707641489927,
            25747725810864661525426071486,
        ),
        expected_maximum_location=(19, 6, 2),
        lower_policy_locations=(
            (12, 6, 1),
            (19, 6, 2),
            (18, 6, 3),
            (14, 6, 4),
            (19, 6, 5),
            (15, 6, 6),
            (19, 6, 7),
        ),
    ),
    ConeSpec(
        name="frontier_t_1_10",
        threshold=Fraction(1, 10),
        first_parent_depth=3,
        weights=tuple(
            Fraction(value, 1_000_000_000)
            for value in (
                1_000_000_000,
                1_103_526_563,
                1_098_866_751,
                1_103_113_704,
                1_092_593_986,
                1_102_660_524,
            )
        ),
        rho=Fraction(13126911, 13132306),
        expected_row_count=503,
        expected_matrix_count=92,
        expected_maximum=Fraction(13126911, 13132306),
        expected_maximum_location=(15, 4, 5),
        lower_policy_locations=(
            (17, 6, 2),
            (12, 4, 3),
            (16, 3, 4),
            (15, 4, 5),
            (17, 4, 6),
            (19, 4, 7),
        ),
    ),
    ConeSpec(
        name="frontier_t_3_20",
        threshold=Fraction(3, 20),
        first_parent_depth=3,
        weights=tuple(
            Fraction(value, 1_000_000_000)
            for value in (
                1_118_644_048,
                1_067_801_896,
                1_114_108_653,
                1_000_000_000,
                1_109_159_419,
            )
        ),
        rho=Fraction(1109159419, 1114108653),
        expected_row_count=427,
        expected_matrix_count=92,
        expected_maximum=Fraction(1109159419, 1114108653),
        expected_maximum_location=(15, 4, 5),
        lower_policy_locations=(
            (12, 4, 3),
            (16, 3, 4),
            (15, 4, 5),
            (17, 4, 6),
            (19, 4, 7),
        ),
    ),
    ConeSpec(
        name="frontier_t_1_5",
        threshold=Fraction(1, 5),
        first_parent_depth=3,
        weights=tuple(
            Fraction(value, 500_000_000)
            for value in (
                618_715_355,
                696_512_628,
                500_000_000,
                684_092_097,
            )
        ),
        rho=Fraction(
            2912532534121995264428473938133,
            2965413132193948656185125405206,
        ),
        expected_row_count=349,
        expected_matrix_count=92,
        expected_maximum=Fraction(
            2912532534121995264428473938133,
            2965413132193948656185125405206,
        ),
        expected_maximum_location=(19, 3, 7),
        lower_policy_locations=(
            (16, 3, 4),
            (15, 4, 5),
            (17, 4, 6),
            (19, 3, 7),
        ),
    ),
    ConeSpec(
        name="frontier_t_1_4",
        threshold=Fraction(1, 4),
        first_parent_depth=3,
        weights=tuple(
            Fraction(value, 1_000_000_000)
            for value in (1_452_832_836, 1_000_000_000, 1_246_903_523)
        ),
        rho=Fraction(1246903523, 1452832836),
        expected_row_count=260,
        expected_matrix_count=92,
        expected_maximum=Fraction(1246903523, 1452832836),
        expected_maximum_location=(15, 4, 5),
        lower_policy_locations=(
            (15, 4, 5),
            (17, 4, 6),
            (19, 3, 7),
        ),
    ),
    ConeSpec(
        name="frontier_t_3_10",
        threshold=Fraction(3, 10),
        first_parent_depth=2,
        weights=(Fraction(1), Fraction(1)),
        rho=Fraction(
            4334815655959768610198, 4845180013388557558821
        ),
        expected_row_count=184,
        expected_matrix_count=100,
        expected_maximum=Fraction(
            4334815655959768610198, 4845180013388557558821
        ),
        expected_maximum_location=(19, 2, 7),
    ),
    ConeSpec(
        name="frontier_t_2_5",
        threshold=Fraction(2, 5),
        first_parent_depth=2,
        weights=(Fraction(1),),
        rho=Fraction(
            4334815655959768610198, 4845180013388557558821
        ),
        expected_row_count=100,
        expected_matrix_count=100,
        expected_maximum=Fraction(
            4334815655959768610198, 4845180013388557558821
        ),
        expected_maximum_location=(19, 2, 7),
    ),
)


# This simpler witness was selected and committed before the floating k=20
# holdout was inspected.  Keep it as a separate regression even though the
# systematic exact frontier above contains a tighter t=1/5 cone.
PREREGISTERED_CONE_SPECS = (
    ConeSpec(
        name="preregistered_t_1_5",
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

    # A stronger exact obstruction rules out every threshold at most 1/4 from
    # beginning at depth two.  The first row forces w5<w7 for rho<1; the
    # second forces w7<w5.  They need not be consecutive: a common cone must
    # satisfy both.
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

    # At t=3/10 and 2/5, the k=19 depth-two B7 row has only a low B5 child
    # and a B7 child.  Its B7 self-coefficient is therefore an unavoidable
    # lower bound for every positive cone, and the unit-weight witness attains
    # it.  This pins the last two optima exactly.
    high_threshold_row = matrices[(19, 2)][7]
    expected_high_threshold_row = {
        5: 510364357428788948623,
        7: 4334815655959768610198,
    }
    if {
        child_bin: mass
        for child_bin, mass in enumerate(high_threshold_row)
        if mass
    } != expected_high_threshold_row:
        raise AssertionError("k=19 high-threshold optimum row changed")
    exact_high_threshold_optimum = Fraction(
        expected_high_threshold_row[7], sum(expected_high_threshold_row.values())
    )
    if any(
        spec.rho != exact_high_threshold_optimum
        for spec in CONE_SPECS[-2:]
    ):
        raise AssertionError("high-threshold exact optimum changed")

    # At t=1/20 the obstruction persists through every start depth <=5.  At
    # depth at least five, each high bin has a row that loses no mass to B0.
    # Choose a minimum-weight high bin: its stochastic average of high-child
    # weights is at least its own weight, so no rho<1 can contract that row.
    lossless_coverage = {
        1: (12, 5),
        2: (15, 5),
        3: (12, 5),
        4: (12, 5),
        5: (13, 5),
        6: (12, 5),
        7: (12, 5),
    }
    for parent_bin, key in lossless_coverage.items():
        row = matrices[key][parent_bin]
        if row[0] != 0 or sum(row) <= 0:
            raise AssertionError(
                f"lossless t=1/20 obstruction row changed at {key}, "
                f"B{parent_bin}"
            )
    print("PASS: exact minimal-burn-in obstruction families")


def verify_cones(
    groups: dict[tuple[int, int], dict[tuple[Fraction, Fraction], dict[str, str]]],
    matrices: dict[tuple[int, int], list[list[int]]],
    totals: dict[tuple[int, int], int],
    input_name: str,
    input_sha256: str,
    input_sha256_verified: bool,
    specs: tuple[ConeSpec, ...] = CONE_SPECS,
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    cone_rows: list[dict[str, object]] = []
    recurrence_rows: list[dict[str, object]] = []

    for spec in specs:
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
                "spec_name": spec.name,
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
                    "spec_name": spec.name,
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
        if not (maximum <= spec.rho < 1):
            raise AssertionError(f"{spec.name}: invalid exact cone bound")

        lower_text = ""
        if spec.lower_policy_locations:
            expected_bins = tuple(range(high, 8))
            policy_bins = tuple(
                parent_bin
                for _, _, parent_bin in spec.lower_policy_locations
            )
            if policy_bins != expected_bins:
                raise AssertionError(
                    f"{spec.name}: lower policy does not cover high bins"
                )
            policy_ratios = []
            for k, parent_depth, parent_bin in spec.lower_policy_locations:
                cells = matrices[(k, parent_depth)]
                parent_mass = sum(cells[parent_bin])
                if parent_mass == 0:
                    raise AssertionError(f"{spec.name}: empty lower-policy row")
                weighted_child = sum(
                    cells[parent_bin][child_bin]
                    * spec.weights[child_bin - high]
                    for child_bin in range(high, 8)
                )
                weighted_parent = (
                    parent_mass * spec.weights[parent_bin - high]
                )
                policy_ratios.append(weighted_child / weighted_parent)
            lower = min(policy_ratios)
            if lower > maximum:
                raise AssertionError(f"{spec.name}: inverted optimum bracket")
            if maximum - lower >= Fraction(7, 10_000_000_000):
                raise AssertionError(f"{spec.name}: optimum bracket widened")
            lower_text = f", rho*>= {float(lower):.12g}"
        print(
            f"PASS: {spec.name}, t={spec.threshold}, "
            f"depth>={spec.first_parent_depth}, "
            f"{observed_rows} rows/{observed_matrices} matrices, "
            f"max={maximum}={float(maximum):.12g} <= "
            f"rho={spec.rho}{lower_text}"
        )
    return cone_rows, recurrence_rows


def verify_terminal_immigration_patterns(
    recurrence_rows: list[dict[str, object]],
) -> None:
    def immigration(row: dict[str, object]) -> Fraction:
        return Fraction(
            int(row["immigration_potential_num"]),
            int(row["immigration_potential_den"]),
        )

    def sequence(spec_name: str, terminal_offset: int) -> list[Fraction]:
        matching = sorted(
            (
                row
                for row in recurrence_rows
                if row["spec_name"] == spec_name
                and int(row["terminal_offset"]) == terminal_offset
            ),
            key=lambda row: int(row["k"]),
        )
        if [int(row["k"]) for row in matching] != list(EXPECTED_LEVELS):
            raise AssertionError(
                f"{spec_name}: incomplete fixed-offset immigration sequence"
            )
        return [immigration(row) for row in matching]

    for spec_name in ("frontier_t_1_5", "frontier_t_3_10"):
        for terminal_offset in range(5):
            values = sequence(spec_name, terminal_offset)
            if not all(right < left for left, right in zip(values, values[1:])):
                raise AssertionError(
                    f"{spec_name}: expected decreasing immigration at "
                    f"offset {terminal_offset}"
                )

    for terminal_offset in range(1, 5):
        values = sequence("frontier_t_1_20", terminal_offset)
        if not all(right > left for left, right in zip(values, values[1:])):
            raise AssertionError(
                "frontier_t_1_20: expected increasing immigration at "
                f"offset {terminal_offset}"
            )
    print("PASS: exact fixed-offset immigration trend regressions")


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
    # Preserve the originally preregistered t=1/5 witness as a regression,
    # but keep the generated tables on the systematic seven-threshold map.
    verify_cones(
        groups,
        matrices,
        totals,
        args.input.name,
        digest,
        not args.skip_sha,
        PREREGISTERED_CONE_SPECS,
    )
    cone_rows, recurrence_rows = verify_cones(
        groups,
        matrices,
        totals,
        args.input.name,
        digest,
        not args.skip_sha,
        CONE_SPECS,
    )
    verify_terminal_immigration_patterns(recurrence_rows)
    write_rows(args.cone_output, cone_rows)
    write_rows(args.recurrence_output, recurrence_rows)


if __name__ == "__main__":
    main()

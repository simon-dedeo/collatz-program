#!/usr/bin/env python3
"""Certify interval bounds for a polynomial genealogy energy envelope.

For a level-k certificate and one genealogy parent, write its three child
masses as ``x_i``, their sum as ``P``, and the total certificate mass as
``T``.  The parent-weighted Pearson divergence from the uniform three-point
law is

    (P/T) chi^2((x_i/P) || uniform_3)
      = (1/(3T)) N/P,
    N = sum_i (3 x_i - P)^2.

If ``N = qP+r``, then

    q <= N/P <= q + 1_(r != 0).

Summing these integer bounds gives a narrow, rigorous interval for every
depth energy ``chi_(k,j)`` without constructing an enormous rational common
denominator.  All envelope and trend decisions use the interval endpoints.
The large fine levels are evaluated by the tracked unsigned-128-bit C++ core;
once a parent could exceed its proved square-sum safety bound, the remaining
at-most-short hierarchy is completed with Python integers.

The current exact tower k=12,...,19 satisfies the post-hoc calibration

    chi_(k,j) <= 6/j^2.

Exploratory calculations on the separately pinned floating k=20 vector and
annealed fixed-depth profile were inspected when choosing the constant, but
they are not certified by this verifier.  This exact finite audit is therefore
a future falsifier, not an all-level theorem.  Unlike the earlier geometric
fits, polynomial decay is not structurally excluded by the proved low-depth
annealed floor.  Since relative entropy is at most Pearson chi-square, a
uniform theorem of this form would imply

    sum_(j>J) h_(k,j) <= 6/J

and the conditional-Pinsker residual bound ``sqrt(12/J)``.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import os
from pathlib import Path
import subprocess
import tempfile

import numpy as np

import multiscale_genealogy as genealogy
from verify_martingale_increment_envelope import exact_nonnegative_sum


HERE = Path(__file__).resolve().parent
CORE_SOURCE = HERE / "chi_square_interval_core.cpp"
DEFAULT_OUTPUT = HERE / "analysis_cache" / "chi_square_intervals_exact.csv"
EXPECTED_LEVELS = tuple(range(12, 20))
ENVELOPE_NUMERATOR = 6
FINITE_ONLY_ENVELOPE_NUMERATOR = 2
BIGINT_HANDOFF_CAP = 100_000
EXPECTED_TOTAL_MASS = {
    12: 1_373_960_412_522_506_741,
    13: 4_475_321_486_922_343_160,
    14: 14_596_152_850_956_151_164,
    15: 47_049_100_452_382_107_460,
    16: 150_018_628_595_844_245_849,
    17: 479_475_287_827_487_078_427,
    18: 1_523_556_169_197_024_107_847,
    19: 4_845_180_013_388_557_558_821,
}


def compile_core(cxx: str, output: Path) -> None:
    """Compile the tracked bulk helper in a temporary directory."""

    command = [
        cxx,
        "-O3",
        "-std=c++17",
        "-Wall",
        "-Wextra",
        str(CORE_SOURCE),
        "-o",
        str(output),
    ]
    try:
        result = subprocess.run(
            command,
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as error:
        raise RuntimeError(f"C++ compiler not found: {cxx}") from error
    except subprocess.CalledProcessError as error:
        raise RuntimeError(
            "failed to compile chi-square interval core:\n" + error.stderr
        ) from error
    if result.stderr.strip():
        print(result.stderr.strip())


def ensure_npy_input(values: np.ndarray, k: int, directory: Path) -> Path:
    """Return the existing sidecar, or materialize a small inline manifest."""

    if isinstance(values, np.memmap):
        path = Path(values.filename)
        if path.suffix == ".npy" and int(getattr(values, "offset", -1)) >= 0:
            return path
    path = directory / f"cert_k{k}_inline.npy"
    np.save(path, np.asarray(values, dtype="<i8"), allow_pickle=False)
    return path


def parse_core_output(
    output: str,
) -> tuple[int, dict[int, tuple[int, int, int, int]], int, int]:
    """Parse total, bulk interval rows, and the bigint handoff descriptor."""

    total: int | None = None
    rows: dict[int, tuple[int, int, int, int]] = {}
    stop: tuple[int, int] | None = None
    for line in output.splitlines():
        fields = line.split("\t")
        if fields[0] == "TOTAL" and len(fields) == 2:
            total = int(fields[1])
        elif fields[0] == "ROW" and len(fields) == 6:
            depth, lower, upper, count, remainders = map(int, fields[1:])
            if depth in rows:
                raise AssertionError(f"duplicate core row at depth {depth}")
            rows[depth] = (lower, upper, count, remainders)
        elif fields[0] == "STOP" and len(fields) == 3:
            stop = (int(fields[1]), int(fields[2]))
        elif line.strip():
            raise AssertionError(f"unrecognized core output: {line}")
    if total is None or stop is None:
        raise AssertionError("bulk core omitted TOTAL or STOP record")
    return total, rows, stop[0], stop[1]


def bigint_tail(
    children: list[int], first_depth: int
) -> tuple[dict[int, tuple[int, int, int, int]], list[int]]:
    """Complete the short coarse hierarchy with arbitrary-precision integers."""

    rows: dict[int, tuple[int, int, int, int]] = {}
    for depth in range(first_depth, 0, -1):
        if len(children) % 3:
            raise AssertionError("bigint genealogy length is not divisible by three")
        parent_count = len(children) // 3
        parents = [0] * parent_count
        lower = 0
        upper = 0
        nonzero_remainders = 0
        for parent_index in range(parent_count):
            x0 = children[parent_index]
            x1 = children[parent_count + parent_index]
            x2 = children[2 * parent_count + parent_index]
            parent = x0 + x1 + x2
            if parent <= 0:
                raise AssertionError("genealogy parent mass must be positive")
            parents[parent_index] = parent
            numerator = sum(
                (3 * child - parent) ** 2 for child in (x0, x1, x2)
            )
            quotient, remainder = divmod(numerator, parent)
            lower += quotient
            upper += quotient + bool(remainder)
            nonzero_remainders += bool(remainder)
        rows[depth] = (lower, upper, parent_count, nonzero_remainders)
        children = parents
    return rows, children


def verify_core_self_tests(core: Path, directory: Path) -> None:
    """Cross-check the accelerator, including its dynamic bigint handoff."""

    cases = {
        "ordinary": np.arange(1, 10, dtype="<i8"),
        "safety_stop": np.full(9, 10**18, dtype="<i8"),
    }
    for name, values in cases.items():
        input_path = directory / f"self_test_{name}.npy"
        coarse_path = directory / f"self_test_{name}.raw"
        np.save(input_path, values, allow_pickle=False)
        result = subprocess.run(
            [str(core), str(input_path), "3", str(coarse_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        core_total, rows, stop_depth, stop_count = parse_core_output(result.stdout)
        coarse = [int(value) for value in np.fromfile(coarse_path, dtype="<u8")]
        if len(coarse) != stop_count:
            raise AssertionError(f"{name}: self-test handoff length changed")
        tail_rows, root = bigint_tail(coarse, stop_depth)
        if set(rows) & set(tail_rows):
            raise AssertionError(f"{name}: self-test duplicated a depth")
        rows.update(tail_rows)
        reference_rows, reference_root = bigint_tail(
            [int(value) for value in values], 2
        )
        if (
            rows != reference_rows
            or root != reference_root
            or core_total != sum(int(value) for value in values)
        ):
            raise AssertionError(f"{name}: C++/Python interval cross-check failed")
        if name == "safety_stop" and (stop_depth, stop_count) != (1, 3):
            raise AssertionError("dynamic square-sum safety stop did not trigger")
    print("PASS: C++ bulk core matches Python bigints, including safety handoff")


def interval_row(
    *,
    k: int,
    depth: int,
    lower: int,
    upper: int,
    parent_count: int,
    nonzero_remainders: int,
    total_mass: int,
    source: str,
    digest: str,
    hash_verified: bool,
    hash_kind: str,
) -> dict[str, object]:
    common_denominator = 3 * total_mass
    envelope = Fraction(ENVELOPE_NUMERATOR, depth**2)
    finite_only_envelope = Fraction(FINITE_ONLY_ENVELOPE_NUMERATOR, depth**2)
    upper_over_envelope = Fraction(upper * depth**2, 18 * total_mass)
    upper_over_finite_only = Fraction(upper * depth**2, 6 * total_mass)
    certified_slack = envelope - Fraction(upper, common_denominator)
    passes = upper * depth**2 <= 18 * total_mass
    passes_finite_only = upper * depth**2 <= 6 * total_mass
    if not passes:
        raise AssertionError(
            f"k={k}, depth={depth}: certified upper exceeds 6/j^2"
        )
    if not passes_finite_only:
        raise AssertionError(
            f"k={k}, depth={depth}: certified upper exceeds finite-only 2/j^2"
        )
    if upper - lower != nonzero_remainders:
        raise AssertionError("interval width does not match remainder count")
    return {
        "k": k,
        "parent_depth": depth,
        "child_depth": depth + 1,
        "terminal_offset": k - 1 - depth,
        "parent_node_count": parent_count,
        "child_node_count": 3 * parent_count,
        "total_mass": total_mass,
        "chi_lower_num": lower,
        "chi_upper_num": upper,
        "chi_common_den": common_denominator,
        "chi_lower_decimal": f"{lower / common_denominator:.17g}",
        "chi_upper_decimal": f"{upper / common_denominator:.17g}",
        "interval_width_num": upper - lower,
        "interval_width_den": common_denominator,
        "interval_width_decimal": f"{(upper - lower) / common_denominator:.17g}",
        "nonzero_remainder_count": nonzero_remainders,
        "envelope_num": envelope.numerator,
        "envelope_den": envelope.denominator,
        "envelope_decimal": f"{float(envelope):.17g}",
        "certified_upper_over_envelope_num": upper_over_envelope.numerator,
        "certified_upper_over_envelope_den": upper_over_envelope.denominator,
        "certified_upper_over_envelope_decimal": f"{float(upper_over_envelope):.17g}",
        "certified_envelope_slack_num": certified_slack.numerator,
        "certified_envelope_slack_den": certified_slack.denominator,
        "certified_envelope_slack_decimal": f"{float(certified_slack):.17g}",
        "passes_envelope": passes,
        "finite_only_envelope_num": finite_only_envelope.numerator,
        "finite_only_envelope_den": finite_only_envelope.denominator,
        "finite_only_envelope_decimal": f"{float(finite_only_envelope):.17g}",
        "certified_upper_over_finite_only_num": upper_over_finite_only.numerator,
        "certified_upper_over_finite_only_den": upper_over_finite_only.denominator,
        "certified_upper_over_finite_only_decimal": f"{float(upper_over_finite_only):.17g}",
        "passes_finite_only_envelope": passes_finite_only,
        "finite_only_scope": "post_hoc_exact_k12_k19; not_an_all_level_target",
        "envelope_scope": "post_hoc_exact_k12_k19",
        "arithmetic": "certified_integer_interval",
        "source_kind": "exact_feasible_certificate",
        "source": source,
        "source_sha256": digest,
        "source_sha256_verified": hash_verified,
        "source_sha256_kind": hash_kind,
    }


def analyze_level(
    k: int,
    chunk_size: int,
    verify_sha: bool,
    core: Path,
    temporary_directory: Path,
) -> list[dict[str, object]]:
    values, source, digest, hash_verified, hash_kind = (
        genealogy.load_certificate(k, verify_sha)
    )
    total_mass = exact_nonnegative_sum(values, chunk_size)
    if total_mass != EXPECTED_TOTAL_MASS[k]:
        raise AssertionError(f"k={k}: exact total-mass regression changed")
    input_path = ensure_npy_input(values, k, temporary_directory)
    coarse_path = temporary_directory / f"chi_k{k}_coarse.raw"
    result = subprocess.run(
        [str(core), str(input_path), str(k), str(coarse_path)],
        check=True,
        capture_output=True,
        text=True,
    )
    core_total, raw_rows, stop_depth, stop_count = parse_core_output(result.stdout)
    if core_total != total_mass:
        raise AssertionError(f"k={k}: Python/core total-mass mismatch")

    coarse_array = np.fromfile(coarse_path, dtype="<u8")
    if len(coarse_array) != stop_count:
        raise AssertionError(f"k={k}: malformed coarse handoff file")
    if stop_count > BIGINT_HANDOFF_CAP:
        raise AssertionError(
            f"k={k}: refusing an oversized bigint handoff of {stop_count} values"
        )
    coarse_children = [int(value) for value in coarse_array]
    if sum(coarse_children) != total_mass:
        raise AssertionError(f"k={k}: coarse handoff changed total mass")
    tail_rows, root = bigint_tail(coarse_children, stop_depth)
    if len(root) != 1 or root[0] != total_mass:
        raise AssertionError(f"k={k}: hierarchy did not reach the exact root")
    overlap = set(raw_rows) & set(tail_rows)
    if overlap:
        raise AssertionError(f"k={k}: duplicate bulk/bigint depths {overlap}")
    raw_rows.update(tail_rows)
    if set(raw_rows) != set(range(1, k)):
        raise AssertionError(f"k={k}: incomplete depth set")
    if k == 12:
        reference_rows, reference_root = bigint_tail(
            [int(value) for value in values], k - 1
        )
        if raw_rows != reference_rows or reference_root != [total_mass]:
            raise AssertionError("k=12: full C++/Python bigint cross-check failed")

    return [
        interval_row(
            k=k,
            depth=depth,
            lower=raw_rows[depth][0],
            upper=raw_rows[depth][1],
            parent_count=raw_rows[depth][2],
            nonzero_remainders=raw_rows[depth][3],
            total_mass=total_mass,
            source=source,
            digest=digest,
            hash_verified=hash_verified,
            hash_kind=hash_kind,
        )
        for depth in range(1, k)
    ]


def lower(row: dict[str, object]) -> Fraction:
    return Fraction(int(row["chi_lower_num"]), int(row["chi_common_den"]))


def upper(row: dict[str, object]) -> Fraction:
    return Fraction(int(row["chi_upper_num"]), int(row["chi_common_den"]))


def upper_ratio(row: dict[str, object]) -> Fraction:
    return Fraction(
        int(row["certified_upper_over_envelope_num"]),
        int(row["certified_upper_over_envelope_den"]),
    )


def verify_patterns(rows: list[dict[str, object]]) -> None:
    expected_count = sum(k - 1 for k in EXPECTED_LEVELS)
    if len(rows) != expected_count:
        raise AssertionError(f"expected {expected_count} rows, got {len(rows)}")

    for k in EXPECTED_LEVELS:
        profile = [row for row in rows if int(row["k"]) == k]
        if not all(
            upper(right) < lower(left)
            for left, right in zip(profile, profile[1:])
        ):
            raise AssertionError(f"k={k}: depth decrease is not interval-certified")

    for depth in range(1, 12):
        sequence = [
            row for row in rows if int(row["parent_depth"]) == depth
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            upper(left) < lower(right)
            for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"depth {depth}: level increase is not interval-certified"
            )

    for terminal_offset in range(11):
        sequence = [
            row for row in rows if int(row["terminal_offset"]) == terminal_offset
        ]
        if len(sequence) != len(EXPECTED_LEVELS) or not all(
            upper(right) < lower(left)
            for left, right in zip(sequence, sequence[1:])
        ):
            raise AssertionError(
                f"offset {terminal_offset}: decrease is not interval-certified"
            )

    worst = max(rows, key=upper_ratio)
    if (int(worst["k"]), int(worst["parent_depth"])) != (19, 8):
        raise AssertionError("certified envelope maximum location changed")
    worst_lower_ratio = Fraction(
        int(worst["chi_lower_num"]) * int(worst["parent_depth"]) ** 2,
        18 * int(worst["total_mass"]),
    )
    if any(
        worst_lower_ratio <= upper_ratio(row)
        for row in rows
        if row is not worst
    ):
        raise AssertionError("the exact worst-envelope location is not separated")

    widest = max(
        rows,
        key=lambda row: Fraction(
            int(row["interval_width_num"]), int(row["interval_width_den"])
        ),
    )
    print(
        "PASS: certified chi-square intervals and 6/j^2 envelope, "
        f"{len(rows)} rows, worst upper ratio="
        f"{float(upper_ratio(worst)):.12g} at k/depth="
        f"{int(worst['k'])}/{int(worst['parent_depth'])}"
    )
    print(
        "PASS: the sharper finite-only 2/j^2 calibration has worst upper ratio="
        f"{3 * float(upper_ratio(worst)):.12g}; it is not the theorem target"
    )
    print(
        "PASS: interval-certified within-level decrease, fixed-depth increase, "
        "and fixed-terminal-offset decrease"
    )
    print(
        "PASS: maximum interval width="
        f"{float(Fraction(int(widest['interval_width_num']), int(widest['interval_width_den']))):.12g} "
        f"at k/depth={int(widest['k'])}/{int(widest['parent_depth'])}"
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
    parser.add_argument("--cxx", default=os.environ.get("CXX", "c++"))
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

    with tempfile.TemporaryDirectory(prefix="collatz_chi_") as temporary_name:
        temporary_directory = Path(temporary_name)
        core = temporary_directory / "chi_square_interval_core"
        compile_core(args.cxx, core)
        verify_core_self_tests(core, temporary_directory)
        rows: list[dict[str, object]] = []
        for k in requested_levels:
            level_rows = analyze_level(
                k,
                args.chunk_size,
                not args.skip_sha,
                core,
                temporary_directory,
            )
            rows.extend(level_rows)
            print(
                f"PASS: k={k}, {len(level_rows)} certified intervals, "
                f"depth-1 chi in [{level_rows[0]['chi_lower_decimal']}, "
                f"{level_rows[0]['chi_upper_decimal']}]"
            )

    rows.sort(key=lambda row: (int(row["k"]), int(row["parent_depth"])))
    if full_regression:
        verify_patterns(rows)
    else:
        print("NOTE: subset run skips full-tower trend regressions")
    write_rows(args.output, rows)


if __name__ == "__main__":
    main()

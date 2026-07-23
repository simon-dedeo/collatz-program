#!/usr/bin/env python3
"""Exact normalized extension-carry audit for period-three EC17 residues.

For a positive period-three schedule let ``U(q)`` be the kernel-checked sharp
upper budget and let ``r_(U+D)`` be the future-forced residue modulo
``2^(U+D)``.  The companion's same-cycle carry theorem identifies

    carry_D(q) = r_(U+D) // 2^U.

Every genuine period-three ray forces this carry to be zero eventually, even
when ``D`` varies with ``q``.  Thus cofinally many nonzero carries would
exclude the schedule.  This worker measures the first nonzero extension bit
above ``U`` and reconstructs every row exactly.  Bounded nonzeroness is only a
diagnostic; it is not a cofinal theorem or a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from concurrent.futures import ProcessPoolExecutor
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence

from breakoff_ether_period3_normalized_margin import (
    MINIMUM_CYCLE,
    phase_sum,
    sharp_upper_budget_bits,
    words_in_box,
)
from breakoff_ether_period3_sieve import (
    backward_residue,
    direct_series_residue,
    stays_positive,
)


SCHEMA = "collatz-breakoff-ether-period3-extension-carry-v1"


@dataclass(frozen=True)
class CarryRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle: int
    cycle_gain: int
    phase_sum: int
    shifted_branch: int
    upper_budget_bits: int
    extension_bits: int
    precision_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    carry_bits: int
    first_nonzero_extension_bit: int
    low_residue_sha256: str
    high_residue_sha256: str
    carry_sha256: str


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    nonzero_carries_by_depth: tuple[int, ...]
    all_rows_nonzero_by_depth: tuple[bool, ...]
    maximum_initial_zero_run_capped: int
    row_sha256: str


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def row_dict(row: CarryRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[CarryRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(
                row_dict(row), sort_keys=True, separators=(",", ":")
            ).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def audit_row(
    start_branch: int,
    word: Sequence[int],
    cycle: int,
    extension_bits: int,
) -> CarryRow:
    normalized_word = tuple(int(value) for value in word)
    if len(normalized_word) != 3 or extension_bits < 1:
        raise ValueError("invalid extension-carry row")
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, normalized_word):
        raise ValueError("row requires q >= 5 and a positive schedule")
    gain = sum(normalized_word)
    budget = sharp_upper_budget_bits(start_branch, normalized_word, cycle)
    precision = budget + extension_bits
    shifted = start_branch + gain * cycle
    high, transitions, accumulated = backward_residue(
        shifted, normalized_word, precision
    )
    low_mask = (1 << budget) - 1
    low = high & low_mask
    carry = high >> budget
    if carry >= 1 << extension_bits:
        raise AssertionError("extension carry exceeded its bit block")
    first_one = (carry & -carry).bit_length() if carry else 0
    if first_one > extension_bits:
        raise AssertionError("first extension bit escaped the audited block")
    return CarryRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle=cycle,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        shifted_branch=shifted,
        upper_budget_bits=budget,
        extension_bits=extension_bits,
        precision_bits=precision,
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        carry_bits=carry.bit_length(),
        first_nonzero_extension_bit=first_one,
        low_residue_sha256=digest_natural(low),
        high_residue_sha256=digest_natural(high),
        carry_sha256=digest_natural(carry),
    )


def carry_nonzero_at_depth(row: CarryRow, depth: int) -> bool:
    if not 1 <= depth <= row.extension_bits:
        raise ValueError("extension depth outside audited block")
    return (
        row.first_nonzero_extension_bit != 0
        and row.first_nonzero_extension_bit <= depth
    )


def summarize_schedule(
    rows: Sequence[CarryRow], extension_bits: int
) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    counts = tuple(
        sum(carry_nonzero_at_depth(row, depth) for row in rows)
        for depth in range(1, extension_bits + 1)
    )
    zero_runs = [
        (row.first_nonzero_extension_bit - 1)
        if row.first_nonzero_extension_bit
        else extension_bits
        for row in rows
    ]
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].cycle,
        maximum_cycle=rows[-1].cycle,
        nonzero_carries_by_depth=counts,
        all_rows_nonzero_by_depth=tuple(count == len(rows) for count in counts),
        maximum_initial_zero_run_capped=max(zero_runs),
        row_sha256=row_digest(rows),
    )


def summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    result["nonzero_carries_by_depth"] = list(
        summary.nonzero_carries_by_depth
    )
    result["all_rows_nonzero_by_depth"] = list(
        summary.all_rows_nonzero_by_depth
    )
    return result


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...], int]
) -> tuple[ScheduleSummary, list[CarryRow]]:
    word, start, cycles, extension_bits = task
    rows = [
        audit_row(start, word, cycle, extension_bits) for cycle in cycles
    ]
    return summarize_schedule(rows, extension_bits), rows


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    minimum_cycle: int,
    maximum_cycle: int,
    cycle_step: int,
    extension_bits: int,
    jobs: int,
    cycle_values: Sequence[int] | None = None,
) -> dict[str, Any]:
    if min(
        increment_abs_bound,
        max_start_branch,
        cycle_step,
        extension_bits,
        jobs,
    ) < 1:
        raise ValueError("scan counts and bounds must be positive")
    if minimum_cycle < MINIMUM_CYCLE or maximum_cycle < minimum_cycle:
        raise ValueError("invalid cycle interval")
    if cycle_values is None:
        cycles = tuple(range(minimum_cycle, maximum_cycle + 1, cycle_step))
        cycle_bounds: dict[str, Any] = {
            "cycles": [minimum_cycle, maximum_cycle, cycle_step]
        }
    else:
        cycles = tuple(int(value) for value in cycle_values)
        if (
            not cycles
            or any(value < MINIMUM_CYCLE for value in cycles)
            or tuple(sorted(set(cycles))) != cycles
        ):
            raise ValueError("cycle values must be unique, increasing, and >= 5")
        cycle_bounds = {"cycle_values": list(cycles)}
    words = words_in_box(increment_abs_bound)
    tasks = [
        (word, start, cycles, extension_bits)
        for word in words
        for start in range(1, max_start_branch + 1)
        if stays_positive(start, word)
    ]
    if jobs == 1:
        results = list(map(scan_schedule, tasks))
    else:
        with ProcessPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(scan_schedule, tasks, chunksize=1))
    summaries = [summary for summary, _ in results]
    rows = [row for _, schedule_rows in results for row in schedule_rows]
    aggregate_counts = [
        sum(carry_nonzero_at_depth(row, depth) for row in rows)
        for depth in range(1, extension_bits + 1)
    ]
    schedule_counts = [
        sum(summary.all_rows_nonzero_by_depth[depth - 1] for summary in summaries)
        for depth in range(1, extension_bits + 1)
    ]
    ordered = sorted(
        summaries,
        key=lambda item: (
            item.maximum_initial_zero_run_capped,
            item.start_branch,
            item.increment_word,
        ),
        reverse=True,
    )
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [-increment_abs_bound, increment_abs_bound],
            "start_branches": [1, max_start_branch],
            **cycle_bounds,
            "extension_bits": extension_bits,
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(summaries),
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "nonzero_carries_by_depth": aggregate_counts,
        "schedules_all_observed_rows_nonzero_by_depth": schedule_counts,
        "maximum_initial_zero_run_capped": max(
            (summary.maximum_initial_zero_run_capped for summary in summaries),
            default=None,
        ),
        "largest_zero_run_schedules": [
            summary_dict(summary) for summary in ordered[:32]
        ],
        "schedule_summaries": [summary_dict(summary) for summary in summaries],
        "theorem_interface": (
            "Companion round 225: every genuine period-three Ray eventually has "
            "shiftedResidueExtensionCarry(q,0,Delta(q),length(q)) = 0; "
            "cofinally many nonzero exact carries exclude the schedule"
        ),
        "claim_scope": (
            "finite exact same-cycle extension carries in the displayed schedule "
            "and cycle box; no finite streak is promoted to cofinal nonzeroness"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized extension-carry artifact schema")
    bounds = artifact["bounds"]
    increment_abs_bound = int(bounds["increment_components"][1])
    if bounds["increment_components"] != [
        -increment_abs_bound,
        increment_abs_bound,
    ]:
        raise ValueError("asymmetric increment bounds")
    start_bounds = bounds["start_branches"]
    if start_bounds[0] != 1:
        raise ValueError("start-branch interval must begin at one")
    cycles = bounds.get("cycles")
    cycle_values = bounds.get("cycle_values")
    if (cycles is None) == (cycle_values is None):
        raise ValueError("artifact must specify exactly one cycle scheme")
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(start_bounds[1]),
        minimum_cycle=(int(cycles[0]) if cycles is not None else MINIMUM_CYCLE),
        maximum_cycle=(int(cycles[1]) if cycles is not None else MINIMUM_CYCLE),
        cycle_step=(int(cycles[2]) if cycles is not None else 1),
        extension_bits=int(bounds["extension_bits"]),
        jobs=jobs,
        cycle_values=(
            tuple(int(value) for value in cycle_values)
            if cycle_values is not None
            else None
        ),
    )


def verify_artifact(path: Path, jobs: int) -> None:
    artifact = json.loads(path.read_text())
    reconstructed = reconstruct(artifact, jobs)
    for key, value in reconstructed.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("extension-carry artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 5, 7),
        (2, (-1, 1, 1), 7, 9),
        (1, (1, -1, 1), 9, 11),
    ]
    for start, word, cycle, extension_bits in cases:
        row = audit_row(start, word, cycle, extension_bits)
        high, _, _ = backward_residue(
            row.shifted_branch, word, row.precision_bits
        )
        if high != direct_series_residue(
            row.shifted_branch, word, row.precision_bits
        ):
            raise AssertionError("direct series disagrees with backward evaluator")
        low, _, _ = backward_residue(
            row.shifted_branch, word, row.upper_budget_bits
        )
        if low != high % (1 << row.upper_budget_bits):
            raise AssertionError("high residue did not reduce to the low residue")
        carry = high >> row.upper_budget_bits
        if digest_natural(carry) != row.carry_sha256:
            raise AssertionError("carry digest mismatch")
    tiny = scan_box(1, 3, 5, 7, 1, 5, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny extension-carry scan failed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    scan = subparsers.add_parser("scan")
    scan.add_argument("--increment-bound", type=int, default=1)
    scan.add_argument("--max-start", type=int, default=8)
    scan.add_argument("--min-cycle", type=int, default=5)
    scan.add_argument("--max-cycle", type=int, default=256)
    scan.add_argument("--cycle-step", type=int, default=1)
    scan.add_argument("--extension-bits", type=int, default=16)
    scan.add_argument("--jobs", type=int, default=1)
    scan.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    verify.add_argument("--jobs", type=int, default=1)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "selftest":
        selftest()
        print("extension-carry period-three self-test passed")
        return
    if args.command == "scan":
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            minimum_cycle=args.min_cycle,
            maximum_cycle=args.max_cycle,
            cycle_step=args.cycle_step,
            extension_bits=args.extension_bits,
            jobs=args.jobs,
        )
        artifact["generated_at"] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps({
            "artifact": str(args.output),
            "exact_rows_checked": artifact["exact_rows_checked"],
            "nonzero_carries_by_depth": artifact["nonzero_carries_by_depth"],
            "schedules_all_observed_rows_nonzero_by_depth":
                artifact["schedules_all_observed_rows_nonzero_by_depth"],
            "counterexample": artifact["counterexample"],
        }, indent=2, sort_keys=True))
        return
    verify_artifact(args.artifact, args.jobs)
    print("extension-carry period-three artifact verified")


if __name__ == "__main__":
    main()

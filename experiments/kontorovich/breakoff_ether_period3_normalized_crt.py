#!/usr/bin/env python3
"""Sharp-band CRT replay certificates for period-three EC17 schedules.

At cycle boundary ``q >= 5``, QM100 bounds the genuine core by

    core(3q) < 2^(U(q)+L0),

where ``L0`` is the initial core's binary digit count and ``U(q)`` is the
kernel-checked sharp upper growth budget.  The prescribed future fixes this
core modulo ``2^U``.  Its immediate predecessor independently fixes it modulo
``3^(6*n_previous+11)``.  Companion commit ``52cd3e1`` kernel-checks
QM105--QM107, under which a failed canonical CRT representative forces

    6*n_previous+11 < L0.

Failures at unbounded cycle indices would exclude the entire prescribed
period-three ray.  Finite rows only certify finite lower bounds after the Lean
consumer is checked.  They do not construct an orbit or a counterexample.
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

from breakoff_ether_period3_crt_sieve import (
    coprime_crt,
    successor_ternary_residue,
)
from breakoff_ether_period3_normalized_margin import (
    MINIMUM_CYCLE,
    phase_sum,
    sharp_upper_budget_bits,
    sharp_upper_exponent,
    words_in_box,
)
from breakoff_ether_period3_sieve import (
    PERIOD,
    backward_residue,
    literal_failure,
    stays_positive,
)


SCHEMA = "collatz-breakoff-ether-period3-normalized-crt-v1"


@dataclass(frozen=True)
class CrtRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle: int
    cycle_gain: int
    phase_sum: int
    previous_branch: int
    successor_branch: int
    predecessor_rotated_word: tuple[int, int, int]
    upper_exponent: int
    binary_precision_bits: int
    ternary_precision_exponent: int
    combined_modulus_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    candidate_bits: int
    candidate_leading_zero_bits: int
    candidate_sha256: str
    failure_step: int | None
    failure_source_branch: int | None
    failure_target_branch: int | None
    failure_numerator_v2: int | None
    failure_required_v2: int | None
    proposed_lower_bound_initial_bits: int | None


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    all_canonical_crt_representatives_failed: bool
    maximum_proposed_lower_bound_initial_bits: int | None
    maximum_candidate_leading_zero_bits: int
    maximum_candidate_leading_zero_cycle: int
    row_sha256: str


def rotate_to_predecessor(word: Sequence[int]) -> tuple[int, int, int]:
    if len(word) != PERIOD:
        raise ValueError("period-three word required")
    return int(word[2]), int(word[0]), int(word[1])


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def audit_row(start_branch: int, word: Sequence[int], cycle: int) -> CrtRow:
    normalized_word = (int(word[0]), int(word[1]), int(word[2]))
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, normalized_word):
        raise ValueError("QM100 requires q >= 5 and a positive schedule")
    gain = sum(normalized_word)
    previous = (
        start_branch
        + normalized_word[0]
        + normalized_word[1]
        + gain * (cycle - 1)
    )
    successor = start_branch + gain * cycle
    rotated = rotate_to_predecessor(normalized_word)
    if previous + rotated[0] != successor:
        raise AssertionError("predecessor rotation missed the cycle boundary")
    precision = sharp_upper_budget_bits(start_branch, normalized_word, cycle)
    upper_exponent = sharp_upper_exponent(start_branch, normalized_word, cycle)
    two_residue, transitions, accumulated = backward_residue(
        successor, normalized_word, precision
    )
    three_residue, three_modulus = successor_ternary_residue(
        previous, successor
    )
    candidate, combined_modulus = coprime_crt(
        two_residue, precision, three_residue, three_modulus
    )
    if candidate < 1:
        raise AssertionError("positive normalized CRT candidate vanished")
    if candidate % (1 << precision) != two_residue:
        raise AssertionError("CRT candidate lost its future residue")
    if candidate % three_modulus != three_residue:
        raise AssertionError("CRT candidate lost its predecessor residue")
    failure = literal_failure(
        candidate,
        successor,
        normalized_word,
        transitions + PERIOD + 64,
    )
    if failure is None:
        failure_fields: tuple[int | None, ...] = (None,) * 5
        lower_bound = None
    else:
        failure_fields = failure
        # Requested QM106 gives E<L0, so the digit count is at least E+1.
        lower_bound = 6 * previous + 12
    return CrtRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle=cycle,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        previous_branch=previous,
        successor_branch=successor,
        predecessor_rotated_word=rotated,
        upper_exponent=upper_exponent,
        binary_precision_bits=precision,
        ternary_precision_exponent=6 * previous + 11,
        combined_modulus_bits=combined_modulus.bit_length(),
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        candidate_bits=candidate.bit_length(),
        candidate_leading_zero_bits=(
            combined_modulus.bit_length() - candidate.bit_length()
        ),
        candidate_sha256=digest_natural(candidate),
        failure_step=failure_fields[0],
        failure_source_branch=failure_fields[1],
        failure_target_branch=failure_fields[2],
        failure_numerator_v2=failure_fields[3],
        failure_required_v2=failure_fields[4],
        proposed_lower_bound_initial_bits=lower_bound,
    )


def row_dict(row: CrtRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    result["predecessor_rotated_word"] = list(row.predecessor_rotated_word)
    return result


def row_digest(rows: Iterable[CrtRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(
                row_dict(row), sort_keys=True, separators=(",", ":")
            ).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def summarize(rows: Sequence[CrtRow]) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    most_zeros = max(
        rows, key=lambda row: (row.candidate_leading_zero_bits, -row.cycle)
    )
    lower_bounds = [
        row.proposed_lower_bound_initial_bits
        for row in rows
        if row.proposed_lower_bound_initial_bits is not None
    ]
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].cycle,
        maximum_cycle=rows[-1].cycle,
        all_canonical_crt_representatives_failed=all(
            row.failure_step is not None for row in rows
        ),
        maximum_proposed_lower_bound_initial_bits=(
            max(lower_bounds) if lower_bounds else None
        ),
        maximum_candidate_leading_zero_bits=(
            most_zeros.candidate_leading_zero_bits
        ),
        maximum_candidate_leading_zero_cycle=most_zeros.cycle,
        row_sha256=row_digest(rows),
    )


def summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    return result


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...]]
) -> tuple[ScheduleSummary, list[CrtRow]]:
    word, start, cycles = task
    rows = [audit_row(start, word, cycle) for cycle in cycles]
    return summarize(rows), rows


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    minimum_cycle: int,
    maximum_cycle: int,
    cycle_step: int,
    jobs: int,
    cycle_values: Sequence[int] | None = None,
) -> dict[str, Any]:
    if min(max_start_branch, cycle_step, jobs) < 1:
        raise ValueError("scan counts and jobs must be positive")
    if minimum_cycle < MINIMUM_CYCLE or maximum_cycle < minimum_cycle:
        raise ValueError("invalid QM100 cycle interval")
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
        (word, start, cycles)
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
    anomalies = sorted(
        rows,
        key=lambda row: (
            row.candidate_leading_zero_bits,
            -row.cycle,
            -row.start_branch,
            row.increment_word,
        ),
        reverse=True,
    )
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [
                -increment_abs_bound,
                increment_abs_bound,
            ],
            "start_branches": [1, max_start_branch],
            **cycle_bounds,
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(summaries),
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "all_canonical_crt_representatives_failed": all(
            summary.all_canonical_crt_representatives_failed
            for summary in summaries
        ),
        "minimum_of_schedule_lower_bounds": min(
            summary.maximum_proposed_lower_bound_initial_bits
            for summary in summaries
            if summary.maximum_proposed_lower_bound_initial_bits is not None
        ) if summaries and all(
            summary.maximum_proposed_lower_bound_initial_bits is not None
            for summary in summaries
        ) else None,
        "maximum_candidate_leading_zero_bits": max(
            row.candidate_leading_zero_bits for row in rows
        ) if rows else None,
        "leading_zero_anomalies": [row_dict(row) for row in anomalies[:64]],
        "schedule_summaries": [summary_dict(summary) for summary in summaries],
        "theorem_interface": (
            "Lean commit 52cd3e1, QM105--QM107: a failed canonical normalized CRT "
            "representative forces 6*n_previous+11 < bits(core(0))"
        ),
        "claim_scope": (
            "finite exact CRT and replay measurements in the displayed "
            "schedule/cycle box; no finite trend is promoted to a no-ray theorem"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized normalized CRT artifact schema")
    bounds = artifact["bounds"]
    increment_abs_bound = int(bounds["increment_components"][1])
    if bounds["increment_components"] != [
        -increment_abs_bound,
        increment_abs_bound,
    ]:
        raise ValueError("asymmetric increment bounds")
    starts = bounds["start_branches"]
    cycles = bounds.get("cycles")
    cycle_values = bounds.get("cycle_values")
    if (cycles is None) == (cycle_values is None):
        raise ValueError("artifact must specify exactly one cycle scheme")
    if starts[0] != 1:
        raise ValueError("start interval must begin at one")
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(starts[1]),
        minimum_cycle=(int(cycles[0]) if cycles is not None else MINIMUM_CYCLE),
        maximum_cycle=(int(cycles[1]) if cycles is not None else MINIMUM_CYCLE),
        cycle_step=(int(cycles[2]) if cycles is not None else 1),
        jobs=jobs,
        cycle_values=(
            tuple(int(value) for value in cycle_values)
            if cycle_values is not None else None
        ),
    )


def verify_artifact(path: Path, jobs: int) -> None:
    artifact = json.loads(path.read_text())
    reconstructed = reconstruct(artifact, jobs)
    for key, value in reconstructed.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("normalized CRT artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 5),
        (2, (-1, 1, 1), 7),
        (1, (1, -1, 1), 9),
    ]
    for start, word, cycle in cases:
        row = audit_row(start, word, cycle)
        if row.predecessor_rotated_word[1:] != word[:2]:
            raise AssertionError("predecessor rotation self-test failed")
        if row.ternary_precision_exponent != 6 * row.previous_branch + 11:
            raise AssertionError("ternary exponent self-test failed")
    tiny = scan_box(1, 2, 5, 7, 1, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny normalized CRT scan failed")


def write_artifact(path: Path, artifact: dict[str, Any]) -> None:
    result = dict(artifact)
    result["generated_at"] = datetime.now(timezone.utc).isoformat()
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subparsers = result.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")

    scan = subparsers.add_parser("scan")
    scan.add_argument("--increment-bound", type=int, default=1)
    scan.add_argument("--max-start", type=int, default=8)
    scan.add_argument("--min-cycle", type=int, default=5)
    scan.add_argument("--max-cycle", type=int, default=128)
    scan.add_argument("--cycle-step", type=int, default=1)
    scan.add_argument(
        "--cycle-values",
        help="comma-separated increasing cycle indices; overrides the interval",
    )
    scan.add_argument("--jobs", type=int, default=1)
    scan.add_argument("--output", type=Path, required=True)

    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    verify.add_argument("--jobs", type=int, default=1)
    return result


def main() -> None:
    args = parser().parse_args()
    if args.command == "selftest":
        selftest()
        print("normalized period-three CRT self-test passed")
        return
    if args.command == "scan":
        selftest()
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            minimum_cycle=args.min_cycle,
            maximum_cycle=args.max_cycle,
            cycle_step=args.cycle_step,
            jobs=args.jobs,
            cycle_values=(
                tuple(int(value) for value in args.cycle_values.split(","))
                if args.cycle_values else None
            ),
        )
        write_artifact(args.output, artifact)
        print(json.dumps({
            "output": str(args.output),
            "positive_schedules_checked": artifact["positive_schedules_checked"],
            "exact_rows_checked": artifact["exact_rows_checked"],
            "all_canonical_crt_representatives_failed": artifact[
                "all_canonical_crt_representatives_failed"
            ],
            "minimum_of_schedule_lower_bounds": artifact[
                "minimum_of_schedule_lower_bounds"
            ],
            "counterexample": None,
        }, sort_keys=True))
        return
    selftest()
    verify_artifact(args.artifact, args.jobs)
    print("normalized period-three CRT artifact verified")


if __name__ == "__main__":
    main()

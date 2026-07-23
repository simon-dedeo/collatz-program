#!/usr/bin/env python3
"""Theorem-directed normalized 2-adic margins for period-three EC17 rays.

For a positive period-three branch schedule with cycle gain ``G``, phase sum
``B``, and cycle index ``q >= 5``, the kernel-checked sharp upper estimate is

    bits(core(3q)) <= bits(core(0)) + U(q),

where

    A(q) = q * (462*B + 2235 + G*(693*q - 3141)),
    U(q) = ceil(A(q)/306).

The prescribed infinite future fixes ``core(3q)`` modulo ``2^P``.  At
``P = U(q)+R``, let ``r`` be the canonical forced residue.  The normalized
margin is

    bits(r)-U(q) = R-leading_zero_bits(r among P bits).

Companion commit ``52cd3e1`` kernel-checks the QM100--QM104 bridge proving
that every genuine ray must have
``bits(core(0)) >= margin``.  Consequently a finite row gives a rigorous
lower bound after that bridge is kernel-checked, while an unbounded sequence
of exact margins excludes the entire prescribed schedule.  This worker does
not infer unboundedness from a finite trend and never reports a counterexample.

The computation is shifted to the cycle boundary before applying the existing
backward EC17 residue recurrence.  It uses exact Python integers throughout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from concurrent.futures import ProcessPoolExecutor
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Sequence

from breakoff_ether_period3_sieve import (
    PERIOD,
    backward_residue,
    direct_series_residue,
    stays_positive,
    valid_period_three_word,
    v2,
)


SCHEMA = "collatz-breakoff-ether-period3-normalized-margin-v3"
UPPER_POWER = 306
UPPER_ROUNDING = UPPER_POWER - 1
MINIMUM_CYCLE = 5


@dataclass(frozen=True)
class MarginRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle: int
    shifted_branch: int
    cycle_gain: int
    phase_sum: int
    upper_exponent: int
    upper_budget_bits: int
    padding_bits: int
    precision_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    residue_bits: int
    leading_zero_bits: int
    normalized_margin_bits: int
    failure_step: int | None
    failure_source_branch: int | None
    failure_target_branch: int | None
    failure_numerator_v2: int | None
    failure_required_v2: int | None
    failure_offset_from_last_precision_transition: int | None
    failure_kind: str | None
    certified_exact_balance_steps: int | None
    certified_prefix_length: int | None
    replay_core_sha256: str | None
    extended_residue_matches: bool | None
    proposed_replay_lower_bound_initial_bits: int | None


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    maximum_margin_bits: int
    maximum_margin_cycle: int
    final_margin_bits: int
    maximum_leading_zero_bits: int
    maximum_leading_zero_cycle: int
    all_canonical_residues_failed: bool
    all_failures_at_last_precision_transition: bool
    maximum_proposed_replay_lower_bound_initial_bits: int | None
    row_sha256: str


def words_in_box(increment_abs_bound: int) -> list[tuple[int, int, int]]:
    if increment_abs_bound < 1:
        raise ValueError("increment bound must be positive")
    values = range(-increment_abs_bound, increment_abs_bound + 1)
    return [
        (a, b, c)
        for a, b, c in product(values, repeat=PERIOD)
        if valid_period_three_word((a, b, c))
    ]


def phase_sum(start_branch: int, word: Sequence[int]) -> int:
    if not stays_positive(start_branch, word):
        raise ValueError("invalid positive period-three schedule")
    return (
        start_branch
        + (start_branch + int(word[0]))
        + (start_branch + int(word[0]) + int(word[1]))
    )


def sharp_upper_exponent(
    start_branch: int, word: Sequence[int], cycle: int
) -> int:
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, word):
        raise ValueError("QM99 requires q >= 5 and a positive schedule")
    gain = sum(word)
    if gain < 1:
        raise AssertionError("positive period-three gain was lost")
    inner = (
        462 * phase_sum(start_branch, word)
        + 2235
        + gain * (693 * cycle - 3141)
    )
    if inner < 1:
        raise AssertionError("QM99 upper exponent is not positive")
    return cycle * inner


def sharp_upper_budget_bits(
    start_branch: int, word: Sequence[int], cycle: int
) -> int:
    exponent = sharp_upper_exponent(start_branch, word, cycle)
    return (exponent + UPPER_ROUNDING) // UPPER_POWER


def backward_residue_for_length(
    start_branch: int,
    word: Sequence[int],
    precision_bits: int,
    length: int,
) -> int:
    """Evaluate the zero-terminal backward recurrence for an exact length."""

    if min(precision_bits, length) < 1 or not stays_positive(start_branch, word):
        raise ValueError("invalid extended backward residue request")
    modulus = 1 << precision_bits
    levels = [start_branch]
    for transition in range(length):
        following = levels[-1] + int(word[transition % PERIOD])
        if following < 1:
            raise AssertionError("extended schedule became nonpositive")
        levels.append(following)
    residue = 0
    for transition in range(length - 1, -1, -1):
        source = levels[transition]
        target = levels[transition + 1]
        residue = (
            ((residue << (8 * target + 15)) - 17)
            * pow(3, -(6 * source + 11), modulus)
        ) % modulus
    return residue


def replay_core_digest(cores: Sequence[int]) -> str:
    digest = hashlib.sha256()
    for core in cores:
        digest.update(f"{core.bit_length()}:{core:x}\n".encode())
    return digest.hexdigest()


def exact_replay_failure_certificate(
    candidate: int,
    start_branch: int,
    word: Sequence[int],
    precision_bits: int,
    minimum_prefix_length: int,
    max_steps: int,
) -> dict[str, Any] | None:
    """Reconstruct the exact Lean replay-certificate seam.

    Under-divisibility certifies failure at the reported transition.  Strict
    over-divisibility supplies an even quotient and requires one additional
    hypothetical transition in the ruled-out natural prefix.
    """

    core = candidate
    source = start_branch
    cores = [candidate]
    for step in range(max_steps):
        target = source + int(word[step % PERIOD])
        if target < 1:
            raise AssertionError("certified schedule became nonpositive")
        numerator = 3 ** (6 * source + 11) * core + 17
        actual = v2(numerator)
        required = 8 * target + 15
        if actual < required:
            prefix_length = max(minimum_prefix_length, step + 1)
            exact_steps = step
            kind = "nondivisible"
        else:
            quotient = numerator >> required
            if actual > required:
                if quotient % 2 != 0:
                    raise AssertionError("over-divisible quotient is not even")
                cores.append(quotient)
                prefix_length = max(minimum_prefix_length, step + 2)
                exact_steps = step + 1
                kind = "even_quotient"
            else:
                core = quotient
                cores.append(core)
                source = target
                continue
        extended = backward_residue_for_length(
            start_branch, word, precision_bits, prefix_length
        )
        if extended != candidate % (1 << precision_bits):
            raise AssertionError("extended zero-terminal residue changed")
        return {
            "failure_step": step,
            "failure_source_branch": source,
            "failure_target_branch": target,
            "failure_numerator_v2": actual,
            "failure_required_v2": required,
            "failure_kind": kind,
            "certified_exact_balance_steps": exact_steps,
            "certified_prefix_length": prefix_length,
            "replay_core_sha256": replay_core_digest(cores),
            "extended_residue_matches": True,
        }
    return None


def audit_row(
    start_branch: int,
    word: Sequence[int],
    cycle: int,
    padding_bits: int,
) -> MarginRow:
    if padding_bits < 1:
        raise ValueError("padding must be positive")
    normalized_word = (int(word[0]), int(word[1]), int(word[2]))
    gain = sum(normalized_word)
    upper_exponent = sharp_upper_exponent(
        start_branch, normalized_word, cycle
    )
    budget = (upper_exponent + UPPER_ROUNDING) // UPPER_POWER
    precision = budget + padding_bits
    shifted_branch = start_branch + gain * cycle
    residue, transitions, accumulated = backward_residue(
        shifted_branch, normalized_word, precision
    )
    if residue < 1 or residue % 2 != 1:
        raise AssertionError("the future-forced EC17 residue is not positive odd")
    residue_bits = residue.bit_length()
    leading_zeros = precision - residue_bits
    margin = residue_bits - budget
    if margin != padding_bits - leading_zeros:
        raise AssertionError("normalized-margin identity failed")
    if not 306 * (budget - 1) < upper_exponent <= 306 * budget:
        raise AssertionError("ceiling conversion failed")
    failure = exact_replay_failure_certificate(
        residue,
        shifted_branch,
        normalized_word,
        precision,
        transitions,
        transitions + PERIOD + 64,
    )
    if failure is None:
        failure_fields: tuple[int | None, ...] = (None,) * 5
        failure_offset = None
        failure_kind = None
        exact_steps = None
        prefix_length = None
        replay_digest = None
        extended_matches = None
        replay_lower_bound = None
    else:
        failure_fields = (
            failure["failure_step"],
            failure["failure_source_branch"],
            failure["failure_target_branch"],
            failure["failure_numerator_v2"],
            failure["failure_required_v2"],
        )
        failure_offset = int(failure["failure_step"]) - (transitions - 1)
        failure_kind = str(failure["failure_kind"])
        exact_steps = int(failure["certified_exact_balance_steps"])
        prefix_length = int(failure["certified_prefix_length"])
        replay_digest = str(failure["replay_core_sha256"])
        extended_matches = bool(failure["extended_residue_matches"])
        # QM104 turns this exact failure into L0 > padding_bits.
        replay_lower_bound = padding_bits + 1
    return MarginRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle=cycle,
        shifted_branch=shifted_branch,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        upper_exponent=upper_exponent,
        upper_budget_bits=budget,
        padding_bits=padding_bits,
        precision_bits=precision,
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        residue_bits=residue_bits,
        leading_zero_bits=leading_zeros,
        normalized_margin_bits=margin,
        failure_step=failure_fields[0],
        failure_source_branch=failure_fields[1],
        failure_target_branch=failure_fields[2],
        failure_numerator_v2=failure_fields[3],
        failure_required_v2=failure_fields[4],
        failure_offset_from_last_precision_transition=failure_offset,
        failure_kind=failure_kind,
        certified_exact_balance_steps=exact_steps,
        certified_prefix_length=prefix_length,
        replay_core_sha256=replay_digest,
        extended_residue_matches=extended_matches,
        proposed_replay_lower_bound_initial_bits=replay_lower_bound,
    )


def row_dict(row: MarginRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[MarginRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(
                row_dict(row), sort_keys=True, separators=(",", ":")
            ).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def summarize_rows(rows: Sequence[MarginRow]) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    best = max(rows, key=lambda row: (row.normalized_margin_bits, -row.cycle))
    most_zeros = max(rows, key=lambda row: (row.leading_zero_bits, -row.cycle))
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].cycle,
        maximum_cycle=rows[-1].cycle,
        maximum_margin_bits=best.normalized_margin_bits,
        maximum_margin_cycle=best.cycle,
        final_margin_bits=rows[-1].normalized_margin_bits,
        maximum_leading_zero_bits=most_zeros.leading_zero_bits,
        maximum_leading_zero_cycle=most_zeros.cycle,
        all_canonical_residues_failed=all(
            row.failure_step is not None for row in rows
        ),
        all_failures_at_last_precision_transition=all(
            row.failure_offset_from_last_precision_transition == 0
            for row in rows
        ),
        maximum_proposed_replay_lower_bound_initial_bits=max(
            (
                row.proposed_replay_lower_bound_initial_bits
                for row in rows
                if row.proposed_replay_lower_bound_initial_bits is not None
            ),
            default=None,
        ),
        row_sha256=row_digest(rows),
    )


def summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    return result


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...], int, int]
) -> tuple[ScheduleSummary, list[MarginRow]]:
    word, start, cycles, padding_slope, padding_intercept = task
    rows = [
        audit_row(
            start,
            word,
            cycle,
            padding_slope * cycle + padding_intercept,
        )
        for cycle in cycles
    ]
    return summarize_rows(rows), rows


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    minimum_cycle: int,
    maximum_cycle: int,
    cycle_step: int,
    padding_slope: int,
    padding_intercept: int,
    jobs: int,
    cycle_values: Sequence[int] | None = None,
) -> dict[str, Any]:
    if min(max_start_branch, cycle_step, padding_slope, jobs) < 1:
        raise ValueError("scan counts, slope, and jobs must be positive")
    if minimum_cycle < MINIMUM_CYCLE or maximum_cycle < minimum_cycle:
        raise ValueError("invalid QM99 cycle interval")
    if padding_intercept < 0:
        raise ValueError("padding intercept must be nonnegative")
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
        (word, start, cycles, padding_slope, padding_intercept)
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
    ordered = sorted(
        summaries,
        key=lambda item: (
            item.maximum_margin_bits,
            item.final_margin_bits,
            -item.start_branch,
            item.increment_word,
        ),
        reverse=True,
    )
    zero_anomalies = sorted(
        rows,
        key=lambda row: (
            row.leading_zero_bits,
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
            "padding_bits": {
                "slope_times_cycle": padding_slope,
                "intercept": padding_intercept,
            },
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(summaries),
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "maximum_margin_bits": max(
            summary.maximum_margin_bits for summary in summaries
        ) if summaries else None,
        "minimum_of_schedule_maximum_margins": min(
            summary.maximum_margin_bits for summary in summaries
        ) if summaries else None,
        "all_canonical_residues_failed": all(
            summary.all_canonical_residues_failed for summary in summaries
        ),
        "all_failures_at_last_precision_transition": all(
            summary.all_failures_at_last_precision_transition
            for summary in summaries
        ),
        "minimum_of_schedule_replay_lower_bounds": min(
            summary.maximum_proposed_replay_lower_bound_initial_bits
            for summary in summaries
            if summary.maximum_proposed_replay_lower_bound_initial_bits is not None
        ) if summaries and all(
            summary.maximum_proposed_replay_lower_bound_initial_bits is not None
            for summary in summaries
        ) else None,
        "largest_margin_schedules": [
            summary_dict(summary) for summary in ordered[:32]
        ],
        "leading_zero_anomalies": [
            row_dict(row) for row in zero_anomalies[:64]
        ],
        "schedule_summaries": [summary_dict(summary) for summary in summaries],
        "theorem_interface": (
            "Lean commit 52cd3e1, QM100--QM104: every genuine period-three Ray must "
            "satisfy bits(core(0)) >= max(0, normalized_margin_bits); if "
            "the canonical residue fails exact replay, bits(core(0)) must "
            "also exceed padding_bits"
        ),
        "claim_scope": (
            "finite exact residue measurements in the displayed schedule "
            "and cycle box; no finite trend is promoted to unboundedness"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized normalized-margin artifact schema")
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
    padding = bounds["padding_bits"]
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(start_bounds[1]),
        minimum_cycle=(int(cycles[0]) if cycles is not None else MINIMUM_CYCLE),
        maximum_cycle=(int(cycles[1]) if cycles is not None else MINIMUM_CYCLE),
        cycle_step=(int(cycles[2]) if cycles is not None else 1),
        padding_slope=int(padding["slope_times_cycle"]),
        padding_intercept=int(padding["intercept"]),
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
        raise ValueError("normalized-margin artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 5, 17),
        (2, (-1, 1, 1), 7, 31),
        (1, (1, -1, 1), 9, 23),
    ]
    for start, word, cycle, padding in cases:
        row = audit_row(start, word, cycle, padding)
        direct = direct_series_residue(
            row.shifted_branch, word, row.precision_bits
        )
        residue, _, _ = backward_residue(
            row.shifted_branch, word, row.precision_bits
        )
        if direct != residue:
            raise AssertionError("independent series residue disagrees")
        larger, _, _ = backward_residue(
            row.shifted_branch, word, row.precision_bits + 11
        )
        if larger % (1 << row.precision_bits) != residue:
            raise AssertionError("forced residues are not precision-compatible")
    tiny = scan_box(1, 2, 5, 7, 1, 1, 3, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny normalized-margin scan failed")


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
    scan.add_argument("--padding-slope", type=int, default=2)
    scan.add_argument("--padding-intercept", type=int, default=32)
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
        print("normalized period-three margin self-test passed")
        return
    if args.command == "scan":
        selftest()
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            minimum_cycle=args.min_cycle,
            maximum_cycle=args.max_cycle,
            cycle_step=args.cycle_step,
            padding_slope=args.padding_slope,
            padding_intercept=args.padding_intercept,
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
            "maximum_margin_bits": artifact["maximum_margin_bits"],
            "minimum_of_schedule_maximum_margins": artifact[
                "minimum_of_schedule_maximum_margins"
            ],
            "all_canonical_residues_failed": artifact[
                "all_canonical_residues_failed"
            ],
            "all_failures_at_last_precision_transition": artifact[
                "all_failures_at_last_precision_transition"
            ],
            "minimum_of_schedule_replay_lower_bounds": artifact[
                "minimum_of_schedule_replay_lower_bounds"
            ],
            "counterexample": None,
        }, sort_keys=True))
        return
    selftest()
    verify_artifact(args.artifact, args.jobs)
    print("normalized period-three margin artifact verified")


if __name__ == "__main__":
    main()

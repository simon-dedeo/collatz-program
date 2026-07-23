#!/usr/bin/env python3
"""Exact tight-budget residue/congruence tests for period-three EC17 rays.

Companion commit ``5a3413a`` proves a sharper period-three digit budget from
``3^971 < 2^1539``.  Put

    U(q) = ceil(G0(q)/306),
    V(q) = ceil(G1(q)/971),

where ``G0`` is the previous sharp growth numerator and

    G1(q) = q*(1466*B + 7092 + K*(2199*q - 9967)).

Every hypothetical ray eventually has ``core(3q) < 2^U``.  Consequently its
canonical future residue at precision ``U`` must satisfy the immediate
predecessor congruence

    2^(8*n_q+15) * residue = 17  (mod 3^(6*n_previous+11)).

Infinitely many exact failures exclude the prescribed schedule.  At any
covered precision ``P >= V``, one failed predecessor congruence also gives
the finite lower bound ``P-V < bits(core(0))``.

This worker computes the residue once at ``P=U+R`` and masks its low ``U``
bits to test the canonical zero-lift target.  It also tests the padded residue
and records the necessary one-trit condition ``residue = 1 (mod 3)``.  All
arithmetic is exact.  Finite rows are never promoted to cofinality, and this
worker never reports a counterexample.
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

from breakoff_ether_period3_crt_sieve import successor_ternary_residue
from breakoff_ether_period3_normalized_margin import (
    MINIMUM_CYCLE,
    phase_sum,
    sharp_upper_budget_bits,
    sharp_upper_exponent,
    words_in_box,
)
from breakoff_ether_period3_sieve import backward_residue, stays_positive


SCHEMA = "collatz-breakoff-ether-period3-tight-residue-v1"
TIGHT_POWER = 971
TIGHT_ROUNDING = TIGHT_POWER - 1


@dataclass(frozen=True)
class TightResidueRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle: int
    cycle_gain: int
    phase_sum: int
    previous_branch: int
    successor_branch: int
    coarse_upper_exponent: int
    coarse_budget_bits: int
    tight971_growth_exponent: int
    tight971_budget_bits: int
    budget_gap_bits: int
    padding_bits: int
    padded_precision_bits: int
    tightened_padded_margin_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    normalized_residue_bits: int
    padded_residue_bits: int
    normalized_residue_mod3: int
    padded_residue_mod3: int
    predecessor_ternary_exponent: int
    required_predecessor_residue_mod3: int
    normalized_one_trit_matches: bool
    padded_one_trit_matches: bool
    normalized_predecessor_congruence_matches: bool
    padded_predecessor_congruence_matches: bool
    normalized_residue_sha256: str
    padded_residue_sha256: str
    proposed_normalized_lower_bound_initial_bits: int | None
    proposed_padded_lower_bound_initial_bits: int | None


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    all_normalized_predecessor_congruences_failed: bool
    all_padded_predecessor_congruences_failed: bool
    normalized_one_trit_failures: int
    padded_one_trit_failures: int
    maximum_budget_gap_bits: int
    maximum_tightened_padded_margin_bits: int
    maximum_proposed_normalized_lower_bound_initial_bits: int | None
    maximum_proposed_padded_lower_bound_initial_bits: int | None
    final_normalized_residue_mod3: int
    final_padded_residue_mod3: int
    row_sha256: str


def tight971_growth_exponent(
    start_branch: int, word: Sequence[int], cycle: int
) -> int:
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, word):
        raise ValueError("tight 971 budget requires q >= 5 and positivity")
    gain = sum(int(value) for value in word)
    result = cycle * (
        1466 * phase_sum(start_branch, word)
        + 7092
        + gain * (2199 * cycle - 9967)
    )
    if result < 1:
        raise AssertionError("tight 971 growth exponent is not positive")
    return result


def tight971_budget_bits(
    start_branch: int, word: Sequence[int], cycle: int
) -> int:
    exponent = tight971_growth_exponent(start_branch, word, cycle)
    return (exponent + TIGHT_ROUNDING) // TIGHT_POWER


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def row_dict(row: TightResidueRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[TightResidueRow]) -> str:
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
    padding_bits: int,
) -> TightResidueRow:
    normalized_word = tuple(int(value) for value in word)
    if len(normalized_word) != 3 or padding_bits < 0:
        raise ValueError("invalid tight-residue row")
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, normalized_word):
        raise ValueError("row requires q >= 5 and a positive schedule")
    gain = sum(normalized_word)
    successor = start_branch + gain * cycle
    previous = (
        start_branch
        + normalized_word[0]
        + normalized_word[1]
        + gain * (cycle - 1)
    )
    coarse_exponent = sharp_upper_exponent(
        start_branch, normalized_word, cycle
    )
    coarse_budget = sharp_upper_budget_bits(
        start_branch, normalized_word, cycle
    )
    tight_exponent = tight971_growth_exponent(
        start_branch, normalized_word, cycle
    )
    tight_budget = (tight_exponent + TIGHT_ROUNDING) // TIGHT_POWER
    if tight_budget > coarse_budget:
        raise AssertionError("tight budget exceeded the coarse budget")
    precision = coarse_budget + padding_bits
    padded_residue, transitions, accumulated = backward_residue(
        successor, normalized_word, precision
    )
    normalized_mask = (1 << coarse_budget) - 1
    normalized_residue = padded_residue & normalized_mask
    if normalized_residue < 1 or normalized_residue % 2 != 1:
        raise AssertionError("normalized future residue is not positive odd")
    if padded_residue < 1 or padded_residue % 2 != 1:
        raise AssertionError("padded future residue is not positive odd")
    required_residue, ternary_modulus = successor_ternary_residue(
        previous, successor
    )
    ternary_exponent = 6 * previous + 11
    if ternary_modulus != 3 ** ternary_exponent:
        raise AssertionError("predecessor ternary modulus mismatch")
    if required_residue % 3 != 1:
        raise AssertionError("EC17 predecessor residue lost its forced trit")
    normalized_matches = normalized_residue % ternary_modulus == required_residue
    padded_matches = padded_residue % ternary_modulus == required_residue
    budget_gap = coarse_budget - tight_budget
    tightened_padded = precision - tight_budget
    return TightResidueRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle=cycle,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        previous_branch=previous,
        successor_branch=successor,
        coarse_upper_exponent=coarse_exponent,
        coarse_budget_bits=coarse_budget,
        tight971_growth_exponent=tight_exponent,
        tight971_budget_bits=tight_budget,
        budget_gap_bits=budget_gap,
        padding_bits=padding_bits,
        padded_precision_bits=precision,
        tightened_padded_margin_bits=tightened_padded,
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        normalized_residue_bits=normalized_residue.bit_length(),
        padded_residue_bits=padded_residue.bit_length(),
        normalized_residue_mod3=normalized_residue % 3,
        padded_residue_mod3=padded_residue % 3,
        predecessor_ternary_exponent=ternary_exponent,
        required_predecessor_residue_mod3=required_residue % 3,
        normalized_one_trit_matches=normalized_residue % 3 == 1,
        padded_one_trit_matches=padded_residue % 3 == 1,
        normalized_predecessor_congruence_matches=normalized_matches,
        padded_predecessor_congruence_matches=padded_matches,
        normalized_residue_sha256=digest_natural(normalized_residue),
        padded_residue_sha256=digest_natural(padded_residue),
        proposed_normalized_lower_bound_initial_bits=(
            None if normalized_matches else budget_gap + 1
        ),
        proposed_padded_lower_bound_initial_bits=(
            None if padded_matches else tightened_padded + 1
        ),
    )


def summarize(rows: Sequence[TightResidueRow]) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    normalized_bounds = [
        row.proposed_normalized_lower_bound_initial_bits
        for row in rows
        if row.proposed_normalized_lower_bound_initial_bits is not None
    ]
    padded_bounds = [
        row.proposed_padded_lower_bound_initial_bits
        for row in rows
        if row.proposed_padded_lower_bound_initial_bits is not None
    ]
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].cycle,
        maximum_cycle=rows[-1].cycle,
        all_normalized_predecessor_congruences_failed=all(
            not row.normalized_predecessor_congruence_matches for row in rows
        ),
        all_padded_predecessor_congruences_failed=all(
            not row.padded_predecessor_congruence_matches for row in rows
        ),
        normalized_one_trit_failures=sum(
            not row.normalized_one_trit_matches for row in rows
        ),
        padded_one_trit_failures=sum(
            not row.padded_one_trit_matches for row in rows
        ),
        maximum_budget_gap_bits=max(row.budget_gap_bits for row in rows),
        maximum_tightened_padded_margin_bits=max(
            row.tightened_padded_margin_bits for row in rows
        ),
        maximum_proposed_normalized_lower_bound_initial_bits=(
            max(normalized_bounds) if normalized_bounds else None
        ),
        maximum_proposed_padded_lower_bound_initial_bits=(
            max(padded_bounds) if padded_bounds else None
        ),
        final_normalized_residue_mod3=rows[-1].normalized_residue_mod3,
        final_padded_residue_mod3=rows[-1].padded_residue_mod3,
        row_sha256=row_digest(rows),
    )


def summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    return result


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...], int, int]
) -> tuple[ScheduleSummary, list[TightResidueRow]]:
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
    return summarize(rows), rows


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
    if min(increment_abs_bound, max_start_branch, cycle_step, jobs) < 1:
        raise ValueError("scan bounds and jobs must be positive")
    if padding_slope < 0 or padding_intercept < 0:
        raise ValueError("padding parameters must be nonnegative")
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
    normalized_one_trit_failures = sum(
        not row.normalized_one_trit_matches for row in rows
    )
    padded_one_trit_failures = sum(
        not row.padded_one_trit_matches for row in rows
    )
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [-increment_abs_bound, increment_abs_bound],
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
        "all_normalized_predecessor_congruences_failed": all(
            not row.normalized_predecessor_congruence_matches for row in rows
        ),
        "all_padded_predecessor_congruences_failed": all(
            not row.padded_predecessor_congruence_matches for row in rows
        ),
        "normalized_one_trit_failure_count": normalized_one_trit_failures,
        "normalized_one_trit_match_count": len(rows) - normalized_one_trit_failures,
        "padded_one_trit_failure_count": padded_one_trit_failures,
        "padded_one_trit_match_count": len(rows) - padded_one_trit_failures,
        "maximum_budget_gap_bits": max(
            row.budget_gap_bits for row in rows
        ) if rows else None,
        "minimum_of_schedule_maximum_budget_gaps": min(
            summary.maximum_budget_gap_bits for summary in summaries
        ) if summaries else None,
        "maximum_tightened_padded_margin_bits": max(
            row.tightened_padded_margin_bits for row in rows
        ) if rows else None,
        "minimum_of_schedule_normalized_lower_bounds": min(
            summary.maximum_proposed_normalized_lower_bound_initial_bits
            for summary in summaries
            if summary.maximum_proposed_normalized_lower_bound_initial_bits
            is not None
        ) if summaries and all(
            summary.maximum_proposed_normalized_lower_bound_initial_bits
            is not None for summary in summaries
        ) else None,
        "minimum_of_schedule_padded_lower_bounds": min(
            summary.maximum_proposed_padded_lower_bound_initial_bits
            for summary in summaries
            if summary.maximum_proposed_padded_lower_bound_initial_bits is not None
        ) if summaries and all(
            summary.maximum_proposed_padded_lower_bound_initial_bits is not None
            for summary in summaries
        ) else None,
        "schedule_summaries": [summary_dict(summary) for summary in summaries],
        "theorem_interface": (
            "Companion commit 5a3413a, QM113--QM116: a hypothetical ray "
            "eventually has zero normalized CRT lift; any failed raw "
            "predecessor congruence at precision P forces "
            "P-tight971_budget < bits(core(0))"
        ),
        "claim_scope": (
            "finite exact future residues and predecessor congruence tests "
            "in the displayed schedule/cycle box; no finite pattern is "
            "promoted to cofinal nonstabilization"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized tight-residue artifact schema")
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
    if starts[0] != 1 or (cycles is None) == (cycle_values is None):
        raise ValueError("invalid artifact bounds")
    padding = bounds["padding_bits"]
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(starts[1]),
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
        raise ValueError("tight-residue artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 5, 0),
        (2, (-1, 1, 1), 7, 19),
        (1, (1, -1, 1), 9, 41),
    ]
    for start, word, cycle, padding in cases:
        row = audit_row(start, word, cycle, padding)
        direct, _, _ = backward_residue(
            row.successor_branch, word, row.coarse_budget_bits
        )
        padded, _, _ = backward_residue(
            row.successor_branch, word, row.padded_precision_bits
        )
        if direct != padded % (1 << row.coarse_budget_bits):
            raise AssertionError("precision masking self-test failed")
        if digest_natural(direct) != row.normalized_residue_sha256:
            raise AssertionError("normalized residue digest self-test failed")
        if row.required_predecessor_residue_mod3 != 1:
            raise AssertionError("predecessor one-trit self-test failed")
    tiny = scan_box(1, 2, 5, 7, 1, 1, 3, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny tight-residue scan failed")


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
    scan.add_argument("--cycle-values")
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
        print("tight period-three residue self-test passed")
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
            "exact_rows_checked": artifact["exact_rows_checked"],
            "all_normalized_predecessor_congruences_failed": artifact[
                "all_normalized_predecessor_congruences_failed"
            ],
            "all_padded_predecessor_congruences_failed": artifact[
                "all_padded_predecessor_congruences_failed"
            ],
            "normalized_one_trit_failure_count": artifact[
                "normalized_one_trit_failure_count"
            ],
            "minimum_of_schedule_padded_lower_bounds": artifact[
                "minimum_of_schedule_padded_lower_bounds"
            ],
            "counterexample": None,
        }, sort_keys=True))
        return
    selftest()
    verify_artifact(args.artifact, args.jobs)
    print("tight period-three residue artifact verified")


if __name__ == "__main__":
    main()

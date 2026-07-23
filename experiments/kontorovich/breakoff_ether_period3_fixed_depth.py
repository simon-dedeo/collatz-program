#!/usr/bin/env python3
"""Exact fixed-depth phase audit for period-three EC17 future residues.

The companion's fixed-depth no-ray consumer says that, for any fixed
``d >= 1``, cofinally many failures of

    2^(8*n_q+15) * r_q = 17  (mod 3^d)

exclude the prescribed period-three ray.  Here ``r_q`` is the canonical
future residue modulo the kernel-checked normalized precision ``2^U(q)``.
The required coefficient has period dividing ``3^(d-1)`` in ``q``.

This worker computes the exact capped ternary match depth and groups rows by
those proved clock phases.  Its purpose is to identify a finite phase on
which a symbolic nonrecurrence proof might be attempted.  A phase with no
matches in a finite interval is only a diagnostic and is never promoted to a
cofinal theorem or a Collatz counterexample.
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
from breakoff_ether_period3_sieve import backward_residue, stays_positive


SCHEMA = "collatz-breakoff-ether-period3-fixed-depth-v1"


@dataclass(frozen=True)
class FixedDepthRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle: int
    cycle_gain: int
    phase_sum: int
    successor_branch: int
    precision_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    residue_bits: int
    residue_mod_3_power: int
    required_residue_mod_3_power: int
    match_depth_capped: int
    residue_sha256: str


@dataclass(frozen=True)
class PhaseSummary:
    depth: int
    clock_period: int
    clock_phase: int
    rows_observed: int
    first_cycle: int
    last_cycle: int
    matches: int
    failures: int
    all_observed_rows_failed: bool
    required_residue_mod_3_power: int


@dataclass(frozen=True)
class DepthSummary:
    depth: int
    modulus: int
    clock_period: int
    rows_observed: int
    matches: int
    failures: int
    phases_observed: int
    phases_with_no_matches: int
    maximum_rows_in_a_no_match_phase: int
    phase_summaries: tuple[PhaseSummary, ...]


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    maximum_match_depth_capped: int
    match_depth_histogram: tuple[int, ...]
    depth_summaries: tuple[DepthSummary, ...]
    row_sha256: str


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def v3_capped(value: int, cap: int) -> int:
    if cap < 1 or value < 0:
        raise ValueError("invalid capped ternary valuation")
    if value == 0:
        return cap
    result = 0
    while result < cap and value % 3 == 0:
        value //= 3
        result += 1
    return result


def row_dict(row: FixedDepthRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[FixedDepthRow]) -> str:
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
    maximum_depth: int,
) -> FixedDepthRow:
    normalized_word = tuple(int(value) for value in word)
    if len(normalized_word) != 3 or maximum_depth < 1:
        raise ValueError("invalid fixed-depth row")
    if cycle < MINIMUM_CYCLE or not stays_positive(start_branch, normalized_word):
        raise ValueError("row requires q >= 5 and a positive schedule")
    gain = sum(normalized_word)
    successor = start_branch + gain * cycle
    precision = sharp_upper_budget_bits(start_branch, normalized_word, cycle)
    residue, transitions, accumulated = backward_residue(
        successor, normalized_word, precision
    )
    modulus = 3 ** maximum_depth
    beta = 8 * successor + 15
    residue_modulus = residue % modulus
    required = 17 * pow(2, -beta, modulus) % modulus
    discrepancy = (
        pow(2, beta, modulus) * residue_modulus - 17
    ) % modulus
    match_depth = v3_capped(discrepancy, maximum_depth)
    for depth in range(1, maximum_depth + 1):
        small_modulus = 3 ** depth
        matches_by_residue = residue % small_modulus == required % small_modulus
        if matches_by_residue != (match_depth >= depth):
            raise AssertionError("fixed-depth congruence equivalence failed")
    return FixedDepthRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        cycle=cycle,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        successor_branch=successor,
        precision_bits=precision,
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        residue_bits=residue.bit_length(),
        residue_mod_3_power=residue_modulus,
        required_residue_mod_3_power=required,
        match_depth_capped=match_depth,
        residue_sha256=digest_natural(residue),
    )


def phase_summary_dict(summary: PhaseSummary) -> dict[str, Any]:
    return asdict(summary)


def depth_summary_dict(summary: DepthSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["phase_summaries"] = [
        phase_summary_dict(phase) for phase in summary.phase_summaries
    ]
    return result


def summarize_depth(
    rows: Sequence[FixedDepthRow], depth: int
) -> DepthSummary:
    modulus = 3 ** depth
    period = 3 ** (depth - 1)
    phase_rows: dict[int, list[FixedDepthRow]] = {}
    for row in rows:
        phase_rows.setdefault(row.cycle % period, []).append(row)
    phase_summaries: list[PhaseSummary] = []
    for phase in sorted(phase_rows):
        group = phase_rows[phase]
        required_values = {
            row.required_residue_mod_3_power % modulus for row in group
        }
        if len(required_values) != 1:
            raise AssertionError("required predecessor clock was not periodic")
        matches = sum(row.match_depth_capped >= depth for row in group)
        phase_summaries.append(PhaseSummary(
            depth=depth,
            clock_period=period,
            clock_phase=phase,
            rows_observed=len(group),
            first_cycle=group[0].cycle,
            last_cycle=group[-1].cycle,
            matches=matches,
            failures=len(group) - matches,
            all_observed_rows_failed=matches == 0,
            required_residue_mod_3_power=next(iter(required_values)),
        ))
    total_matches = sum(row.match_depth_capped >= depth for row in rows)
    no_match_phases = [
        phase for phase in phase_summaries if phase.all_observed_rows_failed
    ]
    return DepthSummary(
        depth=depth,
        modulus=modulus,
        clock_period=period,
        rows_observed=len(rows),
        matches=total_matches,
        failures=len(rows) - total_matches,
        phases_observed=len(phase_summaries),
        phases_with_no_matches=len(no_match_phases),
        maximum_rows_in_a_no_match_phase=max(
            (phase.rows_observed for phase in no_match_phases), default=0
        ),
        phase_summaries=tuple(phase_summaries),
    )


def summarize_schedule(
    rows: Sequence[FixedDepthRow], maximum_depth: int
) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    histogram = tuple(
        sum(row.match_depth_capped == depth for row in rows)
        for depth in range(maximum_depth + 1)
    )
    if sum(histogram) != len(rows):
        raise AssertionError("match-depth histogram lost rows")
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].cycle,
        maximum_cycle=rows[-1].cycle,
        maximum_match_depth_capped=max(
            row.match_depth_capped for row in rows
        ),
        match_depth_histogram=histogram,
        depth_summaries=tuple(
            summarize_depth(rows, depth)
            for depth in range(1, maximum_depth + 1)
        ),
        row_sha256=row_digest(rows),
    )


def schedule_summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    return {
        "increment_word": list(summary.increment_word),
        "start_branch": summary.start_branch,
        "cycle_gain": summary.cycle_gain,
        "phase_sum": summary.phase_sum,
        "rows_checked": summary.rows_checked,
        "minimum_cycle": summary.minimum_cycle,
        "maximum_cycle": summary.maximum_cycle,
        "maximum_match_depth_capped": summary.maximum_match_depth_capped,
        "match_depth_histogram": list(summary.match_depth_histogram),
        "depth_summaries": [
            depth_summary_dict(depth) for depth in summary.depth_summaries
        ],
        "row_sha256": summary.row_sha256,
    }


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...], int]
) -> tuple[ScheduleSummary, list[FixedDepthRow]]:
    word, start, cycles, maximum_depth = task
    rows = [
        audit_row(start, word, cycle, maximum_depth) for cycle in cycles
    ]
    return summarize_schedule(rows, maximum_depth), rows


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    minimum_cycle: int,
    maximum_cycle: int,
    cycle_step: int,
    maximum_depth: int,
    jobs: int,
    cycle_values: Sequence[int] | None = None,
) -> dict[str, Any]:
    if min(
        increment_abs_bound,
        max_start_branch,
        cycle_step,
        maximum_depth,
        jobs,
    ) < 1:
        raise ValueError("scan bounds, depth, and jobs must be positive")
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
        (word, start, cycles, maximum_depth)
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
    aggregate_depths: list[dict[str, Any]] = []
    for depth in range(1, maximum_depth + 1):
        schedule_depths = [summary.depth_summaries[depth - 1] for summary in summaries]
        aggregate_depths.append({
            "depth": depth,
            "modulus": 3 ** depth,
            "clock_period_bound": 3 ** (depth - 1),
            "matches": sum(item.matches for item in schedule_depths),
            "failures": sum(item.failures for item in schedule_depths),
            "schedule_phase_cells_observed": sum(
                item.phases_observed for item in schedule_depths
            ),
            "schedule_phase_cells_with_no_matches": sum(
                item.phases_with_no_matches for item in schedule_depths
            ),
            "maximum_rows_in_a_no_match_phase": max(
                item.maximum_rows_in_a_no_match_phase
                for item in schedule_depths
            ),
            "schedules_with_a_no_match_phase": sum(
                item.phases_with_no_matches > 0 for item in schedule_depths
            ),
        })
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [-increment_abs_bound, increment_abs_bound],
            "start_branches": [1, max_start_branch],
            **cycle_bounds,
            "maximum_ternary_depth": maximum_depth,
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(summaries),
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "maximum_match_depth_capped": max(
            row.match_depth_capped for row in rows
        ) if rows else None,
        "aggregate_depth_summaries": aggregate_depths,
        "schedule_summaries": [
            schedule_summary_dict(summary) for summary in summaries
        ],
        "theorem_interface": (
            "Companion round 222 fixed-depth consumers: at every fixed "
            "depth d, cofinally many failures modulo 3^d exclude the ray; "
            "the required coefficient has q-period dividing 3^(d-1)"
        ),
        "claim_scope": (
            "finite exact normalized residues grouped by the proved clock "
            "phases; a phase with no observed matches is not a cofinal theorem"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized fixed-depth artifact schema")
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
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(starts[1]),
        minimum_cycle=(int(cycles[0]) if cycles is not None else MINIMUM_CYCLE),
        maximum_cycle=(int(cycles[1]) if cycles is not None else MINIMUM_CYCLE),
        cycle_step=(int(cycles[2]) if cycles is not None else 1),
        maximum_depth=int(bounds["maximum_ternary_depth"]),
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
        raise ValueError("fixed-depth artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 5),
        (2, (-1, 1, 1), 7),
        (1, (1, -1, 1), 9),
    ]
    for start, word, cycle in cases:
        row = audit_row(start, word, cycle, 5)
        if row.match_depth_capped < 0 or row.match_depth_capped > 5:
            raise AssertionError("match depth left its cap")
    tiny = scan_box(1, 2, 5, 11, 1, 4, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny fixed-depth scan failed")


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
    scan.add_argument("--maximum-depth", type=int, default=5)
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
        print("fixed-depth period-three self-test passed")
        return
    if args.command == "scan":
        selftest()
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            minimum_cycle=args.min_cycle,
            maximum_cycle=args.max_cycle,
            cycle_step=args.cycle_step,
            maximum_depth=args.maximum_depth,
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
            "maximum_match_depth_capped": artifact[
                "maximum_match_depth_capped"
            ],
            "aggregate_depth_summaries": artifact[
                "aggregate_depth_summaries"
            ],
            "counterexample": None,
        }, sort_keys=True))
        return
    selftest()
    verify_artifact(args.artifact, args.jobs)
    print("fixed-depth period-three artifact verified")


if __name__ == "__main__":
    main()

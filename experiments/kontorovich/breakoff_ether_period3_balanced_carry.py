#!/usr/bin/env python3
"""Exact balanced-precision cycle carries for period-three EC17 schedules.

Fix a positive period-three increment schedule.  At cycle ``q`` write the
three-step EC17 composition as

    2^m(q) y_q = 3^Q(q) r_q + D(q).

This worker transports a deliberately balanced amount of future precision.
Starting from ``P_q0=m(q0)+h``, put

    ell_q = floor(log_2(3^Q(q))),
    P_(q+1) = P_q - m(q) + ell_q.

For ``p_q=P_q-m(q)>0``, canonical future consistency gives

    r_(q+1) - y_q = 2^p_q C_q.

The target representative has only ``ell_q`` unconstrained bits above this
common low block.  The positive EC17 defect also satisfies ``D(q)<3^Q(q)``.
Together these two exact inequalities give ``|C_q|<3^Q(q)``.  Consequently

    2^m(q) r_(q+1) = D(q) (mod 3^Q(q))

if and only if ``C_q=0``, hence if and only if the two canonical
representatives are one literal three-step EC17 link.

Every residue is independently reconstructed by the backward recurrence and
the direct finite-series formula.  Every row is replayed through its three
literal divisions.  Exact hits serialize the ordinary source, intermediate,
and target cores in hexadecimal.  Finite hits or hit streaks are finite orbit
segments only; this worker never promotes them to an infinite ray or a
Collatz counterexample.
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
    words_in_box,
)
from breakoff_ether_period3_sieve import (
    backward_residue,
    direct_series_residue,
    stays_positive,
    v2,
)


SCHEMA = "collatz-breakoff-ether-period3-balanced-carry-v1"
CORE_CONSTANT = 17


@dataclass(frozen=True)
class ResidueData:
    value: int
    transitions: int
    accumulated_binary_precision: int


@dataclass(frozen=True)
class BalancedCarryRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    initial_headroom_bits: int
    source_cycle: int
    target_cycle: int
    cycle_gain: int
    phase_sum: int
    source_branch: int
    target_branch: int
    source_precision_bits: int
    target_precision_bits: int
    source_backward_transitions: int
    target_backward_transitions: int
    source_accumulated_binary_precision: int
    target_accumulated_binary_precision: int
    cycle_binary_exponent: int
    cycle_ternary_exponent: int
    ternary_floor_log_bits: int
    carry_precision_bits: int
    defect_bits: int
    defect_lt_full_ternary_modulus: bool
    source_residue_bits: int
    target_residue_bits: int
    exact_forward_image_bits: int
    low_precision_compatibility: bool
    carry_is_zero: bool
    carry_sign: int
    signed_carry_bits: int
    carry_v2: int | None
    carry_v3: int | None
    ternary_valuation_deficit: int | None
    carry_abs_lt_full_ternary_modulus: bool
    full_ternary_congruence: bool
    source_residue_sha256: str
    target_residue_sha256: str
    exact_forward_image_sha256: str
    signed_carry_sha256: str
    source_core_hex: str | None
    phase_one_core_hex: str | None
    phase_two_core_hex: str | None
    target_core_hex: str | None


@dataclass(frozen=True)
class PathSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    initial_headroom_bits: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    minimum_cycle: int
    maximum_cycle: int
    initial_precision_bits: int
    final_target_precision_bits: int
    exact_hit_count: int
    longest_exact_hit_run: int
    exact_hit_run_intervals: tuple[tuple[int, int], ...]
    positive_carry_count: int
    negative_carry_count: int
    minimum_nonzero_ternary_deficit: int | None
    maximum_nonzero_carry_v3: int | None
    maximum_nonzero_relative_leading_zero_bits: int | None
    row_sha256: str


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    paths_checked: int
    rows_checked: int
    exact_hit_count: int
    paths_with_exact_hit: int
    longest_exact_hit_run: int
    best_run_headroom_bits: int | None
    minimum_nonzero_ternary_deficit: int | None
    maximum_nonzero_carry_v3: int | None
    row_sha256: str


def digest_natural(value: int) -> str:
    if value < 0:
        raise ValueError("natural digest received a negative integer")
    data = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(data).hexdigest()


def digest_signed(value: int) -> str:
    sign = b"-" if value < 0 else b"+"
    magnitude = abs(value)
    data = magnitude.to_bytes(max(1, (magnitude.bit_length() + 7) // 8), "big")
    return hashlib.sha256(sign + data).hexdigest()


def prime_valuation(value: int, prime: int) -> int | None:
    """Return the finite prime valuation, using ``None`` for zero."""

    if prime < 2:
        raise ValueError("valuation prime must be at least two")
    magnitude = abs(value)
    if magnitude == 0:
        return None
    result = 0
    while magnitude % prime == 0:
        magnitude //= prime
        result += 1
    return result


def canonical_residue(
    shifted_branch: int, word: Sequence[int], precision_bits: int
) -> ResidueData:
    """Compute one canonical residue by two independent exact formulas."""

    backward, transitions, accumulated = backward_residue(
        shifted_branch, word, precision_bits
    )
    direct = direct_series_residue(shifted_branch, word, precision_bits)
    if backward != direct:
        raise AssertionError("backward and direct-series residues disagreed")
    if accumulated < precision_bits:
        raise AssertionError("canonical residue lacked requested future precision")
    if not (0 < backward < 1 << precision_bits) or backward % 2 != 1:
        raise AssertionError("canonical residue escaped its positive odd range")
    return ResidueData(backward, transitions, accumulated)


def one_cycle_data(
    start_branch: int, word: Sequence[int], cycle: int
) -> tuple[tuple[int, int, int, int], tuple[int, int, int], tuple[int, int, int], int]:
    """Return levels, binary/ternary exponents, and the composed defect."""

    normalized_word = tuple(int(value) for value in word)
    gain = sum(normalized_word)
    n0 = start_branch + gain * cycle
    n1 = n0 + normalized_word[0]
    n2 = n1 + normalized_word[1]
    n3 = n2 + normalized_word[2]
    levels = (n0, n1, n2, n3)
    if min(levels) < 1:
        raise AssertionError("positive period-three schedule became nonpositive")
    binary = (8 * n1 + 15, 8 * n2 + 15, 8 * n3 + 15)
    ternary = (6 * n0 + 11, 6 * n1 + 11, 6 * n2 + 11)
    defect = CORE_CONSTANT * (
        3 ** (ternary[1] + ternary[2])
        + 2 ** binary[0] * 3 ** ternary[2]
        + 2 ** (binary[0] + binary[1])
    )
    return levels, binary, ternary, defect


def replay_cycle(
    source_core: int,
    levels: Sequence[int],
    binary: Sequence[int],
    ternary: Sequence[int],
) -> tuple[int, int, int, int]:
    """Replay the three literal EC17 divisions and return all four cores."""

    cores = [source_core]
    core = source_core
    for step in range(3):
        numerator = 3 ** ternary[step] * core + CORE_CONSTANT
        actual = v2(numerator)
        if actual != binary[step]:
            raise AssertionError(
                f"cycle replay valuation mismatch at step {step}: "
                f"got {actual}, wanted {binary[step]}"
            )
        core = numerator >> binary[step]
        if core < 1 or core % 2 != 1 or core % 3 != 1:
            raise AssertionError("cycle replay left the positive ternary-core state")
        if levels[step + 1] < 1:
            raise AssertionError("cycle replay reached a nonpositive branch")
        cores.append(core)
    return cores[0], cores[1], cores[2], cores[3]


def row_dict(row: BalancedCarryRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[BalancedCarryRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(row_dict(row), sort_keys=True, separators=(",", ":")).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def audit_row(
    start_branch: int,
    word: Sequence[int],
    initial_headroom_bits: int,
    cycle: int,
    source_precision: int,
    target_precision: int,
    source: ResidueData,
    target: ResidueData,
) -> BalancedCarryRow:
    normalized_word = tuple(int(value) for value in word)
    if (
        len(normalized_word) != 3
        or initial_headroom_bits < 1
        or cycle < MINIMUM_CYCLE
        or not stays_positive(start_branch, normalized_word)
    ):
        raise ValueError("invalid balanced-carry row")

    gain = sum(normalized_word)
    levels, binary, ternary, defect = one_cycle_data(
        start_branch, normalized_word, cycle
    )
    binary_sum = sum(binary)
    ternary_sum = sum(ternary)
    if source_precision <= binary_sum:
        raise AssertionError("balanced source precision did not cover one cycle")
    carry_precision = source_precision - binary_sum
    full_ternary_modulus = 3 ** ternary_sum
    ternary_floor_log = full_ternary_modulus.bit_length() - 1
    if not (
        1 << ternary_floor_log
        <= full_ternary_modulus
        < 1 << (ternary_floor_log + 1)
    ):
        raise AssertionError("ternary floor logarithm was reconstructed incorrectly")
    expected_target_precision = carry_precision + ternary_floor_log
    if target_precision != expected_target_precision:
        raise AssertionError("balanced target precision recurrence disagreed")

    expected_binary = (
        8 * (phase_sum(start_branch, normalized_word) + gain)
        + 45
        + 24 * gain * cycle
    )
    expected_ternary = (
        6 * phase_sum(start_branch, normalized_word)
        + 33
        + 18 * gain * cycle
    )
    if binary_sum != expected_binary or ternary_sum != expected_ternary:
        raise AssertionError("one-cycle exponent sum formula did not close")

    if not defect < full_ternary_modulus:
        raise AssertionError("positive cycle defect reached its ternary modulus")

    composed_numerator = full_ternary_modulus * source.value + defect
    if composed_numerator % (1 << binary_sum):
        raise AssertionError("canonical source did not divide through one cycle")
    forward_image = composed_numerator >> binary_sum
    replayed = replay_cycle(source.value, levels, binary, ternary)
    if replayed[-1] != forward_image:
        raise AssertionError("sequential replay disagreed with cycle composition")

    low_modulus = 1 << carry_precision
    difference = target.value - forward_image
    low_compatible = difference % low_modulus == 0
    if not low_compatible:
        raise AssertionError("canonical residues disagreed below the carry boundary")
    carry = difference // low_modulus
    carry_abs_lt = abs(carry) < full_ternary_modulus
    if not carry_abs_lt:
        raise AssertionError("balanced carry reached the full ternary modulus")

    full_congruence = (
        ((1 << binary_sum) * target.value - defect)
        % full_ternary_modulus
        == 0
    )
    if full_congruence != (carry % full_ternary_modulus == 0):
        raise AssertionError("full predecessor congruence and carry disagreed")
    if full_congruence != (carry == 0):
        raise AssertionError("balanced full congruence did not force zero carry")
    if (carry == 0) != (target.value == forward_image):
        raise AssertionError("zero carry did not equal exact cycle compatibility")

    carry_v2 = prime_valuation(carry, 2)
    carry_v3 = prime_valuation(carry, 3)
    hit = carry == 0
    if hit and replayed[-1] != target.value:
        raise AssertionError("exact hit failed its literal three-step replay")

    return BalancedCarryRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        initial_headroom_bits=initial_headroom_bits,
        source_cycle=cycle,
        target_cycle=cycle + 1,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        source_branch=levels[0],
        target_branch=levels[3],
        source_precision_bits=source_precision,
        target_precision_bits=target_precision,
        source_backward_transitions=source.transitions,
        target_backward_transitions=target.transitions,
        source_accumulated_binary_precision=(
            source.accumulated_binary_precision
        ),
        target_accumulated_binary_precision=(
            target.accumulated_binary_precision
        ),
        cycle_binary_exponent=binary_sum,
        cycle_ternary_exponent=ternary_sum,
        ternary_floor_log_bits=ternary_floor_log,
        carry_precision_bits=carry_precision,
        defect_bits=defect.bit_length(),
        defect_lt_full_ternary_modulus=True,
        source_residue_bits=source.value.bit_length(),
        target_residue_bits=target.value.bit_length(),
        exact_forward_image_bits=forward_image.bit_length(),
        low_precision_compatibility=low_compatible,
        carry_is_zero=hit,
        carry_sign=(carry > 0) - (carry < 0),
        signed_carry_bits=abs(carry).bit_length(),
        carry_v2=carry_v2,
        carry_v3=carry_v3,
        ternary_valuation_deficit=(
            None if carry_v3 is None else ternary_sum - carry_v3
        ),
        carry_abs_lt_full_ternary_modulus=carry_abs_lt,
        full_ternary_congruence=full_congruence,
        source_residue_sha256=digest_natural(source.value),
        target_residue_sha256=digest_natural(target.value),
        exact_forward_image_sha256=digest_natural(forward_image),
        signed_carry_sha256=digest_signed(carry),
        source_core_hex=hex(replayed[0]) if hit else None,
        phase_one_core_hex=hex(replayed[1]) if hit else None,
        phase_two_core_hex=hex(replayed[2]) if hit else None,
        target_core_hex=hex(replayed[3]) if hit else None,
    )


def exact_run_intervals(
    rows: Sequence[BalancedCarryRow],
) -> tuple[tuple[int, int], ...]:
    intervals: list[tuple[int, int]] = []
    run_start: int | None = None
    previous: int | None = None
    for row in rows:
        if row.carry_is_zero:
            if run_start is None or previous is None or row.source_cycle != previous + 1:
                if run_start is not None:
                    intervals.append((run_start, previous if previous is not None else run_start))
                run_start = row.source_cycle
            previous = row.source_cycle
        elif run_start is not None:
            intervals.append((run_start, previous if previous is not None else run_start))
            run_start = None
            previous = None
    if run_start is not None:
        intervals.append((run_start, previous if previous is not None else run_start))
    return tuple(intervals)


def summarize_path(rows: Sequence[BalancedCarryRow]) -> PathSummary:
    if not rows:
        raise ValueError("cannot summarize an empty balanced path")
    intervals = exact_run_intervals(rows)
    nonzero = [row for row in rows if not row.carry_is_zero]
    deficits = [
        row.ternary_valuation_deficit
        for row in nonzero
        if row.ternary_valuation_deficit is not None
    ]
    valuations = [row.carry_v3 for row in nonzero if row.carry_v3 is not None]
    relative_zero_bits = [
        max(row.ternary_floor_log_bits + 1 - row.signed_carry_bits, 0)
        for row in nonzero
    ]
    return PathSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        initial_headroom_bits=rows[0].initial_headroom_bits,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        minimum_cycle=rows[0].source_cycle,
        maximum_cycle=rows[-1].source_cycle,
        initial_precision_bits=rows[0].source_precision_bits,
        final_target_precision_bits=rows[-1].target_precision_bits,
        exact_hit_count=sum(row.carry_is_zero for row in rows),
        longest_exact_hit_run=max(
            (end - start + 1 for start, end in intervals), default=0
        ),
        exact_hit_run_intervals=intervals,
        positive_carry_count=sum(row.carry_sign > 0 for row in rows),
        negative_carry_count=sum(row.carry_sign < 0 for row in rows),
        minimum_nonzero_ternary_deficit=min(deficits, default=None),
        maximum_nonzero_carry_v3=max(valuations, default=None),
        maximum_nonzero_relative_leading_zero_bits=max(
            relative_zero_bits, default=None
        ),
        row_sha256=row_digest(rows),
    )


def path_summary_dict(summary: PathSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    result["exact_hit_run_intervals"] = [
        list(interval) for interval in summary.exact_hit_run_intervals
    ]
    return result


def summarize_schedule(
    paths: Sequence[tuple[PathSummary, Sequence[BalancedCarryRow]]],
) -> ScheduleSummary:
    if not paths:
        raise ValueError("cannot summarize a schedule without paths")
    path_summaries = [summary for summary, _ in paths]
    rows = [row for _, path_rows in paths for row in path_rows]
    best = max(
        path_summaries,
        key=lambda summary: (
            summary.longest_exact_hit_run,
            summary.exact_hit_count,
            -(summary.minimum_nonzero_ternary_deficit or 10**18),
            -summary.initial_headroom_bits,
        ),
    )
    deficits = [
        summary.minimum_nonzero_ternary_deficit
        for summary in path_summaries
        if summary.minimum_nonzero_ternary_deficit is not None
    ]
    valuations = [
        summary.maximum_nonzero_carry_v3
        for summary in path_summaries
        if summary.maximum_nonzero_carry_v3 is not None
    ]
    return ScheduleSummary(
        increment_word=path_summaries[0].increment_word,
        start_branch=path_summaries[0].start_branch,
        cycle_gain=path_summaries[0].cycle_gain,
        phase_sum=path_summaries[0].phase_sum,
        paths_checked=len(paths),
        rows_checked=len(rows),
        exact_hit_count=sum(summary.exact_hit_count for summary in path_summaries),
        paths_with_exact_hit=sum(
            summary.exact_hit_count > 0 for summary in path_summaries
        ),
        longest_exact_hit_run=max(
            summary.longest_exact_hit_run for summary in path_summaries
        ),
        best_run_headroom_bits=(
            best.initial_headroom_bits if best.exact_hit_count > 0 else None
        ),
        minimum_nonzero_ternary_deficit=min(deficits, default=None),
        maximum_nonzero_carry_v3=max(valuations, default=None),
        row_sha256=row_digest(rows),
    )


def schedule_summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    return result


def scan_path(
    start_branch: int,
    word: tuple[int, int, int],
    initial_cycle: int,
    maximum_cycle: int,
    initial_headroom_bits: int,
) -> tuple[PathSummary, list[BalancedCarryRow]]:
    _, initial_binary, _, _ = one_cycle_data(start_branch, word, initial_cycle)
    source_precision = sum(initial_binary) + initial_headroom_bits
    gain = sum(word)
    source = canonical_residue(
        start_branch + gain * initial_cycle, word, source_precision
    )
    rows: list[BalancedCarryRow] = []
    for cycle in range(initial_cycle, maximum_cycle + 1):
        _, binary, ternary, _ = one_cycle_data(start_branch, word, cycle)
        binary_sum = sum(binary)
        if source_precision <= binary_sum:
            raise AssertionError("balanced precision path lost cycle coverage")
        ternary_modulus = 3 ** sum(ternary)
        ell = ternary_modulus.bit_length() - 1
        target_precision = source_precision - binary_sum + ell
        target = canonical_residue(
            start_branch + gain * (cycle + 1), word, target_precision
        )
        row = audit_row(
            start_branch=start_branch,
            word=word,
            initial_headroom_bits=initial_headroom_bits,
            cycle=cycle,
            source_precision=source_precision,
            target_precision=target_precision,
            source=source,
            target=target,
        )
        rows.append(row)
        source_precision = target_precision
        source = target
    return summarize_path(rows), rows


def scan_schedule(
    task: tuple[
        tuple[int, int, int],
        int,
        int,
        int,
        tuple[int, ...],
    ]
) -> tuple[ScheduleSummary, list[tuple[PathSummary, list[BalancedCarryRow]]]]:
    word, start, initial_cycle, maximum_cycle, headrooms = task
    paths = [
        scan_path(start, word, initial_cycle, maximum_cycle, headroom)
        for headroom in headrooms
    ]
    return summarize_schedule(paths), paths


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    initial_cycle: int,
    maximum_cycle: int,
    minimum_headroom: int,
    maximum_headroom: int,
    jobs: int,
) -> dict[str, Any]:
    if min(increment_abs_bound, max_start_branch, minimum_headroom, jobs) < 1:
        raise ValueError("scan bounds and worker count must be positive")
    if initial_cycle < MINIMUM_CYCLE or maximum_cycle < initial_cycle:
        raise ValueError("invalid cycle interval")
    if maximum_headroom < minimum_headroom:
        raise ValueError("invalid initial-headroom interval")

    words = words_in_box(increment_abs_bound)
    headrooms = tuple(range(minimum_headroom, maximum_headroom + 1))
    tasks = [
        (word, start, initial_cycle, maximum_cycle, headrooms)
        for word in words
        for start in range(1, max_start_branch + 1)
        if stays_positive(start, word)
    ]
    if jobs == 1:
        results = list(map(scan_schedule, tasks))
    else:
        with ProcessPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(scan_schedule, tasks, chunksize=1))

    schedule_summaries = [summary for summary, _ in results]
    path_pairs = [path for _, paths in results for path in paths]
    path_summaries = [summary for summary, _ in path_pairs]
    rows = [row for _, path_rows in path_pairs for row in path_rows]
    hit_rows = [row for row in rows if row.carry_is_zero]
    closest_rows = sorted(
        (row for row in rows if not row.carry_is_zero),
        key=lambda row: (
            row.ternary_valuation_deficit
            if row.ternary_valuation_deficit is not None
            else 10**18,
            -(row.carry_v3 or 0),
            -max(row.ternary_floor_log_bits + 1 - row.signed_carry_bits, 0),
            row.source_cycle,
            row.initial_headroom_bits,
            row.start_branch,
            row.increment_word,
        ),
    )
    ranked_paths = sorted(
        path_summaries,
        key=lambda summary: (
            summary.longest_exact_hit_run,
            summary.exact_hit_count,
            -(
                summary.minimum_nonzero_ternary_deficit
                if summary.minimum_nonzero_ternary_deficit is not None
                else 10**18
            ),
            summary.maximum_nonzero_relative_leading_zero_bits or 0,
            -summary.initial_headroom_bits,
        ),
        reverse=True,
    )

    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [-increment_abs_bound, increment_abs_bound],
            "start_branches": [1, max_start_branch],
            "source_cycles": [initial_cycle, maximum_cycle, 1],
            "initial_headroom_bits": [minimum_headroom, maximum_headroom, 1],
        },
        "precision_recurrence": (
            "P(q0)=m(q0)+h; ell(q)=floor(log2(3^Q(q))); "
            "P(q+1)=P(q)-m(q)+ell(q)"
        ),
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(schedule_summaries),
        "precision_paths_checked": len(path_summaries),
        "exact_rows_checked": len(rows),
        "row_sha256": row_digest(rows),
        "exact_full_congruence_hits": len(hit_rows),
        "paths_with_exact_hit": sum(
            summary.exact_hit_count > 0 for summary in path_summaries
        ),
        "schedules_with_exact_hit": sum(
            summary.exact_hit_count > 0 for summary in schedule_summaries
        ),
        "maximum_exact_hit_run": max(
            (summary.longest_exact_hit_run for summary in path_summaries),
            default=0,
        ),
        "positive_carries": sum(row.carry_sign > 0 for row in rows),
        "negative_carries": sum(row.carry_sign < 0 for row in rows),
        "minimum_nonzero_ternary_deficit": min(
            (
                row.ternary_valuation_deficit
                for row in rows
                if row.ternary_valuation_deficit is not None
            ),
            default=None,
        ),
        "maximum_nonzero_carry_v3": max(
            (row.carry_v3 for row in rows if row.carry_v3 is not None),
            default=None,
        ),
        "exact_hit_rows": [row_dict(row) for row in hit_rows],
        "closest_nonzero_rows": [row_dict(row) for row in closest_rows[:64]],
        "construction_candidate_paths": [
            path_summary_dict(summary)
            for summary in ranked_paths
            if summary.exact_hit_count > 0
        ],
        "path_summaries": [
            path_summary_dict(summary) for summary in path_summaries
        ],
        "schedule_summaries": [
            schedule_summary_dict(summary) for summary in schedule_summaries
        ],
        "theorem_interface": (
            "At balanced precision, D(q)<3^Q(q) and the target has ell(q) "
            "free high bits, so |C_q|<3^Q(q). Therefore the full composite "
            "predecessor congruence is equivalent to C_q=0 and to one exact "
            "three-step link between the two canonical representatives. "
            "Only an all-future exact-hit tail would construct an infinite ray."
        ),
        "claim_scope": (
            "finite exact balanced-precision paths in the displayed schedule, "
            "headroom, and cycle box; exact hits are finite EC17 links only"
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized balanced-carry artifact schema")
    bounds = artifact["bounds"]
    increment_abs_bound = int(bounds["increment_components"][1])
    if bounds["increment_components"] != [
        -increment_abs_bound,
        increment_abs_bound,
    ]:
        raise ValueError("asymmetric increment bounds")
    starts = bounds["start_branches"]
    cycles = bounds["source_cycles"]
    headrooms = bounds["initial_headroom_bits"]
    if starts[0] != 1 or cycles[2] != 1 or headrooms[2] != 1:
        raise ValueError("unexpected balanced scan interval")
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(starts[1]),
        initial_cycle=int(cycles[0]),
        maximum_cycle=int(cycles[1]),
        minimum_headroom=int(headrooms[0]),
        maximum_headroom=int(headrooms[1]),
        jobs=jobs,
    )


def verify_artifact(path: Path, jobs: int) -> None:
    artifact = json.loads(path.read_text())
    reconstructed = reconstruct(artifact, jobs)
    for key, value in reconstructed.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("finite balanced-carry artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 14, 1),
        (2, (-1, 1, 1), 17, 4),
        (3, (1, -1, 1), 23, 9),
        (8, (1, 1, 0), 31, 16),
    ]
    for start, word, cycle, headroom in cases:
        _, binary, ternary, defect = one_cycle_data(start, word, cycle)
        source_precision = sum(binary) + headroom
        ell = (3 ** sum(ternary)).bit_length() - 1
        target_precision = headroom + ell
        gain = sum(word)
        source = canonical_residue(start + gain * cycle, word, source_precision)
        target = canonical_residue(
            start + gain * (cycle + 1), word, target_precision
        )
        row = audit_row(
            start,
            word,
            headroom,
            cycle,
            source_precision,
            target_precision,
            source,
            target,
        )
        if not row.defect_lt_full_ternary_modulus or not (
            defect < 3 ** sum(ternary)
        ):
            raise AssertionError("selftest lost the strict defect bound")
        if row.full_ternary_congruence != row.carry_is_zero:
            raise AssertionError("selftest lost the balanced equivalence")

    tiny = scan_box(1, 2, 14, 15, 1, 2, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny balanced-carry scan failed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    scan = subparsers.add_parser("scan")
    scan.add_argument("--increment-bound", type=int, default=1)
    scan.add_argument("--max-start", type=int, default=8)
    scan.add_argument("--initial-cycle", type=int, default=14)
    scan.add_argument("--max-cycle", type=int, default=60)
    scan.add_argument("--min-headroom", type=int, default=1)
    scan.add_argument("--max-headroom", type=int, default=16)
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
        print("balanced period-three carry self-test passed")
        return
    if args.command == "scan":
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            initial_cycle=args.initial_cycle,
            maximum_cycle=args.max_cycle,
            minimum_headroom=args.min_headroom,
            maximum_headroom=args.max_headroom,
            jobs=args.jobs,
        )
        artifact["generated_at"] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(
            json.dumps(
                {
                    "artifact": str(args.output),
                    "precision_paths_checked": artifact["precision_paths_checked"],
                    "exact_rows_checked": artifact["exact_rows_checked"],
                    "exact_full_congruence_hits": artifact[
                        "exact_full_congruence_hits"
                    ],
                    "maximum_exact_hit_run": artifact["maximum_exact_hit_run"],
                    "counterexample": artifact["counterexample"],
                },
                sort_keys=True,
            )
        )
        return
    verify_artifact(args.artifact, args.jobs)
    print(f"verified balanced period-three carry artifact: {args.artifact}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact consecutive-cycle compatibility audit for period-three EC17 rays.

For a positive period-three schedule, let ``r_q`` be the canonical future
residue at the kernel-checked sharp budget ``U(q)``.  Compose the next three
EC17 transitions as

    2^m(q) y_q = 3^a(q) r_q + D(q).

When ``p(q)=U(q)-m(q)>0``, future-residue consistency gives a signed integer
carry

    r_(q+1) - y_q = 2^p(q) C_q.

The exact value ``C_q=0`` is the construction-facing compatibility condition.
An exact research-side derivation says eventual zero carries splice the finite
representatives into an infinite positive EC17 execution, while every genuine
ray has eventual zero carries after the sharp upper bound identifies its cores
with the representatives.  The generic converse is proposed as QM121 and is
not called kernel-checked by this worker.

This worker replays all three internal divisions and reconstructs every row
with exact integers.  A finite zero streak is only a candidate macro; it is
not an infinite ray or a Collatz counterexample.
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
    v2,
)


SCHEMA = "collatz-breakoff-ether-period3-cycle-carry-v1"
CORE_CONSTANT = 17


@dataclass(frozen=True)
class ResidueData:
    value: int
    backward_transitions: int
    accumulated_binary_precision: int


@dataclass(frozen=True)
class CycleCarryRow:
    increment_word: tuple[int, int, int]
    start_branch: int
    source_cycle: int
    target_cycle: int
    cycle_gain: int
    phase_sum: int
    source_branch: int
    target_branch: int
    source_budget_bits: int
    target_budget_bits: int
    source_backward_transitions: int
    target_backward_transitions: int
    source_accumulated_binary_precision: int
    target_accumulated_binary_precision: int
    cycle_binary_exponent: int
    cycle_ternary_exponent: int
    carry_precision_bits: int
    unconstrained_target_high_bits: int
    source_residue_bits: int
    target_residue_bits: int
    exact_forward_image_bits: int
    equal_image_target_bit_length: bool
    carry_is_zero: bool
    carry_sign: int
    signed_carry_bits: int
    carry_leading_zero_bits: int
    carry_v2: int | None
    carry_v3: int | None
    ternary_valuation_deficit: int | None
    full_ternary_divisibility: bool
    carry_abs_lt_full_ternary_modulus: bool
    defect_lt_full_ternary_modulus: bool
    zero_forcing_exponent_gap: bool
    full_ternary_quotient_sign: int | None
    full_ternary_quotient_bits: int | None
    carry_mod_3: int
    carry_mod_27: int
    source_residue_sha256: str
    target_residue_sha256: str
    exact_forward_image_sha256: str
    signed_carry_sha256: str
    full_ternary_quotient_sha256: str | None
    ternary_remainder_sha256: str
    lifted_predecessor_hex_if_full: str | None
    source_residue_hex_if_zero: str | None
    target_residue_hex_if_zero: str | None


@dataclass(frozen=True)
class ScheduleSummary:
    increment_word: tuple[int, int, int]
    start_branch: int
    cycle_gain: int
    phase_sum: int
    rows_checked: int
    independent_series_residues_checked: int
    minimum_cycle: int
    maximum_cycle: int
    zero_carry_count: int
    longest_zero_run: int
    zero_run_intervals: tuple[tuple[int, int], ...]
    positive_carry_count: int
    negative_carry_count: int
    equal_image_target_bit_length_count: int
    full_ternary_divisibility_count: int
    zero_forcing_exponent_gap_count: int
    minimum_ternary_valuation_deficit: int | None
    minimum_ternary_valuation_deficit_cycle: int | None
    maximum_carry_v2: int | None
    maximum_carry_v2_cycle: int | None
    maximum_carry_leading_zero_bits: int
    maximum_carry_leading_zero_cycle: int
    minimum_nonzero_signed_carry_bits: int | None
    minimum_nonzero_signed_carry_cycle: int | None
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
    """Return the exact finite valuation, using ``None`` for zero."""

    if prime < 2:
        raise ValueError("valuation prime must be at least two")
    magnitude = abs(value)
    if magnitude == 0:
        return None
    valuation = 0
    while magnitude % prime == 0:
        magnitude //= prime
        valuation += 1
    return valuation


def incremental_series_residue(
    start_branch: int, word: Sequence[int], precision_bits: int
) -> int:
    """Independent forward-series evaluator with incremental coefficients.

    This is the closed negative EC17 series, accumulated from its low terms
    upward.  It is algebraically independent of the terminal-to-source
    `backward_residue` loop, but avoids recomputing a growing inverse power of
    three from scratch at every term as the slower reference evaluator does.
    """

    if precision_bits < 1 or not stays_positive(start_branch, word):
        raise ValueError("invalid incremental series request")
    modulus = 1 << precision_bits
    mask = modulus - 1
    inverse_three = pow(3, -1, modulus)
    inverse_ternary_prefix = 1
    step_inverse = pow(inverse_three, 6 * start_branch + 11, modulus)
    binary_prefix = 1
    residue = 0
    level = start_branch
    transition = 0
    while binary_prefix:
        target = level + int(word[transition % 3])
        if target < 1:
            raise AssertionError("positive schedule became nonpositive")
        binary = 8 * target + 15
        inverse_ternary_prefix = (
            inverse_ternary_prefix * step_inverse
        ) & mask
        residue = (
            residue
            - CORE_CONSTANT * binary_prefix * inverse_ternary_prefix
        ) & mask
        binary_prefix = (binary_prefix << binary) & mask
        ternary_delta = 6 * (target - level)
        if ternary_delta < 0:
            step_inverse = (
                step_inverse * pow(3, -ternary_delta, modulus)
            ) & mask
        elif ternary_delta > 0:
            step_inverse = (
                step_inverse * pow(inverse_three, ternary_delta, modulus)
            ) & mask
        level = target
        transition += 1
    if residue % 2 != 1:
        raise AssertionError("incremental EC17 series residue is not odd")
    return residue


def row_dict(row: CycleCarryRow) -> dict[str, Any]:
    result = asdict(row)
    result["increment_word"] = list(row.increment_word)
    return result


def row_digest(rows: Iterable[CycleCarryRow]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(
            json.dumps(row_dict(row), sort_keys=True, separators=(",", ":")).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def one_cycle_data(
    start_branch: int, word: Sequence[int], cycle: int
) -> tuple[tuple[int, int, int, int], tuple[int, int, int], tuple[int, int, int], int]:
    """Return levels, binary exponents, ternary exponents, and composed defect."""

    gain = sum(word)
    n0 = start_branch + gain * cycle
    n1 = n0 + int(word[0])
    n2 = n1 + int(word[1])
    n3 = n2 + int(word[2])
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
    source_residue: int,
    levels: Sequence[int],
    binary: Sequence[int],
    ternary: Sequence[int],
) -> int:
    """Replay and valuation-check the three literal EC17 transitions."""

    core = source_residue
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
    return core


def audit_row(
    start_branch: int,
    word: Sequence[int],
    cycle: int,
    source_data: ResidueData | None = None,
    target_data: ResidueData | None = None,
) -> CycleCarryRow:
    normalized_word = tuple(int(value) for value in word)
    if (
        len(normalized_word) != 3
        or cycle < MINIMUM_CYCLE
        or not stays_positive(start_branch, normalized_word)
    ):
        raise ValueError("invalid consecutive-cycle carry row")
    gain = sum(normalized_word)
    levels, binary, ternary, defect = one_cycle_data(
        start_branch, normalized_word, cycle
    )
    source_budget = sharp_upper_budget_bits(start_branch, normalized_word, cycle)
    target_budget = sharp_upper_budget_bits(
        start_branch, normalized_word, cycle + 1
    )
    binary_sum = sum(binary)
    ternary_sum = sum(ternary)
    carry_precision = source_budget - binary_sum
    if carry_precision < 1:
        raise ValueError("cycle does not yet have positive carry precision")
    if target_budget < carry_precision:
        raise AssertionError("target budget does not cover carry precision")

    if source_data is None:
        source_residue, source_transitions, source_accumulated = backward_residue(
            levels[0], normalized_word, source_budget
        )
        source_data = ResidueData(
            source_residue, source_transitions, source_accumulated
        )
    if target_data is None:
        target_residue, target_transitions, target_accumulated = backward_residue(
            levels[3], normalized_word, target_budget
        )
        target_data = ResidueData(
            target_residue, target_transitions, target_accumulated
        )
    source_residue = source_data.value
    target_residue = target_data.value
    if source_data.accumulated_binary_precision < source_budget:
        raise AssertionError("source backward residue did not cover its budget")
    if target_data.accumulated_binary_precision < target_budget:
        raise AssertionError("target backward residue did not cover its budget")
    if source_data.backward_transitions < 4:
        raise AssertionError("source residue did not cover a cycle plus parity bit")
    if not (0 < source_residue < 1 << source_budget):
        raise AssertionError("source residue escaped its canonical range")
    if not (0 < target_residue < 1 << target_budget):
        raise AssertionError("target residue escaped its canonical range")

    full_ternary_modulus = 3 ** ternary_sum
    defect_lt_full_ternary_modulus = defect < full_ternary_modulus
    if not defect_lt_full_ternary_modulus:
        raise AssertionError("one-cycle defect reached its full ternary modulus")
    composed_numerator = full_ternary_modulus * source_residue + defect
    if composed_numerator % (1 << binary_sum):
        raise AssertionError("composed source residue did not divide exactly")
    forward_image = composed_numerator >> binary_sum
    replayed_image = replay_cycle(source_residue, levels, binary, ternary)
    if replayed_image != forward_image:
        raise AssertionError("sequential replay disagrees with composed formula")

    modulus = 1 << carry_precision
    difference = target_residue - forward_image
    if difference % modulus:
        raise AssertionError("canonical future residues disagree below carry boundary")
    carry = difference // modulus
    carry_v2 = prime_valuation(carry, 2)
    carry_v3 = prime_valuation(carry, 3)
    floor_quotient, ternary_remainder = divmod(carry, full_ternary_modulus)
    full_ternary_divisibility = ternary_remainder == 0
    # Reversing the complete cycle from r_(q+1) differs from r_q by
    # 2^U * (C_q / 3^Q).  Thus 3^Q | C_q is the exact full predecessor
    # congruence, while the additional strict magnitude test forces C_q=0.
    if full_ternary_divisibility != (carry % full_ternary_modulus == 0):
        raise AssertionError("full ternary divisibility check disagreed")
    if full_ternary_divisibility and abs(carry) < full_ternary_modulus and carry != 0:
        raise AssertionError("divisible carry below its modulus was nonzero")
    reverse_numerator = (1 << binary_sum) * target_residue - defect
    reverse_divisible = reverse_numerator % full_ternary_modulus == 0
    if reverse_divisible != full_ternary_divisibility:
        raise AssertionError("reverse predecessor check disagreed with carry divisibility")
    full_ternary_quotient = floor_quotient if full_ternary_divisibility else None
    if full_ternary_divisibility:
        predecessor = reverse_numerator // full_ternary_modulus
        lifted = (
            source_residue
            + (1 << source_budget) * full_ternary_quotient
        )
        if predecessor != lifted:
            raise AssertionError("full predecessor lift identity failed")
        if carry < 0:
            raise AssertionError("a nonpositive full-depth lift contradicted positivity")
    unconstrained_high = target_budget - carry_precision
    zero_forcing_exponent_gap = (
        (1 << unconstrained_high) <= full_ternary_modulus
    )
    if (
        full_ternary_divisibility
        and zero_forcing_exponent_gap
        and carry != 0
    ):
        raise AssertionError("full divisibility plus exponent gap failed to force zero")

    expected_binary = 8 * (phase_sum(start_branch, normalized_word) + gain) + 45 + 24 * gain * cycle
    expected_ternary = 6 * phase_sum(start_branch, normalized_word) + 33 + 18 * gain * cycle
    if binary_sum != expected_binary or ternary_sum != expected_ternary:
        raise AssertionError("one-cycle exponent sum formula did not close")

    return CycleCarryRow(
        increment_word=normalized_word,
        start_branch=start_branch,
        source_cycle=cycle,
        target_cycle=cycle + 1,
        cycle_gain=gain,
        phase_sum=phase_sum(start_branch, normalized_word),
        source_branch=levels[0],
        target_branch=levels[3],
        source_budget_bits=source_budget,
        target_budget_bits=target_budget,
        source_backward_transitions=source_data.backward_transitions,
        target_backward_transitions=target_data.backward_transitions,
        source_accumulated_binary_precision=(
            source_data.accumulated_binary_precision
        ),
        target_accumulated_binary_precision=(
            target_data.accumulated_binary_precision
        ),
        cycle_binary_exponent=binary_sum,
        cycle_ternary_exponent=ternary_sum,
        carry_precision_bits=carry_precision,
        unconstrained_target_high_bits=unconstrained_high,
        source_residue_bits=source_residue.bit_length(),
        target_residue_bits=target_residue.bit_length(),
        exact_forward_image_bits=forward_image.bit_length(),
        equal_image_target_bit_length=(
            forward_image.bit_length() == target_residue.bit_length()
        ),
        carry_is_zero=(carry == 0),
        carry_sign=(carry > 0) - (carry < 0),
        signed_carry_bits=abs(carry).bit_length(),
        carry_leading_zero_bits=max(
            unconstrained_high - abs(carry).bit_length(), 0
        ),
        carry_v2=carry_v2,
        carry_v3=carry_v3,
        ternary_valuation_deficit=(
            None if carry_v3 is None else max(ternary_sum - carry_v3, 0)
        ),
        full_ternary_divisibility=full_ternary_divisibility,
        carry_abs_lt_full_ternary_modulus=(
            abs(carry) < full_ternary_modulus
        ),
        defect_lt_full_ternary_modulus=defect_lt_full_ternary_modulus,
        zero_forcing_exponent_gap=zero_forcing_exponent_gap,
        full_ternary_quotient_sign=(
            None if full_ternary_quotient is None
            else (full_ternary_quotient > 0) - (full_ternary_quotient < 0)
        ),
        full_ternary_quotient_bits=(
            None if full_ternary_quotient is None
            else abs(full_ternary_quotient).bit_length()
        ),
        carry_mod_3=carry % 3,
        carry_mod_27=carry % 27,
        source_residue_sha256=digest_natural(source_residue),
        target_residue_sha256=digest_natural(target_residue),
        exact_forward_image_sha256=digest_natural(forward_image),
        signed_carry_sha256=digest_signed(carry),
        full_ternary_quotient_sha256=(
            None if full_ternary_quotient is None
            else digest_signed(full_ternary_quotient)
        ),
        ternary_remainder_sha256=digest_natural(ternary_remainder),
        lifted_predecessor_hex_if_full=(
            hex(reverse_numerator // full_ternary_modulus)
            if full_ternary_divisibility else None
        ),
        source_residue_hex_if_zero=(hex(source_residue) if carry == 0 else None),
        target_residue_hex_if_zero=(hex(target_residue) if carry == 0 else None),
    )


def zero_run_intervals(rows: Sequence[CycleCarryRow]) -> tuple[tuple[int, int], ...]:
    intervals: list[tuple[int, int]] = []
    run_start: int | None = None
    previous: int | None = None
    for row in rows:
        if row.carry_is_zero:
            if run_start is None:
                run_start = row.source_cycle
            elif previous is None or row.source_cycle != previous + 1:
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


def summarize_schedule(
    rows: Sequence[CycleCarryRow], independent_series_residues_checked: int
) -> ScheduleSummary:
    if not rows:
        raise ValueError("cannot summarize an empty schedule")
    intervals = zero_run_intervals(rows)
    nonzero = [row for row in rows if not row.carry_is_zero]
    closest = min(nonzero, key=lambda row: (row.signed_carry_bits, row.source_cycle)) if nonzero else None
    closest_depth = min(
        nonzero,
        key=lambda row: (
            row.ternary_valuation_deficit
            if row.ternary_valuation_deficit is not None else -1,
            row.source_cycle,
        ),
    ) if nonzero else None
    highest_v2 = max(
        nonzero,
        key=lambda row: (row.carry_v2 or 0, -row.source_cycle),
    ) if nonzero else None
    closest_scaled = max(
        rows,
        key=lambda row: (row.carry_leading_zero_bits, -row.source_cycle),
    )
    return ScheduleSummary(
        increment_word=rows[0].increment_word,
        start_branch=rows[0].start_branch,
        cycle_gain=rows[0].cycle_gain,
        phase_sum=rows[0].phase_sum,
        rows_checked=len(rows),
        independent_series_residues_checked=independent_series_residues_checked,
        minimum_cycle=rows[0].source_cycle,
        maximum_cycle=rows[-1].source_cycle,
        zero_carry_count=sum(row.carry_is_zero for row in rows),
        longest_zero_run=max((end - start + 1 for start, end in intervals), default=0),
        zero_run_intervals=intervals,
        positive_carry_count=sum(row.carry_sign > 0 for row in rows),
        negative_carry_count=sum(row.carry_sign < 0 for row in rows),
        equal_image_target_bit_length_count=sum(
            row.equal_image_target_bit_length for row in rows
        ),
        full_ternary_divisibility_count=sum(
            row.full_ternary_divisibility for row in rows
        ),
        zero_forcing_exponent_gap_count=sum(
            row.zero_forcing_exponent_gap for row in rows
        ),
        minimum_ternary_valuation_deficit=(
            closest_depth.ternary_valuation_deficit
            if closest_depth is not None else None
        ),
        minimum_ternary_valuation_deficit_cycle=(
            closest_depth.source_cycle if closest_depth is not None else None
        ),
        maximum_carry_v2=(highest_v2.carry_v2 if highest_v2 is not None else None),
        maximum_carry_v2_cycle=(
            highest_v2.source_cycle if highest_v2 is not None else None
        ),
        maximum_carry_leading_zero_bits=closest_scaled.carry_leading_zero_bits,
        maximum_carry_leading_zero_cycle=closest_scaled.source_cycle,
        minimum_nonzero_signed_carry_bits=(
            closest.signed_carry_bits if closest is not None else None
        ),
        minimum_nonzero_signed_carry_cycle=(
            closest.source_cycle if closest is not None else None
        ),
        row_sha256=row_digest(rows),
    )


def summary_dict(summary: ScheduleSummary) -> dict[str, Any]:
    result = asdict(summary)
    result["increment_word"] = list(summary.increment_word)
    result["zero_run_intervals"] = [list(interval) for interval in summary.zero_run_intervals]
    return result


def scan_schedule(
    task: tuple[tuple[int, int, int], int, tuple[int, ...]]
) -> tuple[ScheduleSummary, list[CycleCarryRow]]:
    word, start, cycles = task
    gain = sum(word)
    residue_cache: dict[int, ResidueData] = {}
    independent_checkpoints = {
        cycles[0],
        cycles[len(cycles) // 2],
        cycles[-1],
        cycles[-1] + 1,
    }
    independently_checked: set[int] = set()
    for cycle in range(cycles[0], cycles[-1] + 2):
        budget = sharp_upper_budget_bits(start, word, cycle)
        shifted = start + gain * cycle
        residue, transitions, accumulated = backward_residue(shifted, word, budget)
        residue_cache[cycle] = ResidueData(residue, transitions, accumulated)
        if cycle in independent_checkpoints:
            if residue != incremental_series_residue(shifted, word, budget):
                raise AssertionError("direct series disagrees with backward residue")
            independently_checked.add(cycle)
    rows = [
        audit_row(
            start,
            word,
            cycle,
            source_data=residue_cache[cycle],
            target_data=residue_cache[cycle + 1],
        )
        for cycle in cycles
    ]
    # Exact-zero or full-depth rows are construction-facing anomalies.  Always
    # reconstruct both endpoints by the independent series, even away from the
    # deterministic schedule checkpoints.
    anomaly_cycles = {
        endpoint
        for row in rows
        if row.carry_is_zero or row.full_ternary_divisibility
        for endpoint in (row.source_cycle, row.target_cycle)
    }
    for cycle in sorted(anomaly_cycles - independently_checked):
        budget = sharp_upper_budget_bits(start, word, cycle)
        shifted = start + gain * cycle
        if residue_cache[cycle].value != incremental_series_residue(
            shifted, word, budget
        ):
            raise AssertionError("anomaly series disagrees with backward residue")
        independently_checked.add(cycle)
    return summarize_schedule(rows, len(independently_checked)), rows


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    minimum_cycle: int,
    maximum_cycle: int,
    jobs: int,
) -> dict[str, Any]:
    if min(increment_abs_bound, max_start_branch, jobs) < 1:
        raise ValueError("scan bounds and worker count must be positive")
    if minimum_cycle < MINIMUM_CYCLE or maximum_cycle < minimum_cycle:
        raise ValueError("invalid cycle interval")
    cycles = tuple(range(minimum_cycle, maximum_cycle + 1))
    words = words_in_box(increment_abs_bound)
    tasks = [
        (word, start, cycles)
        for word in words
        for start in range(1, max_start_branch + 1)
        if stays_positive(start, word)
    ]
    # The criterion is defined only after the source budget covers a complete
    # cycle and leaves at least one consistency bit.  Reject mixed boxes rather
    # than silently dropping early rows.
    for word, start, _ in tasks:
        levels, binary, _, _ = one_cycle_data(start, word, minimum_cycle)
        del levels
        if sharp_upper_budget_bits(start, word, minimum_cycle) <= sum(binary):
            raise ValueError(
                "minimum cycle is below positive carry precision for at least one schedule"
            )
    if jobs == 1:
        results = list(map(scan_schedule, tasks))
    else:
        with ProcessPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(scan_schedule, tasks, chunksize=1))
    summaries = [summary for summary, _ in results]
    rows = [row for _, schedule_rows in results for row in schedule_rows]
    zero_rows = [row for row in rows if row.carry_is_zero]
    full_depth_rows = [row for row in rows if row.full_ternary_divisibility]
    closest_rows = sorted(
        (row for row in rows if not row.carry_is_zero),
        key=lambda row: (
            -row.carry_leading_zero_bits,
            row.source_cycle,
            row.start_branch,
            row.increment_word,
        ),
    )
    closest_full_ternary_rows = sorted(
        (row for row in rows if not row.carry_is_zero),
        key=lambda row: (
            not row.full_ternary_divisibility,
            row.ternary_valuation_deficit
            if row.ternary_valuation_deficit is not None else -1,
            -(row.carry_v2 or 0),
            row.source_cycle,
            row.start_branch,
            row.increment_word,
        ),
    )
    ranked_summaries = sorted(
        summaries,
        key=lambda summary: (
            summary.longest_zero_run,
            summary.zero_carry_count,
            summary.full_ternary_divisibility_count,
            summary.maximum_carry_leading_zero_bits,
            -summary.start_branch,
            summary.increment_word,
        ),
        reverse=True,
    )
    return {
        "schema": SCHEMA,
        "bounds": {
            "increment_components": [-increment_abs_bound, increment_abs_bound],
            "start_branches": [1, max_start_branch],
            "source_cycles": [minimum_cycle, maximum_cycle, 1],
            "target_cycles": [minimum_cycle + 1, maximum_cycle + 1, 1],
        },
        "increment_words_checked": len(words),
        "positive_schedules_checked": len(summaries),
        "exact_rows_checked": len(rows),
        "independent_series_residues_checked": sum(
            summary.independent_series_residues_checked for summary in summaries
        ),
        "row_sha256": row_digest(rows),
        "zero_carry_rows": len(zero_rows),
        "schedules_with_zero_carry": sum(summary.zero_carry_count > 0 for summary in summaries),
        "maximum_zero_carry_run": max(
            (summary.longest_zero_run for summary in summaries), default=0
        ),
        "positive_carries": sum(row.carry_sign > 0 for row in rows),
        "negative_carries": sum(row.carry_sign < 0 for row in rows),
        "equal_image_target_bit_length_rows": sum(
            row.equal_image_target_bit_length for row in rows
        ),
        "full_ternary_divisibility_rows": sum(
            row.full_ternary_divisibility for row in rows
        ),
        "carry_below_full_ternary_modulus_rows": sum(
            row.carry_abs_lt_full_ternary_modulus for row in rows
        ),
        "zero_forcing_exponent_gap_rows": sum(
            row.zero_forcing_exponent_gap for row in rows
        ),
        "maximum_nonzero_carry_v3": max(
            (row.carry_v3 or 0 for row in rows if not row.carry_is_zero),
            default=None,
        ),
        "exact_zero_rows": [row_dict(row) for row in zero_rows],
        "full_ternary_lifted_link_rows": [
            row_dict(row) for row in full_depth_rows
        ],
        "closest_nonzero_rows": [row_dict(row) for row in closest_rows[:64]],
        "closest_full_ternary_rows": [
            row_dict(row) for row in closest_full_ternary_rows[:64]
        ],
        "construction_candidate_schedules": [
            summary_dict(summary)
            for summary in ranked_summaries
            if summary.zero_carry_count > 0
        ],
        "schedule_summaries": [summary_dict(summary) for summary in summaries],
        "theorem_interface": (
            "Proposed QM121: for p(q)=U(q)-m(q)>0, bare-schedule canonical "
            "future consistency defines r_(q+1)-y_q=2^p(q) C_q. Every "
            "genuine period-three ray has eventual C_q=0 after the sharp "
            "core bound. The research-side converse says an eventual exact-"
            "zero carry tail, together with the audited three-step replay, "
            "splices into an infinite positive EC17 ray. "
            "The exact full predecessor screen is 3^Q | C_q; if also "
            "|C_q|<3^Q, it forces C_q=0."
        ),
        "claim_scope": (
            "finite exact consecutive-cycle carry rows in the displayed "
            "schedule and cycle box; only an all-q zero tail would construct "
            "a nonterminating execution. A nonzero full-ternary-divisibility "
            "row is only one lifted finite link and does not stitch to its "
            "neighbors without additional equality."
        ),
        "counterexample": None,
    }


def reconstruct(artifact: dict[str, Any], jobs: int) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ValueError("unrecognized cycle-carry artifact schema")
    bounds = artifact["bounds"]
    increment_abs_bound = int(bounds["increment_components"][1])
    if bounds["increment_components"] != [-increment_abs_bound, increment_abs_bound]:
        raise ValueError("asymmetric increment bounds")
    start_bounds = bounds["start_branches"]
    source_cycles = bounds["source_cycles"]
    target_cycles = bounds["target_cycles"]
    if start_bounds[0] != 1 or source_cycles[2] != 1:
        raise ValueError("unexpected scan interval")
    if target_cycles != [source_cycles[0] + 1, source_cycles[1] + 1, 1]:
        raise ValueError("target-cycle interval does not follow sources")
    return scan_box(
        increment_abs_bound=increment_abs_bound,
        max_start_branch=int(start_bounds[1]),
        minimum_cycle=int(source_cycles[0]),
        maximum_cycle=int(source_cycles[1]),
        jobs=jobs,
    )


def verify_artifact(path: Path, jobs: int) -> None:
    artifact = json.loads(path.read_text())
    reconstructed = reconstruct(artifact, jobs)
    for key, value in reconstructed.items():
        if artifact.get(key) != value:
            raise ValueError(f"artifact mismatch at {key}")
    if artifact.get("counterexample", "missing") is not None:
        raise ValueError("finite cycle-carry artifact claims a counterexample")


def selftest() -> None:
    cases = [
        (1, (0, 0, 1), 14),
        (2, (-1, 1, 1), 17),
        (3, (1, -1, 1), 23),
        (8, (1, 1, 0), 99),
    ]
    for start, word, cycle in cases:
        row = audit_row(start, word, cycle)
        source = backward_residue(
            row.source_branch, word, row.source_budget_bits
        )[0]
        target = backward_residue(
            row.target_branch, word, row.target_budget_bits
        )[0]
        if source != direct_series_residue(
            row.source_branch, word, row.source_budget_bits
        ):
            raise AssertionError("source direct series disagrees with backward evaluator")
        if source != incremental_series_residue(
            row.source_branch, word, row.source_budget_bits
        ):
            raise AssertionError("source incremental series disagrees")
        if target != direct_series_residue(
            row.target_branch, word, row.target_budget_bits
        ):
            raise AssertionError("target direct series disagrees with backward evaluator")
        if target != incremental_series_residue(
            row.target_branch, word, row.target_budget_bits
        ):
            raise AssertionError("target incremental series disagrees")
        if digest_natural(source) != row.source_residue_sha256:
            raise AssertionError("source residue digest mismatch")
        if digest_natural(target) != row.target_residue_sha256:
            raise AssertionError("target residue digest mismatch")
    tiny = scan_box(1, 3, 14, 16, 1)
    if tiny["counterexample"] is not None or tiny["exact_rows_checked"] < 1:
        raise AssertionError("tiny consecutive-cycle scan failed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    scan = subparsers.add_parser("scan")
    scan.add_argument("--increment-bound", type=int, default=1)
    scan.add_argument("--max-start", type=int, default=8)
    scan.add_argument("--min-cycle", type=int, default=14)
    scan.add_argument("--max-cycle", type=int, default=256)
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
        print("consecutive-cycle period-three carry self-test passed")
        return
    if args.command == "scan":
        artifact = scan_box(
            increment_abs_bound=args.increment_bound,
            max_start_branch=args.max_start,
            minimum_cycle=args.min_cycle,
            maximum_cycle=args.max_cycle,
            jobs=args.jobs,
        )
        artifact["generated_at"] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps({
            "artifact": str(args.output),
            "exact_rows_checked": artifact["exact_rows_checked"],
            "zero_carry_rows": artifact["zero_carry_rows"],
            "maximum_zero_carry_run": artifact["maximum_zero_carry_run"],
            "counterexample": artifact["counterexample"],
        }, sort_keys=True))
        return
    verify_artifact(args.artifact, args.jobs)
    print(f"verified consecutive-cycle period-three carry artifact: {args.artifact}")


if __name__ == "__main__":
    main()

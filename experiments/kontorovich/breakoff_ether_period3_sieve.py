#!/usr/bin/env python3
"""Exact ordinary-core lower bounds for period-three EC17 programs.

For a prescribed positive branch schedule, the constant-seventeen recurrence

    2^(8*n_(t+1)+15) u_(t+1) = 3^(6*n_t+11) u_t + 17

has at most one initial core modulo every power of two.  If ``P`` bits of
backward precision have been accumulated, the terminal term vanishes modulo
``2^P`` and gives one exact residue ``r_P``.

Any ordinary core ``0 < u_0 < 2^P`` on that infinite schedule must therefore
equal the literal integer ``r_P``.  We execute ``r_P`` forward with exact
integers.  If it fails a required division, no ordinary core below ``2^P``
can realize the schedule.  This is a finite, machine-checkable lower bound,
not evidence that a larger core or an infinite orbit exists.

The search box consists only of genuinely period-three increment words with
positive cycle sum.  Zero-sum words have periodic branch levels and are
already excluded by the companion periodic-level theorem; negative-sum words
cannot remain in positive branches forever.  The scan is intended for CPU
parallelism and supports reproducible high-precision runs on Akdeniz.
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


SCHEMA = "collatz-breakoff-ether-period3-sieve-v1"
PERIOD = 3
CORE_CONSTANT = 17


@dataclass(frozen=True)
class CandidateRecord:
    increment_word: tuple[int, int, int]
    start_branch: int
    precision_bits: int
    backward_transitions: int
    residue_bits: int
    leading_zero_bits: int
    leading_one_bits: int
    failure_step: int | None
    failure_source_branch: int | None
    failure_target_branch: int | None
    failure_numerator_v2: int | None
    failure_required_v2: int | None
    residue_hex: str


def v2(value: int) -> int:
    if value < 1:
        raise ValueError("valuation requires a positive integer")
    return (value & -value).bit_length() - 1


def valid_period_three_word(word: Sequence[int]) -> bool:
    return (
        len(word) == PERIOD
        and sum(word) > 0
        and not (word[0] == word[1] == word[2])
    )


def stays_positive(start_branch: int, word: Sequence[int]) -> bool:
    if start_branch < 1 or not valid_period_three_word(word):
        return False
    level = start_branch
    for increment in word:
        level += increment
        if level < 1:
            return False
    # Every later cycle is this first cycle translated upward by sum(word).
    return True


def precision_levels(
    start_branch: int, word: Sequence[int], precision_bits: int
) -> tuple[list[int], int]:
    if precision_bits < 1 or not stays_positive(start_branch, word):
        raise ValueError("invalid positive period-three schedule")
    levels = [start_branch]
    accumulated_binary = 0
    transition = 0
    while accumulated_binary < precision_bits:
        following = levels[-1] + word[transition % PERIOD]
        if following < 1:
            raise AssertionError("positive-cycle schedule later became nonpositive")
        levels.append(following)
        accumulated_binary += 8 * following + 15
        transition += 1
    return levels, accumulated_binary


def backward_residue(
    start_branch: int, word: Sequence[int], precision_bits: int
) -> tuple[int, int, int]:
    """Return the unique infinite-candidate residue modulo ``2^P``."""

    levels, accumulated_binary = precision_levels(
        start_branch, word, precision_bits
    )
    modulus = 1 << precision_bits
    residue = 0
    for transition in range(len(levels) - 2, -1, -1):
        source = levels[transition]
        target = levels[transition + 1]
        binary = 8 * target + 15
        ternary = 6 * source + 11
        residue = (
            ((residue << binary) - CORE_CONSTANT)
            * pow(3, -ternary, modulus)
        ) % modulus
    if residue % 2 != 1:
        raise AssertionError("EC17 candidate residue is not odd")
    return residue, len(levels) - 1, accumulated_binary


def direct_series_residue(
    start_branch: int, word: Sequence[int], precision_bits: int
) -> int:
    """Independent forward-sum form used by self-tests."""

    levels, _ = precision_levels(start_branch, word, precision_bits)
    modulus = 1 << precision_bits
    two_exponent = 0
    three_exponent = 0
    residue = 0
    for term in range(len(levels) - 1):
        if term:
            two_exponent += 8 * levels[term] + 15
        three_exponent += 6 * levels[term] + 11
        if two_exponent >= precision_bits:
            break
        residue = (
            residue
            - CORE_CONSTANT
            * (1 << two_exponent)
            * pow(3, -three_exponent, modulus)
        ) % modulus
    return residue


def literal_failure(
    residue: int,
    start_branch: int,
    word: Sequence[int],
    max_steps: int,
) -> tuple[int, int, int, int, int] | None:
    """Execute the prescribed EC17 divisions until the first exact failure."""

    core = residue
    source = start_branch
    for step in range(max_steps):
        target = source + word[step % PERIOD]
        if target < 1:
            raise AssertionError("certified positive schedule became nonpositive")
        numerator = 3 ** (6 * source + 11) * core + CORE_CONSTANT
        actual = v2(numerator)
        required = 8 * target + 15
        if actual < required:
            return step, source, target, actual, required
        if actual > required:
            # Exact EC17 still divides, but the quotient is even and therefore
            # cannot be the normalized odd core selected by this target branch.
            return step, source, target, actual, required
        core = numerator >> required
        if core % 2 != 1:
            raise AssertionError("exact target valuation emitted an even core")
        if core % 3 != 1:
            raise AssertionError("EC17 core lost its forced residue modulo three")
        source = target
    return None


def leading_one_bits(residue: int, precision_bits: int) -> int:
    mask = (1 << precision_bits) - 1
    complement = mask ^ residue
    return precision_bits - complement.bit_length()


def audit_candidate(
    start_branch: int, word: Sequence[int], precision_bits: int
) -> CandidateRecord:
    residue, transitions, accumulated = backward_residue(
        start_branch, word, precision_bits
    )
    if accumulated < precision_bits:
        raise AssertionError("terminal term retained visible binary precision")
    failure = literal_failure(
        residue, start_branch, word, transitions + PERIOD + 64
    )
    zeros = precision_bits - residue.bit_length()
    ones = leading_one_bits(residue, precision_bits)
    if failure is None:
        failure_fields: tuple[int | None, ...] = (None,) * 5
    else:
        failure_fields = failure
    return CandidateRecord(
        increment_word=(int(word[0]), int(word[1]), int(word[2])),
        start_branch=start_branch,
        precision_bits=precision_bits,
        backward_transitions=transitions,
        residue_bits=residue.bit_length(),
        leading_zero_bits=zeros,
        leading_one_bits=ones,
        failure_step=failure_fields[0],
        failure_source_branch=failure_fields[1],
        failure_target_branch=failure_fields[2],
        failure_numerator_v2=failure_fields[3],
        failure_required_v2=failure_fields[4],
        residue_hex=hex(residue),
    )


def words_in_box(increment_abs_bound: int) -> list[tuple[int, int, int]]:
    if increment_abs_bound < 1:
        raise ValueError("increment bound must be positive")
    values = range(-increment_abs_bound, increment_abs_bound + 1)
    return [
        (a, b, c)
        for a, b, c in product(values, repeat=PERIOD)
        if valid_period_three_word((a, b, c))
    ]


def record_digest(records: Iterable[CandidateRecord]) -> str:
    digest = hashlib.sha256()
    for record in records:
        digest.update(
            json.dumps(
                asdict(record), sort_keys=True, separators=(",", ":")
            ).encode()
        )
        digest.update(b"\n")
    return digest.hexdigest()


def record_dict(record: CandidateRecord) -> dict[str, Any]:
    result = asdict(record)
    result["increment_word"] = list(record.increment_word)
    return result


def scan_word(args: tuple[tuple[int, int, int], int, int]) -> list[CandidateRecord]:
    word, max_start_branch, precision_bits = args
    return [
        audit_candidate(start, word, precision_bits)
        for start in range(1, max_start_branch + 1)
        if stays_positive(start, word)
    ]


def scan_box(
    increment_abs_bound: int,
    max_start_branch: int,
    precision_bits: int,
    jobs: int,
) -> dict[str, Any]:
    if min(max_start_branch, precision_bits, jobs) < 1:
        raise ValueError("scan parameters must be positive")
    words = words_in_box(increment_abs_bound)
    tasks = [(word, max_start_branch, precision_bits) for word in words]
    if jobs == 1:
        groups = map(scan_word, tasks)
    else:
        executor = ProcessPoolExecutor(max_workers=jobs)
        groups = executor.map(scan_word, tasks, chunksize=1)
    records: list[CandidateRecord] = []
    try:
        for group in groups:
            records.extend(group)
    finally:
        if jobs != 1:
            executor.shutdown()

    unresolved = [record for record in records if record.failure_step is None]
    if records:
        zero_anomalies = sorted(
            records,
            key=lambda record: (
                record.leading_zero_bits,
                -record.start_branch,
                record.increment_word,
            ),
            reverse=True,
        )[:32]
        one_anomalies = sorted(
            records,
            key=lambda record: (
                record.leading_one_bits,
                -record.start_branch,
                record.increment_word,
            ),
            reverse=True,
        )[:32]
        failure_steps = [
            record.failure_step
            for record in records
            if record.failure_step is not None
        ]
    else:
        zero_anomalies = []
        one_anomalies = []
        failure_steps = []
    return {
        "bounds": {
            "increment_components": [
                -increment_abs_bound, increment_abs_bound
            ],
            "start_branches": [1, max_start_branch],
            "precision_bits": precision_bits,
        },
        "period": PERIOD,
        "increment_words_checked": len(words),
        "positive_schedule_candidates_checked": len(records),
        "record_sha256": record_digest(records),
        "all_literal_residues_failed": not unresolved,
        "unresolved": [record_dict(record) for record in unresolved],
        "failure_step_range": (
            [min(failure_steps), max(failure_steps)] if failure_steps else None
        ),
        "maximum_leading_zero_bits": (
            max(record.leading_zero_bits for record in records)
            if records else None
        ),
        "maximum_leading_one_bits": (
            max(record.leading_one_bits for record in records)
            if records else None
        ),
        "leading_zero_anomalies": [record_dict(record) for record in zero_anomalies],
        "leading_one_anomalies": [record_dict(record) for record in one_anomalies],
        "certified_ordinary_core_lower_bound": (
            f"2^{precision_bits}" if records and not unresolved else None
        ),
        "lower_bound_scope": (
            "for every checked start/word pair, any positive ordinary EC17 "
            "core realizing that entire prescribed schedule is at least the "
            "displayed power of two"
        ),
        "claim_scope": (
            "exhaustive in the stated increment/start box; exact candidate "
            "residues modulo 2^P and exact forward failure of their least "
            "nonnegative representatives; no exclusion above 2^P and no "
            "claim outside the box"
        ),
        "counterexample": None,
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_artifact(
    increment_abs_bound: int,
    max_start_branch: int,
    precision_bits: int,
    jobs: int,
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": scan_box(
            increment_abs_bound, max_start_branch, precision_bits, jobs
        ),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path, jobs: int) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "verifier_sha256", "audit",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["verifier_sha256"] != source_sha256():
        raise ValueError("verifier hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    bounds = data["audit"]["bounds"]
    actual = scan_box(
        int(bounds["increment_components"][1]),
        int(bounds["start_branches"][1]),
        int(bounds["precision_bits"]),
        jobs,
    )
    if data["audit"] != actual:
        raise AssertionError("artifact differs from exact recomputation")
    return {
        "artifact_sha256": advertised,
        "verifier_sha256": data["verifier_sha256"],
        "increment_words_checked": actual["increment_words_checked"],
        "positive_schedule_candidates_checked": actual[
            "positive_schedule_candidates_checked"
        ],
        "ordinary_core_lower_bound": actual[
            "certified_ordinary_core_lower_bound"
        ],
        "counterexample": None,
    }


def selftest() -> None:
    word = (2, -1, 1)
    residue, transitions, accumulated = backward_residue(3, word, 256)
    if transitions < 1 or accumulated < 256:
        raise AssertionError("precision accumulation changed")
    if residue != direct_series_residue(3, word, 256):
        raise AssertionError("backward and direct EC17 residues disagree")
    record = audit_candidate(3, word, 256)
    if record.failure_step is None:
        raise AssertionError("least EC17 representative unexpectedly survived")
    small = scan_box(2, 4, 256, 1)
    if not small["all_literal_residues_failed"]:
        raise AssertionError("small period-three sieve left an unresolved row")


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--increment-abs", type=int, default=4)
    build.add_argument("--max-start", type=int, default=16)
    build.add_argument("--precision", type=int, default=2048)
    build.add_argument("--jobs", type=int, default=1)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    verify.add_argument("--jobs", type=int, default=1)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("breakoff ether period-three sieve selftest: PASS")
    elif args.command == "build":
        artifact = build_artifact(
            args.increment_abs, args.max_start, args.precision, args.jobs
        )
        args.output.write_text(render(artifact))
        print(f"wrote {args.output}")
    else:
        print(json.dumps(
            verify_artifact(args.artifact, args.jobs),
            indent=2,
            sort_keys=True,
        ))


if __name__ == "__main__":
    main()

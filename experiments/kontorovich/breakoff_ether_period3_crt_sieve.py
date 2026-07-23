#!/usr/bin/env python3
"""Exact CRT lower bounds for period-three EC17 programs.

The normalized ether core satisfies

    2^(8*n_(t+1)+15) * u_(t+1)
      = 3^(6*n_t+11) * u_t + 17.                         (EC17)

The existing period-three sieve uses the infinite future schedule to fix
``u_(t+1)`` modulo ``2^P``.  EC17 also fixes the same successor from its
immediate past, independently of the unknown predecessor core:

    u_(t+1) = 17 * 2^(-(8*n_(t+1)+15))
              (mod 3^(6*n_t+11)).

The moduli are coprime.  CRT therefore gives one exact candidate below

    2^P * 3^(6*n_t+11).

If that representative fails the prescribed future divisions, every
positive ordinary successor core realizing the full schedule is at least
the displayed product.  This is a finite lower bound, not an existence
claim.  In particular, ``counterexample`` remains null.
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
    literal_failure,
    stays_positive,
    valid_period_three_word,
)
from breakoff_ether_periodic_theta import replay_core_schedule


SCHEMA = "collatz-breakoff-ether-period3-crt-sieve-v1"
CORE_CONSTANT = 17


@dataclass(frozen=True)
class CandidateRecord:
    increment_word: tuple[int, int, int]
    previous_branch: int
    successor_branch: int
    future_increment_word: tuple[int, int, int]
    precision_bits: int
    ternary_precision_exponent: int
    combined_modulus_bits: int
    backward_transitions: int
    accumulated_binary_precision: int
    candidate_bits: int
    leading_zero_bits: int
    failure_step: int | None
    failure_source_branch: int | None
    failure_target_branch: int | None
    failure_numerator_v2: int | None
    failure_required_v2: int | None
    candidate_hex: str


def rotate_after_first(word: Sequence[int]) -> tuple[int, int, int]:
    if len(word) != PERIOD:
        raise ValueError("period-three word required")
    return int(word[1]), int(word[2]), int(word[0])


def successor_ternary_residue(
    previous_branch: int, successor_branch: int
) -> tuple[int, int]:
    if min(previous_branch, successor_branch) < 1:
        raise ValueError("branches must be positive")
    exponent = 6 * previous_branch + 11
    modulus = 3**exponent
    residue = (
        CORE_CONSTANT
        * pow(2, -(8 * successor_branch + 15), modulus)
    ) % modulus
    if residue % 3 != 1:
        raise AssertionError("successor ternary residue lost u=1 (mod 3)")
    return residue, modulus


def coprime_crt(
    two_residue: int,
    precision_bits: int,
    three_residue: int,
    three_modulus: int,
) -> tuple[int, int]:
    if precision_bits < 1 or three_modulus < 1:
        raise ValueError("invalid CRT moduli")
    two_modulus = 1 << precision_bits
    lift = (
        (three_residue - two_residue)
        * pow(two_modulus, -1, three_modulus)
    ) % three_modulus
    residue = two_residue + two_modulus * lift
    modulus = two_modulus * three_modulus
    if not 0 <= residue < modulus:
        raise AssertionError("CRT representative is not canonical")
    if residue % two_modulus != two_residue:
        raise AssertionError("CRT representative lost binary residue")
    if residue % three_modulus != three_residue:
        raise AssertionError("CRT representative lost ternary residue")
    return residue, modulus


def audit_candidate(
    previous_branch: int, word: Sequence[int], precision_bits: int
) -> CandidateRecord:
    if not stays_positive(previous_branch, word):
        raise ValueError("invalid positive period-three schedule")
    successor_branch = previous_branch + int(word[0])
    future_word = rotate_after_first(word)
    two_residue, transitions, accumulated = backward_residue(
        successor_branch, future_word, precision_bits
    )
    three_residue, three_modulus = successor_ternary_residue(
        previous_branch, successor_branch
    )
    candidate, combined_modulus = coprime_crt(
        two_residue,
        precision_bits,
        three_residue,
        three_modulus,
    )
    if candidate < 1:
        raise AssertionError("positive EC17 CRT candidate vanished")
    failure = literal_failure(
        candidate,
        successor_branch,
        future_word,
        transitions + PERIOD + 64,
    )
    if failure is None:
        failure_fields: tuple[int | None, ...] = (None,) * 5
    else:
        failure_fields = failure
    return CandidateRecord(
        increment_word=(int(word[0]), int(word[1]), int(word[2])),
        previous_branch=previous_branch,
        successor_branch=successor_branch,
        future_increment_word=future_word,
        precision_bits=precision_bits,
        ternary_precision_exponent=6 * previous_branch + 11,
        combined_modulus_bits=combined_modulus.bit_length(),
        backward_transitions=transitions,
        accumulated_binary_precision=accumulated,
        candidate_bits=candidate.bit_length(),
        leading_zero_bits=combined_modulus.bit_length() - candidate.bit_length(),
        failure_step=failure_fields[0],
        failure_source_branch=failure_fields[1],
        failure_target_branch=failure_fields[2],
        failure_numerator_v2=failure_fields[3],
        failure_required_v2=failure_fields[4],
        candidate_hex=hex(candidate),
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
    result["future_increment_word"] = list(record.future_increment_word)
    return result


def scan_word(
    args: tuple[tuple[int, int, int], int, int]
) -> list[CandidateRecord]:
    word, max_previous_branch, precision_bits = args
    return [
        audit_candidate(previous, word, precision_bits)
        for previous in range(1, max_previous_branch + 1)
        if stays_positive(previous, word)
    ]


def scan_box(
    increment_abs_bound: int,
    max_previous_branch: int,
    precision_bits: int,
    jobs: int,
) -> dict[str, Any]:
    if min(max_previous_branch, precision_bits, jobs) < 1:
        raise ValueError("scan parameters must be positive")
    words = words_in_box(increment_abs_bound)
    tasks = [
        (word, max_previous_branch, precision_bits) for word in words
    ]
    if jobs == 1:
        groups = map(scan_word, tasks)
        executor = None
    else:
        executor = ProcessPoolExecutor(max_workers=jobs)
        groups = executor.map(scan_word, tasks, chunksize=1)
    records: list[CandidateRecord] = []
    try:
        for group in groups:
            records.extend(group)
    finally:
        if executor is not None:
            executor.shutdown()

    unresolved = [record for record in records if record.failure_step is None]
    anomalies = sorted(
        records,
        key=lambda record: (
            record.leading_zero_bits,
            -record.previous_branch,
            record.increment_word,
        ),
        reverse=True,
    )[:32]
    failure_steps = [
        record.failure_step
        for record in records
        if record.failure_step is not None
    ]
    minimum_ternary_exponent = 17
    return {
        "bounds": {
            "increment_components": [
                -increment_abs_bound, increment_abs_bound
            ],
            "previous_branches": [1, max_previous_branch],
            "binary_precision_bits": precision_bits,
        },
        "period": PERIOD,
        "increment_words_checked": len(words),
        "positive_schedule_candidates_checked": len(records),
        "record_sha256": record_digest(records),
        "all_literal_crt_representatives_failed": not unresolved,
        "unresolved": [record_dict(record) for record in unresolved],
        "failure_step_range": (
            [min(failure_steps), max(failure_steps)]
            if failure_steps else None
        ),
        "maximum_leading_zero_bits": (
            max(record.leading_zero_bits for record in records)
            if records else None
        ),
        "leading_zero_anomalies": [
            record_dict(record) for record in anomalies
        ],
        "uniform_certified_successor_core_lower_bound": (
            f"2^{precision_bits}*3^{minimum_ternary_exponent}"
            if records and not unresolved else None
        ),
        "rowwise_certified_successor_core_lower_bound": (
            "2^P*3^(6*n_previous+11)"
            if records and not unresolved else None
        ),
        "exact_theorem_used": (
            "EC17 implies u_successor = "
            "17*2^(-(8*n_successor+15)) "
            "mod 3^(6*n_previous+11); the prescribed infinite future "
            "fixes u_successor mod 2^P; CRT combines the coprime moduli"
        ),
        "lower_bound_scope": (
            "for every checked previous-branch/word pair, any positive "
            "ordinary EC17 successor core realizing that entire prescribed "
            "future schedule is at least its rowwise product modulus"
        ),
        "claim_scope": (
            "exhaustive in the stated increment/previous-branch box; exact "
            "binary future residue, exact ternary predecessor residue, exact "
            "CRT lift, and exact forward failure of the least nonnegative "
            "combined representative; no exclusion at or above the rowwise "
            "product modulus and no claim outside the box"
        ),
        "counterexample": None,
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_artifact(
    increment_abs_bound: int,
    max_previous_branch: int,
    precision_bits: int,
    jobs: int,
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_sha256": source_sha256(),
        "audit": scan_box(
            increment_abs_bound,
            max_previous_branch,
            precision_bits,
            jobs,
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
        int(bounds["previous_branches"][1]),
        int(bounds["binary_precision_bits"]),
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
        "uniform_successor_core_lower_bound": actual[
            "uniform_certified_successor_core_lower_bound"
        ],
        "counterexample": None,
    }


def selftest() -> None:
    word = (2, -1, 1)
    cores, _, _ = replay_core_schedule(3, word, 4)
    literal_residue, literal_modulus = successor_ternary_residue(3, 5)
    if cores[1] % literal_modulus != literal_residue:
        raise AssertionError("literal EC17 core missed its ternary residue")
    record = audit_candidate(3, word, 256)
    if record.successor_branch != 5:
        raise AssertionError("successor branch changed")
    if record.future_increment_word != (-1, 1, 2):
        raise AssertionError("period-three rotation changed")
    if record.ternary_precision_exponent != 29:
        raise AssertionError("ternary predecessor precision changed")
    if record.failure_step is None:
        raise AssertionError("least EC17 CRT representative unexpectedly survived")
    small = scan_box(2, 4, 256, 1)
    if not small["all_literal_crt_representatives_failed"]:
        raise AssertionError("small CRT sieve left an unresolved row")


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--increment-abs", type=int, default=4)
    build.add_argument("--max-previous", type=int, default=16)
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
        print("breakoff ether period-three CRT sieve selftest: PASS")
    elif args.command == "build":
        artifact = build_artifact(
            args.increment_abs,
            args.max_previous,
            args.precision,
            args.jobs,
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

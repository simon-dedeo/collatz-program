#!/usr/bin/env python3
"""Exact queue-macro audit for the YAH Collatz string-rewriting system.

Grouping rewrites at the left delimiter exposes a small programming machine.
One leading ternary digit is consumed, one or two binary carry sweeps rewrite
the entire remaining word, and every odd shortcut step appends one terminal
maximal trit.  This worker checks that factorization against literal YAH rule
replay and isolates the resulting nonlocal reproduction type.

It is not a seed search.  The exhaustive part is a bounded equivalence audit
for two independently implemented semantics; the displayed all-length laws
are algebraic/inductive schemas, with their finite regressions stated exactly.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah


SCHEMA = "yah_queue_macro_audit_v1"
TRITS = "012"
ASCII_TRIT = {"0": "e", "1": "f", "2": "g"}
TRIT_ASCII = {value: key for key, value in ASCII_TRIT.items()}

# Long division by two in base three.  The state is the incoming binary
# remainder.  Each transition is (quotient trit, outgoing remainder).
SWEEP_TRANSITION: dict[tuple[int, str], tuple[str, int]] = {
    (0, "0"): ("0", 0),
    (0, "1"): ("0", 1),
    (0, "2"): ("1", 0),
    (1, "0"): ("1", 1),
    (1, "1"): ("2", 0),
    (1, "2"): ("2", 1),
}

PAIR_RULE = {
    "ae": "A_f0",
    "af": "A_f1",
    "ag": "A_f2",
    "be": "A_t0",
    "bf": "A_t1",
    "bg": "A_t2",
}
BOUNDARY_RULE = {"e": "B_0", "f": "B_1", "g": "B_2"}
TERMINAL_RULE = {"a": "DT_f", "b": "DT_t"}

# Composition Q_0(Q_1(.)) on two block types produced by the comb splash.
# Both input blocks advance the same public phase modulo four.  Their outputs
# depend on the phase at entry, and the suffix is the exact two-carry deposit.
PHASE_LONG_OUTPUT = ("0210", "1112", "2022", "0001")  # input 0012
PHASE_SHORT_OUTPUT = ("02", "11", "21", "00")         # input 01
PHASE_TERMINAL = ("1", "2", "22", "")


def validate_trit_word(word: str, *, nonempty: bool = False) -> None:
    if not isinstance(word, str) or any(symbol not in TRITS for symbol in word):
        raise ValueError(f"not a ternary word: {word!r}")
    if nonempty and not word:
        raise ValueError("macro input must be nonempty")


def ascii_canonical(word: str) -> str:
    validate_trit_word(word)
    return "c" + "".join(ASCII_TRIT[symbol] for symbol in word) + "d"


def trit_canonical(word: str) -> str:
    if not yah.is_canonical(word):
        raise ValueError(f"not a canonical YAH word: {word!r}")
    if any(symbol not in TRIT_ASCII for symbol in word[1:-1]):
        raise ValueError("canonical word contains binary digits")
    return "".join(TRIT_ASCII[symbol] for symbol in word[1:-1])


def canonical_value(word: str) -> int:
    """Value of ``/ word .`` with the delimiter's implicit leading one."""

    validate_trit_word(word)
    value = 1
    for symbol in word:
        value = 3 * value + int(symbol)
    return value


def v2_positive(value: int) -> int:
    if value <= 0:
        raise ValueError("2-adic valuation requires a positive integer")
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def alternating_checksum_mod4(word: str) -> int:
    """The canonical value modulo four, visibly distributed over the word."""

    validate_trit_word(word)
    length = len(word)
    total = -1 if length % 2 else 1
    for index, symbol in enumerate(word):
        exponent = length - index - 1
        sign = -1 if exponent % 2 else 1
        total += sign * int(symbol)
    return total % 4


def carry_sweep(start_carry: int, word: str) -> tuple[str, int]:
    """Run one two-state quotient sweep and apply the terminal odd deposit.

    A final carry zero emits nothing.  A final carry one is exactly an odd
    shortcut step and appends one maximal trit ``2``.
    """

    validate_trit_word(word)
    if start_carry not in {0, 1}:
        raise ValueError("carry must be zero or one")
    carry = start_carry
    output: list[str] = []
    for symbol in word:
        quotient, carry = SWEEP_TRANSITION[carry, symbol]
        output.append(quotient)
    if carry:
        output.append("2")
    return "".join(output), carry


def macro_factorized(word: str) -> tuple[str, list[int], list[int]]:
    """Consume one head trit using the exact queue-transducer factorization.

    The three head opcodes compile to incoming carry sequences

        0 -> [1],     1 -> [0,0],     2 -> [1,0].

    The returned carries are the terminal parity bits of those sweeps.
    """

    validate_trit_word(word, nonempty=True)
    head, tail = word[0], word[1:]
    starts = {"0": [1], "1": [0, 0], "2": [1, 0]}[head]
    carries: list[int] = []
    output = tail
    for start in starts:
        output, terminal = carry_sweep(start, output)
        carries.append(terminal)
    return output, starts, carries


def push_rightmost_binary(word: str) -> tuple[str, list[dict[str, Any]], int]:
    """Literally move the rightmost binary digit to ``.`` and fire it."""

    binary_positions = [index for index, symbol in enumerate(word) if symbol in "ab"]
    if not binary_positions:
        raise ValueError("no binary digit to push")
    position = binary_positions[-1]
    steps: list[dict[str, Any]] = []
    while position + 1 < len(word) and word[position + 1] in "efg":
        pair = word[position : position + 2]
        rule_name = PAIR_RULE[pair]
        steps.append({"rule": rule_name, "position": position})
        word = yah.apply_step(word, rule_name, position)
        position += 1
    if position + 1 >= len(word) or word[position + 1] != "d":
        raise AssertionError("binary sweep did not reach the terminal marker")
    terminal_symbol = word[position]
    odd = int(terminal_symbol == "b")
    rule_name = TERMINAL_RULE[terminal_symbol]
    steps.append({"rule": rule_name, "position": position})
    word = yah.apply_step(word, rule_name, position)
    return word, steps, odd


def literal_macro_trace(word: str) -> tuple[str, list[dict[str, Any]], list[int]]:
    """Execute the same head macro by literal applications of the 11 rules."""

    validate_trit_word(word, nonempty=True)
    state = ascii_canonical(word)
    boundary = BOUNDARY_RULE[state[1]]
    steps: list[dict[str, Any]] = [{"rule": boundary, "position": 0}]
    state = yah.apply_step(state, boundary, 0)
    expected_sweeps = 1 if word[0] == "0" else 2
    carries: list[int] = []
    for _ in range(expected_sweeps):
        state, sweep_steps, odd = push_rightmost_binary(state)
        steps.extend(sweep_steps)
        carries.append(odd)
    if not yah.is_canonical(state) or any(symbol in "ab" for symbol in state):
        raise AssertionError("head macro failed to return to a pure ternary word")
    endpoint = trit_canonical(state)
    replayed, _ = yah.replay_trace(ascii_canonical(word), steps)
    if replayed != state:
        raise AssertionError("literal macro trace failed independent replay")
    return endpoint, steps, carries


def macro_record(word: str) -> dict[str, Any]:
    endpoint, starts, carries = macro_factorized(word)
    literal_endpoint, steps, literal_carries = literal_macro_trace(word)
    if (endpoint, carries) != (literal_endpoint, literal_carries):
        raise AssertionError("queue factorization disagrees with literal rules")

    start_value = canonical_value(word)
    value = start_value
    for carry in carries:
        if carry != value % 2:
            raise AssertionError("terminal carry is not the shortcut parity")
        value = yah.shortcut_collatz(value)
    if value != canonical_value(endpoint):
        raise AssertionError("macro value does not match shortcut Collatz")

    delta = len(endpoint) - len(word)
    if delta != sum(carries) - 1:
        raise AssertionError("queue length charge failed")
    if alternating_checksum_mod4(word) != start_value % 4:
        raise AssertionError("alternating checksum failed")

    if word[0] == "0":
        expected_delta = 0 if start_value % 2 else -1
    else:
        expected_delta = {0: -1, 1: 0, 2: 0, 3: 1}[start_value % 4]
    if delta != expected_delta:
        raise AssertionError("nonlocal reproduction type failed")

    start_defect = start_value + 1
    endpoint_defect = value + 1
    start_v2 = v2_positive(start_defect)
    endpoint_v2 = v2_positive(endpoint_defect)
    start_battery = 2 * len(word) + start_v2
    endpoint_battery = 2 * len(endpoint) + endpoint_v2
    battery_delta = endpoint_battery - start_battery
    residue = start_value % 4
    if word[0] == "0":
        expected_battery_delta = (
            v2_positive(start_defect + 1) - 3 if residue % 2 == 0 else -1
        )
    elif residue == 0:
        expected_battery_delta = v2_positive(start_defect + 3) - 4
    elif residue == 1:
        expected_battery_delta = v2_positive(3 * start_defect + 2) - 3
    elif residue == 2:
        expected_battery_delta = v2_positive(start_defect + 1) - 2
    else:
        expected_battery_delta = 0
        if 4 * endpoint_defect != 9 * start_defect:
            raise AssertionError("reproducing macro failed its 9/4 defect law")
    if battery_delta != expected_battery_delta:
        raise AssertionError("dyadic recharge battery law failed")

    return {
        "start": word,
        "endpoint": endpoint,
        "head": word[0],
        "incoming_carries": starts,
        "terminal_carries": carries,
        "dynamic_steps": len(carries),
        "literal_rewrite_steps": len(steps),
        "length_delta": delta,
        "value_mod_4": start_value % 4,
        "start_value": start_value,
        "endpoint_value": value,
        "start_v2_value_plus_one": start_v2,
        "endpoint_v2_value_plus_one": endpoint_v2,
        "start_dyadic_battery": start_battery,
        "endpoint_dyadic_battery": endpoint_battery,
        "dyadic_battery_delta": battery_delta,
        "trace_sha256": yah.sha256_bytes(yah.canonical_json(steps)),
    }


def exhaustive_macro_audit(max_length: int) -> dict[str, Any]:
    if max_length < 1:
        raise ValueError("maximum macro length must be positive")
    total = 0
    by_length: dict[str, Any] = {}
    samples: dict[str, Any] = {}
    for length in range(1, max_length + 1):
        deltas: Counter[int] = Counter()
        battery_deltas: Counter[int] = Counter()
        heads: Counter[str] = Counter()
        residues: Counter[int] = Counter()
        reproduced = 0
        for symbols in itertools.product(TRITS, repeat=length):
            word = "".join(symbols)
            record = macro_record(word)
            deltas[record["length_delta"]] += 1
            battery_deltas[record["dyadic_battery_delta"]] += 1
            heads[record["head"]] += 1
            residues[record["value_mod_4"]] += 1
            reproduced += int(record["length_delta"] == 1)
            total += 1
            if word in {"0", "1", "2", "0022", "1122"}:
                samples[word] = record
        expected_deltas = {
            -1: 3 ** (length - 1),
            0: (3**length + 1) // 2,
            1: (3 ** (length - 1) - 1) // 2,
        }
        if deltas != Counter(expected_deltas):
            raise AssertionError("closed macro-charge census failed")
        by_length[str(length)] = {
            "words": 3**length,
            "head_counts": dict(sorted(heads.items())),
            "value_mod_4_counts": {
                str(key): value for key, value in sorted(residues.items())
            },
            "length_delta_counts": {
                str(key): value for key, value in sorted(deltas.items())
            },
            "dyadic_battery_delta_counts": {
                str(key): value for key, value in sorted(battery_deltas.items())
            },
            "dyadic_recharge_events": sum(
                value for key, value in battery_deltas.items() if key > 0
            ),
            "reproducing_macros": reproduced,
        }
    return {
        "max_trit_length": max_length,
        "words_checked": total,
        "by_length": by_length,
        "samples": samples,
        "all_length_factorization": [
            "M(0v)=Q_1(v)",
            "M(1v)=Q_0(Q_0(v))",
            "M(2v)=Q_0(Q_1(v))",
        ],
        "length_charge": "len(M(w))-len(w)=number_of_odd_sweeps-1",
        "closed_charge_census": (
            "at trit length m>=1: shrink=3^(m-1), "
            "neutral=(3^m+1)/2, grow=(3^(m-1)-1)/2"
        ),
        "mean_length_delta": (
            "under the uniform length-m word measure: "
            "-1/6 - 1/(2*3^m)"
        ),
        "reproduction_type": (
            "head 0 never grows; head 1 or 2 grows by one exactly when "
            "canonical_value(w)=3 (mod 4)"
        ),
        "dyadic_battery": (
            "B(w)=2*len(w)+v2(canonical_value(w)+1); every growing macro "
            "has B(M(w))=B(w), so fresh space spends two units of v2 charge"
        ),
        "recharge_table": [
            "head 0, N mod 2=0: deltaB=v2((N+1)+1)-3",
            "head 0, N mod 2=1: deltaB=-1",
            "head 1/2, N mod 4=0: deltaB=v2((N+1)+3)-4",
            "head 1/2, N mod 4=1: deltaB=v2(3*(N+1)+2)-3",
            "head 1/2, N mod 4=2: deltaB=v2((N+1)+1)-2",
            "head 1/2, N mod 4=3: deltaB=0 and 4*(N'+1)=9*(N+1)",
        ],
        "checksum": (
            "canonical_value modulo 4 is the alternating signed trit sum, "
            "including the implicit leading one"
        ),
        "scope": (
            "factorization, charge, and checksum are all-length induction "
            "schemas; literal replay is exhaustive only through the stated bound"
        ),
    }


def ones_splash_formula(one_count: int, max_count: int) -> str:
    if one_count < 1 or max_count < 0:
        raise ValueError("need one_count>=1 and max_count>=0")
    if one_count % 2 == 0:
        half = one_count // 2
        return "01" * (half - 1) + "0" + "1" * (max_count + 1)
    half = (one_count - 1) // 2
    return "01" * half + "02" * ((max_count + 1) // 2)


def comb_splash_formula(pair01_count: int, pair02_count: int) -> str:
    if pair01_count < 0 or pair02_count < 0 or pair01_count + pair02_count < 1:
        raise ValueError("comb must be nonempty")
    if pair01_count == 0:
        return "2" + "12" * (pair02_count - 1) + "2"
    if pair01_count % 2 == 1:
        half = (pair01_count - 1) // 2
        return "2" + "0012" * half + "01" * pair02_count
    half = (pair01_count - 2) // 2
    return "2" + "0012" * half + "00" + "12" * pair02_count + "2"


def phase_packet_formula(long_count: int, short_count: int) -> str:
    """Compile ``M(2 (0012)^s (01)^q)`` by its four public phases."""

    if long_count < 0 or short_count < 0:
        raise ValueError("block counts must be nonnegative")
    phase = 0
    output: list[str] = []
    for _ in range(long_count):
        output.append(PHASE_LONG_OUTPUT[phase])
        phase = (phase + 1) % 4
    for _ in range(short_count):
        output.append(PHASE_SHORT_OUTPUT[phase])
        phase = (phase + 1) % 4
    output.append(PHASE_TERMINAL[phase])
    return "".join(output)


def structured_opcode_audit(max_coordinate: int) -> dict[str, Any]:
    if max_coordinate < 1:
        raise ValueError("maximum coordinate must be positive")
    transfer_cases = 0
    ones_cases = 0
    comb_cases = 0
    phase_packet_cases = 0
    literal_steps = 0
    samples: dict[str, Any] = {}

    for zero_count in range(1, max_coordinate + 1):
        for max_count in range(max_coordinate + 1):
            word = "0" * zero_count + "2" * max_count
            expected = "1" * (zero_count - 1) + "2" * (max_count + 1)
            record = macro_record(word)
            if record["endpoint"] != expected:
                raise AssertionError("zero reservoir transfer formula failed")
            transfer_cases += 1
            literal_steps += record["literal_rewrite_steps"]
            if (zero_count, max_count) in {(1, 0), (2, 2), (max_coordinate, max_coordinate)}:
                samples[f"transfer:{zero_count},{max_count}"] = record

    for one_count in range(1, max_coordinate + 1):
        for max_count in range(max_coordinate + 1):
            word = "1" * one_count + "2" * max_count
            expected = ones_splash_formula(one_count, max_count)
            record = macro_record(word)
            if record["endpoint"] != expected:
                raise AssertionError("one-run comb splash formula failed")
            ones_cases += 1
            literal_steps += record["literal_rewrite_steps"]
            if (one_count, max_count) in {(1, 2), (2, 2), (max_coordinate, max_coordinate)}:
                samples[f"ones:{one_count},{max_count}"] = record

    for pair01_count in range(max_coordinate + 1):
        for pair02_count in range(max_coordinate + 1):
            if pair01_count + pair02_count == 0:
                continue
            word = "01" * pair01_count + "02" * pair02_count
            expected = comb_splash_formula(pair01_count, pair02_count)
            record = macro_record(word)
            if record["endpoint"] != expected:
                raise AssertionError("distributed-comb splash formula failed")
            comb_cases += 1
            literal_steps += record["literal_rewrite_steps"]
            if (pair01_count, pair02_count) in {
                (0, 1),
                (1, 1),
                (2, 2),
                (max_coordinate, max_coordinate),
            }:
                samples[f"comb:{pair01_count},{pair02_count}"] = record

    phase_counts: Counter[int] = Counter()
    for long_count in range(max_coordinate + 1):
        for short_count in range(max_coordinate + 1):
            word = "2" + "0012" * long_count + "01" * short_count
            expected = phase_packet_formula(long_count, short_count)
            record = macro_record(word)
            if record["endpoint"] != expected:
                raise AssertionError("four-phase packet formula failed")
            phase = (long_count + short_count) % 4
            expected_delta = {0: 0, 1: 0, 2: 1, 3: -1}[phase]
            if record["length_delta"] != expected_delta:
                raise AssertionError("four-phase packet charge failed")
            phase_counts[phase] += 1
            phase_packet_cases += 1
            literal_steps += record["literal_rewrite_steps"]
            if (long_count, short_count) in {
                (0, 0),
                (0, 2),
                (2, 0),
                (max_coordinate, max_coordinate),
            }:
                samples[f"phase:{long_count},{short_count}"] = record

    return {
        "max_coordinate": max_coordinate,
        "zero_reservoir_transfer_cases": transfer_cases,
        "one_run_comb_splash_cases": ones_cases,
        "distributed_comb_splash_cases": comb_cases,
        "four_phase_packet_cases": phase_packet_cases,
        "four_phase_counts": {
            str(key): value for key, value in sorted(phase_counts.items())
        },
        "cases_checked": (
            transfer_cases + ones_cases + comb_cases + phase_packet_cases
        ),
        "literal_rewrite_steps": literal_steps,
        "formulae": [
            "M(0^k 2^n)=1^(k-1) 2^(n+1)",
            "M(1^(2q) 2^n)=(01)^(q-1) 0 1^(n+1)",
            "M(1^(2q+1) 2^n)=(01)^q (02)^ceil(n/2)",
            "M((01)^(2s+1) (02)^q)=2 (0012)^s (01)^q",
            "M((01)^(2s+2) (02)^q)=2 (0012)^s 00 (12)^q 2",
            "M((02)^q)=2 (12)^(q-1) 2",
            (
                "M(2 (0012)^s (01)^q) is the phase-mod-4 block compiler; "
                "it grows exactly when s+q=2 (mod 4)"
            ),
        ],
        "interpretation": (
            "the original contiguous zero reservoir is converted into a "
            "distributed alternating comb and then a four-phase packet; "
            "the reproducing phase is a nonlocal block-count checksum"
        ),
        "four_phase_compiler": {
            "phase_long_output_for_0012": list(PHASE_LONG_OUTPUT),
            "phase_short_output_for_01": list(PHASE_SHORT_OUTPUT),
            "terminal_output": list(PHASE_TERMINAL),
            "phase_update_per_block": "+1 mod 4",
            "length_delta_by_final_phase": {"0": 0, "1": 0, "2": 1, "3": -1},
        },
        "samples": samples,
        "scope": (
            "every bounded instance is literally replayed; the displayed "
            "families are research-side transducer inductions"
        ),
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def dependency_sha256() -> str:
    return yah.sha256_bytes(Path(yah.__file__).read_bytes())


def build_artifact(max_length: int, max_coordinate: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "yah_worker_sha256": dependency_sha256(),
        "upstream": {
            "paper": yah.PAPER_URL,
            "authors_repository_commit": yah.UPSTREAM_COMMIT,
        },
        "rule_table_sha256": yah.sha256_bytes(yah.canonical_json(yah.rule_table())),
        "queue_transducer": {
            f"{carry},{trit}": [output, next_carry]
            for (carry, trit), (output, next_carry) in sorted(SWEEP_TRANSITION.items())
        },
        "macro_exhaustion": exhaustive_macro_audit(max_length),
        "structured_opcodes": structured_opcode_audit(max_coordinate),
        "closure_status": {
            "candidate": None,
            "missing_instruction": (
                "a typed macro chain must repeatedly restore a nonzero head "
                "and global checksum 3 mod 4 while preserving positive net charge"
            ),
        },
    }
    payload = dict(data)
    data["artifact_sha256"] = yah.sha256_bytes(yah.canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema",
        "generated_at_utc",
        "worker_sha256",
        "yah_worker_sha256",
        "upstream",
        "rule_table_sha256",
        "queue_transducer",
        "macro_exhaustion",
        "structured_opcodes",
        "closure_status",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["yah_worker_sha256"] != dependency_sha256():
        raise ValueError("YAH dependency hash mismatch")
    if data["rule_table_sha256"] != yah.sha256_bytes(
        yah.canonical_json(yah.rule_table())
    ):
        raise ValueError("rule table hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    max_length = data["macro_exhaustion"]["max_trit_length"]
    if data["macro_exhaustion"] != exhaustive_macro_audit(max_length):
        raise ValueError("macro exhaustion replay mismatch")
    max_coordinate = data["structured_opcodes"]["max_coordinate"]
    if data["structured_opcodes"] != structured_opcode_audit(max_coordinate):
        raise ValueError("structured opcode replay mismatch")
    if data["closure_status"]["candidate"] is not None:
        raise ValueError("unexpected advertised closure candidate")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "macro_words": data["macro_exhaustion"]["words_checked"],
        "structured_cases": data["structured_opcodes"]["cases_checked"],
        "candidate": None,
    }


def selftest() -> None:
    if carry_sweep(1, "0022") != ("11222", 1):
        raise AssertionError("carry sweep regression failed")
    for word in ("0", "1", "2", "0022", "1122", "01010202"):
        macro_record(word)
    for one_count in range(1, 9):
        for max_count in range(9):
            endpoint, _, _ = macro_factorized("1" * one_count + "2" * max_count)
            if endpoint != ones_splash_formula(one_count, max_count):
                raise AssertionError("one-run formula selftest failed")
    for p in range(7):
        for q in range(7):
            if p + q:
                endpoint, _, _ = macro_factorized("01" * p + "02" * q)
                if endpoint != comb_splash_formula(p, q):
                    raise AssertionError("comb formula selftest failed")
    for s in range(7):
        for q in range(7):
            endpoint, _, _ = macro_factorized("2" + "0012" * s + "01" * q)
            if endpoint != phase_packet_formula(s, q):
                raise AssertionError("phase packet formula selftest failed")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-length", type=int, default=10)
    build.add_argument("--max-coordinate", type=int, default=64)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "selftest":
        selftest()
        print("selftest: ok")
        return 0
    if args.command == "build":
        selftest()
        artifact = build_artifact(args.max_length, args.max_coordinate)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())

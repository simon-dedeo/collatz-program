#!/usr/bin/env python3
"""Exact first-bit decoder for the YAH recharge-amplifier lift register.

At the smallest nontrivial amplifier level K=5, every recharge address is

    q = 17 + 128*t.

Four complete queue macros map the packet ``2(01)^q`` to an exact lasso word
``U V^t Z``.  The repeated block has length 256, the order of three modulo
``2^10``.  A fifth macro reads the low bit of ``t``: the lasso splits into two
explicit successor lassos with 512-trit repeated blocks.

Arithmetically the four-macro endpoint is ``3^7*R(t)-1``.  The normalized
register satisfies ``R(t) mod 2 = t mod 2``, and the next macro implements

    R even:  3^7 R - 1 -> 3^8 (R/2) - 1,
    R odd:   3^7 R - 1 -> (3^7 R - 1)/2.

Thus zero pops one binary register bit and extends the clean ternary
reservoir; one triggers a chart-changing collision.  This is a decoder
instruction, not a regenerative loop or counterexample.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah
import yah_queue_macro as queue


SCHEMA = "yah_lift_decoder_v1"
BASE_Q = 17
Q_STRIDE = 128
FORCED_CHARGE = 5
ENDPOINT_RESERVOIR = 7


@dataclass(frozen=True)
class Lasso:
    """The family ``prefix + block^t + suffix`` for natural ``t``."""

    prefix: str
    block: str
    suffix: str

    def word(self, parameter: int) -> str:
        if parameter < 0:
            raise ValueError("lasso parameter must be nonnegative")
        return self.prefix + self.block * parameter + self.suffix

    def record(self) -> dict[str, Any]:
        return {
            "prefix": self.prefix,
            "block": self.block,
            "suffix": self.suffix,
            "prefix_length": len(self.prefix),
            "block_length": len(self.block),
            "suffix_length": len(self.suffix),
            "prefix_sha256": yah.sha256_bytes(self.prefix.encode()),
            "block_sha256": yah.sha256_bytes(self.block.encode()),
            "suffix_sha256": yah.sha256_bytes(self.suffix.encode()),
        }


def open_sweep(start_carry: int, word: str) -> tuple[str, int]:
    """Run the quotient transducer without applying its terminal deposit."""

    queue.validate_trit_word(word)
    if start_carry not in {0, 1}:
        raise ValueError("carry must be zero or one")
    carry = start_carry
    output: list[str] = []
    for trit in word:
        quotient, carry = queue.SWEEP_TRANSITION[carry, trit]
        output.append(quotient)
    return "".join(output), carry


def fixed_sweep(lasso: Lasso, start_carry: int) -> Lasso:
    """Sweep a lasso whose repeated block fixes the entering carry.

    Checking this one two-state transition is a finite certificate for every
    repetition count, not a sample-based inference.
    """

    prefix, carry = open_sweep(start_carry, lasso.prefix)
    block, next_carry = open_sweep(carry, lasso.block)
    if next_carry != carry:
        raise ValueError("repeated block does not fix the sweep carry")
    suffix, terminal_carry = open_sweep(carry, lasso.suffix)
    if terminal_carry:
        suffix += "2"
    return Lasso(prefix, block, suffix)


def fixed_macro(lasso: Lasso) -> Lasso:
    """Apply one whole queue macro when every sweep is lasso-preserving."""

    if not lasso.prefix:
        raise ValueError("macro head must lie in the fixed prefix")
    head = lasso.prefix[0]
    current = Lasso(lasso.prefix[1:], lasso.block, lasso.suffix)
    starts = {"0": (1,), "1": (0, 0), "2": (1, 0)}[head]
    for start in starts:
        current = fixed_sweep(current, start)
    return current


def split_flipping_sweep(
    lasso: Lasso, start_carry: int
) -> tuple[Lasso, Lasso]:
    """Split ``t`` into ``2s`` and ``2s+1`` when the block flips carry."""

    prefix, carry = open_sweep(start_carry, lasso.prefix)
    first_block, flipped = open_sweep(carry, lasso.block)
    second_block, returned = open_sweep(flipped, lasso.block)
    if flipped == carry or returned != carry:
        raise ValueError("repeated block is not a two-cycle on carry states")

    even_suffix, even_terminal = open_sweep(carry, lasso.suffix)
    if even_terminal:
        even_suffix += "2"
    odd_suffix, odd_terminal = open_sweep(flipped, lasso.suffix)
    if odd_terminal:
        odd_suffix += "2"

    even = Lasso(prefix, first_block + second_block, even_suffix)
    odd = Lasso(prefix + first_block, second_block + first_block, odd_suffix)
    return even, odd


def initial_packet_lasso() -> Lasso:
    return Lasso("2" + "01" * BASE_Q, "01" * Q_STRIDE, "")


def amplified_lasso() -> Lasso:
    lasso = initial_packet_lasso()
    for _ in range(4):
        lasso = fixed_macro(lasso)
    if (len(lasso.prefix), len(lasso.block), len(lasso.suffix)) != (31, 256, 6):
        raise AssertionError("unexpected amplified lasso shape")
    return lasso


def decoder_lassos() -> tuple[Lasso, Lasso]:
    amplified = amplified_lasso()
    if not amplified.prefix or amplified.prefix[0] != "0":
        raise AssertionError("decoder macro is not the zero-head opcode")
    tail = Lasso(amplified.prefix[1:], amplified.block, amplified.suffix)
    even, odd = split_flipping_sweep(tail, 1)
    if len(even.block) != 512 or len(odd.block) != 512:
        raise AssertionError("bit branches have the wrong stride")
    return even, odd


def register_value(parameter: int) -> int:
    """The exact prefix defect after stripping the seven-trit reservoir."""

    if parameter < 0:
        raise ValueError("register parameter must be nonnegative")
    q = BASE_Q + Q_STRIDE * parameter
    numerator = 41 * pow(9, q) + 15
    denominator = 3 * (1 << (FORCED_CHARGE + 5))
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise AssertionError("recharge address did not produce an integer register")
    return quotient


def exact_trace(parameter: int) -> dict[str, Any]:
    if parameter < 0:
        raise ValueError("trace parameter must be nonnegative")
    q = BASE_Q + Q_STRIDE * parameter
    word = "2" + "01" * q
    start_length = len(word)
    for _ in range(4):
        word, _, _ = queue.macro_factorized(word)

    amplified = amplified_lasso()
    if word != amplified.word(parameter):
        raise AssertionError("four-macro lasso identity failed")
    register = register_value(parameter)
    defect = queue.canonical_value(word) + 1
    if defect != 3**ENDPOINT_RESERVOIR * register:
        raise AssertionError("amplified word does not decode to its register")
    if len(word) - len(word.rstrip("2")) != ENDPOINT_RESERVOIR:
        raise AssertionError("amplified word has the wrong clean reservoir")
    if register % 2 != parameter % 2:
        raise AssertionError("lift parity is not the register opcode bit")

    endpoint, starts, carries = queue.macro_factorized(word)
    if starts != [1]:
        raise AssertionError("decoder is not a one-sweep zero-head macro")
    endpoint_defect = queue.canonical_value(endpoint) + 1
    if register % 2 == 0:
        expected_defect = 3 ** (ENDPOINT_RESERVOIR + 1) * (register // 2)
        expected_lasso = decoder_lassos()[0].word(parameter // 2)
        branch = "zero"
        expected_delta = 0
        expected_carries = [1]
        trailing_twos = ENDPOINT_RESERVOIR + 1
    else:
        expected_defect = (3**ENDPOINT_RESERVOIR * register + 1) // 2
        expected_lasso = decoder_lassos()[1].word(parameter // 2)
        branch = "one"
        expected_delta = -1
        expected_carries = [0]
        trailing_twos = 0
    if endpoint != expected_lasso:
        raise AssertionError("parity-branch lasso identity failed")
    if endpoint_defect != expected_defect:
        raise AssertionError("parity-branch arithmetic opcode failed")
    if carries != expected_carries:
        raise AssertionError("parity bit disagrees with terminal carry")
    if len(endpoint) - len(word) != expected_delta:
        raise AssertionError("parity branch has the wrong space charge")
    if len(endpoint) - len(endpoint.rstrip("2")) != trailing_twos:
        raise AssertionError("parity branch has the wrong reservoir output")

    return {
        "parameter_t": parameter,
        "packet_q": q,
        "branch": branch,
        "register_parity": register % 2,
        "packet_length": start_length,
        "amplified_length": len(word),
        "decoder_endpoint_length": len(endpoint),
        "decoder_length_delta": len(endpoint) - len(word),
        "decoder_terminal_carry": carries[0],
        "endpoint_trailing_twos": trailing_twos,
        "amplified_sha256": yah.sha256_bytes(word.encode()),
        "decoder_endpoint_sha256": yah.sha256_bytes(endpoint.encode()),
    }


def build_audit(max_parameter: int) -> dict[str, Any]:
    if max_parameter < 1:
        raise ValueError("maximum parameter must be positive")
    initial = initial_packet_lasso()
    amplified = amplified_lasso()
    even, odd = decoder_lassos()
    traces = [exact_trace(parameter) for parameter in range(max_parameter + 1)]
    branch_counts = {
        "zero": sum(trace["branch"] == "zero" for trace in traces),
        "one": sum(trace["branch"] == "one" for trace in traces),
    }
    order = next(exponent for exponent in range(1, 257) if pow(3, exponent, 1024) == 1)
    if order != 256:
        raise AssertionError("unexpected multiplicative order modulo 2^10")
    return {
        "max_parameter": max_parameter,
        "parameters_checked": max_parameter + 1,
        "initial_packet_lasso": initial.record(),
        "four_macro_amplified_lasso": amplified.record(),
        "fifth_macro_zero_branch_lasso": even.record(),
        "fifth_macro_one_branch_lasso": odd.record(),
        "branch_counts": branch_counts,
        "order_of_3_mod_2_pow_10": order,
        "traces": traces,
        "all_parameter_certificate": {
            "address": "q=17+128*t",
            "amplified_word": "U*V^t*Z with lengths 31,256,6",
            "amplified_defect": "D=3^7*R(t)",
            "register": "R(t)=(41*9^(17+128*t)+15)/(3*2^10)",
            "register_bit": "R(t) mod 2 = t mod 2",
            "zero_branch": "3^7*(2r)-1 -> 3^8*r-1",
            "one_branch": "3^7*(2r+1)-1 -> (3^7*(2r+1)-1)/2",
            "finite_state_scope": (
                "the all-t lasso identities reduce to fixed/flipping carry "
                "transitions of one explicit two-state quotient block"
            ),
        },
        "closure_status": {
            "counterexample": None,
            "achieved_instruction": (
                "an exact LSB-first register read: zero extends the reservoir "
                "and shifts the register; one performs a chart-changing collision"
            ),
            "missing_instruction": (
                "the one branch must restore a recharge packet and write a "
                "new unbounded register instead of eventually draining"
            ),
        },
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def build_artifact(max_parameter: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "queue_worker_sha256": yah.sha256_bytes(Path(queue.__file__).read_bytes()),
        "audit": build_audit(max_parameter),
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
        "queue_worker_sha256",
        "audit",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["queue_worker_sha256"] != yah.sha256_bytes(
        Path(queue.__file__).read_bytes()
    ):
        raise ValueError("queue worker hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    maximum = data["audit"]["max_parameter"]
    if data["audit"] != build_audit(maximum):
        raise ValueError("decoder audit replay mismatch")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "parameters_checked": data["audit"]["parameters_checked"],
        "zero_branches": data["audit"]["branch_counts"]["zero"],
        "one_branches": data["audit"]["branch_counts"]["one"],
        "counterexample": None,
    }


def selftest() -> None:
    initial = initial_packet_lasso()
    if initial.word(0) != "2" + "01" * 17:
        raise AssertionError("initial lasso selftest failed")
    amplified = amplified_lasso()
    word = initial.word(0)
    for _ in range(4):
        word, _, _ = queue.macro_factorized(word)
    if amplified.word(0) != word:
        raise AssertionError("amplified lasso selftest failed")
    exact_trace(0)
    exact_trace(1)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-parameter", type=int, default=64)
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
        artifact = build_artifact(args.max_parameter)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Exact restorative bit-one opcode in the YAH lift-register decoder.

The first lift decoder sends odd ``t=2s+1`` into a chart-changing collision.
On the further cylinder

    s = 45 + 128*u,   equivalently t = 91 + 256*u,

the very next head-one macro is a neutral recharge of depth at least five.
Three safe queue macros spend that charge and return to a head-zero word with
seven trailing maximal trits.  Relative to the incoming decoder state the
five-macro instruction gains one cell.

If ``R`` is the incoming stripped register, the returned register is

    R' = (3^6*R + 1)/2^8.

It is again a 2-adic isometry in ``u`` and has parity ``u+1``.  This is a
genuine register-writing recharge instruction, but not yet closure: the
returned lasso block is a new 65,536-trit type, and no finite recurrent type
cycle or infinite ordinary register orbit is supplied.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah
import yah_lift_decoder as decoder
import yah_queue_macro as queue


SCHEMA = "yah_restorative_decoder_v1"
T_BASE = 91
T_STRIDE = 256
S_BASE = 45
S_STRIDE = 128
RETURN_RESERVOIR = 7


def restrict_lasso(
    lasso: decoder.Lasso, base: int, stride: int
) -> decoder.Lasso:
    if base < 0 or stride < 1:
        raise ValueError("invalid lasso restriction")
    return decoder.Lasso(
        lasso.prefix + lasso.block * base,
        lasso.block * stride,
        lasso.suffix,
    )


def restorative_lassos() -> dict[str, decoder.Lasso]:
    """Generate every all-parameter word type in the restorative opcode."""

    amplified = restrict_lasso(decoder.amplified_lasso(), T_BASE, T_STRIDE)
    odd_chart = restrict_lasso(decoder.decoder_lassos()[1], S_BASE, S_STRIDE)
    if amplified.word(0) == odd_chart.word(0):
        raise AssertionError("bit collision must change the word chart")

    stages: dict[str, decoder.Lasso] = {
        "incoming_decoder": amplified,
        "after_bit_one": odd_chart,
    }
    current = odd_chart
    expected_heads = ("1", "0", "2", "1")
    for name, expected_head in zip(
        ("after_recharge", "after_safe_1", "after_safe_3", "returned_decoder"),
        expected_heads,
        strict=True,
    ):
        if not current.prefix or current.prefix[0] != expected_head:
            raise AssertionError("restorative opcode has the wrong head schedule")
        current = decoder.fixed_macro(current)
        stages[name] = current

    expected_shapes = {
        "incoming_decoder": (23327, 65536, 6),
        "after_bit_one": (23326, 65536, 6),
        "after_recharge": (23325, 65536, 7),
        "after_safe_1": (23324, 65536, 8),
        "after_safe_3": (23323, 65536, 10),
        "returned_decoder": (23322, 65536, 12),
    }
    for name, lasso in stages.items():
        shape = (len(lasso.prefix), len(lasso.block), len(lasso.suffix))
        if shape != expected_shapes[name]:
            raise AssertionError(f"unexpected restorative lasso shape at {name}")
    if stages["returned_decoder"].prefix[0] != "0":
        raise AssertionError("restorative opcode did not return to head zero")
    return stages


def incoming_register(parameter: int) -> int:
    if parameter < 0:
        raise ValueError("parameter must be nonnegative")
    return decoder.register_value(T_BASE + T_STRIDE * parameter)


def returned_register(parameter: int) -> int:
    register = incoming_register(parameter)
    numerator = 3**6 * register + 1
    quotient, remainder = divmod(numerator, 1 << 8)
    if remainder:
        raise AssertionError("bit-one cylinder missed the restorative address")
    return quotient


def v2_nonzero(value: int) -> int:
    if value == 0:
        raise ValueError("valuation difference must be nonzero")
    return (abs(value) & -abs(value)).bit_length() - 1


def exact_trace(parameter: int) -> dict[str, Any]:
    if parameter < 0:
        raise ValueError("trace parameter must be nonnegative")
    stages = restorative_lassos()
    t = T_BASE + T_STRIDE * parameter
    q = decoder.BASE_Q + decoder.Q_STRIDE * t
    word = "2" + "01" * q
    for _ in range(4):
        word, _, _ = queue.macro_factorized(word)
    if word != stages["incoming_decoder"].word(parameter):
        raise AssertionError("incoming decoder lasso failed")
    incoming_word = word
    incoming_length = len(word)
    register = incoming_register(parameter)
    if queue.canonical_value(word) + 1 != 3**7 * register:
        raise AssertionError("incoming register semantics failed")
    if register % 2 != 1:
        raise AssertionError("restorative source did not take the bit-one branch")

    names = (
        "after_bit_one",
        "after_recharge",
        "after_safe_1",
        "after_safe_3",
        "returned_decoder",
    )
    expected_carries = ([0], [0, 1], [1], [1, 1], [1, 1])
    stage_hashes: dict[str, str] = {}
    for name, carries in zip(names, expected_carries, strict=True):
        word, _, observed_carries = queue.macro_factorized(word)
        if observed_carries != carries:
            raise AssertionError(f"wrong terminal carries at {name}")
        if word != stages[name].word(parameter):
            raise AssertionError(f"restorative lasso identity failed at {name}")
        stage_hashes[name] = yah.sha256_bytes(word.encode())

    returned = returned_register(parameter)
    defect = queue.canonical_value(word) + 1
    if defect != 3**RETURN_RESERVOIR * returned:
        raise AssertionError("returned register semantics failed")
    trailing = len(word) - len(word.rstrip("2"))
    if trailing != RETURN_RESERVOIR:
        raise AssertionError("restorative opcode did not rebuild the reservoir")
    if returned % 2 != (parameter + 1) % 2:
        raise AssertionError("returned register parity law failed")
    if len(word) != incoming_length + 1:
        raise AssertionError("restorative opcode did not gain one cell")

    # The neutral recharge occurs after the first two macros.  Its defect is
    # 9*2^5 times the returned register, before five all-odd steps spend it.
    recharged_word = stages["after_recharge"].word(parameter)
    recharged_defect = queue.canonical_value(recharged_word) + 1
    if recharged_defect != 9 * (1 << 5) * returned:
        raise AssertionError("restorative recharge balance failed")

    return {
        "parameter_u": parameter,
        "lift_t": t,
        "packet_q": q,
        "incoming_decoder_length": incoming_length,
        "returned_decoder_length": len(word),
        "net_decoder_length_gain": len(word) - incoming_length,
        "returned_register_parity": returned % 2,
        "returned_trailing_twos": trailing,
        "incoming_sha256": yah.sha256_bytes(incoming_word.encode()),
        "returned_sha256": yah.sha256_bytes(word.encode()),
        "stage_sha256": stage_hashes,
    }


def build_audit(max_parameter: int) -> dict[str, Any]:
    if max_parameter < 1:
        raise ValueError("maximum parameter must be positive")
    stages = restorative_lassos()
    traces = [exact_trace(parameter) for parameter in range(max_parameter + 1)]

    # Bounded independent regression of the isometry; the displayed all-u
    # law follows symbolically by restricting the already proved lift
    # isometry to t=91+256u and dividing the difference by 2^8.
    registers = [returned_register(parameter) for parameter in range(max_parameter + 1)]
    for left in range(len(registers)):
        for right in range(left + 1, len(registers)):
            if v2_nonzero(registers[right] - registers[left]) != v2_nonzero(
                right - left
            ):
                raise AssertionError("returned register isometry failed")

    q_stride = decoder.Q_STRIDE * T_STRIDE
    stride_valuation = v2_nonzero(pow(9, q_stride, 1 << 20) - 1)
    base_register_mod_256 = incoming_register(0) % (1 << 8)
    if q_stride != 32768 or stride_valuation != 18:
        raise AssertionError("source-cylinder stride valuation failed")
    if base_register_mod_256 != 151:
        raise AssertionError("unexpected restorative source address")
    if (3**6 * base_register_mod_256 + 1) % (1 << 8):
        raise AssertionError("source address does not fund the recharge")

    return {
        "max_parameter": max_parameter,
        "parameters_checked": max_parameter + 1,
        "source_cylinder": {
            "t": "91+256*u",
            "s": "45+128*u",
            "q": "11665+32768*u",
            "q_stride": q_stride,
            "v2_9_pow_q_stride_sub_one": stride_valuation,
            "incoming_register_mod_256": base_register_mod_256,
        },
        "lasso_stages": {name: lasso.record() for name, lasso in stages.items()},
        "traces": traces,
        "all_parameter_certificate": {
            "source": "D=3^7*R, with 2^8 dividing 3^6*R+1",
            "returned_register": "R_next=(3^6*R+1)/2^8",
            "recharge": "D_recharge=9*2^5*R_next",
            "return": "D_return=3^7*R_next",
            "space_charge": "+1 cell from incoming decoder to returned decoder",
            "register_isometry": (
                "v2(R_next(u)-R_next(v))=v2(u-v); parity R_next(u)=u+1 mod 2"
            ),
            "word_type": (
                "five exact macros return head zero and seven trailing twos; "
                "the repeated block remains length 65536 but changes value"
            ),
        },
        "closure_status": {
            "counterexample": None,
            "achieved_instruction": (
                "bit-one collision, neutral recharge, five-odd-step spend, "
                "one-cell gain, and return to the head-zero seven-reservoir chart"
            ),
            "missing_instruction": (
                "the returned lasso is a new type; a finite recurrent type "
                "cycle or invariant ordinary register language is still required"
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
        "decoder_worker_sha256": yah.sha256_bytes(Path(decoder.__file__).read_bytes()),
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
        "decoder_worker_sha256",
        "queue_worker_sha256",
        "audit",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["decoder_worker_sha256"] != yah.sha256_bytes(
        Path(decoder.__file__).read_bytes()
    ):
        raise ValueError("decoder worker hash mismatch")
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
        raise ValueError("restorative audit replay mismatch")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "parameters_checked": data["audit"]["parameters_checked"],
        "counterexample": None,
    }


def selftest() -> None:
    stages = restorative_lassos()
    if stages["incoming_decoder"].word(0) == stages["returned_decoder"].word(0):
        raise AssertionError("restorative opcode must not fake a direct self-link")
    exact_trace(0)
    exact_trace(1)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-parameter", type=int, default=4)
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

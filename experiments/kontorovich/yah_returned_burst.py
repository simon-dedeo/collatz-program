#!/usr/bin/env python3
"""Compressed exact certificates for all-odd bursts in the returned YAH chart.

The restorative decoder returns a lasso with a 65,536-trit block and defect

    D(u) = 3^7 * R(u).

The first explicit search found increasingly long alternating head schedules
``0,1,0,1,...`` on the unique residue for which ``2^(3g) | R(u)``.  Expanding
the restricted lasso block multiplies its size by ``2^(3g)`` and quickly makes
an ordinary string search pointless.

This worker represents words by a straight-line program (literal,
concatenation, and repetition nodes).  A two-state sweep is evaluated by its
exact input/output state summary, and repetition is composed by binary
exponentiation.  It therefore checks the complete lasso family on a residue
class without materializing its repeated block.

The result is a finite-burst certificate, not a recurrent chart or a Collatz
counterexample.  Successively deeper source residues form a nonordinary
2-adic tower; an autonomous ordinary orbit would still have to write its next
address and eventually use a non-growing recharge edge.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah
import yah_lift_decoder as decoder
import yah_queue_macro as queue
import yah_restorative_decoder as restorative


SCHEMA = "yah_returned_burst_v1"
BASE_BLOCK_LENGTH = 65536
REGISTER_DENOMINATOR_EXPONENT = 18


@functools.cache
def returned_explicit_lasso() -> decoder.Lasso:
    """Construct the 65,536-trit base chart only once per verifier run."""

    return restorative.restorative_lassos()["returned_decoder"]


@dataclass(frozen=True)
class SLP:
    kind: str
    literal: str = ""
    left: "SLP | None" = None
    right: "SLP | None" = None
    child: "SLP | None" = None
    count: int = 0


EMPTY = SLP("literal", literal="")


def literal(value: str) -> SLP:
    queue.validate_trit_word(value)
    return EMPTY if not value else SLP("literal", literal=value)


def concat(left: SLP, right: SLP) -> SLP:
    if slp_length(left) == 0:
        return right
    if slp_length(right) == 0:
        return left
    return SLP("concat", left=left, right=right)


def repeat(child: SLP, count: int) -> SLP:
    if count < 0:
        raise ValueError("negative SLP repetition")
    if count == 0 or slp_length(child) == 0:
        return EMPTY
    if count == 1:
        return child
    return SLP("repeat", child=child, count=count)


@functools.cache
def slp_length(node: SLP) -> int:
    if node.kind == "literal":
        return len(node.literal)
    if node.kind == "concat":
        assert node.left is not None and node.right is not None
        return slp_length(node.left) + slp_length(node.right)
    if node.kind == "repeat":
        assert node.child is not None
        return slp_length(node.child) * node.count
    raise AssertionError(node.kind)


def split_first(node: SLP) -> tuple[str, SLP]:
    if slp_length(node) == 0:
        raise ValueError("cannot split an empty SLP")
    if node.kind == "literal":
        return node.literal[0], literal(node.literal[1:])
    if node.kind == "concat":
        assert node.left is not None and node.right is not None
        if slp_length(node.left):
            head, rest = split_first(node.left)
            return head, concat(rest, node.right)
        return split_first(node.right)
    if node.kind == "repeat":
        assert node.child is not None and node.count > 0
        head, rest = split_first(node.child)
        return head, concat(rest, repeat(node.child, node.count - 1))
    raise AssertionError(node.kind)


@dataclass(frozen=True)
class SweepSummary:
    outputs: tuple[SLP, SLP]
    ends: tuple[int, int]


IDENTITY_SUMMARY = SweepSummary((EMPTY, EMPTY), (0, 1))


def compose(first: SweepSummary, second: SweepSummary) -> SweepSummary:
    outputs = []
    ends = []
    for carry in (0, 1):
        middle = first.ends[carry]
        outputs.append(concat(first.outputs[carry], second.outputs[middle]))
        ends.append(second.ends[middle])
    return SweepSummary(tuple(outputs), tuple(ends))  # type: ignore[arg-type]


def summary_power(summary: SweepSummary, exponent: int) -> SweepSummary:
    if exponent < 0:
        raise ValueError("negative summary exponent")
    result = IDENTITY_SUMMARY
    power = summary
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = compose(result, power)
        power = compose(power, power)
        remaining >>= 1
    return result


@functools.cache
def sweep_summary(node: SLP) -> SweepSummary:
    if node.kind == "literal":
        outputs: list[SLP] = []
        ends: list[int] = []
        for start in (0, 1):
            carry = start
            digits: list[str] = []
            for trit in node.literal:
                quotient, carry = queue.SWEEP_TRANSITION[carry, trit]
                digits.append(quotient)
            outputs.append(literal("".join(digits)))
            ends.append(carry)
        return SweepSummary(tuple(outputs), tuple(ends))  # type: ignore[arg-type]
    if node.kind == "concat":
        assert node.left is not None and node.right is not None
        return compose(sweep_summary(node.left), sweep_summary(node.right))
    if node.kind == "repeat":
        assert node.child is not None
        return summary_power(sweep_summary(node.child), node.count)
    raise AssertionError(node.kind)


def open_sweep(node: SLP, start: int) -> tuple[SLP, int]:
    summary = sweep_summary(node)
    return summary.outputs[start], summary.ends[start]


def structural_hash(node: SLP) -> str:
    """Hash the exact SLP expression, without expanding repeated blocks."""

    @functools.cache
    def digest(current: SLP) -> bytes:
        if current.kind == "literal":
            payload = b"L" + len(current.literal).to_bytes(8, "big")
            payload += hashlib.sha256(current.literal.encode()).digest()
        elif current.kind == "concat":
            assert current.left is not None and current.right is not None
            payload = b"C" + digest(current.left) + digest(current.right)
        elif current.kind == "repeat":
            assert current.child is not None
            width = max(1, (current.count.bit_length() + 7) // 8)
            payload = b"R" + width.to_bytes(4, "big")
            payload += current.count.to_bytes(width, "big") + digest(current.child)
        else:
            raise AssertionError(current.kind)
        return hashlib.sha256(payload).digest()

    return digest(node).hex()


def materialize(node: SLP, maximum: int) -> str:
    length = slp_length(node)
    if length > maximum:
        raise ValueError(f"refusing to materialize {length} trits")
    if node.kind == "literal":
        return node.literal
    if node.kind == "concat":
        assert node.left is not None and node.right is not None
        return materialize(node.left, maximum) + materialize(node.right, maximum)
    if node.kind == "repeat":
        assert node.child is not None
        return materialize(node.child, maximum) * node.count
    raise AssertionError(node.kind)


def trailing_twos(node: SLP) -> int:
    if slp_length(node) == 0:
        return 0
    if node.kind == "literal":
        return len(node.literal) - len(node.literal.rstrip("2"))
    if node.kind == "concat":
        assert node.left is not None and node.right is not None
        right_count = trailing_twos(node.right)
        if right_count < slp_length(node.right):
            return right_count
        return right_count + trailing_twos(node.left)
    if node.kind == "repeat":
        assert node.child is not None
        child_count = trailing_twos(node.child)
        if child_count < slp_length(node.child):
            return child_count
        return child_count * node.count
    raise AssertionError(node.kind)


@dataclass(frozen=True)
class CompressedLasso:
    prefix: SLP
    block: SLP
    suffix: SLP

    @staticmethod
    def from_explicit(source: decoder.Lasso) -> "CompressedLasso":
        return CompressedLasso(
            literal(source.prefix), literal(source.block), literal(source.suffix)
        )

    def restrict(self, base: int, stride: int) -> "CompressedLasso":
        if base < 0 or stride < 1:
            raise ValueError("invalid lasso restriction")
        return CompressedLasso(
            concat(self.prefix, repeat(self.block, base)),
            repeat(self.block, stride),
            self.suffix,
        )

    def word(self, parameter: int) -> SLP:
        if parameter < 0:
            raise ValueError("negative lasso parameter")
        return concat(concat(self.prefix, repeat(self.block, parameter)), self.suffix)

    def fixed_sweep(self, start: int) -> tuple["CompressedLasso", int]:
        prefix, carry = open_sweep(self.prefix, start)
        block, next_carry = open_sweep(self.block, carry)
        if next_carry != carry:
            raise ValueError("compressed repeated block does not fix carry")
        suffix, terminal = open_sweep(self.suffix, carry)
        if terminal:
            suffix = concat(suffix, literal("2"))
        return CompressedLasso(prefix, block, suffix), terminal

    def fixed_macro(self) -> tuple["CompressedLasso", str, list[int]]:
        head, tail = split_first(self.prefix)
        current = CompressedLasso(tail, self.block, self.suffix)
        carries: list[int] = []
        for start in {"0": (1,), "1": (0, 0), "2": (1, 0)}[head]:
            current, terminal = current.fixed_sweep(start)
            carries.append(terminal)
        return current, head, carries

    def record(self) -> dict[str, Any]:
        return {
            "prefix_length": slp_length(self.prefix),
            "block_length": slp_length(self.block),
            "suffix_length": slp_length(self.suffix),
            "prefix_slp_sha256": structural_hash(self.prefix),
            "block_slp_sha256": structural_hash(self.block),
            "suffix_slp_sha256": structural_hash(self.suffix),
            "trailing_twos": trailing_twos(self.word(0)),
        }


def returned_register_mod(parameter: int, bits: int) -> int:
    """Return ``R_next(parameter) mod 2^bits`` without constructing ``9^q``."""

    if parameter < 0 or bits < 0:
        raise ValueError("invalid modular register query")
    modulus = 1 << (REGISTER_DENOMINATOR_EXPONENT + bits)
    q = 11665 + 32768 * parameter
    numerator = (9963 * pow(9, q, modulus) + 4669) % modulus
    if numerator % (1 << REGISTER_DENOMINATOR_EXPONENT):
        raise AssertionError("returned-register numerator lost integrality")
    return numerator >> REGISTER_DENOMINATOR_EXPONENT


def root_address(bits: int) -> int:
    """Unique residue ``u mod 2^bits`` with ``R_next(u)=0 mod 2^bits``."""

    address = 0
    for known in range(bits):
        candidates = (address, address + (1 << known))
        winners = [u for u in candidates if returned_register_mod(u, known + 1) == 0]
        if len(winners) != 1:
            raise AssertionError("returned-register Hensel lift was not unique")
        address = winners[0]
    return address


def burst(depth_pairs: int) -> dict[str, Any]:
    if depth_pairs < 1:
        raise ValueError("burst depth must be positive")
    bits = 3 * depth_pairs
    address = root_address(bits)
    stride = 1 << bits
    if returned_register_mod(address, bits) != 0:
        raise AssertionError("burst address lacks its advertised dyadic charge")
    if returned_register_mod(address + stride, bits) != 0:
        raise AssertionError("burst source cylinder is not uniform")

    returned = returned_explicit_lasso()
    current = CompressedLasso.from_explicit(returned).restrict(address, stride)
    source = current.record()
    observed: list[dict[str, Any]] = []
    all_carries: list[list[int]] = []
    for index in range(2 * depth_pairs):
        before_intercept = slp_length(current.word(0))
        current, head, carries = current.fixed_macro()
        after_intercept = slp_length(current.word(0))
        expected_carries = [1] if head == "0" else [1, 1]
        if carries != expected_carries:
            raise AssertionError("returned-chart all-odd burst pattern failed")
        observed.append(
            {
                "macro": index + 1,
                "head": head,
                "terminal_carries": carries,
                "length_delta": after_intercept - before_intercept,
                "endpoint": current.record(),
            }
        )
        all_carries.append(carries)

    endpoint = current.record()
    if endpoint["trailing_twos"] != 7 + bits:
        raise AssertionError("burst did not write the predicted ternary reservoir")
    if sum(len(carries) for carries in all_carries) != bits:
        raise AssertionError("burst did not spend exactly its advertised charge")
    if sum(item["head"] != "0" for item in observed) != depth_pairs:
        raise AssertionError("burst has the wrong number of two-sweep macros")
    net_charge = endpoint["prefix_length"] + endpoint["suffix_length"]
    net_charge -= source["prefix_length"] + source["suffix_length"]
    if net_charge != depth_pairs:
        raise AssertionError("burst has the wrong net space charge")
    return {
        "pair_depth_g": depth_pairs,
        "dyadic_depth": bits,
        "source_residue": address,
        "source_modulus": stride,
        "source_register_modulus_check": returned_register_mod(address, bits),
        "source": source,
        "macros": observed,
        "endpoint": endpoint,
        "head_schedule": "".join(item["head"] for item in observed),
        "carry_schedule": all_carries,
        "net_space_charge": net_charge,
        "defect_multiplier": {"numerator": 27**depth_pairs, "denominator": 8**depth_pairs},
        "endpoint_reservoir": 7 + bits,
        "certificate_scope": (
            "the entire residue-class lasso is checked by exact SLP composition; "
            "the repeated block is never expanded"
        ),
    }


def literal_regression(depth_pairs: int, maximum: int = 2_000_000) -> dict[str, Any]:
    """Independently compare the compressed source/trace at the least address."""

    bits = 3 * depth_pairs
    address = root_address(bits)
    explicit = returned_explicit_lasso()
    word = explicit.word(address)
    if len(word) > maximum:
        raise ValueError("literal regression exceeds its stated bound")
    compressed = CompressedLasso.from_explicit(explicit).restrict(address, 1 << bits)
    if materialize(compressed.word(0), maximum) != word:
        raise AssertionError("compressed source disagrees with explicit lasso")
    trace = []
    for _ in range(2 * depth_pairs):
        word, _, carries = queue.macro_factorized(word)
        compressed, head, compressed_carries = compressed.fixed_macro()
        endpoint = materialize(compressed.word(0), maximum)
        if endpoint != word or compressed_carries != carries:
            raise AssertionError("compressed burst disagrees with literal sweep")
        trace.append(
            {
                "head": head,
                "terminal_carries": carries,
                "word_length": len(word),
                "word_sha256": yah.sha256_bytes(word.encode()),
            }
        )
    return {
        "pair_depth_g": depth_pairs,
        "source_residue": address,
        "source_word_length": len(explicit.word(address)),
        "source_word_sha256": yah.sha256_bytes(explicit.word(address).encode()),
        "trace": trace,
    }


def build_audit(max_depth: int) -> dict[str, Any]:
    if max_depth < 2:
        raise ValueError("maximum depth must include the two observed bursts")
    for parameter in range(4):
        exact = restorative.returned_register(parameter)
        if returned_register_mod(parameter, 24) != exact % (1 << 24):
            raise AssertionError("modular returned-register formula failed")
    bursts = [burst(depth) for depth in range(1, max_depth + 1)]
    residues = [item["source_residue"] for item in bursts]
    for depth in range(1, max_depth):
        if residues[depth] % (1 << (3 * depth)) != residues[depth - 1]:
            raise AssertionError("burst addresses are not a nested 2-adic tower")
    return {
        "max_pair_depth": max_depth,
        "bursts": bursts,
        "literal_regressions": [literal_regression(1), literal_regression(2)],
        "certified_burst_law_through_max_depth": {
            "source": "2^(3g) divides R_next(u) on one residue u=a_g mod 2^(3g)",
            "nested_addresses": "a_(g+1)=a_g mod 2^(3g)",
            "macro_count": "2g, with g one-sweep and g two-sweep heads",
            "terminal_carries": "all 3g quotient sweeps terminate odd",
            "defect": "D'=(27/8)^g*D",
            "space": "+g ternary cells",
            "reservoir": "7+3g trailing twos",
        },
        "closure_status": {
            "counterexample": None,
            "achieved": (
                "compressed exact all-parameter burst certificates and the "
                "nested dyadic source law"
            ),
            "missing": (
                "a collision/recharge edge with a genuinely different affine "
                "register update in a finite recurrent ordinary chart graph"
            ),
        },
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def build_artifact(max_depth: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "restorative_worker_sha256": yah.sha256_bytes(Path(restorative.__file__).read_bytes()),
        "queue_worker_sha256": yah.sha256_bytes(Path(queue.__file__).read_bytes()),
        "audit": build_audit(max_depth),
    }
    payload = dict(data)
    data["artifact_sha256"] = yah.sha256_bytes(yah.canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "worker_sha256",
        "restorative_worker_sha256", "queue_worker_sha256", "audit",
        "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["restorative_worker_sha256"] != yah.sha256_bytes(Path(restorative.__file__).read_bytes()):
        raise ValueError("restorative worker hash mismatch")
    if data["queue_worker_sha256"] != yah.sha256_bytes(Path(queue.__file__).read_bytes()):
        raise ValueError("queue worker hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    maximum = data["audit"]["max_pair_depth"]
    if data["audit"] != build_audit(maximum):
        raise ValueError("returned-burst audit replay mismatch")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "max_pair_depth": maximum,
        "deepest_source_residue": data["audit"]["bursts"][-1]["source_residue"],
        "counterexample": None,
    }


def selftest() -> None:
    sample = literal("012210")
    for carry in (0, 1):
        output, terminal = open_sweep(sample, carry)
        expected, expected_terminal = decoder.open_sweep(carry, "012210")
        if materialize(output, 100) != expected or terminal != expected_terminal:
            raise AssertionError("SLP sweep selftest failed")
    if root_address(3) != 3 or root_address(6) != 27:
        raise AssertionError("known returned-chart roots were not recovered")
    burst(1)
    burst(2)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-depth", type=int, default=4)
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
        artifact = build_artifact(args.max_depth)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())

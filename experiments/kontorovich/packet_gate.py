#!/usr/bin/env python3
"""Exact dyadic--triadic instruction gates for Mersenne packet renewal.

This is a symbolic checker, not a seed sweep.  At counter level ``m`` and
collision extra ``e``, it computes the unique low binary address which makes

    2^e (2^(m+1) h' - 1) = 3^m h - 1

hold with a positive odd next packet.  Every packet at that address is split
as a fixed suffix plus an arbitrarily large payload, and the payload is sent
through one exact affine map.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path


def v2(n: int) -> int:
    """Return the exponent of two in a positive integer."""
    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    return (n & -n).bit_length() - 1


@dataclass(frozen=True)
class PacketGate:
    level: int
    extra: int
    address_width: int
    address_modulus: int
    address_residue: int
    next_offset: int
    payload_multiplier: int
    next_mod_three: int
    next_residue_mod_three: int

    def apply_payload(self, payload: int) -> tuple[int, int]:
        """Return ``(h,h')`` for a nonnegative high payload."""
        if payload < 0:
            raise ValueError("payload must be nonnegative")
        h = self.address_residue + self.address_modulus * payload
        next_h = self.next_offset + self.payload_multiplier * payload
        return h, next_h


def packet_gate(level: int, extra: int) -> PacketGate:
    """Construct the exact affine gate for one renewal instruction."""
    if level < 1 or extra < 1:
        raise ValueError("level and extra must be positive")

    power_three = pow(3, level)
    address_width = level + extra + 2
    address_modulus = 1 << address_width

    # Oddness of h' is the one extra bit beyond divisibility by 2^(m+1+e).
    target = 1 - (1 << extra) + (1 << (level + extra + 1))
    address_residue = (
        target * pow(power_three, -1, address_modulus)
    ) % address_modulus

    numerator = power_three * address_residue + (1 << extra) - 1
    denominator = 1 << (level + extra + 1)
    if numerator % denominator:
        raise AssertionError("constructed address does not make an integer packet")
    next_offset = numerator // denominator

    next_mod_three = power_three
    next_residue_mod_three = (
        ((1 << extra) - 1)
        * pow(1 << (level + extra + 1), -1, next_mod_three)
    ) % next_mod_three

    gate = PacketGate(
        level=level,
        extra=extra,
        address_width=address_width,
        address_modulus=address_modulus,
        address_residue=address_residue,
        next_offset=next_offset,
        payload_multiplier=2 * power_three,
        next_mod_three=next_mod_three,
        next_residue_mod_three=next_residue_mod_three,
    )
    _check_symbolic_fields(gate)
    return gate


def _check_symbolic_fields(gate: PacketGate) -> None:
    """Check all coefficient identities defining a gate."""
    m = gate.level
    e = gate.extra
    power_three = pow(3, m)
    assert gate.address_modulus == 1 << (m + e + 2)
    assert 0 < gate.address_residue < gate.address_modulus
    assert gate.address_residue % 2 == 1
    assert gate.next_offset > 0 and gate.next_offset % 2 == 1
    assert gate.payload_multiplier == 2 * power_three
    assert (
        power_three * gate.address_residue + (1 << e) - 1
        == (1 << (m + e + 1)) * gate.next_offset
    )
    assert gate.next_mod_three == power_three
    assert (
        (1 << (m + e + 1)) * gate.next_residue_mod_three
        - ((1 << e) - 1)
    ) % power_three == 0


def check_payload(gate: PacketGate, payload: int) -> tuple[int, int]:
    """Literally verify one member of the infinite affine gate family."""
    h, next_h = gate.apply_payload(payload)
    m = gate.level
    e = gate.extra
    raw = pow(3, m) * h - 1
    assert v2(raw) == e
    assert next_h > 0 and next_h % 2 == 1
    assert raw == (1 << e) * ((1 << (m + 1)) * next_h - 1)
    assert next_h % gate.next_mod_three == gate.next_residue_mod_three
    return h, next_h


def detected_renewal(level: int, h: int) -> tuple[int, int] | None:
    """Return the literal ``(extra,next_h)`` renewal, when one occurs."""
    if level < 1 or h <= 0 or h % 2 == 0:
        raise ValueError("expected a positive level and positive odd packet")
    raw = pow(3, level) * h - 1
    extra = v2(raw)
    odd_endpoint = raw >> extra
    divisor = 1 << (level + 1)
    if (odd_endpoint + 1) % divisor:
        return None
    next_h = (odd_endpoint + 1) // divisor
    if next_h % 2 == 0:
        return None
    return extra, next_h


def selftest() -> None:
    for level in range(1, 9):
        for extra in range(1, 9):
            gate = packet_gate(level, extra)
            for payload in range(128):
                h, next_h = check_payload(gate, payload)
                assert detected_renewal(level, h) == (extra, next_h)

    # Exhaustive converse: every detected small renewal belongs to the gate
    # selected by its literal valuation, including extras outside 1..8.
    for level in range(1, 9):
        for h in range(1, 1 << 16, 2):
            renewal = detected_renewal(level, h)
            if renewal is None:
                continue
            extra, next_h = renewal
            gate = packet_gate(level, extra)
            quotient, remainder = divmod(
                h - gate.address_residue, gate.address_modulus
            )
            assert remainder == 0 and quotient >= 0
            assert gate.apply_payload(quotient) == (h, next_h)

    # Regressions from independently replayed renewal chains.
    assert detected_renewal(1, 15_301_803_983) == (2, 2_869_088_247)
    assert detected_renewal(2, 186_391) == (1, 104_845)


def audit(max_level: int, max_extra: int, payloads: int, converse_limit: int) -> dict:
    if min(max_level, max_extra, payloads, converse_limit) < 1:
        raise ValueError("audit bounds must be positive")
    checked_family_members = 0
    gates = []
    for level in range(1, max_level + 1):
        for extra in range(1, max_extra + 1):
            gate = packet_gate(level, extra)
            for payload in range(payloads):
                check_payload(gate, payload)
                checked_family_members += 1
            gates.append(asdict(gate))

    detected = 0
    for level in range(1, max_level + 1):
        for h in range(1, converse_limit, 2):
            renewal = detected_renewal(level, h)
            if renewal is None:
                continue
            detected += 1
            extra, next_h = renewal
            gate = packet_gate(level, extra)
            payload, remainder = divmod(
                h - gate.address_residue, gate.address_modulus
            )
            if remainder or payload < 0:
                raise AssertionError("detected renewal missed its symbolic gate")
            if gate.apply_payload(payload) != (h, next_h):
                raise AssertionError("symbolic gate failed converse replay")

    return {
        "schema": "collatz-mersenne-packet-gate-audit-v1",
        "arithmetic": "python_exact_integer",
        "claim_scope": {
            "symbolic_identity": (
                "each listed gate was checked coefficientwise and on every "
                "payload in the stated half-open interval"
            ),
            "bounded_converse": (
                "every literal renewal for odd h below the stated bound was "
                "recovered from its unique exact-valuation gate"
            ),
        },
        "bounds": {
            "levels": [1, max_level],
            "extras": [1, max_extra],
            "payloads": [0, payloads],
            "odd_h_less_than": converse_limit,
        },
        "checked_gate_payload_pairs": checked_family_members,
        "detected_renewals_in_converse_audit": detected,
        "gates": gates,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")

    describe = subparsers.add_parser("describe")
    describe.add_argument("level", type=int)
    describe.add_argument("extra", type=int)

    run_audit = subparsers.add_parser("audit")
    run_audit.add_argument("--max-level", type=int, default=8)
    run_audit.add_argument("--max-extra", type=int, default=8)
    run_audit.add_argument("--payloads", type=int, default=128)
    run_audit.add_argument("--converse-limit", type=int, default=1 << 16)
    run_audit.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("packet_gate selftest: PASS")
    elif args.command == "describe":
        print(json.dumps(asdict(packet_gate(args.level, args.extra)), indent=2))
    else:
        result = audit(
            args.max_level, args.max_extra, args.payloads, args.converse_limit
        )
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output is None:
            print(rendered, end="")
        else:
            args.output.write_text(rendered)
            print(f"wrote {args.output}")


if __name__ == "__main__":
    main()

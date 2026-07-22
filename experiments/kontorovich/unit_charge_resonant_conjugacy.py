#!/usr/bin/env python3
"""Exact determinant-four conjugacies between public bouncer opcodes.

For a canonical public-tail branch write

    2^P t' = 3^Q t + kappa,
    P=154h+23m',  Q=114h+17m.

The exponent matrix has determinant four.  Consequently

    (m,h,m') -> (m+2622k, h-391k, m'+2618k)

preserves both ``P`` and ``Q`` whenever all opcodes remain positive.  The
source and target defect phases differ by ``4k`` after this resonance shift.

Two branches with the same ``P,Q`` are parallel affine maps.  If

    gcd(kappa_a, 3^Q-2^P) | kappa_b,

then an integral affine map ``E(t)=s*t+c`` can satisfy

    E(F_a(t)) = F_b(E(t)).

The source-cylinder compatibility is automatic from the same identity.  This
worker constructs and exactly replays two first examples:

* the phase-down cell ``(1,392,1) -> (2623,1,2619)``;
* the phase-up cell ``(1,392,5) -> (2623,1,2623)``.

Their affine embeddings have about seventy thousand bits, at the program
scale suggested by the Kontorovich challenge.  They are arithmetic bouncer
conjugacies, not an invariant language, literal Collatz compiler, or infinite
orbit.  A periodic up/down bounce is already ruled out; useful closure would
have to make the jump size or direction depend on the surviving payload.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from unit_charge_public_cofactor import branch, replay_branch_member


SCHEMA = "collatz-unit-charge-resonant-conjugacy-v1"
SOURCE_SHIFT = 2622
RECHARGE_SHIFT = 391
TARGET_SHIFT = 2618
PHASE_SLIP = SOURCE_SHIFT - TARGET_SHIFT


@dataclass(frozen=True)
class OpcodeTriple:
    m: int
    h: int
    next_m: int


@dataclass(frozen=True)
class ResonantPair:
    name: str
    source: OpcodeTriple
    target: OpcodeTriple


def decimal_sha256(value: int) -> str:
    return hashlib.sha256(str(value).encode()).hexdigest()


def down_pair(r: int, k: int) -> ResonantPair:
    """A low-phase self cell conjugate to a phase-down high cell."""
    if min(r, k) < 1:
        raise ValueError("resonance parameters must be positive")
    return ResonantPair(
        name="phase_down",
        source=OpcodeTriple(r, RECHARGE_SHIFT * k + 1, r),
        target=OpcodeTriple(
            r + SOURCE_SHIFT * k,
            1,
            r + TARGET_SHIFT * k,
        ),
    )


def up_pair(r: int, k: int) -> ResonantPair:
    """A phase-up low cell conjugate to a high-phase self cell."""
    if min(r, k) < 1:
        raise ValueError("resonance parameters must be positive")
    return ResonantPair(
        name="phase_up",
        source=OpcodeTriple(
            r,
            RECHARGE_SHIFT * k + 1,
            r + PHASE_SLIP * k,
        ),
        target=OpcodeTriple(
            r + SOURCE_SHIFT * k,
            1,
            r + SOURCE_SHIFT * k,
        ),
    )


def branch_row(opcode: OpcodeTriple) -> dict[str, int | str | bool]:
    return branch(opcode.m, opcode.h, opcode.next_m)


def least_positive_conjugacy(
    first: dict[str, int | str | bool],
    second: dict[str, int | str | bool],
) -> tuple[int, int, int, int]:
    """Return ``(s,c,v0,g)`` for the least positive cylinder embedding."""
    if first["P"] != second["P"] or first["Q"] != second["Q"]:
        raise ValueError("conjugacy requires equal tail slopes")
    p = int(first["P"])
    q = int(first["Q"])
    ternary = pow(3, q)
    binary = 1 << p
    gap = ternary - binary
    if gap <= 0:
        raise ValueError("selected resonance is not outward")
    kappa_a = int(first["kappa"])
    kappa_b = int(second["kappa"])
    divisor = math.gcd(kappa_a, gap)
    if kappa_b % divisor:
        raise ValueError("parallel branches have no integral affine conjugacy")
    modulus = gap // divisor
    slope = (
        (kappa_b // divisor)
        * pow((kappa_a // divisor) % modulus, -1, modulus)
    ) % modulus
    if slope == 0:
        slope = modulus

    def values(candidate: int) -> tuple[int, int]:
        numerator = candidate * kappa_a - kappa_b
        if numerator % gap:
            raise AssertionError("conjugacy congruence solver failed")
        intercept = numerator // gap
        cylinder_numerator = (
            candidate * int(first["source_tail_residue"])
            + intercept
            - int(second["source_tail_residue"])
        )
        if cylinder_numerator % binary:
            raise AssertionError("conjugacy missed the target source cylinder")
        return intercept, cylinder_numerator // binary

    intercept, surviving_base = values(slope)
    while intercept < 0 or surviving_base < 0:
        slope += modulus
        intercept, surviving_base = values(slope)
    return slope, intercept, surviving_base, divisor


def conjugacy_record(pair: ResonantPair) -> dict[str, object]:
    first = branch_row(pair.source)
    second = branch_row(pair.target)
    p = int(first["P"])
    q = int(first["Q"])
    if p != int(second["P"]) or q != int(second["Q"]):
        raise AssertionError("determinant-four resonance lost its gain")
    slope, intercept, surviving_base, gcd_value = least_positive_conjugacy(
        first, second
    )
    binary = 1 << p
    ternary = pow(3, q)
    kappa_a = int(first["kappa"])
    kappa_b = int(second["kappa"])
    if (ternary - binary) * intercept != slope * kappa_a - kappa_b:
        raise AssertionError("affine conjugacy constant identity failed")
    if (
        slope * int(first["source_tail_residue"])
        + intercept
        != int(second["source_tail_residue"])
        + binary * surviving_base
    ):
        raise AssertionError("source cylinders did not embed exactly")
    if (
        slope * int(first["target_tail_base"]) + intercept
        != int(second["target_tail_base"])
        + ternary * surviving_base
    ):
        raise AssertionError("target tails did not embed exactly")

    samples: list[dict[str, object]] = []
    for surviving_tail in (0, 1):
        first_member = replay_branch_member(first, surviving_tail)
        mapped_tail = surviving_base + slope * surviving_tail
        second_member = replay_branch_member(second, mapped_tail)
        if (
            int(second_member["source_tail"])
            != slope * int(first_member["source_tail"]) + intercept
            or int(second_member["target_tail"])
            != slope * int(first_member["target_tail"]) + intercept
        ):
            raise AssertionError("sampled public tails missed the conjugacy")
        samples.append(
            {
                "source_surviving_tail": surviving_tail,
                "target_surviving_tail_bits": mapped_tail.bit_length(),
                "target_surviving_tail_decimal_sha256": decimal_sha256(
                    mapped_tail
                ),
                "source_input_y_bits": int(first_member["input_y"]).bit_length(),
                "source_output_y_bits": int(first_member["output_y"]).bit_length(),
                "target_input_y_bits": int(second_member["input_y"]).bit_length(),
                "target_output_y_bits": int(second_member["output_y"]).bit_length(),
                "target_input_y_decimal_sha256": decimal_sha256(
                    int(second_member["input_y"])
                ),
                "target_output_y_decimal_sha256": decimal_sha256(
                    int(second_member["output_y"])
                ),
                "arithmetic_bouncer_replays_checked": 2,
                "source_and_target_tail_embedding_checked": True,
            }
        )

    return {
        "name": pair.name,
        "source_opcode": asdict(pair.source),
        "target_opcode": asdict(pair.target),
        "source_phase_change": pair.source.next_m - pair.source.m,
        "target_phase_change": pair.target.next_m - pair.target.m,
        "P": p,
        "Q": q,
        "gain_gap_positive": ternary > binary,
        "kappa_gcd_with_gain_gap": gcd_value,
        "embedding_slope_bits": slope.bit_length(),
        "embedding_slope_decimal_digits": len(str(slope)),
        "embedding_slope_decimal_sha256": decimal_sha256(slope),
        "embedding_intercept_bits": intercept.bit_length(),
        "embedding_intercept_decimal_digits": len(str(intercept)),
        "embedding_intercept_decimal_sha256": decimal_sha256(intercept),
        "surviving_tail_base_bits": surviving_base.bit_length(),
        "surviving_tail_base_decimal_sha256": decimal_sha256(surviving_base),
        "affine_conjugacy_identity_checked": True,
        "source_cylinder_embedding_checked": True,
        "target_tail_embedding_checked": True,
        "samples": samples,
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_public_cofactor.py"),
        Path(__file__).with_name("unit_charge_bouncer.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def build_certificate() -> dict[str, object]:
    if (
        114 * RECHARGE_SHIFT != 17 * SOURCE_SHIFT
        or 154 * RECHARGE_SHIFT != 23 * TARGET_SHIFT
        or PHASE_SLIP != 4
    ):
        raise AssertionError("determinant-four resonance constants changed")
    pairs = [down_pair(1, 1), up_pair(1, 1)]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "two exact arithmetic public-tail conjugacies at the first "
            "determinant-four resonance, including canonical source-cylinder "
            "and bounded bouncer-formula replays; no literal Collatz semantic "
            "compiler, invariant language, infinite orbit, or counterexample"
        ),
        "resonance": {
            "opcode_shift": [SOURCE_SHIFT, -RECHARGE_SHIFT, TARGET_SHIFT],
            "P_invariance": "154*391=23*2618",
            "Q_invariance": "114*391=17*2622",
            "phase_slip": PHASE_SLIP,
        },
        "conjugacy_criterion": (
            "gcd(kappa_a,3^Q-2^P)|kappa_b implies an integral affine "
            "E(t)=s*t+c with E after F_a = F_b after E"
        ),
        "records": [conjugacy_record(pair) for pair in pairs],
        "strategic_scope": (
            "the resonance produces exact phase-up and phase-down glider "
            "cells; closure still requires payload-driven direction/jump "
            "renewal because every fixed periodic bounce is obstructed"
        ),
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported resonant conjugacy schema")
    if data != build_certificate():
        raise ValueError("resonant conjugacy artifact failed reconstruction")


def selftest() -> None:
    for pair in (down_pair(1, 1), up_pair(1, 1)):
        record = conjugacy_record(pair)
        if not record["affine_conjugacy_identity_checked"]:
            raise AssertionError("resonant conjugacy selftest failed")


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(500_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()
    if args.command == "selftest":
        selftest()
        print("unit charge resonant conjugacy selftest: PASS")
    elif args.command == "build":
        data = build_certificate()
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit charge resonant conjugacy artifact: PASS")


if __name__ == "__main__":
    main()

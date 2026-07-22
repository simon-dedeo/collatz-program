#!/usr/bin/env python3
"""Exact two-layer gap splashes in the invariant unit-register ISA.

At one fixed hierarchy level write

    2^(p(m)) h' = 3^(q(n)) h + s,

where ``p(m)=a*m+b+e`` and ``q(n)=c*n+d``.  To make ``h'`` execute the
following branch ``m -> ell``, first choose its exact low instruction prefix
``C``.  A first correction block ``A`` makes the current collision emit C;
a second, sacrificial word ``z`` cancels the remaining carry and forces any
chosen number D of zero bits immediately above C.  The untouched tail is
mapped affinely by a power of three.

This is a literal unit-level version of Simon Dedeo's "splash the gap" idea.
The worker checks the symbolic integer identities and links two genuine
compiled macros at all six finite hierarchy levels.  It constructs arbitrary
finite regenerated gaps, not an infinite ordinary orbit: repeating the
operation still requires the surviving tail to generate its own future
sacrificial words.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_renormalization import construct_hierarchy
from breakoff_superether import RegisterISA
from breakoff_unit_slice import UnitBranch, unit_branch, unit_isa


SCHEMA = "collatz-unit-gap-regenerator-v1"


@dataclass(frozen=True)
class GapRegenerator:
    level: int
    collision_sign: int
    source_cells: int
    target_cells: int
    following_cells: int
    regenerated_gap_bits: int
    source_public_exponent: int
    target_public_exponent: int
    following_public_exponent: int
    first_division_exponent: int
    second_division_exponent: int
    first_ternary_exponent: int
    second_ternary_exponent: int
    next_instruction_prefix: int
    next_instruction_width: int
    first_correction: int
    carry_before_splash: int
    sacrificial_word: int
    carry_after_splash: int
    invariant_tail_base: int
    residual_base: int
    source_core_base: int
    source_core_stride: int
    target_core_base: int
    target_core_stride: int
    following_core_base: int
    following_core_stride: int

    def cores(self, tail: int) -> tuple[int, int, int]:
        if tail < 0:
            raise ValueError("regenerator tail must be nonnegative")
        return (
            self.source_core_base + self.source_core_stride * tail,
            self.target_core_base + self.target_core_stride * tail,
            self.following_core_base + self.following_core_stride * tail,
        )


def branch_exponents(parent: RegisterISA, cells: int) -> tuple[int, int, int]:
    if cells < 1:
        raise ValueError("unit cell counts must be positive")
    unit = unit_isa(parent)
    public = unit.binary_cell * cells + unit.binary_offset
    division = public + unit.division_exponent
    ternary = unit.ternary_cell * cells + unit.ternary_offset
    return public, division, ternary


def exact_instruction_prefix(sign: int, ternary: int, division: int) -> int:
    """Low ``division+1`` bits giving valuation exactly ``division``."""
    if sign not in (-1, 1) or min(ternary, division) < 1:
        raise ValueError("invalid exact-instruction parameters")
    modulus = 1 << (division + 1)
    power = pow(3, ternary)
    divisible_one_bit_further = (-sign * pow(power, -1, modulus)) % modulus
    prefix = divisible_one_bit_further ^ (1 << division)
    numerator = power * prefix + sign
    if v2(numerator) != division:
        raise AssertionError("instruction prefix is not valuation-exact")
    return prefix


def construct_regenerator(
    parent: RegisterISA,
    source_cells: int,
    target_cells: int,
    following_cells: int,
    gap_bits: int,
) -> GapRegenerator:
    """Construct one universal two-layer correction/gap family."""
    if gap_bits < 1:
        raise ValueError("the regenerated gap must be nonempty")
    unit = unit_isa(parent)
    source_public, _, source_ternary = branch_exponents(
        parent, source_cells
    )
    target_public, first_division, target_ternary = branch_exponents(
        parent, target_cells
    )
    following_public, second_division, _ = branch_exponents(
        parent, following_cells
    )
    sign = unit.collision_sign
    first_power = pow(3, source_ternary)
    second_power = pow(3, target_ternary)

    # C is the complete, valuation-exact binary instruction which makes the
    # next core execute target_cells -> following_cells.  Its width includes
    # the one bit which certifies that the valuation stops at p(following).
    prefix = exact_instruction_prefix(
        sign, target_ternary, second_division
    )
    prefix_width = second_division + 1

    # A emits C after the first division, up to a carry B above C.
    first_modulus = 1 << (first_division + prefix_width)
    correction = (
        pow(first_power, -1, first_modulus)
        * ((1 << first_division) * prefix - sign)
    ) % first_modulus
    carry_numerator = (
        first_power * correction
        + sign
        - (1 << first_division) * prefix
    )
    if carry_numerator % first_modulus:
        raise AssertionError("first correction did not isolate its carry")
    carry = carry_numerator // first_modulus

    # The next D payload bits are sacrificial.  Choose them to cancel B.
    gap_modulus = 1 << gap_bits
    sacrificial = (-carry * pow(first_power, -1, gap_modulus)) % gap_modulus
    cleaned_numerator = carry + first_power * sacrificial
    if cleaned_numerator % gap_modulus:
        raise AssertionError("sacrificial word did not eat the carry")
    cleaned_carry = cleaned_numerator // gap_modulus

    # The public register is an odd affine congruence.  Restrict the untouched
    # tail once modulo its stride so every member is a genuine unit branch.
    register_modulus = unit.register_stride
    raw_source = correction + first_modulus * sacrificial
    tail_coefficient = 1 << (
        first_division + prefix_width + gap_bits
    )
    invariant_core = (
        unit.register_offset
        * pow(1 << source_public, -1, register_modulus)
    ) % register_modulus
    invariant_tail = (
        (invariant_core - raw_source)
        * pow(tail_coefficient, -1, register_modulus)
    ) % register_modulus
    residual = cleaned_carry + first_power * invariant_tail
    if residual <= 0:
        lifts = (-residual + first_power * register_modulus) // (
            first_power * register_modulus
        )
        invariant_tail += register_modulus * lifts
        residual += first_power * register_modulus * lifts

    source_core = raw_source + tail_coefficient * invariant_tail
    source_stride = tail_coefficient * register_modulus
    target_core = prefix + (1 << (prefix_width + gap_bits)) * residual
    target_stride = (
        (1 << (prefix_width + gap_bits))
        * first_power
        * register_modulus
    )

    # After the second genuine branch the clean gap has done its job.  The
    # deterministic low collision carry remains, while the remote packet
    # starts D+1 bits above it.  This is the exact input to the next splash.
    second_carry_numerator = second_power * prefix + sign
    if v2(second_carry_numerator) != second_division:
        raise AssertionError("next instruction lost exact valuation")
    second_carry = second_carry_numerator >> second_division
    remote_shift = prefix_width + gap_bits - second_division
    if remote_shift != gap_bits + 1:
        raise AssertionError("instruction-width accounting changed")
    following_core = (
        second_carry
        + (1 << remote_shift) * second_power * residual
    )
    following_stride = (
        (1 << remote_shift)
        * second_power
        * first_power
        * register_modulus
    )

    return GapRegenerator(
        level=unit.level,
        collision_sign=sign,
        source_cells=source_cells,
        target_cells=target_cells,
        following_cells=following_cells,
        regenerated_gap_bits=gap_bits,
        source_public_exponent=source_public,
        target_public_exponent=target_public,
        following_public_exponent=following_public,
        first_division_exponent=first_division,
        second_division_exponent=second_division,
        first_ternary_exponent=source_ternary,
        second_ternary_exponent=target_ternary,
        next_instruction_prefix=prefix,
        next_instruction_width=prefix_width,
        first_correction=correction,
        carry_before_splash=carry,
        sacrificial_word=sacrificial,
        carry_after_splash=cleaned_carry,
        invariant_tail_base=invariant_tail,
        residual_base=residual,
        source_core_base=source_core,
        source_core_stride=source_stride,
        target_core_base=target_core,
        target_core_stride=target_stride,
        following_core_base=following_core,
        following_core_stride=following_stride,
    )


def packet_for_core(
    parent: RegisterISA, public_exponent: int, core: int
) -> int:
    unit = unit_isa(parent)
    register = (1 << public_exponent) * core
    difference = register - unit.register_offset
    if difference < 0 or difference % unit.register_stride:
        raise AssertionError("core is not in the invariant public register")
    return difference // unit.register_stride


def branch_tail(branch: UnitBranch, packet: int) -> int:
    difference = packet - branch.input_packet_base
    stride = 1 << branch.input_packet_stride_exponent
    if difference < 0 or difference % stride:
        raise AssertionError("packet is not in the compiled unit branch")
    return difference // stride


def verify_member(
    parent: RegisterISA, candidate: GapRegenerator, tail: int
) -> dict[str, int | bool]:
    unit = unit_isa(parent)
    source_core, target_core, following_core = candidate.cores(tail)
    first_power = pow(3, candidate.first_ternary_exponent)
    second_power = pow(3, candidate.second_ternary_exponent)
    sign = candidate.collision_sign
    if (
        first_power * source_core + sign
        != (1 << candidate.first_division_exponent) * target_core
    ):
        raise AssertionError("first splash recurrence failed")
    if (
        second_power * target_core + sign
        != (1 << candidate.second_division_exponent) * following_core
    ):
        raise AssertionError("second splash recurrence failed")
    if v2(first_power * source_core + sign) != candidate.first_division_exponent:
        raise AssertionError("first splash valuation is not exact")
    if v2(second_power * target_core + sign) != candidate.second_division_exponent:
        raise AssertionError("second splash valuation is not exact")
    if any(core % 2 != 1 or core % 3 == 0 for core in (
        source_core,
        target_core,
        following_core,
    )):
        raise AssertionError("splash core is not coprime to six")

    prefix_modulus = 1 << candidate.next_instruction_width
    if target_core % prefix_modulus != candidate.next_instruction_prefix:
        raise AssertionError("collision did not emit the next instruction")
    gap_mask = (1 << candidate.regenerated_gap_bits) - 1
    if (target_core >> candidate.next_instruction_width) & gap_mask:
        raise AssertionError("collision did not regenerate a clean gap")

    source_packet = packet_for_core(
        parent, candidate.source_public_exponent, source_core
    )
    target_packet = packet_for_core(
        parent, candidate.target_public_exponent, target_core
    )
    following_packet = packet_for_core(
        parent, candidate.following_public_exponent, following_core
    )
    first_branch = unit_branch(parent, candidate.source_cells)
    second_branch = unit_branch(parent, candidate.target_cells)
    first_tail = branch_tail(first_branch, source_packet)
    second_tail = branch_tail(second_branch, target_packet)
    if first_branch.member(first_tail) != (source_packet, target_packet):
        raise AssertionError("first compiled macro linkage failed")
    if second_branch.member(second_tail) != (target_packet, following_packet):
        raise AssertionError("second compiled macro linkage failed")

    return {
        "tail": tail,
        "source_core_bits": source_core.bit_length(),
        "target_core_bits": target_core.bit_length(),
        "following_core_bits": following_core.bit_length(),
        "source_packet_bits": source_packet.bit_length(),
        "target_packet_bits": target_packet.bit_length(),
        "following_packet_bits": following_packet.bit_length(),
        "first_compiled_tail_bits": first_tail.bit_length(),
        "second_compiled_tail_bits": second_tail.bit_length(),
        "two_exact_unit_branches_checked": True,
        "instruction_prefix_and_gap_checked": True,
        "cores_coprime_to_six_checked": True,
        "register_invariance_checked": (
            all(
                (
                    (1 << exponent) * core - unit.register_offset
                )
                % unit.register_stride
                == 0
                for exponent, core in (
                    (candidate.source_public_exponent, source_core),
                    (candidate.target_public_exponent, target_core),
                    (candidate.following_public_exponent, following_core),
                )
            )
        ),
    }


def integer_digest(candidate: GapRegenerator) -> str:
    payload = json.dumps(
        asdict(candidate), sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("breakoff_unit_slice.py"),
        Path(__file__).with_name("breakoff_renormalization.py"),
        Path(__file__).with_name("breakoff_superether.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def compact_record(
    parent: RegisterISA, candidate: GapRegenerator, tails: int
) -> dict[str, object]:
    checks = [verify_member(parent, candidate, tail) for tail in range(tails)]
    record: dict[str, object] = {
        "level": candidate.level,
        "collision_sign": candidate.collision_sign,
        "source_cells": candidate.source_cells,
        "target_cells": candidate.target_cells,
        "following_cells": candidate.following_cells,
        "regenerated_gap_bits": candidate.regenerated_gap_bits,
        "next_instruction_width": candidate.next_instruction_width,
        "sacrificial_word": candidate.sacrificial_word,
        "family_sha256": integer_digest(candidate),
        "source_core_base_bits": candidate.source_core_base.bit_length(),
        "target_core_base_bits": candidate.target_core_base.bit_length(),
        "following_core_base_bits": candidate.following_core_base.bit_length(),
        "carry_before_splash_bits": abs(candidate.carry_before_splash).bit_length(),
        "carry_after_splash_bits": abs(candidate.carry_after_splash).bit_length(),
        "members": checks,
    }
    if (
        candidate.level == 1
        and candidate.source_cells == 1
        and candidate.target_cells == 2
        and candidate.following_cells == 3
        and candidate.regenerated_gap_bits == 12
    ):
        record["worked_core_triple"] = list(candidate.cores(0))
    return record


def build_certificate(
    cell_bound: int = 3,
    gap_sizes: tuple[int, ...] = (1, 4, 12),
    tails: int = 2,
) -> dict[str, object]:
    if min(cell_bound, tails, *gap_sizes) < 1:
        raise ValueError("all audit bounds must be positive")
    hierarchy, _ = construct_hierarchy(6)
    records = []
    for parent in hierarchy:
        for source in range(1, cell_bound + 1):
            for target in range(1, cell_bound + 1):
                for following in range(1, cell_bound + 1):
                    for gap in gap_sizes:
                        candidate = construct_regenerator(
                            parent, source, target, following, gap
                        )
                        records.append(compact_record(parent, candidate, tails))
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "research-side exact universal two-layer carry-cancellation "
            "identity in the unit ISA, with bounded reconstruction and two-"
            "macro replay at six compiled hierarchy levels; no infinite "
            "ordinary orbit is claimed"
        ),
        "symbolic_identity": {
            "first_layer": (
                "3^q*A+s=2^p*C+2^(p+L)*B"
            ),
            "sacrificial_layer": (
                "B+3^q*z=2^D*B2"
            ),
            "family": (
                "h=A+2^(p+L)*(z+2^D*u) -> "
                "h'=C+2^(L+D)*(B2+3^q*u)"
            ),
            "interpretation": (
                "A emits the next exact instruction C; z eats the collision "
                "carry B; D clean zero bits are regenerated; the untouched "
                "tail survives affinely"
            ),
        },
        "bounds": {
            "compiled_levels": 6,
            "cell_bound_each_of_three_positions": cell_bound,
            "gap_sizes": list(gap_sizes),
            "members_per_family": tails,
            "families": len(records),
            "two_branch_member_replays": len(records) * tails,
        },
        "records": records,
    }


def render(data: dict[str, object]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported unit-gap artifact schema")
    bounds = data["bounds"]
    expected = build_certificate(
        int(bounds["cell_bound_each_of_three_positions"]),
        tuple(int(value) for value in bounds["gap_sizes"]),
        int(bounds["members_per_family"]),
    )
    if data != expected:
        raise ValueError("unit gap-regenerator artifact failed reconstruction")


def selftest() -> None:
    hierarchy, _ = construct_hierarchy(6)
    for parent in hierarchy:
        for gap in (1, 7):
            candidate = construct_regenerator(parent, 1, 2, 3, gap)
            verify_member(parent, candidate, 0)
            verify_member(parent, candidate, 1)


def main() -> None:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--cell-bound", type=int, default=3)
    build.add_argument("--gap-sizes", default="1,4,12")
    build.add_argument("--tails", type=int, default=2)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("unit gap-regenerator selftest: PASS")
    elif args.command == "build":
        gap_sizes = tuple(int(value) for value in args.gap_sizes.split(","))
        data = build_certificate(args.cell_bound, gap_sizes, args.tails)
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("unit gap-regenerator artifact: PASS")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""A three-bit-capped super-ether made from returning glider macros.

The one-cell returning glider B=M_1 self-links in its macro-tail coordinate
q.  If

    B: K=R+2^23*q -> K'=S+3^17*q,

then, with D=2^23, P=3^17, C=S-R, and G=P-D,

    F(q)=G*q+C,             D*F(q')=P*F(q).

Thus one B self-link consumes 23 binary bits of F.  A B->M_2->B composite
acts as a defect.  Exact cancellation gives the primitive defect register

    V = -8744697538656344367967
        + 671265207750760396088265*K.

An exhausted super-ether (odd F) has the wrong parity to re-enter any glider
defect.  Retaining exactly three bits fixes the interface.  For every N>=1
the resulting returning super-macro has the autonomous normal form

    V = 2^(23*N+3)*g,
    V' = (3^(17*N+40)*g - 17)/2^51,

and the complete affine packet branch

    K=R_N+2^(23*N+54)*t -> K'=S_N+3^(17*N+40)*t.

This is an arbitrarily long finite second-scale delay line, not an infinite
orbit.  The verifier checks its exact affine construction and bounded literal
replay through the lower returning-glider and delay-gate layers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from functools import cache
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_ether_glider import glider_macro, replay_macro_member


SCHEMA = "collatz-breakoff-superether-v1"
COLLISION_CONSTANT = 17


def vp(value: int, prime: int) -> int:
    """Exact p-adic valuation of a nonzero integer."""
    if value == 0:
        raise ValueError("valuation of zero is not used here")
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


@dataclass(frozen=True)
class RegisterISA:
    level: int
    register_offset: int
    register_stride: int
    binary_cell: int
    binary_offset: int
    ternary_cell: int
    ternary_offset: int
    division_exponent: int
    collision_sign: int


@dataclass(frozen=True)
class AffineMacro:
    cells: int
    input_packet_base: int
    input_packet_stride_exponent: int
    output_packet_base: int
    output_packet_stride: int

    def member(self, tail: int) -> tuple[int, int]:
        if tail < 0:
            raise ValueError("macro tail must be nonnegative")
        return (
            self.input_packet_base
            + (1 << self.input_packet_stride_exponent) * tail,
            self.output_packet_base + self.output_packet_stride * tail,
        )


@dataclass(frozen=True)
class SuperEtherComponents:
    background_input_base: int
    background_input_exponent: int
    background_output_base: int
    background_output_stride: int
    background_link_source: int
    background_link_target: int
    fixed_form_slope: int
    fixed_form_constant: int
    into_defect_source: int
    into_defect_target: int
    from_defect_source: int
    from_defect_target: int
    bridge_residual_base: int
    bridge_tail_base: int
    raw_input_tail: int
    raw_return_tail: int
    return_stride: int
    shifted_return_tail: int
    inherited_binary_bits: int
    common_ternary_factor: int
    defect_input_constant: int
    defect_input_exponent: int
    primitive_register_offset: int
    primitive_register_stride: int
    retained_cap_bits: int


@dataclass(frozen=True)
class SuperReplay:
    super_cells: int
    macro_tail: int
    input_packet: int
    output_packet: int
    defect_input_background_tail: int
    defect_tail: int
    returned_background_tail: int
    exposed_capped_tail: int
    exposed_fixed_form_valuation: int
    glider_macro_members_replayed: int
    lower_linked_members_replayed: int
    literal_gate_macros_replayed: int


def level_one_isa() -> RegisterISA:
    """The primitive +17 coordinate of breakoff_ether_counter.py."""
    return RegisterISA(
        level=1,
        register_offset=-291427,
        register_stride=27930177,
        binary_cell=8,
        binary_offset=-5,
        ternary_cell=6,
        ternary_offset=11,
        division_exponent=20,
        collision_sign=1,
    )


def affine_macro(isa: RegisterISA, cells: int) -> AffineMacro:
    """Construct one complete CRT branch of a register ISA."""
    if cells < 1:
        raise ValueError("cell count must be positive")
    binary_exponent = isa.binary_cell * cells + isa.binary_offset
    ternary_exponent = isa.ternary_cell * cells + isa.ternary_offset
    if binary_exponent < 1:
        raise ValueError("branch has no positive binary valuation")

    invariant_residue = (
        isa.register_offset
        * pow(1 << binary_exponent, -1, isa.register_stride)
    ) % isa.register_stride
    execution_residue = (
        -isa.collision_sign
        * COLLISION_CONSTANT
        * pow(pow(3, ternary_exponent), -1, 1 << isa.division_exponent)
    ) % (1 << isa.division_exponent)
    odd_base = invariant_residue + isa.register_stride * (
        (execution_residue - invariant_residue)
        * pow(isa.register_stride, -1, 1 << isa.division_exponent)
        % (1 << isa.division_exponent)
    )
    if odd_base == 0:
        odd_base = isa.register_stride * (1 << isa.division_exponent)
    if odd_base % 2 != 1:
        raise AssertionError("CRT branch base is not odd")

    input_register = (1 << binary_exponent) * odd_base
    numerator = (
        pow(3, ternary_exponent) * odd_base
        + isa.collision_sign * COLLISION_CONSTANT
    )
    if numerator % (1 << isa.division_exponent):
        raise AssertionError("register branch missed its fixed division")
    output_register = numerator >> isa.division_exponent
    if (
        (input_register - isa.register_offset) % isa.register_stride
        or (output_register - isa.register_offset) % isa.register_stride
    ):
        raise AssertionError("register branch lost its packet invariant")

    result = AffineMacro(
        cells=cells,
        input_packet_base=(input_register - isa.register_offset)
        // isa.register_stride,
        input_packet_stride_exponent=(
            binary_exponent + isa.division_exponent
        ),
        output_packet_base=(output_register - isa.register_offset)
        // isa.register_stride,
        output_packet_stride=pow(3, ternary_exponent),
    )
    if result.output_packet_base <= result.input_packet_base:
        raise AssertionError("register branch base is not outward")
    return result


def link_macros(first: AffineMacro, second: AffineMacro) -> tuple[int, int]:
    """Least natural tails q,s with first.output(q)=second.input(s)."""
    modulus = 1 << second.input_packet_stride_exponent
    q = (
        (second.input_packet_base - first.output_packet_base)
        * pow(first.output_packet_stride, -1, modulus)
    ) % modulus
    difference = (
        first.output_packet_base
        + first.output_packet_stride * q
        - second.input_packet_base
    )
    if difference % modulus:
        raise AssertionError("macro link missed its dyadic target")
    s = difference // modulus
    if s < 0:
        lifts = (-s + first.output_packet_stride - 1) // first.output_packet_stride
        q += modulus * lifts
        s += first.output_packet_stride * lifts
    if first.member(q)[1] != second.member(s)[0]:
        raise AssertionError("macro link endpoints disagree")
    return q, s


@cache
def components() -> SuperEtherComponents:
    isa = level_one_isa()
    background = affine_macro(isa, 1)
    defect = affine_macro(isa, 2)
    compiled_background = glider_macro(1)
    compiled_defect = glider_macro(2)
    for abstract, compiled in (
        (background, compiled_background),
        (defect, compiled_defect),
    ):
        if (
            abstract.input_packet_base != compiled.input_packet_base
            or abstract.input_packet_stride_exponent
            != compiled.input_packet_stride_exponent
            or abstract.output_packet_base != compiled.output_packet_base
            or abstract.output_packet_stride != compiled.output_packet_stride
        ):
            raise AssertionError("primitive ISA and literal glider disagree")

    background_source, background_target = link_macros(
        background, background
    )
    into_source, into_target = link_macros(background, defect)
    from_source, from_target = link_macros(defect, background)
    binary_stride = 1 << background.input_packet_stride_exponent
    fixed_slope = background.output_packet_stride - binary_stride
    fixed_constant = (
        background.output_packet_base - background.input_packet_base
    )

    residual = (
        (from_source - into_target)
        * pow(background.output_packet_stride, -1, binary_stride)
    ) % binary_stride
    bridge_tail = (
        into_target
        + background.output_packet_stride * residual
        - from_source
    ) // binary_stride
    if bridge_tail < 0:
        lifts = (
            -bridge_tail + background.output_packet_stride - 1
        ) // background.output_packet_stride
        residual += binary_stride * lifts
        bridge_tail += background.output_packet_stride * lifts
    if (
        into_target + background.output_packet_stride * residual
        != from_source + binary_stride * bridge_tail
    ):
        raise AssertionError("super-defect bridge does not meet")

    defect_binary_stride = 1 << defect.input_packet_stride_exponent
    raw_input = into_source + defect_binary_stride * residual
    raw_return = from_target + defect.output_packet_stride * bridge_tail
    return_stride = (
        defect.output_packet_stride * background.output_packet_stride
    )
    shifted_return = raw_return - return_stride

    def fixed_form(tail: int) -> int:
        return fixed_slope * tail + fixed_constant

    inherited = v2(abs(fixed_form(shifted_return)))
    odd_offset = fixed_form(shifted_return) >> inherited
    odd_stride = fixed_slope * return_stride
    ternary_factor = min(vp(odd_offset, 3), vp(odd_stride, 3))
    primitive_offset = odd_offset // pow(3, ternary_factor)
    primitive_stride = odd_stride // pow(3, ternary_factor)
    input_exponent = (
        defect.input_packet_stride_exponent
        + background.input_packet_stride_exponent
        + inherited
    )
    input_constant = raw_input - (
        1
        << (
            defect.input_packet_stride_exponent
            + background.input_packet_stride_exponent
        )
    )

    if inherited != 0 or ternary_factor != 7:
        raise AssertionError("super-defect inherited factors changed")
    if primitive_offset != -8744697538656344367967:
        raise AssertionError("primitive super-register offset changed")
    if primitive_stride != 671265207750760396088265:
        raise AssertionError("primitive super-register stride changed")
    if input_exponent != 54:
        raise AssertionError("super-defect input width changed")

    # Fully exhausting F gives the parity opposite every glider input.
    # Keeping v2(F)=3 after the super-ether makes the boundary fixed modulo
    # 2^4.  It is exactly the next defect input residue.
    retained_cap = 3
    if input_constant % 16 != 9:
        raise AssertionError("three-bit cap interface changed")
    if background.output_packet_stride % 16 != 3:
        raise AssertionError("background phase modulo 16 changed")
    if fixed_constant % 16 != 13 or fixed_slope % 16 != 3:
        raise AssertionError("fixed-form phase modulo 16 changed")

    return SuperEtherComponents(
        background_input_base=background.input_packet_base,
        background_input_exponent=background.input_packet_stride_exponent,
        background_output_base=background.output_packet_base,
        background_output_stride=background.output_packet_stride,
        background_link_source=background_source,
        background_link_target=background_target,
        fixed_form_slope=fixed_slope,
        fixed_form_constant=fixed_constant,
        into_defect_source=into_source,
        into_defect_target=into_target,
        from_defect_source=from_source,
        from_defect_target=from_target,
        bridge_residual_base=residual,
        bridge_tail_base=bridge_tail,
        raw_input_tail=raw_input,
        raw_return_tail=raw_return,
        return_stride=return_stride,
        shifted_return_tail=shifted_return,
        inherited_binary_bits=inherited,
        common_ternary_factor=ternary_factor,
        defect_input_constant=input_constant,
        defect_input_exponent=input_exponent,
        primitive_register_offset=primitive_offset,
        primitive_register_stride=primitive_stride,
        retained_cap_bits=retained_cap,
    )


def level_two_isa() -> RegisterISA:
    data = components()
    return RegisterISA(
        level=2,
        register_offset=data.primitive_register_offset,
        register_stride=data.primitive_register_stride,
        binary_cell=23,
        binary_offset=3,
        ternary_cell=17,
        ternary_offset=40,
        division_exponent=51,
        collision_sign=-1,
    )


def replay_super_member(candidate: AffineMacro, tail: int) -> SuperReplay:
    if candidate.cells < 1 or tail < 0:
        raise ValueError("positive cell count and natural tail required")
    data = components()
    background = affine_macro(level_one_isa(), 1)
    defect = affine_macro(level_one_isa(), 2)
    input_packet, output_packet = candidate.member(tail)

    # The B->M_2->B defect uses u=K-1 because its inherited binary
    # valuation is zero.
    u = input_packet - 1
    if u < 0:
        raise AssertionError("super-packet does not give a natural bridge")
    residual = data.bridge_residual_base + (
        1 << background.input_packet_stride_exponent
    ) * u
    first_tail = data.into_defect_source + (
        1 << defect.input_packet_stride_exponent
    ) * residual
    if first_tail != data.defect_input_constant + (
        1 << data.defect_input_exponent
    ) * input_packet:
        raise AssertionError("super-defect input normal form failed")
    defect_tail = (
        data.into_defect_target
        + background.output_packet_stride * residual
    )
    bridge_tail = (
        data.bridge_tail_base + background.output_packet_stride * u
    )
    if defect_tail != data.from_defect_source + (
        1 << background.input_packet_stride_exponent
    ) * bridge_tail:
        raise AssertionError("super-defect bridge tails disagree")
    returned = data.from_defect_target + defect.output_packet_stride * bridge_tail
    if returned != data.shifted_return_tail + data.return_stride * input_packet:
        raise AssertionError("super-defect return formula failed")

    first_replay = replay_macro_member(glider_macro(1), first_tail)
    defect_replay = replay_macro_member(glider_macro(2), defect_tail)
    if first_replay.output_packet != defect_replay.input_packet:
        raise AssertionError("literal B->M_2 macro link failed")
    if defect_replay.output_packet != glider_macro(1).member(returned)[0]:
        raise AssertionError("literal M_2->B macro link failed")

    def fixed_form(q: int) -> int:
        return data.fixed_form_slope * q + data.fixed_form_constant

    expected_valuation = 23 * candidate.cells + data.retained_cap_bits
    if v2(fixed_form(returned)) != expected_valuation:
        raise AssertionError("returned super-ether has the wrong depth")

    current = returned
    lower_links = first_replay.linked_members_replayed + defect_replay.linked_members_replayed
    gate_macros = (
        first_replay.literal_gate_macros_replayed
        + defect_replay.literal_gate_macros_replayed
    )
    for remaining in range(candidate.cells, 0, -1):
        if v2(fixed_form(current)) != 23 * remaining + 3:
            raise AssertionError("super-ether depth did not decrement")
        difference = current - data.background_link_source
        binary_stride = 1 << data.background_input_exponent
        if difference < 0 or difference % binary_stride:
            raise AssertionError("super-ether tail missed its B self-link")
        link_tail = difference // binary_stride
        following = (
            data.background_link_target
            + data.background_output_stride * link_tail
        )
        literal = replay_macro_member(glider_macro(1), current)
        if literal.output_packet != glider_macro(1).member(following)[0]:
            raise AssertionError("literal super-ether B link failed")
        lower_links += literal.linked_members_replayed
        gate_macros += literal.literal_gate_macros_replayed
        current = following

    if v2(fixed_form(current)) != 3:
        raise AssertionError("three-bit cap was not retained")
    expected_boundary = data.defect_input_constant + (
        1 << data.defect_input_exponent
    ) * output_packet
    if current != expected_boundary:
        raise AssertionError("capped boundary missed the next super-defect")
    return SuperReplay(
        super_cells=candidate.cells,
        macro_tail=tail,
        input_packet=input_packet,
        output_packet=output_packet,
        defect_input_background_tail=first_tail,
        defect_tail=defect_tail,
        returned_background_tail=returned,
        exposed_capped_tail=current,
        exposed_fixed_form_valuation=v2(fixed_form(current)),
        glider_macro_members_replayed=candidate.cells + 2,
        lower_linked_members_replayed=lower_links,
        literal_gate_macros_replayed=gate_macros,
    )


def check_branch(cells: int, tails: int) -> tuple[AffineMacro, list[SuperReplay]]:
    candidate = affine_macro(level_two_isa(), cells)
    if candidate.input_packet_stride_exponent != 23 * cells + 54:
        raise AssertionError("super-macro input exponent changed")
    if candidate.output_packet_stride != pow(3, 17 * cells + 40):
        raise AssertionError("super-macro output stride changed")
    replays = [replay_super_member(candidate, tail) for tail in range(tails)]
    return candidate, replays


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    max_super_cells: int, tails_per_branch: int, literal_replay_cells: int
) -> dict[str, object]:
    if min(max_super_cells, tails_per_branch, literal_replay_cells) < 1:
        raise ValueError("all bounds must be positive")
    if literal_replay_cells > max_super_cells:
        raise ValueError("literal replay bound exceeds branch bound")
    branches = [
        affine_macro(level_two_isa(), n)
        for n in range(1, max_super_cells + 1)
    ]
    checks = 0
    for candidate in branches:
        for tail in range(tails_per_branch):
            source, target = candidate.member(tail)
            isa = level_two_isa()
            source_register = isa.register_offset + isa.register_stride * source
            target_register = isa.register_offset + isa.register_stride * target
            exponent = 23 * candidate.cells + 3
            if v2(source_register) != exponent:
                raise AssertionError("super-register branch valuation failed")
            odd = source_register >> exponent
            expected = (
                pow(3, 17 * candidate.cells + 40) * odd - 17
            )
            if expected % (1 << 51) or expected >> 51 != target_register:
                raise AssertionError("autonomous super-register map failed")
            checks += 1
    replays = [
        replay_super_member(branches[n - 1], tail)
        for n in range(1, literal_replay_cells + 1)
        for tail in range(min(2, tails_per_branch))
    ]
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact second-scale affine constructor and autonomous register "
            "for every listed N; bounded literal replay through returning "
            "glider and delay-gate layers; no infinite orbit claim"
        ),
        "level_one_isa": asdict(level_one_isa()),
        "level_two_isa": asdict(level_two_isa()),
        "components": asdict(components()),
        "autonomous_map": (
            "V=2^(23N+3)g -> V'=(3^(17N+40)g-17)/2^51"
        ),
        "universal_super_macro": (
            "K=R_N+2^(23N+54)t -> K'=S_N+3^(17N+40)t"
        ),
        "bounds": {
            "super_cells": [1, max_super_cells],
            "tails_per_branch": tails_per_branch,
            "literal_replay_cells": [1, literal_replay_cells],
        },
        "branch_count": len(branches),
        "exact_branch_members_checked": checks,
        "literal_super_macro_members": len(replays),
        "glider_macro_members_replayed": sum(
            replay.glider_macro_members_replayed for replay in replays
        ),
        "lower_linked_members_replayed": sum(
            replay.lower_linked_members_replayed for replay in replays
        ),
        "literal_gate_macros_replayed": sum(
            replay.literal_gate_macros_replayed for replay in replays
        ),
        "branches": [asdict(candidate) for candidate in branches],
        "replay_samples": [
            asdict(replays[index])
            for index in sorted({0, len(replays) // 2, len(replays) - 1})
        ],
    }


def selftest() -> None:
    candidate, replays = check_branch(1, 2)
    if candidate.input_packet_stride_exponent != 77:
        raise AssertionError("one-cell super-macro width changed")
    if any(replay.exposed_fixed_form_valuation != 3 for replay in replays):
        raise AssertionError("one-cell super-macro lost its cap")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--max-super-cells", type=int, default=64)
    build.add_argument("--tails-per-branch", type=int, default=4)
    build.add_argument("--literal-replay-cells", type=int, default=16)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff super-ether selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.max_super_cells,
            args.tails_per_branch,
            args.literal_replay_cells,
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["super_cells"][1]),
            int(bounds["tails_per_branch"]),
            int(bounds["literal_replay_cells"][1]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff super-ether artifact: PASS")


if __name__ == "__main__":
    main()

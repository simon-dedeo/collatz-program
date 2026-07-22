#!/usr/bin/env python3
"""Exact finite renormalization hierarchy of capped Collatz super-ethers.

A register ISA in this hierarchy has the form

    V = r + m*K,
    V = 2^(a*n+b)*g,
    V' = (3^(c*n+d)*g + s*17)/2^e,       s in {+1,-1}.

Its complete length-n branch is

    K=R_n+2^(a*n+b+e)*q -> K'=S_n+3^(c*n+d)*q.

To renormalize, use branch 1 as a background cell B and branch 2 as a
defect B->H->B.  Let F be the affine fixed form of the B self-link.  Retain
``a+b`` low bits of F at the boundary instead of exhausting it.  When the
phase congruence and exact constant identity pass, the primitive defect
register is another ISA of the same shape, with collision sign -s.

This verifier constructs six exact levels, checks every displayed phase and
constant identity, independently builds child branches both by CRT and by
literal parent-macro composition, and replays bounded members at the parent
macro layer.  A generic positivity identity also proves that every positive
child packet enters its parent background at a strictly positive tail, so an
infinite tower of these canonical extensions cannot stabilize to one ordinary
packet.  It does not construct an infinite hierarchy or an autonomous orbit at
a fixed level.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from breakoff_delay_gate import v2
from breakoff_ether_glider import glider_macro, replay_macro_member
from breakoff_superether import (
    COLLISION_CONSTANT,
    AffineMacro,
    RegisterISA,
    affine_macro,
    level_one_isa,
    level_two_isa,
    link_macros,
    vp,
)


SCHEMA = "collatz-breakoff-renormalization-v1"


@dataclass(frozen=True)
class RenormalizationStep:
    parent_level: int
    child_level: int
    background: AffineMacro
    defect: AffineMacro
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
    retained_cap_bits: int
    defect_input_constant: int
    defect_input_exponent: int
    normalized_collision_constant: int
    child: RegisterISA


@dataclass(frozen=True)
class AbstractReplay:
    child_level: int
    child_cells: int
    macro_tail: int
    input_packet: int
    output_packet: int
    first_background_tail: int
    defect_tail: int
    returned_background_tail: int
    capped_boundary_tail: int
    capped_fixed_form_valuation: int
    parent_macro_members_replayed: int


@dataclass(frozen=True)
class CanonicalDepthAudit:
    depth: int
    leaf_macro_members: int
    one_cell_leaves: int
    two_cell_leaves: int
    input_packet_bits: int
    input_packet_decimal_digits: int
    input_packet_decimal_sha256: str
    ordinary_start_bits: int
    ordinary_start_decimal_digits: int
    ordinary_start_decimal_sha256: str
    shared_low_packet_bits_with_previous_depth: int | None
    strictly_larger_than_previous_depth: bool | None
    lower_linked_members_replayed: int
    literal_gate_macros_replayed: int


def renormalize(
    parent: RegisterISA, background_cells: int = 1
) -> RenormalizationStep:
    """Validate a capped B_j/M_(j+1) renormalization."""
    if background_cells < 1:
        raise ValueError("background cell count must be positive")
    background = affine_macro(parent, background_cells)
    defect = affine_macro(parent, background_cells + 1)
    binary_stride = 1 << background.input_packet_stride_exponent
    ternary_stride = background.output_packet_stride
    fixed_slope = ternary_stride - binary_stride
    fixed_constant = (
        background.output_packet_base - background.input_packet_base
    )
    background_source, background_target = link_macros(
        background, background
    )
    into_source, into_target = link_macros(background, defect)
    from_source, from_target = link_macros(defect, background)

    residual = (
        (from_source - into_target)
        * pow(ternary_stride, -1, binary_stride)
    ) % binary_stride
    bridge_tail = (
        into_target + ternary_stride * residual - from_source
    ) // binary_stride
    if bridge_tail < 0:
        lifts = (-bridge_tail + ternary_stride - 1) // ternary_stride
        residual += binary_stride * lifts
        bridge_tail += ternary_stride * lifts
    if (
        into_target + ternary_stride * residual
        != from_source + binary_stride * bridge_tail
    ):
        raise AssertionError("renormalized defect bridge does not meet")

    defect_binary_stride = 1 << defect.input_packet_stride_exponent
    raw_input = into_source + defect_binary_stride * residual
    if raw_input <= 0:
        raise AssertionError("renormalized defect has no positive raw input")
    raw_return = from_target + defect.output_packet_stride * bridge_tail
    return_stride = defect.output_packet_stride * ternary_stride
    shifted_return = raw_return - return_stride
    fixed_return = fixed_slope * shifted_return + fixed_constant
    inherited = v2(abs(fixed_return))
    odd_offset = fixed_return >> inherited
    odd_stride = fixed_slope * return_stride
    common_ternary = min(vp(odd_offset, 3), vp(odd_stride, 3))
    child_offset = odd_offset // pow(3, common_ternary)
    child_stride = odd_stride // pow(3, common_ternary)
    if child_stride % 2 != 1:
        raise AssertionError("renormalized register stride is not odd")

    base_input_exponent = (
        defect.input_packet_stride_exponent
        + background.input_packet_stride_exponent
    )
    defect_input_exponent = base_input_exponent + inherited
    defect_input_constant = raw_input - (1 << base_input_exponent)
    retained_cap = (
        parent.binary_cell * background_cells + parent.binary_offset
    )
    if retained_cap < 1 or defect_input_exponent <= retained_cap + 1:
        raise AssertionError("invalid retained-cap geometry")

    # For an exact cap, the boundary fixed form is 2^cap modulo
    # 2^(cap+1), independent of its odd payload and of the number of cells.
    phase_modulus = 1 << (retained_cap + 1)
    boundary_phase = (
        ((1 << retained_cap) - fixed_constant)
        * pow(fixed_slope, -1, phase_modulus)
    ) % phase_modulus
    if defect_input_constant % phase_modulus != boundary_phase:
        raise AssertionError("retained cap misses the next defect phase")

    # Normalize the boundary quotient.  Division by the retained cap must
    # reproduce the collision constant with opposite sign.
    normalized_numerator = (
        child_offset * (1 << defect_input_exponent)
        - (return_stride // pow(3, common_ternary))
        * (fixed_constant + fixed_slope * defect_input_constant)
    )
    if normalized_numerator % (1 << retained_cap):
        raise AssertionError("collision normalization lost its cap factor")
    normalized_collision = normalized_numerator >> retained_cap
    if normalized_collision != -parent.collision_sign * COLLISION_CONSTANT:
        raise AssertionError("collision constant was not preserved with sign flip")

    child = RegisterISA(
        level=parent.level + 1,
        register_offset=child_offset,
        register_stride=child_stride,
        binary_cell=background.input_packet_stride_exponent,
        binary_offset=retained_cap - inherited,
        ternary_cell=(
            parent.ternary_cell * background_cells
            + parent.ternary_offset
        ),
        ternary_offset=(
            parent.ternary_cell * (2 * background_cells + 1)
            + 2 * parent.ternary_offset
        ),
        division_exponent=defect_input_exponent - retained_cap,
        collision_sign=-parent.collision_sign,
    )
    return RenormalizationStep(
        parent_level=parent.level,
        child_level=child.level,
        background=background,
        defect=defect,
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
        common_ternary_factor=common_ternary,
        retained_cap_bits=retained_cap,
        defect_input_constant=defect_input_constant,
        defect_input_exponent=defect_input_exponent,
        normalized_collision_constant=normalized_collision,
        child=child,
    )


def parent_input_tail(step: RenormalizationStep, child_packet: int) -> int:
    """Tail at which a positive child packet enters the parent background."""
    if child_packet < 1:
        raise ValueError("child packet must be positive")
    tail = step.defect_input_constant + (
        (1 << step.defect_input_exponent) * child_packet
    )
    base_exponent = (
        step.background.input_packet_stride_exponent
        + step.defect.input_packet_stride_exponent
    )
    expected = step.raw_input_tail + (1 << base_exponent) * (
        (1 << step.inherited_binary_bits) * child_packet - 1
    )
    if tail != expected:
        raise AssertionError("parent-tail positivity identity failed")
    if tail <= 0:
        raise AssertionError("positive child packet gave a canonical parent tail")
    return tail


def direct_nested_macro(step: RenormalizationStep, cells: int) -> AffineMacro:
    """Build a child branch directly from the parent defect and capped ether."""
    if cells < 1:
        raise ValueError("child cell count must be positive")
    background = step.background
    binary_cell = background.input_packet_stride_exponent
    ternary_cell = background.output_packet_stride
    cap = step.retained_cap_bits
    inherited = step.inherited_binary_bits
    child = step.child
    child_binary_exponent = binary_cell * cells + cap - inherited
    packet_modulus = 1 << (child_binary_exponent + 1)
    packet = (
        ((1 << child_binary_exponent) - child.register_offset)
        * pow(child.register_stride, -1, packet_modulus)
    ) % packet_modulus
    if packet == 0:
        packet = packet_modulus

    returned = step.shifted_return_tail + (
        (1 << inherited) * step.return_stride * packet
    )
    fixed_return = (
        step.fixed_form_slope * returned + step.fixed_form_constant
    )
    expected_depth = binary_cell * cells + cap
    if v2(fixed_return) != expected_depth:
        raise AssertionError("direct child packet has the wrong ether depth")
    boundary_fixed = pow(ternary_cell, cells) * (
        fixed_return >> (binary_cell * cells)
    )
    boundary_numerator = boundary_fixed - step.fixed_form_constant
    if boundary_numerator % step.fixed_form_slope:
        raise AssertionError("capped boundary tail is not integral")
    boundary = boundary_numerator // step.fixed_form_slope

    boundary_stride = (
        (1 << (cap + 1))
        * step.return_stride
        * pow(ternary_cell, cells)
    )
    reduced_exponent = step.defect_input_exponent - cap - 1
    reduced_modulus = 1 << reduced_exponent
    difference = step.defect_input_constant - boundary
    if difference % (1 << (cap + 1)):
        raise AssertionError("direct child boundary missed the cap phase")
    lift = (
        (difference >> (cap + 1))
        * pow(boundary_stride >> (cap + 1), -1, reduced_modulus)
    ) % reduced_modulus
    output = (
        boundary
        + boundary_stride * lift
        - step.defect_input_constant
    ) >> step.defect_input_exponent
    output_stride = step.return_stride * pow(ternary_cell, cells)
    if output < 0:
        extra = (-output + output_stride - 1) // output_stride
        lift += reduced_modulus * extra
        output += output_stride * extra

    input_base = packet + packet_modulus * lift
    input_exponent = (
        child_binary_exponent
        + step.defect_input_exponent
        - cap
    )
    result = AffineMacro(
        cells=cells,
        input_packet_base=input_base,
        input_packet_stride_exponent=input_exponent,
        output_packet_base=output,
        output_packet_stride=output_stride,
    )
    if result != affine_macro(child, cells):
        raise AssertionError("direct nested branch and child CRT branch disagree")
    return result


def replay_parent_member(
    step: RenormalizationStep, candidate: AffineMacro, tail: int
) -> AbstractReplay:
    """Replay one child member as B->H->B followed by B self-links."""
    input_packet, output_packet = candidate.member(tail)
    background = step.background
    defect = step.defect
    binary_stride = 1 << background.input_packet_stride_exponent
    defect_stride = 1 << defect.input_packet_stride_exponent
    u = (1 << step.inherited_binary_bits) * input_packet - 1
    if u < 0:
        raise AssertionError("child packet gives a negative defect bridge")
    residual = step.bridge_residual_base + binary_stride * u
    first_tail = step.into_defect_source + defect_stride * residual
    if first_tail != parent_input_tail(step, input_packet):
        raise AssertionError("child defect input normal form failed")
    defect_tail = step.into_defect_target + (
        background.output_packet_stride * residual
    )
    bridge_tail = step.bridge_tail_base + (
        background.output_packet_stride * u
    )
    if defect_tail != step.from_defect_source + binary_stride * bridge_tail:
        raise AssertionError("child defect bridge tails disagree")
    returned = step.from_defect_target + defect.output_packet_stride * bridge_tail
    if returned != step.shifted_return_tail + (
        (1 << step.inherited_binary_bits) * step.return_stride * input_packet
    ):
        raise AssertionError("child defect return formula failed")
    if background.member(first_tail)[1] != defect.member(defect_tail)[0]:
        raise AssertionError("abstract B->H link failed")
    if defect.member(defect_tail)[1] != background.member(returned)[0]:
        raise AssertionError("abstract H->B link failed")

    def fixed_form(value: int) -> int:
        return step.fixed_form_slope * value + step.fixed_form_constant

    expected = (
        background.input_packet_stride_exponent * candidate.cells
        + step.retained_cap_bits
    )
    if v2(fixed_form(returned)) != expected:
        raise AssertionError("abstract returned ether has the wrong depth")
    current = returned
    for remaining in range(candidate.cells, 0, -1):
        if v2(fixed_form(current)) != (
            background.input_packet_stride_exponent * remaining
            + step.retained_cap_bits
        ):
            raise AssertionError("abstract ether depth did not decrement")
        difference = current - step.background_link_source
        if difference < 0 or difference % binary_stride:
            raise AssertionError("abstract ether missed its background link")
        residual = difference // binary_stride
        following = step.background_link_target + (
            background.output_packet_stride * residual
        )
        if background.member(current)[1] != background.member(following)[0]:
            raise AssertionError("abstract background endpoints disagree")
        current = following
    if v2(fixed_form(current)) != step.retained_cap_bits:
        raise AssertionError("abstract boundary lost its retained cap")
    if current != step.defect_input_constant + (
        1 << step.defect_input_exponent
    ) * output_packet:
        raise AssertionError("abstract boundary missed the next child defect")
    return AbstractReplay(
        child_level=step.child_level,
        child_cells=candidate.cells,
        macro_tail=tail,
        input_packet=input_packet,
        output_packet=output_packet,
        first_background_tail=first_tail,
        defect_tail=defect_tail,
        returned_background_tail=returned,
        capped_boundary_tail=current,
        capped_fixed_form_valuation=v2(fixed_form(current)),
        parent_macro_members_replayed=candidate.cells + 2,
    )


def construct_hierarchy(
    levels: int, background_word: list[int] | None = None
) -> tuple[list[RegisterISA], list[RenormalizationStep]]:
    if levels < 2:
        raise ValueError("hierarchy must contain at least two levels")
    if background_word is None:
        background_word = [1] * (levels - 1)
    if len(background_word) != levels - 1 or any(
        cells < 1 for cells in background_word
    ):
        raise ValueError("background word must have one positive entry per step")
    hierarchy = [level_one_isa()]
    steps: list[RenormalizationStep] = []
    while len(hierarchy) < levels:
        background_cells = background_word[len(steps)]
        step = renormalize(hierarchy[-1], background_cells)
        if (
            step.parent_level == 1
            and background_cells == 1
            and step.child != level_two_isa()
        ):
            raise AssertionError("generic level-two ISA disagrees with literal super-ether")
        steps.append(step)
        hierarchy.append(step.child)
    return hierarchy, steps


def adjacent_background_alphabet(max_background_cells: int) -> list[dict[str, int]]:
    """Check all adjacent B_j/M_(j+1) sign-preserving defects in a box."""
    if max_background_cells < 1:
        raise ValueError("background alphabet bound must be positive")
    parent = level_one_isa()
    records: list[dict[str, int]] = []
    for background_cells in range(1, max_background_cells + 1):
        step = renormalize(parent, background_cells)
        records.append(
            {
                "background_cells": background_cells,
                "defect_cells": background_cells + 1,
                "retained_cap_bits": step.retained_cap_bits,
                "inherited_binary_bits": step.inherited_binary_bits,
                "common_ternary_factor": step.common_ternary_factor,
                "normalized_collision_constant": (
                    step.normalized_collision_constant
                ),
                "child_binary_cell": step.child.binary_cell,
                "child_binary_offset": step.child.binary_offset,
                "child_ternary_cell": step.child.ternary_cell,
                "child_ternary_offset": step.child.ternary_offset,
                "child_division_exponent": step.child.division_exponent,
            }
        )
    return records


def alternative_choice_words() -> list[dict[str, object]]:
    """Exercise nonconstant meta-programs through four renormalizations."""
    words = ([2, 2, 2, 2], [3, 1, 4, 2], [8, 5, 3, 1])
    records: list[dict[str, object]] = []
    for word in words:
        hierarchy, steps = construct_hierarchy(len(word) + 1, list(word))
        records.append(
            {
                "background_word": list(word),
                "collision_signs": [isa.collision_sign for isa in hierarchy],
                "binary_cell_widths": [isa.binary_cell for isa in hierarchy],
                "retained_caps": [step.retained_cap_bits for step in steps],
                "normalized_collision_constants": [
                    step.normalized_collision_constant for step in steps
                ],
                "terminal_offset_decimal_sha256": hashlib.sha256(
                    str(hierarchy[-1].register_offset).encode()
                ).hexdigest(),
                "terminal_stride_decimal_sha256": hashlib.sha256(
                    str(hierarchy[-1].register_stride).encode()
                ).hexdigest(),
            }
        )
    return records


def canonical_meta_quine_search(
    choice_bound: int, max_depth: int
) -> dict[str, object]:
    """Search a bounded meta-word tree for exact canonical-seed stabilization."""
    if min(choice_bound, max_depth) < 1:
        raise ValueError("meta-quine bounds must be positive")
    nodes_by_depth = [0] * (max_depth + 1)
    stabilizations: list[list[int]] = []
    decreases: list[list[int]] = []
    closest: dict[int, dict[str, object]] = {}

    def visit(
        isa: RegisterISA,
        embedding_base: int,
        embedding_exponent: int,
        previous_packet: int | None,
        prefix: tuple[int, ...],
        depth: int,
    ) -> None:
        if depth > max_depth:
            return
        for background_cells in range(1, choice_bound + 1):
            packet = embedding_base + (
                (1 << embedding_exponent)
                * affine_macro(isa, background_cells).input_packet_base
            )
            word = prefix + (background_cells,)
            nodes_by_depth[depth] += 1
            if previous_packet is not None:
                difference = packet - previous_packet
                if difference == 0:
                    stabilizations.append(list(word))
                elif difference < 0:
                    decreases.append(list(word))
                else:
                    record = {
                        "word": list(word),
                        "previous_packet_bits": previous_packet.bit_length(),
                        "extended_packet_bits": packet.bit_length(),
                        "difference_bits": difference.bit_length(),
                        "shared_low_bits": v2(difference),
                    }
                    prior = closest.get(depth)
                    if prior is None or (
                        int(record["difference_bits"]), record["word"]
                    ) < (int(prior["difference_bits"]), prior["word"]):
                        closest[depth] = record

            step = renormalize(isa, background_cells)
            background = step.background
            local_base = background.input_packet_base + (
                (1 << background.input_packet_stride_exponent)
                * step.defect_input_constant
            )
            local_exponent = (
                background.input_packet_stride_exponent
                + step.defect_input_exponent
            )
            visit(
                step.child,
                embedding_base + (1 << embedding_exponent) * local_base,
                embedding_exponent + local_exponent,
                packet,
                word,
                depth + 1,
            )

    visit(level_one_isa(), 0, 0, None, (), 1)
    return {
        "choice_alphabet": [1, choice_bound],
        "max_depth": max_depth,
        "nodes_by_depth": nodes_by_depth[1:],
        "nodes_checked": sum(nodes_by_depth),
        "canonical_stabilizations": stabilizations,
        "canonical_decreases": decreases,
        "all_extensions_strictly_increase": (
            not stabilizations and not decreases
        ),
        "closest_strict_extension_by_depth": [
            closest[depth] for depth in range(2, max_depth + 1)
        ],
    }


def expand_to_level_one(
    steps: list[RenormalizationStep], level: int, cells: int, tail: int
) -> list[tuple[int, int]]:
    """Expand one level-L macro member to linked level-one macro members."""
    if level < 1 or level > len(steps) + 1:
        raise ValueError("requested level is outside the constructed hierarchy")
    if level == 1:
        return [(cells, tail)]
    step = steps[level - 2]
    candidate = direct_nested_macro(step, cells)
    input_packet, output_packet = candidate.member(tail)
    background = step.background
    defect = step.defect
    binary_stride = 1 << background.input_packet_stride_exponent
    defect_stride = 1 << defect.input_packet_stride_exponent
    u = (1 << step.inherited_binary_bits) * input_packet - 1
    residual = step.bridge_residual_base + binary_stride * u
    first_tail = step.into_defect_source + defect_stride * residual
    defect_tail = step.into_defect_target + (
        background.output_packet_stride * residual
    )
    bridge_tail = step.bridge_tail_base + (
        background.output_packet_stride * u
    )
    current = step.from_defect_target + defect.output_packet_stride * bridge_tail
    parent_members = [
        (step.background.cells, first_tail),
        (step.defect.cells, defect_tail),
    ]
    for _ in range(cells):
        parent_members.append((step.background.cells, current))
        difference = current - step.background_link_source
        if difference < 0 or difference % binary_stride:
            raise AssertionError("recursive expansion missed a background link")
        current = step.background_link_target + (
            background.output_packet_stride * (difference // binary_stride)
        )
    if current != step.defect_input_constant + (
        1 << step.defect_input_exponent
    ) * output_packet:
        raise AssertionError("recursive expansion missed its child output")
    leaves: list[tuple[int, int]] = []
    for parent_cells, parent_tail in parent_members:
        leaves.extend(
            expand_to_level_one(
                steps, level - 1, parent_cells, parent_tail
            )
        )
    return leaves


def canonical_depth_audit(
    hierarchy: list[RegisterISA], steps: list[RenormalizationStep]
) -> list[CanonicalDepthAudit]:
    """Replay the tail-zero length-one program at every constructed depth."""
    audits: list[CanonicalDepthAudit] = []
    previous_packet: int | None = None
    for depth, isa in enumerate(hierarchy, start=1):
        # The top-level tail is zero, but its branch base is an ordinary
        # positive packet.  Recursive expansion exposes the corresponding
        # first-scale packet and literal Collatz start.
        affine_macro(isa, 1)
        leaves = expand_to_level_one(steps, depth, 1, 0)
        if not leaves or leaves[0][0] != 1:
            raise AssertionError("canonical hierarchy lost its first background cell")
        first_packet = glider_macro(1).member(leaves[0][1])[0]
        ordinary_start = replay_macro_member(
            glider_macro(1), leaves[0][1]
        ).ordinary_start
        previous_output: int | None = None
        lower_links = 0
        gate_macros = 0
        for leaf_cells, leaf_tail in leaves:
            if leaf_cells not in {1, 2}:
                raise AssertionError("canonical hierarchy emitted a nonprimitive leaf")
            macro = glider_macro(leaf_cells)
            member_input, member_output = macro.member(leaf_tail)
            if previous_output is not None and member_input != previous_output:
                raise AssertionError("canonical leaf macro sequence is not linked")
            literal = replay_macro_member(macro, leaf_tail)
            if (
                literal.input_packet != member_input
                or literal.output_packet != member_output
            ):
                raise AssertionError("canonical literal leaf replay disagrees")
            previous_output = member_output
            lower_links += literal.linked_members_replayed
            gate_macros += literal.literal_gate_macros_replayed

        shared_bits: int | None = None
        increases: bool | None = None
        if previous_packet is not None:
            difference = first_packet - previous_packet
            if difference == 0:
                raise AssertionError("canonical packet unexpectedly stabilized")
            shared_bits = v2(abs(difference))
            increases = difference > 0
            if not increases:
                raise AssertionError("canonical packet did not grow with depth")
        packet_decimal = str(first_packet)
        start_decimal = str(ordinary_start)
        audits.append(
            CanonicalDepthAudit(
                depth=depth,
                leaf_macro_members=len(leaves),
                one_cell_leaves=sum(cells == 1 for cells, _ in leaves),
                two_cell_leaves=sum(cells == 2 for cells, _ in leaves),
                input_packet_bits=first_packet.bit_length(),
                input_packet_decimal_digits=len(packet_decimal),
                input_packet_decimal_sha256=hashlib.sha256(
                    packet_decimal.encode()
                ).hexdigest(),
                ordinary_start_bits=ordinary_start.bit_length(),
                ordinary_start_decimal_digits=len(start_decimal),
                ordinary_start_decimal_sha256=hashlib.sha256(
                    start_decimal.encode()
                ).hexdigest(),
                shared_low_packet_bits_with_previous_depth=shared_bits,
                strictly_larger_than_previous_depth=increases,
                lower_linked_members_replayed=lower_links,
                literal_gate_macros_replayed=gate_macros,
            )
        )
        previous_packet = first_packet
    return audits


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(
    levels: int,
    max_branch_cells: int,
    tails_per_branch: int,
    max_background_alphabet: int,
    meta_quine_choice_bound: int,
    meta_quine_depth: int,
) -> dict[str, object]:
    if min(levels - 1, max_branch_cells, tails_per_branch) < 1:
        raise ValueError("invalid hierarchy or replay bounds")
    hierarchy, steps = construct_hierarchy(levels)
    canonical = canonical_depth_audit(hierarchy, steps)
    alphabet = adjacent_background_alphabet(max_background_alphabet)
    alternative_words = alternative_choice_words()
    meta_quine = canonical_meta_quine_search(
        meta_quine_choice_bound, meta_quine_depth
    )
    direct_checks = 0
    replays: list[AbstractReplay] = []
    branch_samples: list[dict[str, object]] = []
    for step in steps:
        for cells in range(1, max_branch_cells + 1):
            candidate = direct_nested_macro(step, cells)
            direct_checks += 1
            for tail in range(tails_per_branch):
                replays.append(replay_parent_member(step, candidate, tail))
            if cells in {1, max_branch_cells}:
                branch_samples.append(
                    {
                        "child_level": step.child_level,
                        **asdict(candidate),
                    }
                )
    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "six exact finite renormalization levels by default; phase and "
            "sign-flip identities; bounded direct-branch comparison and "
            "parent-macro replay; bounded adjacent-background alphabet; "
            "no infinite hierarchy or ordinary orbit"
        ),
        "bounds": {
            "levels": levels,
            "branch_cells_per_step": [1, max_branch_cells],
            "tails_per_branch": tails_per_branch,
            "level_one_background_alphabet": [1, max_background_alphabet],
            "meta_quine_choice_alphabet": [1, meta_quine_choice_bound],
            "meta_quine_depth": meta_quine_depth,
        },
        "level_count": len(hierarchy),
        "renormalization_step_count": len(steps),
        "collision_signs": [isa.collision_sign for isa in hierarchy],
        "binary_cell_widths": [isa.binary_cell for isa in hierarchy],
        "direct_child_branches_checked": direct_checks,
        "parent_macro_members_replayed": len(replays),
        "parent_macro_blocks_replayed": sum(
            replay.parent_macro_members_replayed for replay in replays
        ),
        "canonical_tail_zero_depths_replayed": len(canonical),
        "canonical_leaf_macro_members_replayed": sum(
            audit.leaf_macro_members for audit in canonical
        ),
        "canonical_lower_linked_members_replayed": sum(
            audit.lower_linked_members_replayed for audit in canonical
        ),
        "canonical_literal_gate_macros_replayed": sum(
            audit.literal_gate_macros_replayed for audit in canonical
        ),
        "adjacent_background_choices_checked": len(alphabet),
        "canonical_extension_obstruction": (
            "for every positive child K, parent tail = raw_input + "
            "2^(E_B+E_H)*(2^r0*K-1) > 0; recursive canonical "
            "addresses never stabilize"
        ),
        "levels": [asdict(isa) for isa in hierarchy],
        "steps": [asdict(step) for step in steps],
        "branch_samples": branch_samples,
        "replay_samples": [
            asdict(replays[index])
            for index in sorted({0, len(replays) // 2, len(replays) - 1})
        ],
        "canonical_tail_zero_audit": [asdict(audit) for audit in canonical],
        "adjacent_background_alphabet": alphabet,
        "alternative_choice_words": alternative_words,
        "canonical_meta_quine_search": meta_quine,
    }


def selftest() -> None:
    hierarchy, steps = construct_hierarchy(4)
    expected = [8, 23, 77, 254]
    if [isa.binary_cell for isa in hierarchy] != expected:
        raise AssertionError("renormalized cell widths changed")
    if [isa.collision_sign for isa in hierarchy] != [1, -1, 1, -1]:
        raise AssertionError("collision signs no longer alternate")
    for step in steps:
        candidate = direct_nested_macro(step, 1)
        replay_parent_member(step, candidate, 0)
        parent_input_tail(step, 1)
    canonical_depth_audit(hierarchy, steps)
    tiny_quines = canonical_meta_quine_search(2, 2)
    if tiny_quines["nodes_checked"] != 6:
        raise AssertionError("tiny meta-quine tree size changed")


def render(certificate: dict[str, object]) -> str:
    return json.dumps(certificate, indent=2, sort_keys=True) + "\n"


def main() -> None:
    # Level seven exceeds Python's default decimal conversion guard.  The
    # verifier's default six levels stay below it, but permit exact rebuilds
    # of explicitly larger user-selected artifacts.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--levels", type=int, default=6)
    build.add_argument("--max-branch-cells", type=int, default=8)
    build.add_argument("--tails-per-branch", type=int, default=2)
    build.add_argument("--max-background-alphabet", type=int, default=64)
    build.add_argument("--meta-quine-choice-bound", type=int, default=8)
    build.add_argument("--meta-quine-depth", type=int, default=3)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff renormalization selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(
            args.levels,
            args.max_branch_cells,
            args.tails_per_branch,
            args.max_background_alphabet,
            args.meta_quine_choice_bound,
            args.meta_quine_depth,
        )
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["bounds"]
        actual = build_certificate(
            int(bounds["levels"]),
            int(bounds["branch_cells_per_step"][1]),
            int(bounds["tails_per_branch"]),
            int(bounds["level_one_background_alphabet"][1]),
            int(bounds["meta_quine_choice_alphabet"][1]),
            int(bounds["meta_quine_depth"]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff renormalization artifact: PASS")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Compose saturated compiler edges through one ordinary splash relay.

The direct saturated-bridge graph has no two-edge path in the committed source
box.  This checker allows one ordinary parity-complete splash between two
saturated edges.  Dyadic and triadic family strides are coprime, so every
spatially compatible pair has a complete affine intersection; the checker
constructs that intersection and literally replays two members.

The resulting finite relay graph contains one self-loop and no other directed
cycle.  Repeating that loop repeats a fixed valuation block, so the existing
eventually-periodic obstruction rules it out as an ordinary infinite glider.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from math import gcd
from pathlib import Path

from complete_splash_isa import (
    CompleteSplashGate,
    link_instruction,
    ordinary_continuation,
    verify_member,
)
from complete_u_bridge_graph import Shape


SCHEMA = "collatz-complete-u-relay-graph-v1"
UPSTREAM = Path(__file__).with_name("complete_u_bridge_graph_audit.json")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gate_word(gate: CompleteSplashGate) -> list[int]:
    word = [1] * gate.amp_ticks
    word.append(1 + gate.to_plus_extra)
    word.extend([2] * gate.clean_ticks)
    if gate.branch == "odd_catcher":
        word.append(1)
    elif gate.terminal_extra is not None:
        word.append(2 + gate.terminal_extra)
    else:
        raise AssertionError("even cleanup lost its terminal extra")
    return word


def intersect_progressions(
    left_base: int,
    left_stride: int,
    right_base: int,
    right_stride: int,
) -> dict[str, int]:
    """Least natural intersection of two coprime affine progressions."""
    if min(left_base, right_base) < 0 or min(left_stride, right_stride) <= 0:
        raise ValueError("progressions must have natural bases and positive strides")
    if gcd(left_stride, right_stride) != 1:
        raise ValueError("relay progressions must have coprime strides")
    left_index = (
        (right_base - left_base)
        * pow(left_stride, -1, right_stride)
    ) % right_stride
    common = left_base + left_stride * left_index
    if common < right_base:
        period = left_stride * right_stride
        lifts = (right_base - common + period - 1) // period
        left_index += right_stride * lifts
        common += period * lifts
    right_index = (common - right_base) // right_stride
    if common != left_base + left_stride * left_index:
        raise AssertionError("left progression intersection failed")
    if common != right_base + right_stride * right_index:
        raise AssertionError("right progression intersection failed")
    return {
        "common_base": common,
        "common_stride": left_stride * right_stride,
        "left_index_base": left_index,
        "left_index_stride": right_stride,
        "right_index_base": right_index,
        "right_index_stride": left_stride,
    }


def selected_indices(hit: dict[str, object]) -> tuple[dict[str, int], dict[str, int]]:
    return (
        {
            "base": int(hit["source_index_base"]),
            "stride": int(hit["source_index_stride"]),
        },
        {
            "base": int(hit["target_index_base"]),
            "stride": int(hit["target_index_stride"]),
        },
    )


def compose_relay(
    left_id: int,
    left: dict[str, object],
    right_id: int,
    right: dict[str, object],
) -> dict[str, object]:
    """Compile ``A -U-> B -ordinary-> C -U-> D`` on one affine tail."""
    gate_a = Shape(**left["source_shape"]).build()
    gate_b = Shape(**left["target_shape"]).build()
    gate_c = Shape(**right["source_shape"]).build()
    gate_d = Shape(**right["target_shape"]).build()
    if gate_b.output_gap != gate_c.input_gap:
        raise ValueError("relay shapes do not have matching sparse gaps")

    a_progression, b_incoming = selected_indices(left)
    c_saturated, d_progression = selected_indices(right)
    ordinary = link_instruction(gate_b, gate_c)
    b_outgoing = {
        "base": ordinary.source_index_base,
        "stride": ordinary.source_index_stride,
    }
    c_incoming = {
        "base": ordinary.target_index_base,
        "stride": ordinary.target_index_stride,
    }

    first_intersection = intersect_progressions(
        b_incoming["base"],
        b_incoming["stride"],
        b_outgoing["base"],
        b_outgoing["stride"],
    )
    # If v parameterizes the first intersection, the ordinary target index is
    # c0 + cStride * (u0 + bIncomingStride*v).
    raw_c_base = (
        c_incoming["base"]
        + c_incoming["stride"] * first_intersection["right_index_base"]
    )
    raw_c_stride = (
        c_incoming["stride"] * first_intersection["right_index_stride"]
    )
    second_intersection = intersect_progressions(
        raw_c_base,
        raw_c_stride,
        c_saturated["base"],
        c_saturated["stride"],
    )

    v_base = second_intersection["left_index_base"]
    v_stride = second_intersection["left_index_stride"]
    first_t_base = first_intersection["left_index_base"]
    first_t_stride = first_intersection["left_index_stride"]
    first_u_base = first_intersection["right_index_base"]
    first_u_stride = first_intersection["right_index_stride"]
    q_base = second_intersection["right_index_base"]
    q_stride = second_intersection["right_index_stride"]

    t_base = first_t_base + first_t_stride * v_base
    t_stride = first_t_stride * v_stride
    u_base = first_u_base + first_u_stride * v_base
    u_stride = first_u_stride * v_stride

    progressions = {
        "A_index": {
            "base": a_progression["base"] + a_progression["stride"] * t_base,
            "stride": a_progression["stride"] * t_stride,
        },
        "B_index": {
            "base": b_incoming["base"] + b_incoming["stride"] * t_base,
            "stride": b_incoming["stride"] * t_stride,
        },
        "C_index": {
            "base": second_intersection["common_base"],
            "stride": second_intersection["common_stride"],
        },
        "D_index": {
            "base": d_progression["base"] + d_progression["stride"] * q_base,
            "stride": d_progression["stride"] * q_stride,
        },
        "ordinary_relay_tail": {"base": u_base, "stride": u_stride},
    }

    state_rows: list[list[int]] = []
    for tail in (0, 1):
        indices = {
            name: values["base"] + values["stride"] * tail
            for name, values in progressions.items()
            if name.endswith("_index")
        }
        start_a, end_a = verify_member(gate_a, indices["A_index"])
        start_b, end_b = verify_member(gate_b, indices["B_index"])
        start_c, end_c = verify_member(gate_c, indices["C_index"])
        start_d, end_d = verify_member(gate_d, indices["D_index"])
        if not (end_a == start_b and end_b == start_c and end_c == start_d):
            raise AssertionError("relay gate endpoints do not link")
        states = [start_a, end_a, end_b, end_c, end_d]
        if not all(x < y for x, y in zip(states, states[1:])):
            raise AssertionError("relay gate sequence is not all outward")
        state_rows.append(states)

    state_names = ["start_A", "after_A", "after_B", "after_C", "after_D"]
    state_affine = {
        name: {
            "base": state_rows[0][index],
            "stride": state_rows[1][index] - state_rows[0][index],
        }
        for index, name in enumerate(state_names)
    }
    bases = [state_affine[name]["base"] for name in state_names]
    strides = [state_affine[name]["stride"] for name in state_names]
    if not all(x < y for x, y in zip(bases, bases[1:])):
        raise AssertionError("relay base states are not outward")
    if not all(x <= y for x, y in zip(strides, strides[1:])):
        raise AssertionError("relay strides do not preserve outwardness")

    return {
        "from_node": left_id,
        "to_node": right_id,
        "ordinary_link": asdict(ordinary),
        "selected_index_progressions": progressions,
        "state_affine_formulas": state_affine,
        "all_four_gates_universally_outward": True,
        "shape_word": [
            asdict(Shape.of(gate)) for gate in (gate_a, gate_b, gate_c, gate_d)
        ],
        "valuation_word": (
            gate_word(gate_a)
            + gate_word(gate_b)
            + gate_word(gate_c)
            + gate_word(gate_d)
        ),
    }


def strongly_connected_components(
    node_count: int, adjacency: dict[int, list[int]]
) -> list[list[int]]:
    reach = [[False] * node_count for _ in range(node_count)]
    for node in range(node_count):
        reach[node][node] = True
        for target in adjacency.get(node, []):
            reach[node][target] = True
    for middle in range(node_count):
        for left in range(node_count):
            if reach[left][middle]:
                for right in range(node_count):
                    reach[left][right] = reach[left][right] or reach[middle][right]
    remaining = set(range(node_count))
    components: list[list[int]] = []
    while remaining:
        first = min(remaining)
        component = sorted(
            node
            for node in remaining
            if reach[first][node] and reach[node][first]
        )
        components.append(component)
        remaining.difference_update(component)
    return components


def build_certificate() -> dict[str, object]:
    upstream = json.loads(UPSTREAM.read_text())
    hits = [
        hit
        for hit in upstream["hits"]
        if hit["target_selected_family_universally_outward"]
    ]
    if len(hits) != 11:
        raise AssertionError("upstream outward bridge count changed")

    nodes = [
        {
            "node": node,
            "source_shape": hit["source_shape"],
            "target_shape": hit["target_shape"],
            "address_bits": hit["address_bits"],
            "source_index_base": hit["source_index_base"],
            "target_index_base": hit["target_index_base"],
        }
        for node, hit in enumerate(hits)
    ]
    transitions: list[dict[str, object]] = []
    adjacency: dict[int, list[int]] = {node: [] for node in range(len(hits))}
    for left_id, left in enumerate(hits):
        target = Shape(**left["target_shape"]).build()
        for right_id, right in enumerate(hits):
            source = Shape(**right["source_shape"]).build()
            if target.output_gap == source.input_gap:
                adjacency[left_id].append(right_id)
                transitions.append(
                    compose_relay(left_id, left, right_id, right)
                )

    if len(transitions) != 22:
        raise AssertionError("ordinary-relay edge count changed")
    components = strongly_connected_components(len(hits), adjacency)
    cyclic_components = [
        component
        for component in components
        if len(component) > 1
        or component[0] in adjacency.get(component[0], [])
    ]
    if cyclic_components != [[3]]:
        raise AssertionError("relay graph cycle classification changed")

    self_loop = next(
        transition
        for transition in transitions
        if transition["from_node"] == 3 and transition["to_node"] == 3
    )
    self_loop_seed = self_loop["state_affine_formulas"]["start_A"]["base"]
    continuation = ordinary_continuation(self_loop_seed)
    if not continuation["reached_one"]:
        raise AssertionError("relay self-loop witness unexpectedly survived")

    minimum = min(
        transitions,
        key=lambda transition: transition["state_affine_formulas"]["start_A"][
            "base"
        ],
    )
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact one-ordinary-gate relay graph on the 11 two-outward "
            "saturated edges from the stated upstream bounded source search; "
            "not an all-shape or multi-relay exclusion"
        ),
        "upstream": {
            "artifact": UPSTREAM.name,
            "sha256": sha256(UPSTREAM),
            "two_outward_nodes": len(hits),
        },
        "nodes": nodes,
        "adjacency": {str(node): targets for node, targets in adjacency.items()},
        "relay_edges": len(transitions),
        "transitions": transitions,
        "strongly_connected_components": components,
        "cyclic_components": cyclic_components,
        "only_infinite_shape_path": (
            "eventually node 3 self-loop; hence an eventually periodic "
            "valuation-word schedule"
        ),
        "node_3_self_loop": self_loop
        | {
            "canonical_continuation": continuation,
        },
        "least_canonical_relay": {
            "from_node": minimum["from_node"],
            "to_node": minimum["to_node"],
            "states": [
                values["base"]
                for values in minimum["state_affine_formulas"].values()
            ],
        },
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != build_certificate():
        raise ValueError("complete U-relay graph artifact failed reconstruction")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_certificate()
        print("complete_u_relay_graph selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(build_certificate(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("complete_u_relay_graph artifact: PASS")


if __name__ == "__main__":
    main()

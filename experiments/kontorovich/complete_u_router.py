#!/usr/bin/env python3
"""A universal outward catcher routes between saturated compiler blocks.

For every incoming rail length ``r>=0`` and desired output gap ``L>=1``, the
odd catcher shape ``(r,s,a,L)=(r,0,1,L)`` has word ``[1]^r ++ [2,1]``.  Its
leading multiplier is ``3^(r+2)/2^(r+3)>1``, so every legal member is outward.

Using one such gate between two ordinary affine links, this checker routes
every one of the 11 two-outward saturated compiler nodes in the committed
bridge artifact to every other.  It constructs and literally replays the
complete 11x11 family of five-gate transitions.  This proves finite compiler
expressivity, not that an infinite nested tail is an ordinary integer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from pathlib import Path

from complete_splash_isa import (
    CompleteSplashGate,
    link_instruction,
    odd_gap_catcher,
    ordinary_continuation,
    verify_member,
)
from complete_u_bridge_graph import Shape
from complete_u_relay_graph import gate_word, intersect_progressions


SCHEMA = "collatz-complete-u-router-v1"
UPSTREAM = Path(__file__).with_name("complete_u_bridge_graph_audit.json")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hit_progressions(
    hit: dict[str, object]
) -> tuple[dict[str, int], dict[str, int]]:
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


def restrict_and_map(
    path: dict[str, dict[str, int]],
    source_name: str,
    required_source: dict[str, int],
    target_name: str,
    required_target: dict[str, int],
) -> dict[str, dict[str, int]]:
    """Restrict one affine path coordinate and append its linked target."""
    current = path[source_name]
    intersection = intersect_progressions(
        current["base"],
        current["stride"],
        required_source["base"],
        required_source["stride"],
    )
    old_parameter_base = intersection["left_index_base"]
    old_parameter_stride = intersection["left_index_stride"]
    link_parameter_base = intersection["right_index_base"]
    link_parameter_stride = intersection["right_index_stride"]
    restricted = {
        name: {
            "base": values["base"] + values["stride"] * old_parameter_base,
            "stride": values["stride"] * old_parameter_stride,
        }
        for name, values in path.items()
    }
    restricted[target_name] = {
        "base": (
            required_target["base"]
            + required_target["stride"] * link_parameter_base
        ),
        "stride": required_target["stride"] * link_parameter_stride,
    }
    if restricted[source_name] != {
        "base": intersection["common_base"],
        "stride": intersection["common_stride"],
    }:
        raise AssertionError("path restriction disagrees with intersection")
    return restricted


def ordinary_requirements(
    source: CompleteSplashGate, target: CompleteSplashGate
) -> tuple[dict[str, int], dict[str, int], dict[str, int]]:
    link = link_instruction(source, target)
    return (
        {
            "base": link.source_index_base,
            "stride": link.source_index_stride,
        },
        {
            "base": link.target_index_base,
            "stride": link.target_index_stride,
        },
        asdict(link),
    )


def router_outward_at(r: int, output_gap: int) -> bool:
    """Exact two-coefficient audit for one universal router shape."""
    router = odd_gap_catcher(r, 0, 1, output_gap)
    start0, end0 = verify_member(router, 0)
    start1, end1 = verify_member(router, 1)
    return end0 > start0 and end1 - end0 >= start1 - start0


def compile_transition(
    left_id: int,
    left: dict[str, object],
    right_id: int,
    right: dict[str, object],
) -> dict[str, object]:
    """Compile ``A -U-> B -> R -> C -U-> D`` on an affine tail."""
    gate_a = Shape(**left["source_shape"]).build()
    gate_b = Shape(**left["target_shape"]).build()
    gate_c = Shape(**right["source_shape"]).build()
    gate_d = Shape(**right["target_shape"]).build()
    router = odd_gap_catcher(
        gate_b.output_gap - 1,
        0,
        1,
        gate_c.input_gap,
    )
    if not router_outward_at(router.amp_ticks, router.output_gap):
        raise AssertionError("universal router lost outwardness")

    a_progression, b_progression = hit_progressions(left)
    c_saturated, d_progression = hit_progressions(right)
    path = {"A_index": a_progression, "B_index": b_progression}

    b_required, router_incoming, first_link = ordinary_requirements(gate_b, router)
    path = restrict_and_map(
        path, "B_index", b_required, "R_index", router_incoming
    )
    router_required, c_incoming, second_link = ordinary_requirements(router, gate_c)
    path = restrict_and_map(
        path, "R_index", router_required, "C_index", c_incoming
    )
    path = restrict_and_map(
        path, "C_index", c_saturated, "D_index", d_progression
    )

    gates = [gate_a, gate_b, router, gate_c, gate_d]
    index_names = ["A_index", "B_index", "R_index", "C_index", "D_index"]
    state_rows: list[list[int]] = []
    for tail in (0, 1):
        indices = [
            path[name]["base"] + path[name]["stride"] * tail
            for name in index_names
        ]
        states: list[int] = []
        previous_endpoint: int | None = None
        for gate, index in zip(gates, indices):
            start, endpoint = verify_member(gate, index)
            if previous_endpoint is not None and previous_endpoint != start:
                raise AssertionError("router transition broke gate linkage")
            if not start < endpoint:
                raise AssertionError("router transition contains a shrinking gate")
            if not states:
                states.append(start)
            states.append(endpoint)
            previous_endpoint = endpoint
        state_rows.append(states)

    state_names = [
        "start_A",
        "after_A",
        "after_B",
        "after_router",
        "after_C",
        "after_D",
    ]
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
        raise AssertionError("router base states are not strictly outward")
    if not all(x <= y for x, y in zip(strides, strides[1:])):
        raise AssertionError("router state strides do not preserve outwardness")

    return {
        "from_node": left_id,
        "to_node": right_id,
        "router_shape": asdict(Shape.of(router)),
        "first_ordinary_link": first_link,
        "second_ordinary_link": second_link,
        "selected_index_progressions": path,
        "state_affine_formulas": state_affine,
        "all_five_gates_universally_outward": True,
        "valuation_word": sum((gate_word(gate) for gate in gates), []),
    }


def build_certificate() -> dict[str, object]:
    upstream = json.loads(UPSTREAM.read_text())
    hits = [
        hit
        for hit in upstream["hits"]
        if hit["target_selected_family_universally_outward"]
    ]
    if len(hits) != 11:
        raise AssertionError("upstream two-outward node count changed")

    router_shapes = {
        (
            Shape(**left["target_shape"]).build().output_gap - 1,
            Shape(**right["source_shape"]).build().input_gap,
        )
        for left in hits
        for right in hits
    }
    if not all(router_outward_at(r, output_gap) for r, output_gap in router_shapes):
        raise AssertionError("a required router shape is not outward")

    transitions = [
        compile_transition(left_id, left, right_id, right)
        for left_id, left in enumerate(hits)
        for right_id, right in enumerate(hits)
    ]
    if len(transitions) != 121:
        raise AssertionError("complete router graph is not 11 by 11")
    adjacency = {str(node): list(range(11)) for node in range(11)}
    minimum = min(
        transitions,
        key=lambda transition: transition["state_affine_formulas"]["start_A"][
            "base"
        ],
    )
    minimum_seed = minimum["state_affine_formulas"]["start_A"]["base"]
    continuation = ordinary_continuation(minimum_seed)
    if not continuation["reached_one"]:
        raise AssertionError("least router witness unexpectedly survived")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact two-ordinary-link router on the 11 two-outward saturated "
            "nodes from the stated upstream source box; complete finite path "
            "expressivity, not an ordinary infinite seed"
        ),
        "upstream": {
            "artifact": UPSTREAM.name,
            "sha256": sha256(UPSTREAM),
            "nodes": len(hits),
        },
        "universal_router": {
            "shape": "odd_catcher(r,0,1,L)",
            "word": "[1]^r ++ [2,1]",
            "odd_steps": "r+2",
            "halvings": "r+3",
            "outward_inequality": "3^(r+2)>2^(r+3) for every r>=0",
            "output_gap": "arbitrary L>=1",
            "required_shapes_in_graph": [
                {"amp_ticks": r, "output_gap": output_gap}
                for r, output_gap in sorted(router_shapes)
            ],
            "all_required_shape_families_universally_outward": True,
        },
        "adjacency": adjacency,
        "transitions": len(transitions),
        "complete_directed_graph": True,
        "supports_arbitrary_finite_node_words": True,
        "transition_certificates": transitions,
        "least_canonical_transition": {
            "from_node": minimum["from_node"],
            "to_node": minimum["to_node"],
            "states": [
                values["base"]
                for values in minimum["state_affine_formulas"].values()
            ],
            "continuation": continuation,
        },
        "infinite_caveat": (
            "an infinite aperiodic node word determines nested dyadic "
            "cylinders and generally a 2-adic tail; ordinary positive-integer "
            "realization remains unproved"
        ),
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != build_certificate():
        raise ValueError("complete U-router artifact failed reconstruction")


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
        print("complete_u_router selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(build_certificate(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("complete_u_router artifact: PASS")


if __name__ == "__main__":
    main()

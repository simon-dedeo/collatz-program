#!/usr/bin/env python3
"""Exact finite KL bridge for literal compiled returning-glider macros.

The companion core-boundary audit proves that ``2*EC17 core`` follows a
ternary odometer clock but does *not* follow KL edges.  This worker uses the
correct semantic route instead:

1. construct a finite returning glider macro;
2. replay its exact break-off states;
3. expand every break-off step through ``router_breakoff.literal_step``;
4. concatenate the linked accelerated-Collatz words;
5. expand those words into every one-halving Syracuse state;
6. sample successive states congruent to 2 modulo 3 and reverse them;
7. require every reversed pair to be exactly one KL principal edge;
8. only then compute finite rational edge deviations from a stored, exactly
   verified KL certificate vector.

The stored KL certificate is a feasible subeigenvector with certified
rational *lower* branch weights, not an exact critical eigenvector.  Hence
this worker does not assume the critical calibration inequality.  It checks
the required inequality separately, in exact rational arithmetic, on every
audited edge and refuses to emit a tax row if any check fails.

Everything here is finite.  The artifact claims no infinite EC17 execution,
Collatz counterexample, critical-eigenvector identity, or precision-uniform
tax theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
KL_DIR = HERE.parent / "kl"
if str(KL_DIR) not in sys.path:
    sys.path.insert(0, str(KL_DIR))

import certify  # type: ignore  # local exact KL certificate verifier
from breakoff_ether_glider import components, glider_macro, machines, replay_macro_member
from breakoff_ether_period3_kl_bridge import schedule_audit as core_schedule_audit
from router_breakoff import literal_step, v2


SCHEMA = "collatz-breakoff-ether-glider-kl-bridge-v1"
DEFAULT_CERTIFICATE = KL_DIR / "cert_k12.json"
CORE_BRIDGE_WORKER = HERE / "breakoff_ether_period3_kl_bridge.py"
CORE_BRIDGE_ARTIFACT = HERE / "breakoff_ether_period3_kl_bridge_audit.json"


@dataclass(frozen=True)
class KLEdge:
    kind: str
    source: int
    target: int


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_record(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
    }


def syracuse_step(state: int) -> int:
    if state < 1:
        raise ValueError("one-halving Syracuse trace requires a positive state")
    return state // 2 if state % 2 == 0 else (3 * state + 1) // 2


def classify_exact_kl_edge(source: int, target: int) -> str:
    """Classify a reversed 2-mod-3 visit pair by exact integer equality."""

    hits: list[str] = []
    if target == 4 * source:
        hits.append("transport")
    if source % 9 == 2 and 3 * target == 4 * source - 2:
        hits.append("r2")
    if source % 9 == 8 and 3 * target == 2 * source - 1:
        hits.append("r8")
    if len(hits) != 1:
        raise AssertionError(
            "sampled Syracuse visits do not determine exactly one KL edge: "
            f"source={source}, target={target}, hits={hits}"
        )
    return hits[0]


def packet_boundary(packet: int) -> tuple[int, int, int]:
    """Return (defect tail, break-off state, literal Collatz state) for K."""

    if packet < 1:
        raise ValueError("packet boundary requires a positive packet")
    data = components()
    ether = machines()[0]
    tail = (
        data.defect_input_constant
        + (1 << data.defect_input_stride_exponent) * packet
    )
    breakoff_state = ether.member(tail)[3]
    segment = literal_step(breakoff_state)
    if segment is None:
        raise AssertionError("packet boundary has no literal Collatz semantics")
    return tail, breakoff_state, segment.collatz_start


def trace_breakoff_macro(ether_cells: int, tail: int) -> dict[str, object]:
    macro = glider_macro(ether_cells)
    replay = replay_macro_member(macro, tail)

    source_tail, source_breakoff, source_collatz = packet_boundary(
        replay.input_packet
    )
    target_tail, target_breakoff, target_collatz = packet_boundary(
        replay.output_packet
    )
    if source_tail != replay.defect_input_tail:
        raise AssertionError("packet coordinate missed the compiled defect input")
    if source_breakoff != replay.ordinary_start:
        raise AssertionError("packet coordinate missed the source break-off state")
    if target_tail != replay.exposed_boundary_tail:
        raise AssertionError("output packet missed the exposed defect boundary")
    if target_breakoff != replay.ordinary_endpoint:
        raise AssertionError("packet coordinate missed the target break-off state")

    breakoff_state = replay.ordinary_start
    literal_segments = []
    for _ in range(replay.literal_gate_macros_replayed):
        segment = literal_step(breakoff_state)
        if segment is None:
            raise AssertionError("compiled break-off state lost literal semantics")
        if segment.k != breakoff_state:
            raise AssertionError("literal segment starts at another break-off state")
        literal_segments.append(segment)
        breakoff_state = segment.next_k
    if breakoff_state != replay.ordinary_endpoint:
        raise AssertionError("literal break-off trace missed the compiled endpoint")
    if len(literal_segments) != 2 * (ether_cells + 2):
        raise AssertionError("unexpected number of literal gate macros")
    if any(
        literal_segments[index].collatz_endpoint
        != literal_segments[index + 1].collatz_start
        for index in range(len(literal_segments) - 1)
    ):
        raise AssertionError("successive literal Collatz segments do not link")

    collatz_state = literal_segments[0].collatz_start
    one_halving_states = [collatz_state]
    valuation_word: list[int] = []
    segment_rows: list[dict[str, object]] = []
    for index, segment in enumerate(literal_segments):
        if collatz_state != segment.collatz_start:
            raise AssertionError("combined Collatz trace lost a segment boundary")
        if (
            len(segment.valuation_word) < 2
            or segment.valuation_word[-2:] != [2, 1]
            or any(value != 1 for value in segment.valuation_word[:-2])
        ):
            raise AssertionError("literal router word lost its [1]^r+[2,1] form")
        segment_start_step = len(one_halving_states) - 1
        for valuation in segment.valuation_word:
            if collatz_state % 2 != 1:
                raise AssertionError("accelerated valuation starts at an even state")
            numerator = 3 * collatz_state + 1
            if v2(numerator) != valuation:
                raise AssertionError("stored accelerated valuation is not exact")
            valuation_word.append(valuation)
            for _ in range(valuation):
                collatz_state = syracuse_step(collatz_state)
                one_halving_states.append(collatz_state)
        if collatz_state != segment.collatz_endpoint:
            raise AssertionError("one-halving expansion missed a segment endpoint")
        segment_rows.append(
            {
                "index": index,
                "breakoff_source": str(segment.k),
                "breakoff_target": str(segment.next_k),
                "collatz_source": str(segment.collatz_start),
                "collatz_target": str(segment.collatz_endpoint),
                "valuation_word": list(segment.valuation_word),
                "one_halving_start_index": segment_start_step,
                "one_halving_end_index": len(one_halving_states) - 1,
            }
        )

    if collatz_state != literal_segments[-1].collatz_endpoint:
        raise AssertionError("combined literal Collatz trace missed its endpoint")
    if literal_segments[0].collatz_start != source_collatz:
        raise AssertionError("literal trace source is not C(input_packet)")
    if literal_segments[-1].collatz_endpoint != target_collatz:
        raise AssertionError("literal trace endpoint is not C(output_packet)")
    if len(one_halving_states) - 1 != sum(valuation_word):
        raise AssertionError("one-halving length disagreed with valuation sum")

    sampled = [state for state in one_halving_states if state % 3 == 2]
    if sampled[0] != literal_segments[0].collatz_start:
        raise AssertionError("literal Collatz source is not the first sampled state")
    if sampled[-1] != literal_segments[-1].collatz_endpoint:
        raise AssertionError("literal Collatz endpoint is not the last sampled state")

    # Reverse the forward visit list so edge endpoints concatenate in the KL
    # predecessor direction: v_N -> v_(N-1) -> ... -> v_0.
    edges = [
        KLEdge(
            classify_exact_kl_edge(sampled[index + 1], sampled[index]),
            sampled[index + 1],
            sampled[index],
        )
        for index in range(len(sampled) - 2, -1, -1)
    ]
    if edges:
        if edges[0].source != sampled[-1] or edges[-1].target != sampled[0]:
            raise AssertionError("reversed KL path has the wrong endpoints")
        if any(edges[index].target != edges[index + 1].source
               for index in range(len(edges) - 1)):
            raise AssertionError("reversed KL edges do not concatenate")

    counts = {
        kind: sum(edge.kind == kind for edge in edges)
        for kind in ("transport", "r2", "r8")
    }
    odd_count = counts["r2"] + counts["r8"]
    one_halving_count = (
        2 * counts["transport"] + 2 * counts["r2"] + counts["r8"]
    )
    if odd_count != len(valuation_word):
        raise AssertionError("KL chord count disagreed with accelerated-step count")
    if one_halving_count != len(one_halving_states) - 1:
        raise AssertionError("KL edge lengths disagreed with the literal trace")
    expected_r2 = len(literal_segments)
    expected_r8 = sum(len(segment.valuation_word) - 1
                      for segment in literal_segments)
    if counts != {"transport": 0, "r2": expected_r2, "r8": expected_r8}:
        raise AssertionError("KL counts lost the router-word structural formula")

    return {
        "ether_cells": ether_cells,
        "tail": tail,
        "input_packet": str(replay.input_packet),
        "output_packet": str(replay.output_packet),
        "packet_boundary_formula": (
            "tail=-10941+2^20*K; breakoff=E.member(tail)[3]; "
            "C(K)=literal_step(breakoff).collatz_start"
        ),
        "source_defect_tail": str(source_tail),
        "target_defect_tail": str(target_tail),
        "breakoff_source": str(replay.ordinary_start),
        "breakoff_target": str(replay.ordinary_endpoint),
        "breakoff_steps": len(literal_segments),
        "expected_breakoff_steps": replay.literal_gate_macros_replayed,
        "collatz_source": str(literal_segments[0].collatz_start),
        "collatz_target": str(literal_segments[-1].collatz_endpoint),
        "collatz_source_equals_C_input_packet": True,
        "collatz_target_equals_C_output_packet": True,
        "collatz_source_mod_3": literal_segments[0].collatz_start % 3,
        "collatz_target_mod_3": literal_segments[-1].collatz_endpoint % 3,
        "accelerated_steps": len(valuation_word),
        "one_halving_steps": len(one_halving_states) - 1,
        "sampled_2_mod_3_states": len(sampled),
        "kl_edges": len(edges),
        "kl_edge_counts": counts,
        "router_word_shape": "[1]^r+[2,1]",
        "structural_kl_counts_verified": True,
        "valuation_word": valuation_word,
        "segment_rows": segment_rows,
        "sampled_states": [str(state) for state in sampled],
        "edge_objects": edges,
    }


def load_and_verify_certificate(path: Path) -> dict[str, object]:
    certificate = json.loads(path.read_text())
    required = {"k", "A", "SC_L", "B2", "B8", "SC_W", "SC_C", "C"}
    if not required.issubset(certificate):
        raise ValueError("KL certificate is missing required fields")
    if certificate["SC_L"] != certify.SC_L:
        raise AssertionError("certificate lambda scale disagrees with verifier")
    if certificate["SC_W"] != certify.SC_W:
        raise AssertionError("certificate weight scale disagrees with verifier")
    if certificate["SC_C"] != certify.SC_C:
        raise AssertionError("certificate potential scale disagrees with verifier")
    result = certify.verify_exact(
        int(certificate["k"]),
        int(certificate["A"]),
        int(certificate["B2"]),
        int(certificate["B8"]),
        [int(value) for value in certificate["C"]],
        verbose=False,
    )
    if not result["ok"]:
        raise AssertionError(f"stored KL certificate failed exact verification: {result}")
    return certificate


def potential_index(residue: int, modulus: int) -> int:
    residue %= modulus
    if residue % 3 != 2:
        raise AssertionError("KL potential lookup left Y_k")
    return (residue - 2) // 3


def chord_fiber(edge: KLEdge, modulus: int) -> tuple[int, int, int]:
    coarse_modulus = modulus // 3
    source = edge.source % modulus
    if edge.kind == "r2":
        base = ((4 * source - 2) // 3) % coarse_modulus
    elif edge.kind == "r8":
        base = ((2 * source - 1) // 3) % coarse_modulus
    else:
        raise ValueError("transport edge has no chord fiber")
    result = (base, base + coarse_modulus, base + 2 * coarse_modulus)
    if edge.target % modulus not in result:
        raise AssertionError("literal chord target is not a full KL lift")
    return result


def calibrate_trace(
    trace: dict[str, object], certificate: dict[str, object]
) -> dict[str, object]:
    k = int(certificate["k"])
    modulus = 3**k
    C = [int(value) for value in certificate["C"]]
    A = int(certificate["A"])
    scale_lambda = int(certificate["SC_L"])
    scale_weight = int(certificate["SC_W"])
    weights = {
        "transport": Fraction(scale_lambda**2, A**2),
        "r2": Fraction(int(certificate["B2"]), scale_weight),
        "r8": Fraction(int(certificate["B8"]), scale_weight),
    }

    edges: Sequence[KLEdge] = trace["edge_objects"]  # type: ignore[assignment]
    edge_rows: list[dict[str, object]] = []
    weight_product = Fraction(1)
    deviation_product = Fraction(1)
    for index, edge in enumerate(edges):
        source_residue = edge.source % modulus
        target_residue = edge.target % modulus
        source_potential = C[potential_index(source_residue, modulus)]
        target_potential = C[potential_index(target_residue, modulus)]
        weight = weights[edge.kind]
        if edge.kind == "transport":
            if target_residue != 4 * source_residue % modulus:
                raise AssertionError("literal transport failed at certificate precision")
            fiber: tuple[int, ...] = ()
            minimum = target_potential
            deviation = Fraction(1)
        else:
            fiber = chord_fiber(edge, modulus)
            fiber_potentials = tuple(
                C[potential_index(residue, modulus)] for residue in fiber
            )
            minimum = min(fiber_potentials)
            deviation = Fraction(target_potential, minimum)

        left = weight * target_potential
        right = deviation * source_potential
        if left > right:
            raise AssertionError(
                "stored feasible vector does not calibrate this literal edge; "
                "tax row refused"
            )
        margin = right - left
        weight_product *= weight
        deviation_product *= deviation
        edge_rows.append(
            {
                "index": index,
                "kind": edge.kind,
                "source_residue": source_residue,
                "target_residue": target_residue,
                "source_potential_integer": str(source_potential),
                "target_potential_integer": str(target_potential),
                "fiber_residues": list(fiber),
                "fiber_minimum_potential_integer": str(minimum),
                "selected_lift": deviation == 1,
                "certified_rational_lower_weight": fraction_record(weight),
                "deviation": fraction_record(deviation),
                "edge_inequality_margin": fraction_record(margin),
                "edge_inequality_verified": True,
            }
        )

    if not edges:
        raise AssertionError("literal macro produced an empty KL path")
    path_source_residue = edges[0].source % modulus
    path_target_residue = edges[-1].target % modulus
    path_source_potential = C[potential_index(path_source_residue, modulus)]
    path_target_potential = C[potential_index(path_target_residue, modulus)]
    left_product = weight_product * path_target_potential
    right_product = deviation_product * path_source_potential
    if left_product > right_product:
        raise AssertionError("exact edge products failed to telescope")
    calibrated_slack = right_product / left_product

    counts: dict[str, int] = trace["kl_edge_counts"]  # type: ignore[assignment]
    odd_count = counts["r2"] + counts["r8"]
    one_halving_count = (
        2 * counts["transport"] + 2 * counts["r2"] + counts["r8"]
    )
    leading_multiplier = Fraction(3**odd_count, 2**one_halving_count)
    return {
        "certificate_level": k,
        "certificate_modulus": modulus,
        "path_source_residue": path_source_residue,
        "path_target_residue": path_target_residue,
        "path_source_potential_integer": str(path_source_potential),
        "path_target_potential_integer": str(path_target_potential),
        "edge_rows": edge_rows,
        "all_edge_inequalities_verified": True,
        "weight_product": fraction_record(weight_product),
        "deviation_product": fraction_record(deviation_product),
        "endpoint_potential_ratio_source_over_target": fraction_record(
            Fraction(path_source_potential, path_target_potential)
        ),
        "calibrated_product_slack": fraction_record(calibrated_slack),
        "product_inequality_verified": True,
        "selected_edges": sum(row["selected_lift"] for row in edge_rows),
        "nonselected_edges": sum(not row["selected_lift"] for row in edge_rows),
        "symbolic_odd_steps": odd_count,
        "symbolic_one_halving_steps": one_halving_count,
        "forward_leading_multiplier": fraction_record(leading_multiplier),
        "forward_leading_multiplier_gt_one": leading_multiplier > 1,
    }


def core_boundary_comparison() -> dict[str, object]:
    rows = [core_schedule_audit(depth, 2, (-1, 1, 1)) for depth in (3, 4)]
    return {
        "normalization": "m=2*EC17_core",
        "verdict": "odometer endpoints are not a KL path",
        "tax_ready": False,
        "reason": (
            "at each audited phase, only one source is an R2 edge and one is "
            "an R8 edge; all remaining phase pairs are not KL edges"
        ),
        "phase_counts": [
            {
                "depth": row["depth"],
                "state_count": row["state_count"],
                "counts": [
                    phase["counts_on_macro_orbit"] for phase in row["phase_rows"]
                ],
            }
            for row in rows
        ],
    }


def artifact_sources(certificate_path: Path) -> dict[str, str]:
    paths = {
        "worker": Path(__file__),
        "breakoff_ether_glider": HERE / "breakoff_ether_glider.py",
        "breakoff_delay_gate": HERE / "breakoff_delay_gate.py",
        "router_breakoff": HERE / "router_breakoff.py",
        "complete_splash_isa": HERE / "complete_splash_isa.py",
        "path_compiler": HERE / "path_compiler.py",
        "kl_certify": KL_DIR / "certify.py",
        "kl_certificate": certificate_path,
        "false_core_bridge_worker": CORE_BRIDGE_WORKER,
        "false_core_bridge_artifact": CORE_BRIDGE_ARTIFACT,
    }
    return {name: file_sha256(path) for name, path in paths.items()}


def build_artifact(
    maximum_ether_cells: int,
    tail: int,
    certificate_path: Path,
) -> dict[str, object]:
    if maximum_ether_cells < 1:
        raise ValueError("maximum ether-cell count must be positive")
    if tail < 0:
        raise ValueError("macro tail must be nonnegative")
    certificate_path = certificate_path.resolve()
    certificate = load_and_verify_certificate(certificate_path)
    macro_rows: list[dict[str, object]] = []
    for ether_cells in range(1, maximum_ether_cells + 1):
        trace = trace_breakoff_macro(ether_cells, tail)
        tax = calibrate_trace(trace, certificate)
        trace.pop("edge_objects")
        macro_rows.append(
            {
                "trace": trace,
                "finite_exact_tax": tax,
                "semantic_bridge_verified": True,
                "tax_ready": True,
            }
        )

    return {
        "schema": SCHEMA,
        "scope": (
            "finite literal compiled glider macros only; exact break-off, "
            "Collatz, KL-edge, stored-certificate, and audited path-product "
            "checks at the stated bounds; no infinite orbit, critical "
            "eigenvector, precision-uniform theorem, or counterexample claim"
        ),
        "counterexample": None,
        "bounds": {
            "ether_cells": [1, maximum_ether_cells],
            "tail": tail,
            "certificate_level": int(certificate["k"]),
        },
        "certificate": {
            "path": str(certificate_path.relative_to(HERE.parent.parent)),
            "level": int(certificate["k"]),
            "lambda": f"{certificate['A']}/{certificate['SC_L']}",
            "weight_kind": "certified rational lower weights",
            "potential_kind": "exactly verified feasible subeigenvector",
            "exact_verification_passed": True,
        },
        "sources_sha256": artifact_sources(certificate_path),
        "false_core_boundary_comparison": core_boundary_comparison(),
        "actual_packet_macro_bridge": {
            "verdict": "finite semantic bridge and audited tax rows verified",
            "tax_interpretation": (
                "direct exact edge inequalities for this stored feasible vector "
                "and these finite paths; not an assumed critical calibration"
            ),
            "macro_rows": macro_rows,
        },
    }


def write_artifact(path: Path, artifact: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")


def verify_artifact(path: Path) -> None:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unrecognized glider/KL bridge artifact schema")
    bounds = expected["bounds"]
    certificate_path = HERE.parent.parent / expected["certificate"]["path"]
    actual = build_artifact(
        int(bounds["ether_cells"][1]),
        int(bounds["tail"]),
        certificate_path,
    )
    if actual != expected:
        raise AssertionError("glider/KL bridge artifact reconstruction disagreed")


def selftest(maximum_ether_cells: int) -> None:
    artifact = build_artifact(maximum_ether_cells, 0, DEFAULT_CERTIFICATE)
    rows = artifact["actual_packet_macro_bridge"]["macro_rows"]
    for index, row in enumerate(rows, start=1):
        if row["trace"]["ether_cells"] != index:
            raise AssertionError("self-test macro order changed")
        if not row["semantic_bridge_verified"] or not row["tax_ready"]:
            raise AssertionError("self-test lost a verified bridge row")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    test = subparsers.add_parser("selftest")
    test.add_argument("--maximum-ether-cells", type=int, default=3)

    build = subparsers.add_parser("build")
    build.add_argument("artifact", type=Path)
    build.add_argument("--maximum-ether-cells", type=int, default=6)
    build.add_argument("--tail", type=int, default=0)
    build.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)

    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)

    args = parser.parse_args()
    if args.command == "selftest":
        selftest(args.maximum_ether_cells)
        print("literal glider/KL bridge self-test: PASS")
    elif args.command == "build":
        artifact = build_artifact(
            args.maximum_ether_cells, args.tail, args.certificate
        )
        write_artifact(args.artifact, artifact)
        print(f"wrote exact literal glider/KL bridge artifact: {args.artifact}")
    elif args.command == "verify":
        verify_artifact(args.artifact)
        print(f"verified exact literal glider/KL bridge artifact: {args.artifact}")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()

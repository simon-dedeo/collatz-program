#!/usr/bin/env python3
"""Exact 3-adic tail chart and linked-ray KL synchronization audit.

For the returning glider packet K, the true literal Collatz boundary is

    Z(K) = 2^35*K - 358513857,
    r = v3(Z),
    C(K)+1 = 3*2^(r+1)*(Z/3^r).

For a free branch-n macro tail K=R_n+2^(8n+15)q, the q coefficient in Z is
the 3-adic unit 2^(8n+50).  Thus the free-tail rail distribution is exactly
geometric on every complete q residue system.  This is only a chart theorem,
not a law along one Collatz orbit.

The coherent-chain theorem is much sharper.  If u is the normalized EC17
core and a branch n links to a successor branch m, then

    473*3^10*Z(K) = 2^(8n+30)*u - 9591553,
    2^(8m+15)*u' = 3^(6n+11)*u + 17.

Since 9591553=17*(2^15+3^12), substitution forces the successor rail to be
exactly r'=2.  Equivalently, its true Collatz boundary C' obeys

    473*C' + 881 = 2^18*3^(6n)*u.

Consequently a linked chain whose branch lengths tend to infinity converges
3-adically to -881/473 at its packet boundaries, and the repeated ether cell
is the exact six-chord cycle

    F_E(x) = (729*x+881)/256.

At fixed KL precision this makes the post-transient tax deterministic, not
Haar-random.  This worker reconstructs the formulas, bounded literal links,
and exact k=12 certificate products.  It claims no infinite linked orbit and
no Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
KL_DIR = HERE.parent / "kl"
if str(KL_DIR) not in sys.path:
    sys.path.insert(0, str(KL_DIR))

from breakoff_ether_counter import REGISTER_OFFSET, REGISTER_STRIDE
from breakoff_ether_glider import components, glider_macro, link_macros, machines
from breakoff_ether_glider_kl_bridge import (
    DEFAULT_CERTIFICATE,
    calibrate_trace,
    load_and_verify_certificate,
    packet_boundary,
    trace_breakoff_macro,
)


SCHEMA = "collatz-breakoff-ether-glider-kl-tail-chart-v1"
Z_CONSTANT = 358_513_857
CORE_CENTER = 9_591_553
BOUNDARY_CENTER_NUMERATOR = 881
BOUNDARY_CENTER_DENOMINATOR = 473


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fraction_record(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def v3(value: int) -> int:
    if value == 0:
        raise ValueError("v3(0) is not finite")
    value = abs(value)
    result = 0
    while value % 3 == 0:
        value //= 3
        result += 1
    return result


def z_of_packet(packet: int) -> int:
    return (1 << 35) * packet - Z_CONSTANT


def chart_boundary(packet: int) -> tuple[int, int, int]:
    z = z_of_packet(packet)
    if z <= 0:
        raise ValueError("audited packet is below the positive chart")
    rail = v3(z)
    unit = z // 3**rail
    boundary = 3 * (1 << (rail + 1)) * unit - 1
    return rail, unit, boundary


def normalized_core(ether_cells: int, packet: int) -> int:
    register = REGISTER_STRIDE * packet + REGISTER_OFFSET
    denominator = 3 * (1 << (8 * ether_cells - 5))
    if register % denominator:
        raise AssertionError("branch packet has no integral normalized EC17 core")
    core = register // denominator
    if core < 1 or core % 3 != 1:
        raise AssertionError("normalized EC17 core lost positivity or u=1 mod 3")
    return core


def verify_chart_constants() -> dict[str, object]:
    data = components()
    ether = machines()[0]
    if (ether.coefficient_residue, ether.coefficient_modulus) != (13, 512):
        raise AssertionError("ether coefficient chart changed")
    constant = (
        64 * ether.coefficient_residue
        - 1
        + 64 * ether.coefficient_modulus * data.defect_input_constant
    )
    slope = (
        64
        * ether.coefficient_modulus
        * (1 << data.defect_input_stride_exponent)
    )
    if constant != -Z_CONSTANT or slope != 1 << 35:
        raise AssertionError("closed Z(K) constants changed")
    if CORE_CENTER != 17 * ((1 << 15) + 3**12):
        raise AssertionError("linked-ray cancellation constant changed")
    for n in range(1, 5):
        macro = glider_macro(n)
        for tail in (0, 1, 2):
            packet = macro.member(tail)[0]
            _, _, literal = packet_boundary(packet)
            rail, unit, closed = chart_boundary(packet)
            if literal != closed or z_of_packet(packet) != 3**rail * unit:
                raise AssertionError("closed chart missed the literal packet boundary")
    return {
        "ether_coefficient": "c=13+512*(-10941+2^20*K)",
        "breakoff_state": "kappa=72*c-1",
        "chart_numerator": "Z=(8*kappa-1)/9=64*c-1=2^35*K-358513857",
        "boundary": "C(K)+1=3*2^(r+1)*(Z/3^r), r=v3(Z)",
        "literal_checks": {"ether_cells": [1, 4], "tails": [0, 1, 2]},
    }


def free_tail_distribution(maximum_n: int, depth: int) -> list[dict[str, object]]:
    modulus = 3**depth
    expected = {r: 2 * 3 ** (depth - r - 1) for r in range(depth)}
    expected[depth] = 1
    rows: list[dict[str, object]] = []
    for n in range(1, maximum_n + 1):
        macro = glider_macro(n)
        base = z_of_packet(macro.input_packet_base)
        slope = 1 << (8 * n + 50)
        if v3(slope) != 0:
            raise AssertionError("free macro-tail coefficient is not a 3-adic unit")
        root = (-base * pow(slope, -1, modulus)) % modulus
        histogram = Counter(min(v3(base + slope * q), depth) for q in range(modulus))
        if dict(histogram) != expected:
            raise AssertionError("free-tail valuation histogram is not geometric")
        if root % 3 != macro.input_packet_base % 3:
            raise AssertionError("root class q=R_n mod 3 changed")

        # A separately labelled diagnostic slice.  It is not an EC17 input
        # condition: the true core u below is automatically 1 mod 3.
        slice_values = [1 + 3 * s for s in range(3 ** (depth - 1))]
        slice_histogram = Counter(
            min(v3(base + slope * q), depth) for q in slice_values
        )
        if macro.input_packet_base % 3 == 1:
            expected_slice = {
                r: 2 * 3 ** (depth - r - 1) for r in range(1, depth)
            }
            expected_slice[depth] = 1
        else:
            expected_slice = {0: 3 ** (depth - 1)}
        if dict(slice_histogram) != expected_slice:
            raise AssertionError("q=1 mod 3 diagnostic slice changed")

        core0 = normalized_core(n, macro.member(0)[0])
        core1 = normalized_core(n, macro.member(1)[0])
        core_slope = 473 * (1 << 20) * 3**10
        if core1 - core0 != core_slope:
            raise AssertionError("macro tail did not first enter the core at trit 10")
        for tail in (0, 1, 2):
            packet = macro.member(tail)[0]
            core = normalized_core(n, packet)
            if core != core0 + core_slope * tail:
                raise AssertionError("affine normalized-core relation failed")
            left = 473 * 3**10 * z_of_packet(packet)
            right = (1 << (8 * n + 30)) * core - CORE_CENTER
            if left != right:
                raise AssertionError("moving-target chart identity failed")
        rows.append(
            {
                "ether_cells": n,
                "R_n_mod_3": macro.input_packet_base % 3,
                "Z_base": str(base),
                "Z_tail_coefficient": str(slope),
                "root_mod_3_to_depth": root,
                "root_mod_3": root % 3,
                "valuation_histogram_capped_at_depth": {
                    str(key): value for key, value in sorted(histogram.items())
                },
                "q_equals_1_mod_3_diagnostic_histogram": {
                    str(key): value for key, value in sorted(slice_histogram.items())
                },
                "normalized_core_base": str(core0),
                "normalized_core_tail_coefficient": str(core_slope),
                "core_tail_first_changed_trit": 10,
                "core_mod_3_is_automatic_not_a_q_restriction": True,
            }
        )
    return rows


def verify_piecewise_affine_charts() -> dict[str, object]:
    checks = 0
    for n in range(1, 4):
        macro = glider_macro(n)
        z0 = z_of_packet(macro.input_packet_base)
        slope = 1 << (8 * n + 50)
        for rail in range(5):
            rail_modulus = 3**rail
            root = (-z0 * pow(slope, -1, rail_modulus)) % rail_modulus
            h0 = (z0 + slope * root) // rail_modulus
            for k in range(2, 6):
                residues: set[int] = set()
                for tail_coordinate in range(3 ** (k - 1)):
                    h = h0 + slope * tail_coordinate
                    if h % 3 == 0:
                        continue
                    q = root + rail_modulus * tail_coordinate
                    packet = macro.member(q)[0]
                    actual_rail, actual_h, boundary = chart_boundary(packet)
                    if actual_rail != rail or actual_h != h:
                        raise AssertionError("piecewise-affine rail chart failed")
                    predicted = 3 * (1 << (rail + 1)) * h - 1
                    if boundary != predicted:
                        raise AssertionError("piecewise-affine boundary failed")
                    residues.add(boundary % 3**k)
                    checks += 1
                expected = {
                    residue
                    for residue in range(3**k)
                    if v3(residue + 1) == 1
                }
                if residues != expected:
                    raise AssertionError("fixed-rail chart is not uniform on v3(C+1)=1")
    return {
        "bounds": {"ether_cells": [1, 3], "rail": [0, 4], "k": [2, 5]},
        "checks": checks,
        "chart": "q=rho_(n,r)+3^r*t; h=h_(n,r)+2^(8n+50)*t",
        "boundary": "C=-1+3*2^(r+1)*h, excluding the one h=0 mod 3 class",
        "image_mod_3^k": "{C: v3(C+1)=1}={C=2 or 5 mod 9}",
        "bijective_at_each_bound": True,
    }


def linked_synchronization(maximum_branch: int, lifts: int) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    checks = 0
    synchronization_checks = 0
    maximum_synchronization_depth = 0
    for previous_n in range(1, maximum_branch + 1):
        previous = glider_macro(previous_n)
        for current_n in range(1, maximum_branch + 1):
            current = glider_macro(current_n)
            previous_tail, current_tail = link_macros(previous, current)
            for lift in range(lifts):
                q_previous = previous_tail + (1 << current.input_packet_stride_exponent) * lift
                q_current = current_tail + previous.output_packet_stride * lift
                output_packet = previous.member(q_previous)[1]
                input_packet = current.member(q_current)[0]
                if output_packet != input_packet:
                    raise AssertionError("lifted macro link failed")
                u = normalized_core(previous_n, previous.member(q_previous)[0])
                u_next = normalized_core(current_n, input_packet)
                if (
                    (1 << (8 * current_n + 15)) * u_next
                    != 3 ** (6 * previous_n + 11) * u + 17
                ):
                    raise AssertionError("linked packets lost EC17")
                d_next = (1 << (8 * current_n + 30)) * u_next - CORE_CENTER
                bracket = (1 << 15) * 3 ** (6 * previous_n - 1) * u - 17
                if d_next != 3**12 * bracket or bracket % 3 == 0:
                    raise AssertionError("linked rail cancellation failed")
                rail, _, boundary = chart_boundary(input_packet)
                if rail != 2:
                    raise AssertionError("linked successor rail is not exactly two")
                if 473 * boundary + 881 != (1 << 18) * 3 ** (6 * previous_n) * u:
                    raise AssertionError("boundary-center contraction identity failed")
                if v3(473 * boundary + 881) != 6 * previous_n:
                    raise AssertionError("boundary has the wrong exact center precision")

                # At every depth d <= 6n+1 the predecessor term in EC17
                # vanishes modulo 3^(d+10).  Division by the fixed 3^10 in
                # u'=U_m+473*2^20*3^10*q' then leaves one target-tail class
                # depending only on the target branch m and d.
                target_core_base = normalized_core(
                    current_n, current.input_packet_base
                )
                for depth in range(1, 6 * previous_n + 2):
                    core_modulus = 3 ** (depth + 10)
                    forced_core = (
                        17
                        * pow(
                            2,
                            -(8 * current_n + 15),
                            core_modulus,
                        )
                    ) % core_modulus
                    if u_next % core_modulus != forced_core:
                        raise AssertionError("successor core did not synchronize")
                    difference = (
                        forced_core - target_core_base
                    ) % core_modulus
                    if difference % 3**10:
                        raise AssertionError("synchronized core lost ten fixed trits")
                    tail_modulus = 3**depth
                    forced_tail = (
                        (difference // 3**10)
                        * pow(473 * (1 << 20), -1, tail_modulus)
                    ) % tail_modulus
                    if q_current % tail_modulus != forced_tail:
                        raise AssertionError("successor macro tail did not synchronize")
                    synchronization_checks += 1
                    maximum_synchronization_depth = max(
                        maximum_synchronization_depth, depth
                    )
                checks += 1
            rows.append(
                {
                    "previous_ether_cells": previous_n,
                    "current_ether_cells": current_n,
                    "least_previous_tail": str(previous_tail),
                    "least_current_tail": str(current_tail),
                    "lifts_checked": lifts,
                    "successor_rail": 2,
                }
            )
    return {
        "bounds": {
            "previous_ether_cells": [1, maximum_branch],
            "current_ether_cells": [1, maximum_branch],
            "affine_lifts_per_link": lifts,
        },
        "checks": checks,
        "fixed_depth_synchronization_checks": synchronization_checks,
        "maximum_synchronization_depth_checked": maximum_synchronization_depth,
        "rows": rows,
        "theorem": (
            "EC17 substitution gives 2^(8m+30)u'-9591553="
            "3^12*(2^15*3^(6n-1)u-17), with unit bracket; hence r'=2"
        ),
        "moving_target": (
            "r+10=v3(2^(8n+30)u-9591553), equivalently the target is "
            "alpha_n=9591553/2^(8n+30) in Q_3"
        ),
        "boundary_contraction": "473*C'+881=2^18*3^(6n)*u",
        "boundary_limit_Q3": (
            "v3(473*C'+881)=6n exactly; hence C' -> -881/473 along "
            "any linked chain with n -> infinity"
        ),
        "finite_precision_synchronization": (
            "if 6n+11>=d+10 then u' mod 3^(d+10), hence the successor "
            "tail chart mod 3^d, is fixed by m"
        ),
    }


def structural_kl_audit() -> dict[str, object]:
    checks = 0
    for n in range(1, 5):
        for tail in range(9):
            trace = trace_breakoff_macro(n, tail)
            rails = [len(row["valuation_word"]) - 2 for row in trace["segment_rows"]]
            expected = [rails[0], 0, 2, 0, 1, 0] + [2, 0] * (n - 1)
            if rails != expected:
                raise AssertionError("literal macro lost the symbolic rail skeleton")
            counts = trace["kl_edge_counts"]
            if counts != {
                "transport": 0,
                "r2": 2 * n + 4,
                "r8": rails[0] + 4 * n + 5,
            }:
                raise AssertionError("literal KL counts lost the rail formula")
            checks += 1
    return {
        "literal_bounds": {"ether_cells": [1, 4], "tails": [0, 8]},
        "literal_checks": checks,
        "rail_vector": "[r,0,2,0,1,0]+[2,0]^(n-1)",
        "general_counts": {"R2": "2n+4", "R8": "r+4n+5", "S": 0},
        "linked_post_initial_counts": {
            "R2": "2n+4",
            "R8": "4n+7",
            "odd_steps": "6n+11",
            "one_halving_steps": "8n+15",
            "leading_multiplier": "3^(6n+11)/2^(8n+15)",
        },
    }


def kl_tax_audit(certificate_path: Path) -> dict[str, object]:
    certificate = load_and_verify_certificate(certificate_path)
    deviations: dict[int, Fraction] = {}
    selections: dict[int, tuple[int, int]] = {}
    cycle_edges: list[dict[str, int | str]] = []
    # A preceding n=2 packet is synchronized modulo 3^12.  Current n>=2
    # then exposes the stable base plus repeated ether-cell cycle.
    previous = glider_macro(2)
    for n in range(2, 7):
        _, tail = link_macros(previous, glider_macro(n))
        trace = trace_breakoff_macro(n, tail)
        tax = calibrate_trace(trace, certificate)
        deviations[n] = Fraction(
            int(tax["deviation_product"]["numerator"]),
            int(tax["deviation_product"]["denominator"]),
        )
        selections[n] = (int(tax["selected_edges"]), int(tax["nonselected_edges"]))
        if selections[n] != (n + 2, 5 * n + 9):
            raise AssertionError("synchronized selected/nonselected count changed")
        if n == 3:
            modulus = 3 ** int(certificate["k"])
            for edge in trace["edge_objects"][:6]:
                cycle_edges.append(
                    {
                        "kind": edge.kind,
                        "source_residue": edge.source % modulus,
                        "target_residue": edge.target % modulus,
                    }
                )
    ether_factor = deviations[3] / deviations[2]
    if any(deviations[n + 1] / deviations[n] != ether_factor for n in range(3, 6)):
        raise AssertionError("linked KL tax is not geometric in ether length")
    base_factor = deviations[2] / ether_factor**2

    scale = int(certificate["SC_W"])
    weight_two = Fraction(int(certificate["B2"]), scale)
    weight_eight = Fraction(int(certificate["B8"]), scale)
    ether_weight = weight_eight**4 * weight_two**2
    base_weight = weight_eight**7 * weight_two**4
    center_modulus = 3**int(certificate["k"])
    center_residue = (-881 * pow(473, -1, center_modulus)) % center_modulus
    if center_residue != 17975:
        raise AssertionError("level-12 rational center residue changed")
    if (
        [edge["kind"] for edge in cycle_edges]
        != ["r2", "r8", "r2", "r8", "r8", "r8"]
        or cycle_edges[0]["source_residue"] != center_residue
        or cycle_edges[-1]["target_residue"] != center_residue
    ):
        raise AssertionError("literal level-12 ether center cycle changed")
    return {
        "certificate_path": str(certificate_path.relative_to(HERE.parent.parent)),
        "certificate_level": int(certificate["k"]),
        "exact_verification_passed": True,
        "synchronized_predecessor_ether_cells": 2,
        "current_ether_cells": [2, 6],
        "center_residue_mod_3^k": center_residue,
        "ether_cycle": {
            "affine_map": "F_E(x)=(729*x+881)/256",
            "fixed_point": "-881/473",
            "reverse_KL_cycle_edges": cycle_edges,
            "deviation_factor": fraction_record(ether_factor),
            "certified_lower_weight_product": fraction_record(ether_weight),
            "calibrated_slack_factor": fraction_record(ether_factor / ether_weight),
            "selected_edges": 1,
            "nonselected_edges": 5,
        },
        "stable_base": {
            "deviation_factor": fraction_record(base_factor),
            "certified_lower_weight_product": fraction_record(base_weight),
            "calibrated_slack_factor": fraction_record(base_factor / base_weight),
            "R8": 7,
            "R2": 4,
            "selected_edges": 2,
            "nonselected_edges": 9,
        },
        "factorization": "Dev(n)=Dev_base*Dev_E^n for synchronized n=2..6",
        "deviation_products": {
            str(n): fraction_record(deviations[n]) for n in sorted(deviations)
        },
        "selected_nonselected_counts": {
            str(n): list(selections[n]) for n in sorted(selections)
        },
        "interpretation": (
            "fixed-level exact rational calibration for the stored feasible "
            "subeigenvector; not a critical-tower or infinite-orbit theorem"
        ),
    }


def artifact_sources(certificate_path: Path) -> dict[str, str]:
    paths = {
        "worker": Path(__file__),
        "glider": HERE / "breakoff_ether_glider.py",
        "counter": HERE / "breakoff_ether_counter.py",
        "literal_kl_bridge": HERE / "breakoff_ether_glider_kl_bridge.py",
        "router": HERE / "router_breakoff.py",
        "kl_certificate": certificate_path,
        "kl_verifier": KL_DIR / "certify.py",
    }
    return {name: file_sha256(path) for name, path in paths.items()}


def build_artifact(
    maximum_free_n: int,
    tail_depth: int,
    maximum_link_n: int,
    link_lifts: int,
    certificate_path: Path,
) -> dict[str, object]:
    if min(maximum_free_n, tail_depth, maximum_link_n, link_lifts) < 1:
        raise ValueError("all bounds must be positive")
    certificate_path = certificate_path.resolve()
    return {
        "schema": SCHEMA,
        "scope": (
            "universal exact algebra plus bounded literal reconstruction at the "
            "stated bounds; fixed k=12 feasible-certificate calibration; no "
            "infinite linked EC17 ray and no Collatz counterexample"
        ),
        "counterexample": None,
        "bounds": {
            "maximum_free_ether_cells": maximum_free_n,
            "free_tail_residue_depth": tail_depth,
            "maximum_link_ether_cells": maximum_link_n,
            "affine_lifts_per_link": link_lifts,
        },
        "sources_sha256": artifact_sources(certificate_path),
        "closed_chart": verify_chart_constants(),
        "free_tail_chart": {
            "warning": (
                "the geometric distribution is over a complete free q residue "
                "system and is not a distribution along one linked EC17 ray"
            ),
            "universal_histogram": (
                "#v3(Z)=r is 2*3^(d-r-1) for r<d, with one root class >=d"
            ),
            "rows": free_tail_distribution(maximum_free_n, tail_depth),
        },
        "piecewise_affine_chart": verify_piecewise_affine_charts(),
        "linked_ray_synchronization": linked_synchronization(
            maximum_link_n, link_lifts
        ),
        "literal_kl_structure": structural_kl_audit(),
        "fixed_precision_kl_tax": kl_tax_audit(certificate_path),
        "verdict": {
            "free_Haar_tail_model_for_a_coherent_chain": False,
            "post_initial_linked_rail": 2,
            "fixed_precision_tax_random_over_linked_tails": False,
            "counterexample_found": False,
            "remaining_seam": (
                "construct one positive infinite EC17/glider chain.  The chart "
                "now fixes its post-initial KL skeleton and fixed-precision tax; "
                "the existing all-branch Lyapunov theorem would make any such "
                "chain an outward Collatz escape, but no chain is supplied."
            ),
        },
    }


def write_artifact(path: Path, artifact: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")


def verify_artifact(path: Path) -> None:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unrecognized tail-chart artifact schema")
    bounds = expected["bounds"]
    certificate_path = HERE.parent.parent / expected["fixed_precision_kl_tax"]["certificate_path"]
    actual = build_artifact(
        int(bounds["maximum_free_ether_cells"]),
        int(bounds["free_tail_residue_depth"]),
        int(bounds["maximum_link_ether_cells"]),
        int(bounds["affine_lifts_per_link"]),
        certificate_path,
    )
    if actual != expected:
        raise AssertionError("tail-chart artifact reconstruction disagreed")


def selftest() -> None:
    artifact = build_artifact(4, 3, 3, 2, DEFAULT_CERTIFICATE)
    if artifact["counterexample"] is not None:
        raise AssertionError("self-test manufactured a counterexample")
    if artifact["verdict"]["post_initial_linked_rail"] != 2:
        raise AssertionError("self-test lost the linked rail theorem")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("artifact", type=Path)
    build.add_argument("--maximum-free-n", type=int, default=12)
    build.add_argument("--tail-depth", type=int, default=5)
    build.add_argument("--maximum-link-n", type=int, default=8)
    build.add_argument("--link-lifts", type=int, default=3)
    build.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()
    if args.command == "selftest":
        selftest()
        print("glider/KL tail-chart self-test: PASS")
    elif args.command == "build":
        artifact = build_artifact(
            args.maximum_free_n,
            args.tail_depth,
            args.maximum_link_n,
            args.link_lifts,
            args.certificate,
        )
        write_artifact(args.artifact, artifact)
        print(f"wrote exact glider/KL tail-chart artifact: {args.artifact}")
    elif args.command == "verify":
        verify_artifact(args.artifact)
        print(f"verified exact glider/KL tail-chart artifact: {args.artifact}")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()

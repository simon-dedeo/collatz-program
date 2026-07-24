#!/usr/bin/env python3
"""Exact invariant-CEGIS on writer--decoder payload triples.

A complete writer--resonant-decoder cell has the exact coordinates

    H(p,b,Q) = (2^D Q - B(p))/9  ->  3^(p+o(p)+b) Q.

This worker audits the smallest predicate refinements on ``(p,b,Q)``.  It
does not rank long trajectories.  It records exact closure witnesses for the
base and next-writer architectures, checks the mandatory mod-nine quotient,
exhibits coefficientwise ordinary one-edge cylinders, derives the exact
two-edge mixed-base parameter map, rejects finite ternary-cylinder selectors
with a fixed symbol alphabet, and regression-checks the fixed-precision
perturbation obstruction.  No bounded row is promoted to an invariant or a
Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

from outward_charge_invariant_cegis import integer_sha256
from outward_writer_decoder_cegis import Cell, make_cell


SCHEMA = "collatz-outward-writer-decoder-invariant-cegis-v2"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def v2(value: int) -> tuple[int, int]:
    if value <= 0:
        raise ValueError("v2 requires a positive integer")
    exponent = 0
    while value % 2 == 0:
        exponent += 1
        value //= 2
    return exponent, value


def v3(value: int) -> tuple[int, int]:
    if value <= 0:
        raise ValueError("v3 requires a positive integer")
    exponent = 0
    while value % 3 == 0:
        exponent += 1
        value //= 3
    return exponent, value


@dataclass(frozen=True)
class Triple:
    p: int
    b: int
    Q: int
    H: int
    output: int


def make_triple(p: int, b: int, Q: int) -> Triple:
    cell = make_cell(p, b)
    if Q <= 0 or Q % 2 == 0:
        raise ValueError("payload Q must be positive and odd")
    numerator = 2**cell.Dg * Q - cell.Bg
    if numerator <= 0 or numerator % 9:
        raise ValueError("payload misses the positive mod-nine source class")
    H = numerator // 9
    if H % 2 == 0 or 9 * H + cell.Bg != 2**cell.Dg * Q:
        raise AssertionError("triple source identity failed")
    output = 3 ** (p + cell.o + b) * Q
    return Triple(p, b, Q, H, output)


def triple_record(triple: Triple) -> dict[str, Any]:
    return {
        "p": triple.p,
        "b": triple.b,
        "Q": str(triple.Q),
        "Q_bits": triple.Q.bit_length(),
        "Q_sha256": integer_sha256(triple.Q),
        "H": str(triple.H),
        "H_bits": triple.H.bit_length(),
        "H_sha256": integer_sha256(triple.H),
        "output": str(triple.output),
        "output_bits": triple.output.bit_length(),
        "output_sha256": integer_sha256(triple.output),
    }


def next_diagnostic(triple: Triple) -> dict[str, Any]:
    g = triple.p + make_cell(triple.p, triple.b).o + triple.b
    writer_v2, _ = v2(3 ** (g + 2) * triple.Q + 7)
    next_p = writer_v2 - 4
    if next_p < 2:
        return {
            "kind": "next_writer_undefined",
            "g": g,
            "v2_9Hprime_plus_7": writer_v2,
            "derived_p": next_p,
        }
    target = make_cell(next_p, 0)
    composite_v2, next_Q = v2(3 ** (g + 2) * triple.Q + target.Bg)
    required = target.S + next_p + 4
    if composite_v2 < required:
        return {
            "kind": "next_decoder_shortfall",
            "g": g,
            "derived_p": next_p,
            "v2_composite_gate": composite_v2,
            "required": required,
            "shortfall": required - composite_v2,
        }
    next_b = composite_v2 - required
    target_triple = make_triple(next_p, next_b, next_Q)
    if target_triple.H != triple.output:
        raise AssertionError("triple transition did not identify its target source")
    return {
        "kind": "defined_triple_transition",
        "g": g,
        "target": triple_record(target_triple),
    }


def source_residue(cell: Cell) -> tuple[int, int]:
    modulus = 2 ** (cell.Dg + 1)
    residue = (2**cell.Dg - cell.Bg) * pow(9, -1, modulus) % modulus
    if residue == 0:
        residue = modulus
    if residue % 2 == 0:
        raise AssertionError("writer--decoder source residue is not odd")
    return residue, modulus


def smallest_base_failure() -> dict[str, Any]:
    witness = make_triple(2, 0, 7)
    diagnostic = next_diagnostic(witness)
    if diagnostic["kind"] != "next_writer_undefined":
        raise AssertionError("base-architecture witness changed")

    # PT26 makes this a finite global minimality check, rather than an integer
    # scan.  Any smaller legal H has 4*3^p+p+4+b <= floor(log2(9H_w)).
    floor_log = (9 * witness.H).bit_length() - 1
    compared: list[dict[str, Any]] = []
    p = 2
    while 4 * 3**p + p + 4 <= floor_log:
        maximum_b = floor_log - (4 * 3**p + p + 4)
        for b in range(maximum_b + 1):
            cell = make_cell(p, b)
            residue, modulus = source_residue(cell)
            compared.append(
                {
                    "p": p,
                    "b": b,
                    "least_source": str(residue),
                    "source_modulus_bits": modulus.bit_length(),
                }
            )
            if residue < witness.H:
                raise AssertionError("smaller writer--decoder source exists")
        p += 1
    return {
        "architecture": "all_positive_integral_payload_triples",
        "status": "universally_rejected_by_exact_witness",
        "globally_smallest_source_with_PT26_research_bound": True,
        "witness": triple_record(witness),
        "first_failure": diagnostic,
        "minimality_bound": {
            "floor_log2_9H": floor_log,
            "PT26_candidate_symbols": compared,
            "scope": (
                "finite candidates checked exactly; global minimality additionally "
                "uses the universal PT26 research derivation pending QM168"
            ),
        },
    }


def next_writer_refinement_failure() -> dict[str, Any]:
    cell = make_cell(2, 0)
    g = 2 + cell.o
    modulus = 9 * 2**8
    candidates = [
        Q
        for Q in range(1, modulus + 1, 2)
        if (2**cell.Dg * Q - cell.Bg) % 9 == 0
        and (3 ** (g + 2) * Q + cell.Bg) % 2**8 == 2**7
    ]
    if not candidates or candidates[0] != 187:
        raise AssertionError("canonical next-writer CRT witness changed")
    witness = make_triple(2, 0, candidates[0])
    diagnostic = next_diagnostic(witness)
    if diagnostic["kind"] != "next_decoder_shortfall":
        raise AssertionError("writer-refined witness lost its decoder failure")
    return {
        "architecture": "base_triple_plus_exact_next_writer_binder",
        "status": "rejected_by_exact_witness",
        "CRT_modulus": modulus,
        "canonical_Q": str(candidates[0]),
        "witness": triple_record(witness),
        "first_failure": diagnostic,
    }


def quotient_node(p: int) -> str:
    residue = p % 6
    if residue % 2 == 0:
        return "v3_Q_eq_0"
    if residue in (1, 3):
        return "v3_Q_eq_1"
    return "v3_Q_ge_2"


def mod9_quotient(maximum_p: int) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for p in range(2, maximum_p + 1):
        cell = make_cell(p, 0)
        B_mod9 = cell.Bg % 9
        expected_node = quotient_node(p)
        if cell.d % 9 != 7:
            raise AssertionError("d(p) mod-nine stabilization failed")
        if B_mod9 != 7 * (1 + pow(2, p + 4, 9)) % 9:
            raise AssertionError("B(p) mod-nine formula failed")
        Q_residue = B_mod9 * pow(2**cell.Dg, -1, 9) % 9
        exponent, _ = v3(Q_residue if Q_residue else 9)
        actual_node = (
            "v3_Q_ge_2" if Q_residue == 0 else f"v3_Q_eq_{exponent}"
        )
        if actual_node != expected_node:
            raise AssertionError("three-node quotient classification failed")
        rows.append(
            {
                "p": p,
                "p_mod_6": p % 6,
                "d_mod_9": cell.d % 9,
                "B_mod_9": B_mod9,
                "Q_mod_9": Q_residue,
                "node": actual_node,
            }
        )
    return {
        "architecture": "mandatory_mod9_three_node_quotient",
        "rows": rows,
        "universal_derivation": {
            "recurrence": (
                "d_(p+1)=d_p+3^(p+1)d_p^2+3^(2p+1)d_p^3"
            ),
            "base": "d_2=9709=7 mod 9",
            "B_formula": "B(p)=7*(1+2^(p+4)) mod 9",
            "classification": {
                "p_even": "v3(Q)=0",
                "p_mod_6_in_{1,3}": "v3(Q)=1",
                "p_mod_6_eq_5": "v3(Q)>=2",
            },
            "status": "research derivation pending Lean",
        },
        "closure_scope": (
            "mandatory exact quotient only; it does not force the next dyadic gate"
        ),
    }


def construct_edge(p: int, b: int, next_p: int, next_b: int) -> dict[str, Any]:
    source = make_cell(p, b)
    target = make_cell(next_p, next_b)
    g = p + source.o + b
    modulus = 3 ** (g + 4)
    rhs = (
        2**source.Dg * target.Bg + 3 ** (g + 2) * source.Bg
    ) % modulus
    next_Q = rhs * pow(2 ** (source.Dg + target.Dg), -1, modulus) % modulus
    if next_Q == 0:
        next_Q = modulus
    if next_Q % 2 == 0:
        next_Q += modulus
    while 2**target.Dg * next_Q <= target.Bg:
        next_Q += 2 * modulus
    numerator = 2**target.Dg * next_Q - target.Bg
    divisor = 3 ** (g + 2)
    if numerator % divisor:
        raise AssertionError("edge cylinder missed source payload integrality")
    Q = numerator // divisor
    triple = make_triple(p, b, Q)
    diagnostic = next_diagnostic(triple)
    if diagnostic["kind"] != "defined_triple_transition":
        raise AssertionError("constructed symbolic edge is not defined")
    target_record = diagnostic["target"]
    if (
        int(target_record["p"]) != next_p
        or int(target_record["b"]) != next_b
        or int(target_record["Q"]) != next_Q
    ):
        raise AssertionError("constructed edge landed in the wrong target symbol")
    return {
        "source_symbol": [p, b],
        "target_symbol": [next_p, next_b],
        "Q": str(Q),
        "Q_bits": Q.bit_length(),
        "Q_sha256": integer_sha256(Q),
        "Q_prime": str(next_Q),
        "Q_prime_bits": next_Q.bit_length(),
        "Q_prime_sha256": integer_sha256(next_Q),
        "H": str(triple.H),
        "H_bits": triple.H.bit_length(),
        "H_sha256": integer_sha256(triple.H),
        "H_prime": str(triple.output),
        "H_prime_bits": triple.output.bit_length(),
        "H_prime_sha256": integer_sha256(triple.output),
        "coefficient_congruence_modulus_bits": modulus.bit_length(),
    }


def edge_family_regression(maximum_p: int, maximum_b: int) -> dict[str, Any]:
    rows = [
        construct_edge(p, b, next_p, next_b)
        for p in range(2, maximum_p + 1)
        for b in range(maximum_b + 1)
        for next_p in range(2, maximum_p + 1)
        for next_b in range(maximum_b + 1)
    ]
    return {
        "symbols": {
            "p_interval": [2, maximum_p],
            "b_interval": [0, maximum_b],
        },
        "exact_ordinary_edges": len(rows),
        "edges_sha256": hashlib.sha256(canonical_json(rows)).hexdigest(),
        "witnesses": rows,
        "universal_statement": (
            "the displayed construction works coefficientwise for every prescribed "
            "pair of legal symbols; finite local edge existence is not invariant closure"
        ),
        "scope": (
            "displayed edges checked exactly; the all-symbol construction is a "
            "research derivation pending Lean"
        ),
    }


def two_edge_parameter_map(
    p: int,
    b: int,
    next_p: int,
    next_b: int,
    final_p: int,
    final_b: int,
) -> dict[str, Any]:
    """Return the exact mixed-base parameter map for two prescribed edges."""

    first = construct_edge(p, b, next_p, next_b)
    second = construct_edge(next_p, next_b, final_p, final_b)
    source = make_cell(p, b)
    middle = make_cell(next_p, next_b)
    final = make_cell(final_p, final_b)
    g = p + source.o + b

    first_Q = int(first["Q"])
    first_Q_prime = int(first["Q_prime"])
    second_Q = int(second["Q"])
    difference = second_Q - first_Q_prime
    if difference % 18:
        raise AssertionError("consecutive edge bases miss their common mod-18 class")

    parameter_modulus = 2**final.Dg
    n0 = (
        difference
        // 18
        * pow(3 ** (g + 2), -1, parameter_modulus)
    ) % parameter_modulus
    numerator = (
        first_Q_prime
        + 2 * 3 ** (g + 4) * n0
        - second_Q
    )
    next_stride = 9 * 2 ** (final.Dg + 1)
    if numerator % next_stride:
        raise AssertionError("two-edge parameter intersection is not integral")
    u0 = numerator // next_stride

    # Check both affine progressions, the exact triple transitions, and the
    # parameter update on several coefficients.  This is not a trajectory
    # search: every check is coefficientwise in the free parameter m.
    for m in range(3):
        n = n0 + 2**final.Dg * m
        u = u0 + 3 ** (g + 2) * m
        Q = first_Q + 9 * 2 ** (middle.Dg + 1) * n
        Q_prime_left = first_Q_prime + 2 * 3 ** (g + 4) * n
        Q_prime_right = second_Q + next_stride * u
        if Q_prime_left != Q_prime_right:
            raise AssertionError("two-edge parameter map lost coefficient equality")
        first_transition = next_diagnostic(make_triple(p, b, Q))
        if first_transition["kind"] != "defined_triple_transition":
            raise AssertionError("first member of the two-edge family is undefined")
        first_target = first_transition["target"]
        if (
            int(first_target["p"]) != next_p
            or int(first_target["b"]) != next_b
            or int(first_target["Q"]) != Q_prime_left
        ):
            raise AssertionError("first family edge landed at the wrong triple")
        second_transition = next_diagnostic(
            make_triple(next_p, next_b, Q_prime_left)
        )
        if second_transition["kind"] != "defined_triple_transition":
            raise AssertionError("second member of the two-edge family is undefined")
        second_target = second_transition["target"]
        if (
            int(second_target["p"]) != final_p
            or int(second_target["b"]) != final_b
        ):
            raise AssertionError("second family edge landed at the wrong symbol")

    return {
        "symbols": [[p, b], [next_p, next_b], [final_p, final_b]],
        "g": g,
        "D_prime": middle.Dg,
        "D_double_prime": final.Dg,
        "first_progression": {
            "Q_base": str(first_Q),
            "Q_stride": str(9 * 2 ** (middle.Dg + 1)),
            "Q_prime_base": str(first_Q_prime),
            "Q_prime_stride": str(2 * 3 ** (g + 4)),
        },
        "intersection": {
            "n0": str(n0),
            "n0_bits": n0.bit_length(),
            "n_modulus": str(parameter_modulus),
            "n_modulus_bits": parameter_modulus.bit_length(),
            "u0": str(u0),
            "m_to_n_multiplier": str(2**final.Dg),
            "m_to_u_multiplier": str(3 ** (g + 2)),
        },
    }


def two_edge_parameter_regression(
    maximum_p: int, maximum_b: int
) -> dict[str, Any]:
    rows = [
        two_edge_parameter_map(p, b, next_p, next_b, final_p, final_b)
        for p in range(2, maximum_p + 1)
        for b in range(maximum_b + 1)
        for next_p in range(2, maximum_p + 1)
        for next_b in range(maximum_b + 1)
        for final_p in range(2, maximum_p + 1)
        for final_b in range(maximum_b + 1)
    ]
    smallest = min(
        rows,
        key=lambda row: (
            int(row["intersection"]["n0"]),
            row["symbols"],
        ),
    )
    return {
        "symbols": {
            "p_interval": [2, maximum_p],
            "b_interval": [0, maximum_b],
        },
        "exact_two_edge_maps": len(rows),
        "maps_sha256": hashlib.sha256(canonical_json(rows)).hexdigest(),
        "zero_n0_rows": sum(
            int(row["intersection"]["n0"]) == 0 for row in rows
        ),
        "negative_u0_rows": sum(
            int(row["intersection"]["u0"]) < 0 for row in rows
        ),
        "smallest_n0_row": smallest,
        "sample_rows": rows[: min(9, len(rows))],
        "universal_formula": {
            "first_edge": (
                "Q=q0+9*2^(D'+1)*n; Q'=q0'+2*3^(g+4)*n"
            ),
            "next_edge": (
                "n=n0+2^D''*m; u=u0+3^(g+2)*m"
            ),
            "resource_reading": (
                "the following symbol consumes D'' dyadic bits of n and the "
                "next edge parameter receives a 3^(g+2)-scaled free tail"
            ),
            "status": "research derivation pending Lean",
        },
        "scope": (
            "all displayed coefficient maps are exact; bounded absence of n0=0 "
            "is not promoted to a universal nonzero-carry theorem"
        ),
    }


def fixed_symbol_kraft_ledger(maximum_p: int) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    partial = Fraction(0, 1)
    for p in range(2, maximum_p + 1):
        cell = make_cell(p, 0)
        # Summing b>=0 gives sum_b 2^-(D(p,0)+b)=2^(1-D(p,0)).
        mass = Fraction(1, 2 ** (cell.Dg - 1))
        partial += mass
        rows.append(
            {
                "p": p,
                "S": cell.S,
                "D_at_b_0": cell.Dg,
                "all_b_dyadic_mass": f"2^-{cell.Dg - 1}",
            }
        )
    if not partial < Fraction(1, 2**53):
        raise AssertionError("displayed writer--decoder Kraft mass bound failed")
    return {
        "guard_for_target_symbol": (
            "after division by two, n=n0(p,b) mod 2^D(p,b)"
        ),
        "guards_are_disjoint": (
            "the deterministic next writer/decoder valuations select at most one symbol"
        ),
        "displayed_p_rows": rows,
        "displayed_partial_mass": {
            "numerator": str(partial.numerator),
            "denominator": str(partial.denominator),
        },
        "all_symbol_bound": {
            "inequality": (
                "sum_(p>=2,b>=0) 2^-D(p,b) < 2^-53"
            ),
            "derivation": (
                "S(p)>=49 gives D(p,b)>=p+53+b; equality in S occurs only at p=2"
            ),
            "status": "research derivation pending Lean",
        },
        "finite_architecture_obstruction": {
            "theorem": (
                "no nonempty finite union of ternary parameter cylinders can "
                "force the next symbol to lie in a fixed finite target-symbol list"
            ),
            "proof": (
                "a finite target list is a finite union of disjoint dyadic "
                "cylinders with nonempty dyadic-open complement; CRT makes every "
                "nonempty ternary cylinder meet that complement in arbitrarily "
                "large positive parameters"
            ),
            "does_not_exclude": (
                "an unbounded recursively selected target symbol; the global "
                "Kraft bound alone does not make the infinite-union complement open"
            ),
            "status": "research theorem pending Lean",
        },
    }


def ternary_cylinder_cegis(maximum_precision: int) -> dict[str, Any]:
    """Reject anchored ternary-only refinements with exact first witnesses."""

    first = construct_edge(2, 0, 2, 0)
    parameter_map = two_edge_parameter_map(2, 0, 2, 0, 2, 0)
    anchor = int(parameter_map["intersection"]["n0"])
    Q_prime_base = int(first["Q_prime"])
    Q_prime_stride = 2 * 3 ** (2 + make_cell(2, 0).o + 4)

    anchor_Q_prime = Q_prime_base + Q_prime_stride * anchor
    anchor_diagnostic = next_diagnostic(make_triple(2, 0, anchor_Q_prime))
    if anchor_diagnostic["kind"] != "defined_triple_transition":
        raise AssertionError("ternary CEGIS anchor is not a legal second edge")
    if (
        int(anchor_diagnostic["target"]["p"]) != 2
        or int(anchor_diagnostic["target"]["b"]) != 0
    ):
        raise AssertionError("ternary CEGIS anchor landed at the wrong symbol")

    rows: list[dict[str, Any]] = []
    for precision in range(maximum_precision + 1):
        modulus = 3**precision
        residue = anchor % modulus
        parameter = residue
        tested = 0
        while True:
            Q_prime = Q_prime_base + Q_prime_stride * parameter
            triple = make_triple(2, 0, Q_prime)
            diagnostic = next_diagnostic(triple)
            tested += 1
            if diagnostic["kind"] != "defined_triple_transition":
                break
            parameter += modulus
        rows.append(
            {
                "architecture": (
                    "one_step_symbol_memory_plus_parameter_mod_3^k"
                ),
                "precision_k": precision,
                "predicate": f"current_edge=(2,0)->(2,0), n={residue} mod 3^{precision}",
                "legal_anchor_n": str(anchor),
                "smallest_closure_failure_n": str(parameter),
                "representatives_tested_through_first_failure": tested,
                "failure_triple": triple_record(triple),
                "first_failure": diagnostic,
                "status": "rejected_by_exact_witness",
            }
        )
    return {
        "meaning": (
            "complexity ladder for a legal anchored edge with one-step memory "
            "and successively finer pure ternary parameter cylinders"
        ),
        "rows": rows,
        "universal_class_rejection": (
            "the finite-symbol CRT obstruction rejects every finite precision "
            "and every nonempty finite union, not only the displayed anchors"
        ),
    }


def fixed_precision_regression(minimum_k: int, maximum_k: int) -> dict[str, Any]:
    base = construct_edge(2, 0, 2, 0)
    Q = int(base["Q"])
    source = make_cell(2, 0)
    g = 2 + source.o
    ell = 3
    rows: list[dict[str, Any]] = []
    for k in range(minimum_k, maximum_k + 1):
        if not 7 <= k < source.Dg:
            raise ValueError("regression range must satisfy 7<=k<55")
        perturbed_Q = Q + 9 * 3**ell * 2**k
        perturbed = make_triple(2, 0, perturbed_Q)
        if perturbed_Q % 2**k != Q % 2**k or perturbed_Q % 3**ell != Q % 3**ell:
            raise AssertionError("fixed residue guards were not preserved")
        writer_v2, _ = v2(3 ** (g + 2) * perturbed_Q + 7)
        composite_v2, _ = v2(3 ** (g + 2) * perturbed_Q + source.Bg)
        if writer_v2 != 6 or composite_v2 != k:
            raise AssertionError("fixed-precision perturbation did not expose its failure")
        rows.append(
            {
                "k": k,
                "ell": ell,
                "perturbed_Q_bits": perturbed_Q.bit_length(),
                "perturbed_Q_sha256": integer_sha256(perturbed_Q),
                "preserved_mod_2k": True,
                "preserved_mod_3ell": True,
                "next_writer_v2": writer_v2,
                "target_composite_v2": composite_v2,
                "target_required_v2": source.Dg,
                "decoder_shortfall": source.Dg - composite_v2,
                "source_H_bits": perturbed.H.bit_length(),
            }
        )
    return {
        "architecture": "fixed_Q_residues_mod_2k_3ell",
        "status": "research_rejection_with_bounded_exact_regression",
        "base_exact_edge": base,
        "rows": rows,
        "universal_perturbation": (
            "Q -> Q+9*3^ell*2^k*T preserves fixed residues; when a branch "
            "requires D'>k and T is odd, the target affine valuation drops to k"
        ),
        "scope": (
            "rows regression-check p'=2 for 7<=k<55; the all-precision "
            "statement is an exact research derivation pending Lean"
        ),
    }


def build_audit(args: argparse.Namespace) -> dict[str, Any]:
    if args.maximum_mod9_counter < 2 or args.maximum_edge_counter < 2:
        raise ValueError("counter bounds must be at least two")
    if args.maximum_edge_drain < 0:
        raise ValueError("edge drain bound must be nonnegative")
    if not 7 <= args.minimum_perturb_precision <= args.maximum_perturb_precision < 55:
        raise ValueError("perturbation precisions must lie in [7,54]")
    if args.maximum_ternary_selector_precision < 0:
        raise ValueError("ternary selector precision must be nonnegative")
    return {
        "meaning": (
            "exact invariant-CEGIS on charge-dependent writer--decoder payload triples"
        ),
        "bounds": {
            "maximum_mod9_counter": args.maximum_mod9_counter,
            "maximum_edge_counter": args.maximum_edge_counter,
            "maximum_edge_drain": args.maximum_edge_drain,
            "minimum_perturb_precision": args.minimum_perturb_precision,
            "maximum_perturb_precision": args.maximum_perturb_precision,
            "maximum_ternary_selector_precision": (
                args.maximum_ternary_selector_precision
            ),
        },
        "triple_semantics": {
            "source": "H=(2^D(p,b)*Q-B(p))/9",
            "source_conditions": (
                "p>=2, b>=0, Q positive odd, 2^D Q=B(p) mod9"
            ),
            "output": "H'=3^(p+o(p)+b)*Q",
            "next_p": "v2(3^(p+o+b+2)*Q+7)-4",
            "next_b": (
                "v2(3^(p+o+b+2)*Q+B(p'))-(S(p')+p'+4)"
            ),
        },
        "architecture_failures": [
            smallest_base_failure(),
            next_writer_refinement_failure(),
            fixed_precision_regression(
                args.minimum_perturb_precision,
                args.maximum_perturb_precision,
            ),
            {
                "architecture": "fixed_or_eventually_periodic_symbols",
                "status": "universally_rejected",
                "reason": (
                    "a fixed symbol would require (2^D-3^(p+o+b+2))*Q=B(p) "
                    "although the cell is outward; eventual periods are covered "
                    "by ShortcutParityPeriodicNoGo"
                ),
            },
        ],
        "mandatory_ternary_quotient": mod9_quotient(args.maximum_mod9_counter),
        "local_edge_family_regression": edge_family_regression(
            args.maximum_edge_counter, args.maximum_edge_drain
        ),
        "two_edge_parameter_regression": two_edge_parameter_regression(
            args.maximum_edge_counter, args.maximum_edge_drain
        ),
        "fixed_symbol_kraft_ledger": fixed_symbol_kraft_ledger(
            args.maximum_edge_counter
        ),
        "ternary_cylinder_architecture_cegis": ternary_cylinder_cegis(
            args.maximum_ternary_selector_precision
        ),
        "next_architecture": {
            "predicate": "recursive mixed-base family P(p,b,Q)",
            "required_features": [
                "the mandatory three-node mod-nine quotient",
                "unbounded exact next-p and next-b valuation binders",
                "runtime dyadic precision growing at least as D(p,b)",
                "a genuinely aperiodic or unbounded symbol update",
                "coefficientwise triple recurrence and explicit ordinary root",
            ],
            "exact_parameter_seam": (
                "n=n0+2^D''*m and u=u0+3^(g+2)*m"
            ),
            "status": "not_synthesized",
        },
        "universal_invariant": None,
        "counterexample": None,
        "claim_scope": (
            "exact arithmetic failures and local edge witnesses; universal algebraic "
            "statements remain research derivations pending Lean, and no recursive "
            "mixed-base invariant or nonterminating ordinary orbit is claimed"
        ),
    }


def build_artifact(args: argparse.Namespace) -> dict[str, Any]:
    artifact = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": build_audit(args),
    }
    artifact["artifact_sha256"] = hashlib.sha256(canonical_json(artifact)).hexdigest()
    return artifact


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "base_failure_H": audit["architecture_failures"][0]["witness"]["H"],
        "writer_refined_failure_Q": audit["architecture_failures"][1]["canonical_Q"],
        "ternary_nodes": sorted(
            {row["node"] for row in audit["mandatory_ternary_quotient"]["rows"]}
        ),
        "exact_local_edges": audit["local_edge_family_regression"][
            "exact_ordinary_edges"
        ],
        "exact_two_edge_maps": audit["two_edge_parameter_regression"][
            "exact_two_edge_maps"
        ],
        "ternary_architectures_rejected": len(
            audit["ternary_cylinder_architecture_cegis"]["rows"]
        ),
        "universal_invariant": audit["universal_invariant"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported writer--decoder invariant schema")
    args = argparse.Namespace(**stored["audit"]["bounds"])
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("writer--decoder invariant artifact reconstruction failed")
    return report(stored)


def selftest() -> None:
    args = argparse.Namespace(
        maximum_mod9_counter=5,
        maximum_edge_counter=3,
        maximum_edge_drain=1,
        minimum_perturb_precision=7,
        maximum_perturb_precision=10,
        maximum_ternary_selector_precision=2,
    )
    audit = build_audit(args)
    if audit["counterexample"] is not None or audit["universal_invariant"] is not None:
        raise AssertionError("triple invariant CEGIS overclaimed")
    if audit["local_edge_family_regression"]["exact_ordinary_edges"] != 16:
        raise AssertionError("local edge regression count changed")
    if audit["two_edge_parameter_regression"]["exact_two_edge_maps"] != 64:
        raise AssertionError("two-edge parameter regression count changed")
    if len(audit["ternary_cylinder_architecture_cegis"]["rows"]) != 3:
        raise AssertionError("ternary architecture CEGIS count changed")


def add_bounds(command: argparse.ArgumentParser) -> None:
    command.add_argument("--maximum-mod9-counter", type=int, default=6)
    command.add_argument("--maximum-edge-counter", type=int, default=4)
    command.add_argument("--maximum-edge-drain", type=int, default=2)
    command.add_argument("--minimum-perturb-precision", type=int, default=7)
    command.add_argument("--maximum-perturb-precision", type=int, default=16)
    command.add_argument(
        "--maximum-ternary-selector-precision", type=int, default=6
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    probe = sub.add_parser("probe")
    build = sub.add_parser("build")
    verify = sub.add_parser("verify")
    add_bounds(probe)
    add_bounds(build)
    build.add_argument("artifact", type=Path)
    verify.add_argument("artifact", type=Path)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward writer--decoder invariant CEGIS selftest: PASS")
        return 0
    if args.command == "probe":
        print(json.dumps(report(build_artifact(args)), indent=2, sort_keys=True))
        return 0
    if args.command == "build":
        artifact = build_artifact(args)
        args.artifact.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return 0
    print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

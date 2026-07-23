#!/usr/bin/env python3
"""Exact bounded architecture audit for primitive-coordinate recharge invariants.

This is an invariant-synthesis lane, not a survivor claim.  It writes every
positive odd charge as ``H = 3^c u`` with ``gcd(u, 6) = 1`` and checks the
exact recharge update in the three defect cases determined by
``v3(e_w)`` versus ``O_w + c``.  The drain and resonant cancellation are
unbounded arithmetic binders in the proposed grammar; they are not capped
selector features.

The bounded CEGIS component uses only descendants of the theorem-driven
pure-power cylinder ``C = 12 (mod 16)``.  Finite residue architectures are
ranked by their first exact transition-cell ambiguity.  A separate coherent
pilot refines one nested cylinder of root exponents, never independent depth
minima, and records whether its canonical natural address stabilizes.

No bounded survivor, symbolic rewrite schema, or nested 2-adic exponent is a
Collatz counterexample.  Every artifact therefore records
``universal_invariant: null`` and ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

from outward_charge_invariant_cegis import exact_recharge, integer_sha256, valuation
from outward_coherent_cegis import bounded_first_passage_words


SCHEMA = "collatz-outward-primitive-invariant-cegis-v1"
ROOT_WORD = "010111"
UNDEFINED = "UNDEFINED"
UNKNOWN = "UNKNOWN"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def primitive_coordinates(charge: int) -> tuple[int, int]:
    if charge <= 0 or charge % 2 == 0:
        raise ValueError("primitive coordinates require a positive odd charge")
    c, unit = valuation(charge, 3)
    if unit % 2 == 0 or unit % 3 == 0:
        raise AssertionError("primitive unit is not a 2,3-unit")
    return c, unit


def transition_cell_label(transition: dict[str, Any]) -> str:
    if transition["status"] == "defined":
        return f'{transition["word"]}:a={transition["forced_one_blocks"]}'
    if transition["status"] == "unknown_frontier":
        return UNKNOWN
    return UNDEFINED


def defect_transition(charge: int, transition: dict[str, Any]) -> dict[str, Any]:
    """Check and expose the exact LOW/HIGH/RESONANT primitive update."""

    if transition["status"] != "defined":
        raise ValueError("undefined recharge has no primitive defect transition")
    c, unit = primitive_coordinates(charge)
    S = int(transition["S"])
    O = int(transition["O"])
    e = int(transition["e"])
    a = int(transition["forced_one_blocks"])
    t, defect_unit = valuation(e, 3)
    numerator = 3 ** (O + c) * unit + e
    n_v2, n_after_2 = valuation(numerator, 2)
    n_v3, _ = valuation(numerator, 3)
    if n_v2 != S + a:
        raise AssertionError("unbounded drain binder disagrees with exact recharge")
    output = int(transition["output"])
    output_c, output_unit = primitive_coordinates(output)
    if output_c != a + n_v3:
        raise AssertionError("primitive target exponent identity failed")
    denominator = 2 ** (S + a) * 3**n_v3
    if numerator != denominator * output_unit:
        raise AssertionError("primitive target unit identity failed")

    if t < O + c:
        case = "LOW"
        cancellation_v3 = 0
        if n_v3 != t:
            raise AssertionError("low-defect valuation identity failed")
        reduced = 3 ** (O + c - t) * unit + defect_unit
        if reduced != 2 ** (S + a) * output_unit:
            raise AssertionError("low-defect unit rewrite failed")
    elif t > O + c:
        case = "HIGH"
        cancellation_v3 = 0
        if n_v3 != O + c:
            raise AssertionError("high-defect valuation identity failed")
        reduced = unit + 3 ** (t - O - c) * defect_unit
        if reduced != 2 ** (S + a) * output_unit:
            raise AssertionError("high-defect unit rewrite failed")
    else:
        case = "RESONANT"
        cancellation_v3, cancellation_unit = valuation(unit + defect_unit, 3)
        if n_v3 != t + cancellation_v3:
            raise AssertionError("resonant cancellation identity failed")
        if cancellation_unit != 2 ** (S + a) * output_unit:
            raise AssertionError("resonant unit rewrite failed")

    if n_after_2 % 2 == 0:
        raise AssertionError("exact drain left an even quotient")
    return {
        "case": case,
        "c": c,
        "u": unit,
        "word": str(transition["word"]),
        "S": S,
        "O": O,
        "e": e,
        "defect_v3_t": t,
        "defect_unit_d": defect_unit,
        "drain_a": a,
        "numerator_v3": n_v3,
        "resonant_extra_v3": cancellation_v3,
        "target_c": output_c,
        "target_u": output_unit,
        "target": output,
        "chart_depth_increment": S + a,
    }


def root_first_transition(exponent: int, maximum_shortcut_steps: int) -> tuple[int, dict[str, Any]]:
    if exponent < 12 or exponent % 16 != 12:
        raise ValueError("root exponent must lie in C=12 (mod 16)")
    charge = 3**exponent
    transition = exact_recharge(charge, maximum_shortcut_steps)
    if transition["status"] != "defined" or transition["word"] != ROOT_WORD:
        raise AssertionError("theorem-driven root cylinder changed")
    a = int(transition["forced_one_blocks"])
    expected = 3 ** (a + 2) * (3 ** (exponent + 2) + 7) // 2 ** (a + 6)
    if int(transition["output"]) != expected:
        raise AssertionError("exact root formula failed")
    defect = defect_transition(charge, transition)
    if defect["case"] != "LOW" or defect["defect_v3_t"] != 2:
        raise AssertionError("root 010111 defect type changed")
    return expected, defect


@dataclass(frozen=True)
class TraceState:
    root_exponent: int
    depth: int
    charge: int
    previous_word: str
    previous_drain: int
    transition: dict[str, Any]


def root_trace(
    exponent: int, maximum_macro_depth: int, maximum_shortcut_steps: int
) -> tuple[list[TraceState], dict[str, Any]]:
    if maximum_macro_depth < 1:
        raise ValueError("macro depth must be positive")
    charge = 3**exponent
    previous_word = "ROOT"
    previous_drain = 0
    rows: list[TraceState] = []
    chart_depth = 0
    resource_rows: list[dict[str, Any]] = []
    terminal: dict[str, Any] | None = None
    for depth in range(maximum_macro_depth):
        transition = exact_recharge(charge, maximum_shortcut_steps)
        rows.append(
            TraceState(
                exponent,
                depth,
                charge,
                previous_word,
                previous_drain,
                transition,
            )
        )
        if transition["status"] != "defined":
            terminal = {
                "depth": depth,
                "status": transition["status"],
                "H": str(charge),
                "H_bits": charge.bit_length(),
                "H_sha256": integer_sha256(charge),
            }
            break
        defect = defect_transition(charge, transition)
        chart_depth += int(defect["chart_depth_increment"])
        resource_rows.append(
            {
                "depth": depth,
                "H_bits": charge.bit_length(),
                "D_chart_depth": chart_depth,
                "D_increment": int(defect["chart_depth_increment"]),
                "P": {
                    "word": defect["word"],
                    "case": defect["case"],
                    "c": defect["c"],
                    "u_mod_3^4": int(defect["u"]) % 3**4,
                    "u_mod_2^8": int(defect["u"]) % 2**8,
                    "drain_a": defect["drain_a"],
                    "numerator_v3": defect["numerator_v3"],
                },
                "chi": -chart_depth,
            }
        )
        previous_word = str(transition["word"])
        previous_drain = int(transition["forced_one_blocks"])
        charge = int(transition["output"])
    return rows, {
        "root_exponent": exponent,
        "ordinary_H0": str(3**exponent),
        "ordinary_x0": str(3 ** (exponent + 1) - 1),
        "defined_recharges": len(resource_rows),
        "resource_ledger": resource_rows,
        "terminal_or_frontier": terminal,
    }


def root_trace_task(
    task: tuple[int, int, int]
) -> tuple[int, list[TraceState], dict[str, Any]]:
    exponent, maximum_macro_depth, maximum_shortcut_steps = task
    root_first_transition(exponent, maximum_shortcut_steps)
    trace, ledger = root_trace(
        exponent, maximum_macro_depth, maximum_shortcut_steps
    )
    return exponent, trace, ledger


@dataclass(frozen=True)
class Architecture:
    name: str
    memory: bool
    previous_drain: bool
    dyadic: bool
    exponent_residue: bool


ARCHITECTURES = (
    Architecture("finite_charge", False, False, False, False),
    Architecture("finite_charge+memory", True, False, False, False),
    Architecture("finite_charge+carry", False, True, False, False),
    Architecture("finite_charge+dyadic", False, False, True, False),
    Architecture("finite_charge+exponent-residue", False, False, False, True),
    Architecture("finite_charge+memory+exponent-residue", True, False, False, True),
    Architecture("finite_charge+dyadic+exponent-residue", False, False, True, True),
    Architecture(
        "finite_charge+memory+carry+dyadic+exponent-residue",
        True,
        True,
        True,
        True,
    ),
)


def feature_key(
    state: TraceState,
    architecture: Architecture,
    ternary_digits: int,
    valuation_cap: int,
    dyadic_bits: int,
    exponent_bits: int,
    coordinates: tuple[int, int] | None = None,
) -> tuple[Any, ...]:
    c, unit = coordinates if coordinates is not None else primitive_coordinates(state.charge)
    key: list[Any] = [min(c, valuation_cap), unit % 3**ternary_digits]
    if architecture.memory:
        key.append(state.previous_word)
    if architecture.previous_drain:
        key.append(min(state.previous_drain, valuation_cap))
    if architecture.dyadic:
        key.append(unit % 2**dyadic_bits)
    if architecture.exponent_residue:
        key.append(c % 2**exponent_bits)
    return tuple(key)


def ambiguity_record(
    feature: tuple[Any, ...], states: Iterable[TraceState]
) -> dict[str, Any]:
    ordered = sorted(
        states,
        key=lambda row: (
            row.charge,
            row.root_exponent,
            row.depth,
            transition_cell_label(row.transition),
        ),
    )
    first = ordered[0]
    first_label = transition_cell_label(first.transition)
    other = next(
        row for row in ordered if transition_cell_label(row.transition) != first_label
    )
    return {
        "feature": list(feature),
        "first": {
            "H": str(first.charge),
            "H_sha256": integer_sha256(first.charge),
            "root_C": first.root_exponent,
            "depth": first.depth,
            "cell": first_label,
        },
        "conflicting": {
            "H": str(other.charge),
            "H_sha256": integer_sha256(other.charge),
            "root_C": other.root_exponent,
            "depth": other.depth,
            "cell": transition_cell_label(other.transition),
        },
    }


def audit_architecture(
    states: list[TraceState], architecture: Architecture, args: argparse.Namespace
) -> dict[str, Any]:
    best: tuple[tuple[int, int, int, int, int], dict[str, Any]] | None = None
    trial_count = 0
    trial_hasher = hashlib.sha256()
    prepared_states = [(state, primitive_coordinates(state.charge)) for state in states]
    dyadic_range = range(1, args.maximum_dyadic_bits + 1) if architecture.dyadic else (0,)
    exponent_range = (
        range(1, args.maximum_exponent_residue_bits + 1)
        if architecture.exponent_residue
        else (0,)
    )
    for ternary_digits in range(1, args.maximum_ternary_digits + 1):
        for valuation_cap in range(1, args.maximum_valuation_cap + 1):
            for dyadic_bits in dyadic_range:
                for exponent_bits in exponent_range:
                    buckets: dict[tuple[Any, ...], list[TraceState]] = defaultdict(list)
                    for state, coordinates in prepared_states:
                        buckets[
                            feature_key(
                                state,
                                architecture,
                                ternary_digits,
                                valuation_cap,
                                dyadic_bits,
                                exponent_bits,
                                coordinates,
                            )
                        ].append(state)
                    ambiguous = {
                        key: rows
                        for key, rows in buckets.items()
                        if len({transition_cell_label(row.transition) for row in rows}) > 1
                    }
                    minority_errors = 0
                    conflicting_pairs = 0
                    for rows in buckets.values():
                        counts = Counter(transition_cell_label(row.transition) for row in rows)
                        total = sum(counts.values())
                        minority_errors += total - max(counts.values())
                        conflicting_pairs += (
                            total * total - sum(value * value for value in counts.values())
                        ) // 2
                    feature_cost = (
                        ternary_digits
                        + valuation_cap
                        + dyadic_bits
                        + exponent_bits
                        + 4 * architecture.memory
                        + 4 * architecture.previous_drain
                        + 4 * architecture.dyadic
                        + 4 * architecture.exponent_residue
                    )
                    objective = (
                        minority_errors,
                        conflicting_pairs,
                        len(ambiguous),
                        feature_cost,
                        len(buckets),
                    )
                    record = {
                        "ternary_digits": ternary_digits,
                        "valuation_cap": valuation_cap,
                        "dyadic_bits": dyadic_bits,
                        "exponent_residue_bits": exponent_bits,
                        "observed_feature_cells": len(buckets),
                        "minority_transition_errors": minority_errors,
                        "conflicting_label_pairs": conflicting_pairs,
                        "ambiguous_feature_cells": len(ambiguous),
                        "objective": list(objective),
                    }
                    trial_count += 1
                    trial_hasher.update(canonical_json(record) + b"\n")
                    if best is None or objective < best[0]:
                        best = (objective, record)
    if best is None:
        raise AssertionError("architecture search was empty")
    best_record = dict(best[1])
    best_buckets: dict[tuple[Any, ...], list[TraceState]] = defaultdict(list)
    for state, coordinates in prepared_states:
        best_buckets[
            feature_key(
                state,
                architecture,
                int(best_record["ternary_digits"]),
                int(best_record["valuation_cap"]),
                int(best_record["dyadic_bits"]),
                int(best_record["exponent_residue_bits"]),
                coordinates,
            )
        ].append(state)
    best_ambiguous = {
        key: rows
        for key, rows in best_buckets.items()
        if len({transition_cell_label(row.transition) for row in rows}) > 1
    }
    least = None
    if best_ambiguous:
        records = [ambiguity_record(key, rows) for key, rows in best_ambiguous.items()]
        least = min(
            records,
            key=lambda row: (int(row["first"]["H"]), int(row["conflicting"]["H"])),
        )
    best_record["first_exact_ambiguity"] = least
    return {
        "architecture": architecture.name,
        "best_bounded_partition": best_record,
        "trial_count": trial_count,
        "trials_sha256": trial_hasher.hexdigest(),
        "universal_closed": False,
        "unbounded_obligation": (
            "finite observed separation does not prove that every predicate member has "
            "defined R or that its target remains in the predicate"
        ),
        "smallest_guard_ambiguity": best_record["first_exact_ambiguity"],
        "rejection_reason": (
            "exact observed ambiguity"
            if best_record["first_exact_ambiguity"] is not None
            else "bounded separation only; universal definedness and target inclusion unproved"
        ),
    }


def survival_depth(states: list[TraceState]) -> int:
    return sum(row.transition["status"] == "defined" for row in states)


def coherent_root_cylinder(
    traces: dict[int, list[TraceState]], maximum_precision_bits: int
) -> list[dict[str, Any]]:
    """Choose one nested exponent cylinder by worst-case tested survival."""

    rho = 12
    rows: list[dict[str, Any]] = []
    previous_rho = rho
    for bits in range(4, maximum_precision_bits + 1):
        modulus = 2**bits
        candidates = [rho] if bits == 4 else [previous_rho, previous_rho + 2 ** (bits - 1)]
        scored: list[tuple[tuple[int, int, int, int], int, list[int], list[int]]] = []
        for candidate in candidates:
            members = sorted(C for C in traces if C % modulus == candidate % modulus)
            depths = [survival_depth(traces[C]) for C in members]
            if not members:
                continue
            score = (min(depths), max(depths), len(members), -candidate)
            scored.append((score, candidate, members, depths))
        if not scored:
            rows.append(
                {
                    "precision_bits": bits,
                    "status": "no_tested_ordinary_representative",
                    "rho": previous_rho,
                    "modulus": modulus,
                }
            )
            break
        scored.sort(key=lambda row: row[0], reverse=True)
        score, rho, members, depths = scored[0]
        carry = 0 if bits == 4 else (rho - previous_rho) // 2 ** (bits - 1)
        least_bad = next(
            (
                C
                for C in members
                if survival_depth(traces[C]) == min(depths)
            ),
            None,
        )
        rows.append(
            {
                "precision_bits": bits,
                "status": "bounded_exact_test_only",
                "rho": rho,
                "modulus": modulus,
                "lift_bit": carry,
                "ordinary_representatives_tested": len(members),
                "least_representative": members[0],
                "minimum_defined_recharges": min(depths),
                "maximum_defined_recharges": max(depths),
                "least_minimum_survival_witness_C": least_bad,
                "canonical_address_stable_from_previous": rho == previous_rho,
            }
        )
        previous_rho = rho
    return rows


def grammar_record() -> dict[str, Any]:
    return {
        "coordinates": "H=3^c*u with c>=0, u positive, gcd(u,6)=1",
        "word_data": "w=(S,O,e), e=3^t*d, 3 does not divide d",
        "unbounded_binders": [
            "a=v2(3^(O+c)*u+e)-S",
            "v=v3(u+d) in the resonant case t=O+c",
        ],
        "transition_types": {
            "LOW_t_lt_O_plus_c": {
                "equation": "2^(S+a)u'=3^(O+c-t)u+d",
                "target": "(c',u')=(t+a,u')",
            },
            "HIGH_t_gt_O_plus_c": {
                "equation": "2^(S+a)u'=u+3^(t-O-c)d",
                "target": "(c',u')=(O+c+a,u')",
            },
            "RESONANT_t_eq_O_plus_c": {
                "equation": "2^(S+a)3^v*u'=u+d, v=v3(u+d)",
                "target": "(c',u')=(t+a+v,u')",
            },
        },
        "candidate_predicate_type": (
            "finite node types over unbounded (c,u,a,v), with exact word legality, "
            "valuation binders, dyadic/cross-prime guards, and clausewise target inclusion"
        ),
        "universal_checker_obligations": [
            "positive primitive source",
            "legal first-passage word and exact valuation binders",
            "RechargeThenDrain soundness",
            "target predicate inclusion after exact substitution",
            "total outgoing guard coverage",
            "nonempty ordinary root arithmetic progression",
        ],
        "fixed_chart_rank_filter": {
            "chi": "Int(v2(alpha))-Int(d)",
            "edge_law": "chi' = chi-(S+a)",
            "consequence": (
                "reject every finite SCC of fixed chart instances; a viable chart type "
                "must carry runtime rank unbounded below"
            ),
            "formal_status": (
                "kernel checked in KontoroC.OutwardChartRankNoGo: exact leading-balance "
                "rank drop and finite total graph contradiction"
            ),
        },
    }


def resonant_word_lemma_regression(maximum_word_length: int) -> dict[str, Any]:
    """Bounded exact audit of the mod-nine lemma requested as QM163a."""

    words, frontier = bounded_first_passage_words(maximum_word_length)
    relevant: list[dict[str, Any]] = []
    for row in words:
        if row.word == "1" or row.defect is None:
            continue
        t, defect_unit = valuation(int(row.defect), 3)
        if t != 1:
            continue
        right_v3, _ = valuation(defect_unit + 7 * 2**row.S, 3)
        if right_v3 != 1:
            raise AssertionError("bounded QM163a regression found a counterexample")
        relevant.append(
            {
                "word": row.word,
                "S": row.S,
                "O": row.O,
                "e": row.defect,
                "d": defect_unit,
                "v3_d_plus_7_times_2_pow_S": right_v3,
            }
        )
    return {
        "maximum_word_length": maximum_word_length,
        "complete_first_passage_words": len(words),
        "nonoutward_prefix_frontier": frontier,
        "words_with_v3_e_eq_1": len(relevant),
        "failures": 0,
        "relevant_rows_sha256": hashlib.sha256(canonical_json(relevant)).hexdigest(),
        "unbounded_status": "pending_companion_Lean_proof_QM163a",
    }


def minimal_terminal_ones(zero_count: int) -> int:
    if zero_count < 1:
        raise ValueError("resonant decoder needs a nonempty zero run")
    odd_count = 1
    while 3**odd_count <= 2 ** (zero_count + odd_count):
        odd_count += 1
    if 3 ** (odd_count - 1) > 2 ** (zero_count + odd_count - 1):
        raise AssertionError("minimal terminal-one count missed first passage")
    return odd_count


def resonant_decoder_regression(maximum_shortcut_steps: int) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for c in range(3):
        z = 2 * 3**c
        o = minimal_terminal_ones(z)
        S = z + o
        numerator = 2**z - 1
        t, d = valuation(numerator, 3)
        if t != c + 1:
            raise AssertionError("resonant decoder LTE calibration failed")
        word = "0" * z + "1" * o
        for q in (1, 3, 4, 9, 10):
            u = 2**S * q - d
            if u % 3 == 0:
                continue
            charge = 3**c * u
            transition = exact_recharge(charge, maximum_shortcut_steps)
            if transition["status"] != "defined" or transition["word"] != word:
                raise AssertionError("resonant decoder word regression changed")
            if int(transition["pre_drain"]) != 3 ** (c + o) * q:
                raise AssertionError("resonant decoder pre-drain identity failed")
            a, after_2 = valuation(q, 2)
            v, primitive = valuation(after_2, 3)
            expected = 3 ** (c + o + a + v) * primitive
            if int(transition["output"]) != expected:
                raise AssertionError("resonant decoder target identity failed")
            if not primitive <= q < u:
                raise AssertionError("resonant decoder payload did not decrease")
            rows.append(
                {
                    "c": c,
                    "z": z,
                    "o": o,
                    "S": S,
                    "d": d,
                    "q": q,
                    "source_u": u,
                    "target_u": primitive,
                    "target_c": c + o + a + v,
                    "word_sha256": hashlib.sha256(word.encode()).hexdigest(),
                }
            )
    return {
        "instances": len(rows),
        "maximum_c": 2,
        "all_exact_replays_pass": True,
        "all_primitive_payloads_strictly_decrease": True,
        "rows_sha256": hashlib.sha256(canonical_json(rows)).hexdigest(),
        "unbounded_status": "pending_companion_Lean_proof_QM164",
    }


def discrete_log9_mod_two_power(value: int, modulus_power: int) -> int:
    """Return q with 9^q=value mod 2^M for value=1 mod 8."""

    if modulus_power < 3 or value % 8 != 1:
        raise ValueError("base-nine logarithm requires M>=3 and value=1 mod8")
    q = 0
    for precision in range(3, modulus_power):
        modulus = 2 ** (precision + 1)
        lifted = q + 2 ** (precision - 3)
        old_holds = pow(9, q, modulus) == value % modulus
        lifted_holds = pow(9, lifted, modulus) == value % modulus
        if old_holds == lifted_holds:
            raise AssertionError("base-nine Hensel lift lost uniqueness")
        if lifted_holds:
            q = lifted
    if pow(9, q, 2**modulus_power) != value % 2**modulus_power:
        raise AssertionError("base-nine logarithm reconstruction failed")
    return q


def symbolic_sum_v2(exponent: int, constant: int, known_power: int) -> int:
    """Compute v2(3^exponent+constant) from modular powers only."""

    if (pow(3, exponent, 2**known_power) + constant) % 2**known_power:
        raise ValueError("claimed lower dyadic valuation is false")
    power = known_power
    while (pow(3, exponent, 2 ** (power + 1)) + constant) % 2 ** (power + 1) == 0:
        power += 1
    return power


def restorative_writer_decoder_cylinders(maximum_counter: int) -> dict[str, Any]:
    """Construct exact root-writer to resonant-decoder exponent cylinders."""

    if maximum_counter < 0:
        raise ValueError("restorative counter bound must be nonnegative")
    rows: list[dict[str, Any]] = []
    for c in range(maximum_counter + 1):
        z = 2 * 3**c
        o = minimal_terminal_ones(z)
        S = z + o
        d = (2**z - 1) // 3 ** (c + 1)
        D = S + c + 4
        constant = 7 + 2 ** (c + 4) * d
        target_residue = (-constant) % 2**D
        logarithm = discrete_log9_mod_two_power(target_residue, D)
        period = 2 ** (D - 2)
        C = (2 * logarithm - 2) % period
        if pow(3, C + 2, 2**D) != target_residue:
            raise AssertionError("writer-decoder exponent cylinder failed")
        compatible = c >= 2 and C % 16 == 12
        row: dict[str, Any] = {
            "counter_c": c,
            "decoder_zero_count_z": z,
            "decoder_one_count_o": o,
            "decoder_word_length_S": S,
            "decoder_d": str(d),
            "exponent_modulus_power": D - 2,
            "canonical_root_exponent_C": str(C),
            "canonical_root_exponent_bits": C.bit_length(),
            "C_mod_16": C % 16,
            "root_010111_compatible": compatible,
        }
        if compatible:
            root_drain = c - 2
            root_numerator_v2 = symbolic_sum_v2(C + 2, 7, c + 4)
            if root_numerator_v2 != c + 4:
                raise AssertionError("root writer has the wrong exact drain")
            total_v2 = symbolic_sum_v2(C + 2, constant, D)
            decoder_drain = total_v2 - D
            constant_v3, constant_unit = valuation(constant, 3)
            if C + 2 <= constant_v3:
                raise AssertionError("constant valuation does not determine decoder q")
            target_c = c + o + decoder_drain + constant_v3
            target_minimum_z = 2 * 3**target_c
            if constant.bit_length() >= C + 2:
                raise AssertionError("decoder constant is not smaller than its exponential rail")
            immediate_decoder_size_no_go = C + 3 <= target_minimum_z
            row.update(
                {
                    "root_drain_a": root_drain,
                    "decoder_drain_a": decoder_drain,
                    "decoder_q_v3": constant_v3,
                    "decoder_q_primitive_constant_unit": str(constant_unit),
                    "target_charge_exponent_c": target_c,
                    "ordinary_seed_encoding": f"3^({C + 1})-1",
                    "two_recharge_words": [ROOT_WORD, "0" * z + "1" * o],
                    "output_primitive_chart": {
                        "numerator": f"3^({C + 2})+{constant}",
                        "division_power_2": D + decoder_drain,
                        "division_power_3": constant_v3,
                    },
                    "immediate_resonant_decoder_size_no_go": immediate_decoder_size_no_go,
                    "size_no_go_reason": (
                        "C+3<=2*3^c_target implies output unit plus every resonant "
                        "decoder defect is smaller than its required 2^S address"
                        if immediate_decoder_size_no_go
                        else "displayed elementary size comparison is inconclusive"
                    ),
                }
            )
        rows.append(row)
    compatible_rows = [row for row in rows if row["root_010111_compatible"]]
    return {
        "maximum_counter": maximum_counter,
        "rows": rows,
        "rows_sha256": hashlib.sha256(canonical_json(rows)).hexdigest(),
        "compatible_counters": [row["counter_c"] for row in compatible_rows],
        "least_compatible_ordinary_root_exponent": (
            compatible_rows[0]["canonical_root_exponent_C"]
            if compatible_rows
            else None
        ),
        "unbounded_status": (
            "bounded exact cylinders; no invariant closure and no claim that the "
            "canonical exponents cohere as the counter grows"
        ),
    }


def build_audit(args: argparse.Namespace) -> dict[str, Any]:
    if args.maximum_root_exponent < 12 or args.maximum_root_exponent % 2:
        raise ValueError("root exponent bound must be at least 12 and even")
    if args.maximum_macro_depth < 1 or args.maximum_shortcut_steps < 1:
        raise ValueError("execution bounds must be positive")
    if args.processes < 1:
        raise ValueError("process count must be positive")
    if args.maximum_root_precision_bits < 4:
        raise ValueError("root precision must include C=12 mod 16")
    exponents = list(range(12, args.maximum_root_exponent + 1, 16))
    traces: dict[int, list[TraceState]] = {}
    ledgers: list[dict[str, Any]] = []
    all_states: list[TraceState] = []
    defect_counts: Counter[str] = Counter()
    status_counts: Counter[str] = Counter()
    root_tasks = [
        (exponent, args.maximum_macro_depth, args.maximum_shortcut_steps)
        for exponent in exponents
    ]
    if args.processes > 1:
        with mp.Pool(args.processes) as pool:
            root_results = pool.map(root_trace_task, root_tasks, chunksize=1)
    else:
        root_results = [root_trace_task(task) for task in root_tasks]
    for exponent, trace, ledger in root_results:
        traces[exponent] = trace
        ledgers.append(ledger)
        all_states.extend(trace)
        for state in trace:
            status_counts[state.transition["status"]] += 1
            if state.transition["status"] == "defined":
                defect_counts[defect_transition(state.charge, state.transition)["case"]] += 1

    architecture_tasks = [
        (all_states, architecture, args) for architecture in ARCHITECTURES
    ]
    if args.processes > 1:
        with mp.Pool(args.processes) as pool:
            architecture_rows = pool.starmap(audit_architecture, architecture_tasks)
    else:
        architecture_rows = [
            audit_architecture(states, architecture, task_args)
            for states, architecture, task_args in architecture_tasks
        ]
    coherent = coherent_root_cylinder(traces, args.maximum_root_precision_bits)
    champion = max(
        ledgers,
        key=lambda row: (row["defined_recharges"], -row["root_exponent"]),
    )
    least_terminal = min(
        (
            row
            for row in ledgers
            if row["terminal_or_frontier"] is not None
            and row["terminal_or_frontier"]["status"] != "unknown_frontier"
        ),
        key=lambda row: row["root_exponent"],
        default=None,
    )
    return {
        "meaning": (
            "bounded exact invariant-architecture CEGIS in primitive coordinates, "
            "restricted to descendants of C=12 mod16 pure-power roots"
        ),
        "bounds": {
            "maximum_root_exponent": args.maximum_root_exponent,
            "maximum_macro_depth": args.maximum_macro_depth,
            "maximum_shortcut_steps": args.maximum_shortcut_steps,
            "maximum_ternary_digits": args.maximum_ternary_digits,
            "maximum_valuation_cap": args.maximum_valuation_cap,
            "maximum_dyadic_bits": args.maximum_dyadic_bits,
            "maximum_exponent_residue_bits": args.maximum_exponent_residue_bits,
            "maximum_root_precision_bits": args.maximum_root_precision_bits,
            "maximum_word_length": args.maximum_word_length,
            "processes": args.processes,
            "maximum_restorative_counter": args.maximum_restorative_counter,
        },
        "grammar": grammar_record(),
        "resonant_return_no_go": {
            "word_lemma_regression": resonant_word_lemma_regression(
                args.maximum_word_length
            ),
            "research_derivation": (
                "QM163a forces any final return to H_L to have L=1; monotone "
                "recharge excludes C>=28 and the exact C=12 continuation has undefined R"
            ),
            "universal_status": "pending_companion_Lean_proof_QM163",
        },
        "resonant_decoder_family": resonant_decoder_regression(
            args.maximum_shortcut_steps
        ),
        "restorative_writer_decoder_cylinders": restorative_writer_decoder_cylinders(
            args.maximum_restorative_counter
        ),
        "exact_test_population": {
            "root_exponents": len(exponents),
            "least_C": exponents[0],
            "greatest_C": exponents[-1],
            "transition_states": len(all_states),
            "status_counts": dict(sorted(status_counts.items())),
            "defect_case_counts": dict(sorted(defect_counts.items())),
        },
        "architecture_outer_loop": architecture_rows,
        "coherent_root_cylinder": {
            "semantics": "one ancestry-compatible nested C residue, selected by tested worst-case survival",
            "rows": coherent,
            "ordinary_compatibility": (
                "an infinite natural exponent would require the canonical rho to stabilize; "
                "finite displayed stabilization is not enough"
            ),
        },
        "resource_ledger_champion": champion,
        "least_tested_terminal_root": least_terminal,
        "symbolic_transition_algebra_closed": False,
        "symbolic_transition_algebra_status": (
            "research normal form with exact bounded regression; universal Lean proof requested in QM163"
        ),
        "symbolic_transition_algebra_scope": (
            "the displayed LOW/HIGH/RESONANT identities normalize every already-legal "
            "recharge; they do not prove a total closed predicate"
        ),
        "universal_invariant": None,
        "counterexample": None,
        "claim_scope": (
            "exact arithmetic inside all displayed bounds; architecture separation and "
            "coherent cylinder survival are finite diagnostics only"
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
    champion = audit["resource_ledger_champion"]
    restorative = audit["restorative_writer_decoder_cylinders"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "root_exponents": audit["exact_test_population"]["root_exponents"],
        "transition_states": audit["exact_test_population"]["transition_states"],
        "defect_case_counts": audit["exact_test_population"]["defect_case_counts"],
        "champion_root_C": champion["root_exponent"],
        "champion_defined_recharges": champion["defined_recharges"],
        "restorative_compatible_counters": restorative["compatible_counters"],
        "least_restorative_root_C": restorative[
            "least_compatible_ordinary_root_exponent"
        ],
        "universal_invariant": audit["universal_invariant"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported primitive invariant CEGIS schema")
    args = argparse.Namespace(**stored["audit"]["bounds"])
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("primitive invariant artifact failed exact reconstruction")
    return report(stored)


def selftest() -> None:
    for exponent in (12, 28, 44):
        target, defect = root_first_transition(exponent, 20_000)
        if target <= 3**exponent or defect["case"] != "LOW":
            raise AssertionError("root regression changed")
    args = argparse.Namespace(
        maximum_root_exponent=76,
        maximum_macro_depth=5,
        maximum_shortcut_steps=20_000,
        maximum_ternary_digits=2,
        maximum_valuation_cap=3,
        maximum_dyadic_bits=3,
        maximum_exponent_residue_bits=3,
        maximum_root_precision_bits=6,
        maximum_word_length=12,
        processes=1,
        maximum_restorative_counter=2,
    )
    audit = build_audit(args)
    if audit["counterexample"] is not None or audit["universal_invariant"] is not None:
        raise AssertionError("bounded primitive invariant audit overclaimed")
    if audit["symbolic_transition_algebra_closed"]:
        raise AssertionError("finite primitive audit promoted an unproved universal schema")


def add_bounds(command: argparse.ArgumentParser) -> None:
    command.add_argument("--maximum-root-exponent", type=int, default=1000)
    command.add_argument("--maximum-macro-depth", type=int, default=24)
    command.add_argument("--maximum-shortcut-steps", type=int, default=250_000)
    command.add_argument("--maximum-ternary-digits", type=int, default=5)
    command.add_argument("--maximum-valuation-cap", type=int, default=8)
    command.add_argument("--maximum-dyadic-bits", type=int, default=10)
    command.add_argument("--maximum-exponent-residue-bits", type=int, default=10)
    command.add_argument("--maximum-root-precision-bits", type=int, default=10)
    command.add_argument("--maximum-word-length", type=int, default=24)
    command.add_argument("--processes", type=int, default=4)
    command.add_argument("--maximum-restorative-counter", type=int, default=5)


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
        print("outward primitive invariant CEGIS selftest: PASS")
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

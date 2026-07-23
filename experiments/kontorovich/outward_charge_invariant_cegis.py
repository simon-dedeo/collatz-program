#!/usr/bin/env python3
"""Exact bounded invariant-CEGIS for the odd-charge recharge map ``R``.

This is deliberately separate from next-word prediction.  It synthesizes
arithmetic predicates on positive odd charges, asks for the least exact
closure/definedness failure, and feeds that witness back to the predicate
learner.  The grammar contains valuation and congruence cylinders, exact
first-passage step cells, and named instances of a recursively parameterized
cylinder-family grammar.

Finite survival is only ``bounded_status``.  A periodic step-DNF receives a
universal closure verdict only when its complete arithmetic-progression
certificate is enumerated within the stated symbolic budget.  Family
predicates remain test-only unless an explicit all-parameter transition
certificate is supplied.  This worker never promotes either case to a
Collatz counterexample, and every artifact records ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


SCHEMA = "collatz-outward-charge-invariant-cegis-v1"
GRAMMAR_VERSION = "odd-charge-invariant-grammar-v1"
RESONANT_LENGTH = 17
RESONANT_SHIFT = 12


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def integer_sha256(value: int) -> str:
    if value < 0:
        raise ValueError("integer hash requires a nonnegative value")
    width = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(width, "big")).hexdigest()


def valuation(value: int, prime: int) -> tuple[int, int]:
    if value <= 0 or prime <= 1:
        raise ValueError("valuation requires a positive integer and prime")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent, value


def word_affine_constant(word: str) -> int:
    constant = 0
    length = 0
    for bit in word:
        if bit == "1":
            constant = 3 * constant + 2**length
        elif bit != "0":
            raise ValueError("parity words use only 0 and 1")
        length += 1
    return constant


def is_first_passage(word: str) -> bool:
    if not word:
        return False
    odds = 0
    for index, bit in enumerate(word, 1):
        odds += bit == "1"
        outward = 3**odds > 2**index
        if index < len(word) and outward:
            return False
        if index == len(word):
            return outward
    raise AssertionError("unreachable first-passage test")


def execute_word(word: str, source: int) -> int:
    state = source
    for bit in word:
        if state % 2 != (bit == "1"):
            raise AssertionError("word replay parity mismatch")
        state = (3 * state + 1) // 2 if bit == "1" else state // 2
    return state


def step_data(word: str, forced_one_blocks: int) -> dict[str, Any]:
    if not is_first_passage(word) or forced_one_blocks < 0:
        raise ValueError("invalid recharge step cell")
    S = len(word)
    O = word.count("1")
    A = word_affine_constant(word)
    numerator = A + 2**S - 3**O
    if numerator <= 0 or numerator % 3:
        raise AssertionError("first-passage defect is not positive integral")
    e = numerator // 3
    r = (-A * pow(3**O, -1, 2**S)) % 2**S
    a = forced_one_blocks
    modulus_exponent = S + a + 1
    h_residue = (
        (2 ** (S + a) - e) * pow(3**O, -1, 2**modulus_exponent)
    ) % 2**modulus_exponent
    if (3 * h_residue - 1 - r) % 2**S:
        raise AssertionError("exact drain residue missed its word cylinder")
    return {
        "word": word,
        "S": S,
        "O": O,
        "A": A,
        "e": e,
        "a": a,
        "source_residue_mod_2_power": h_residue,
        "source_modulus_power": modulus_exponent,
        "division_power": S + a,
    }


def step_cell_holds(charge: int, step: dict[str, Any]) -> bool:
    if charge <= 0 or charge % 2 == 0:
        return False
    power = int(step["source_modulus_power"])
    return charge % 2**power == int(step["source_residue_mod_2_power"])


def exact_recharge(charge: int, maximum_shortcut_steps: int) -> dict[str, Any]:
    """Evaluate the partial recharge map, distinguishing cutoff from failure."""

    if charge <= 0 or charge % 2 == 0:
        raise ValueError("R requires a positive odd charge")
    if maximum_shortcut_steps < 1:
        raise ValueError("shortcut-step bound must be positive")
    state = 3 * charge - 1
    word: list[str] = []
    odd_count = 0
    seen: dict[int, tuple[int, int]] = {}
    for _ in range(maximum_shortcut_steps):
        if state in (1, 2):
            return {
                "status": "undefined_terminal",
                "input": charge,
                "terminal_state": state,
                "steps": len(word),
                "word_prefix": "".join(word),
            }
        previous = seen.get(state)
        if previous is not None:
            old_length, old_odds = previous
            loop_length = len(word) - old_length
            loop_odds = odd_count - old_odds
            if 3**loop_odds <= 2**loop_length:
                return {
                    "status": "undefined_subcritical_lasso",
                    "input": charge,
                    "lasso_state": state,
                    "prefix_length": old_length,
                    "loop_length": loop_length,
                    "loop_odd_count": loop_odds,
                    "steps": len(word),
                    "word_prefix": "".join(word),
                }
        else:
            seen[state] = (len(word), odd_count)

        odd = state % 2
        word.append("1" if odd else "0")
        if odd:
            odd_count += 1
            state = (3 * state + 1) // 2
        else:
            state //= 2
        if 3**odd_count <= 2 ** len(word):
            continue

        literal_word = "".join(word)
        if not is_first_passage(literal_word) or state % 3 != 2:
            raise AssertionError("literal recharge missed first-passage semantics")
        pre_drain = (state + 1) // 3
        a, odd_part = valuation(pre_drain, 2)
        output = 3**a * odd_part
        step = step_data(literal_word, a)
        affine_numerator = 3 ** int(step["O"]) * charge + int(step["e"])
        if affine_numerator != 2 ** int(step["S"]) * pre_drain:
            raise AssertionError("pre-drain affine equation failed")
        if output != (
            3**a * affine_numerator // 2 ** int(step["division_power"])
        ):
            raise AssertionError("compressed recharge equation failed")
        if not step_cell_holds(charge, step):
            raise AssertionError("literal recharge missed exact step cell")
        output_v3, output_unit = valuation(output, 3)
        if output % 2 == 0 or output <= charge or output_v3 < a + 1:
            raise AssertionError("recharge growth/valuation theorem failed")
        return {
            "status": "defined",
            "input": charge,
            "output": output,
            "pre_drain": pre_drain,
            "steps": len(word),
            "word": literal_word,
            "S": step["S"],
            "O": step["O"],
            "A": step["A"],
            "e": step["e"],
            "forced_one_blocks": a,
            "division_power": step["division_power"],
            "output_v3": output_v3,
            "output_unit": output_unit,
        }
    return {
        "status": "unknown_frontier",
        "input": charge,
        "steps": maximum_shortcut_steps,
        "state_bits": state.bit_length(),
        "state_sha256": integer_sha256(state),
        "word_prefix_sha256": hashlib.sha256("".join(word).encode()).hexdigest(),
    }


def transition_step(transition: dict[str, Any]) -> dict[str, Any]:
    if transition["status"] != "defined":
        raise ValueError("undefined transition has no step cell")
    return step_data(str(transition["word"]), int(transition["forced_one_blocks"]))


def power_of_three_exponent(value: int) -> int | None:
    exponent, unit = valuation(value, 3)
    return exponent if unit == 1 else None


def resonant_parameter(value: int) -> int | None:
    if value % 3:
        return None
    shifted = value // 3 + 7
    if shifted % 2**RESONANT_LENGTH:
        return None
    return power_of_three_exponent(shifted // 2**RESONANT_LENGTH)


def family_parameter(kind: str, charge: int) -> int | None:
    if kind == "pure_power":
        return power_of_three_exponent(charge)
    if kind == "resonant":
        return resonant_parameter(charge)
    raise ValueError("unknown recursive family")


def family_value(kind: str, parameter: int) -> int:
    if parameter < 0:
        raise ValueError("family parameter must be nonnegative")
    if kind == "pure_power":
        return 3**parameter
    if kind == "resonant":
        return 3 * (2**RESONANT_LENGTH * 3**parameter - 7)
    raise ValueError("unknown recursive family")


def family_ast(kind: str, parameter_bits: int, residues: Iterable[int]) -> dict[str, Any]:
    modulus = 2**parameter_bits
    transforms = (
        [{"alpha": 1, "m": 1, "r": 0, "beta": 0, "d": 0}]
        if kind == "pure_power"
        else [
            {
                "alpha": 3 * 2**RESONANT_LENGTH,
                "m": 1,
                "r": 0,
                "beta": -21,
                "d": 0,
            }
        ]
    )
    return {
        "kind": kind,
        "grammar": "T0(t,z)=z; T{i+1}=(alpha*3^(m*t+r)*Ti+beta)/2^d",
        "recursive_depth": 1,
        "z_values": [1],
        "transforms": transforms,
        "domain": {
            "t_min": 1 if kind == "pure_power" else 0,
            "t_modulus": modulus,
            "t_residues": sorted({value % modulus for value in residues}),
        },
        "universal_transition_rule": None,
    }


def member_family(charge: int, family: dict[str, Any]) -> bool:
    parameter = family_parameter(str(family["kind"]), charge)
    if parameter is None:
        return False
    domain = family["domain"]
    return parameter >= int(domain["t_min"]) and (
        parameter % int(domain["t_modulus"]) in set(domain["t_residues"])
    )


def clause_member(charge: int, clause: dict[str, Any]) -> bool:
    if charge <= 0 or charge % 2 == 0:
        return False
    step = clause.get("step")
    if step is not None and not step_cell_holds(charge, step):
        return False
    c, unit = valuation(charge, 3)
    for atom in clause["atoms"]:
        kind = atom["kind"]
        if kind == "v3_eq" and c != int(atom["value"]):
            return False
        if kind == "v3_ge" and c < int(atom["value"]):
            return False
        if kind == "v3_mod" and c % int(atom["modulus"]) != int(atom["residue"]):
            return False
        if kind == "h_mod2" and charge % 2 ** int(atom["bits"]) != int(atom["residue"]):
            return False
        if kind == "unit_mod2" and unit % 2 ** int(atom["bits"]) != int(atom["residue"]):
            return False
        if kind == "unit_mod3" and unit % 3 ** int(atom["digits"]) != int(atom["residue"]):
            return False
    return True


def predicate_member(charge: int, candidate: dict[str, Any]) -> bool:
    return any(member_family(charge, family) for family in candidate["families"]) or any(
        clause_member(charge, clause) for clause in candidate["clauses"]
    )


@dataclass(frozen=True)
class Architecture:
    name: str
    require_step: bool
    allow_unit3: bool
    allow_dyadic: bool
    allow_families: bool = False


ARCHITECTURES = (
    Architecture("valuation", False, False, False),
    Architecture("valuation+primitive3", False, True, False),
    Architecture("valuation+dyadic", False, False, True),
    Architecture("valuation+primitive3+dyadic", False, True, True),
    Architecture("step+valuation", True, False, False),
    Architecture("step+valuation+primitive3", True, True, False),
    Architecture("step+valuation+primitive3+dyadic", True, True, True),
    Architecture("recursive-family+step-dnf", True, True, True, True),
)


def make_clause(
    charge: int,
    transition: dict[str, Any],
    architecture: Architecture,
    unit3_digits: int,
    dyadic_bits: int,
) -> dict[str, Any] | None:
    if architecture.require_step and transition["status"] != "defined":
        return None
    c, unit = valuation(charge, 3)
    atoms: list[dict[str, Any]] = [{"kind": "v3_eq", "value": c}]
    if unit3_digits:
        atoms.append(
            {
                "kind": "unit_mod3",
                "digits": unit3_digits,
                "residue": unit % 3**unit3_digits,
            }
        )
    if dyadic_bits:
        atoms.append(
            {
                "kind": "h_mod2",
                "bits": dyadic_bits,
                "residue": charge % 2**dyadic_bits,
            }
        )
    return {
        "step": transition_step(transition) if architecture.require_step else None,
        "atoms": atoms,
    }


def normalize_clauses(clauses: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    unique = {canonical_json(clause): clause for clause in clauses}
    return [unique[key] for key in sorted(unique)]


def description_complexity(candidate: dict[str, Any]) -> dict[str, Any]:
    families = candidate["families"]
    clauses = candidate["clauses"]
    recursive_depth = max(
        [int(family["recursive_depth"]) for family in families], default=0
    )
    parameter_dimension = len(families)
    atoms = sum(len(clause["atoms"]) + (clause["step"] is not None) for clause in clauses)
    modulus_budget = 0
    coefficient_bits = 0
    threshold_bits = 0
    for clause in clauses:
        for atom in clause["atoms"]:
            modulus_budget += int(atom.get("bits", atom.get("digits", 0)))
            threshold_bits += int(atom.get("value", 0)).bit_length()
        if clause["step"] is not None:
            modulus_budget += int(clause["step"]["source_modulus_power"])
            coefficient_bits += int(clause["step"]["e"]).bit_length()
    for family in families:
        modulus_budget += int(math.log2(int(family["domain"]["t_modulus"])))
        threshold_bits += int(family["domain"]["t_min"]).bit_length()
        for transform in family["transforms"]:
            coefficient_bits += sum(
                abs(int(transform[key])).bit_length()
                for key in ("alpha", "m", "r", "beta", "d")
            )
    kappa = [
        recursive_depth,
        parameter_dimension,
        len(families),
        len(clauses),
        atoms,
        modulus_budget,
        coefficient_bits,
        threshold_bits,
    ]
    scalar = (
        64 * recursive_depth
        + 32 * parameter_dimension
        + 16 * len(families)
        + 8 * max(0, len(clauses) - 1)
        + 2 * atoms
        + modulus_budget
        + coefficient_bits
        + threshold_bits
    )
    return {"kappa": kappa, "scalar": scalar}


def finalize_candidate(
    architecture: Architecture,
    clauses: list[dict[str, Any]],
    families: list[dict[str, Any]],
    parameters: dict[str, Any],
) -> dict[str, Any]:
    candidate = {
        "kind": "finite_dnf_plus_recursive_families",
        "architecture": architecture.name,
        "clauses": normalize_clauses(clauses),
        "families": sorted(families, key=lambda row: canonical_json(row)),
        "synthesis_parameters": parameters,
    }
    candidate["description_complexity"] = description_complexity(candidate)
    candidate["canonical_sha256"] = hashlib.sha256(canonical_json(candidate)).hexdigest()
    return candidate


def synthesize_candidate(
    architecture: Architecture,
    positives: list[int],
    negatives: set[int],
    transition_cache: dict[int, dict[str, Any]],
    maximum_unit3_digits: int,
    maximum_dyadic_bits: int,
    maximum_family_parameter_bits: int,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    unit3_range = (
        range(1, maximum_unit3_digits + 1) if architecture.allow_unit3 else (0,)
    )
    dyadic_range = (
        range(1, maximum_dyadic_bits + 1) if architecture.allow_dyadic else (0,)
    )
    family_range = range(maximum_family_parameter_bits + 1) if architecture.allow_families else (0,)
    tried = 0
    feasible: list[tuple[tuple[Any, ...], dict[str, Any]]] = []
    for family_bits in family_range:
        family_positive: dict[str, list[int]] = {"pure_power": [], "resonant": []}
        if architecture.allow_families:
            for charge in positives:
                for kind in family_positive:
                    parameter = family_parameter(kind, charge)
                    if parameter is not None:
                        family_positive[kind].append(parameter)
                        break
        families = [
            family_ast(kind, family_bits, parameters)
            for kind, parameters in family_positive.items()
            if parameters
        ]
        nonfamily_positives = [
            charge
            for charge in positives
            if not any(member_family(charge, family) for family in families)
        ]
        for unit3_digits in unit3_range:
            for dyadic_bits in dyadic_range:
                tried += 1
                clauses: list[dict[str, Any]] = []
                representable = True
                for charge in nonfamily_positives:
                    transition = transition_cache[charge]
                    clause = make_clause(
                        charge,
                        transition,
                        architecture,
                        unit3_digits,
                        dyadic_bits,
                    )
                    if clause is None:
                        representable = False
                        break
                    clauses.append(clause)
                if not representable:
                    continue
                candidate = finalize_candidate(
                    architecture,
                    clauses,
                    families,
                    {
                        "unit3_digits": unit3_digits,
                        "dyadic_bits": dyadic_bits,
                        "family_parameter_bits": family_bits,
                    },
                )
                if not all(predicate_member(charge, candidate) for charge in positives):
                    raise AssertionError("synthesized predicate lost a positive example")
                if any(predicate_member(charge, candidate) for charge in negatives):
                    continue
                complexity = candidate["description_complexity"]
                key = (
                    int(complexity["scalar"]),
                    complexity["kappa"],
                    candidate["canonical_sha256"],
                )
                feasible.append((key, candidate))
    if not feasible:
        return None, {"parameterizations_tried": tried, "feasible": 0}
    feasible.sort(key=lambda row: row[0])
    return feasible[0][1], {
        "parameterizations_tried": tried,
        "feasible": len(feasible),
        "selected_rank": 0,
    }


def recharge_public_record(transition: dict[str, Any]) -> dict[str, Any]:
    result = dict(transition)
    for key in ("input", "output", "pre_drain", "terminal_state", "lasso_state"):
        if key in result:
            result[key] = str(result[key])
    return result


def failure_record(
    charge: int, transition: dict[str, Any], kind: str, candidate: dict[str, Any]
) -> dict[str, Any]:
    result = {
        "kind": kind,
        "H": str(charge),
        "H_bits": charge.bit_length(),
        "H_sha256": integer_sha256(charge),
        "candidate_sha256": candidate["canonical_sha256"],
        "transition": recharge_public_record(transition),
    }
    if transition["status"] == "defined":
        output = int(transition["output"])
        result["R_H"] = str(output)
        result["failed_target_clause_truth"] = [
            clause_member(output, clause) for clause in candidate["clauses"]
        ]
        result["failed_target_family_truth"] = [
            member_family(output, family) for family in candidate["families"]
        ]
    return result


def clause_representatives(clause: dict[str, Any]) -> list[int]:
    step = clause.get("step")
    if step is None:
        return []
    k2 = int(step["source_modulus_power"])
    r2 = int(step["source_residue_mod_2_power"])
    c_atom = next(atom for atom in clause["atoms"] if atom["kind"] == "v3_eq")
    c = int(c_atom["value"])
    unit_atom = next(
        (atom for atom in clause["atoms"] if atom["kind"] == "unit_mod3"), None
    )
    if unit_atom is None:
        k3 = c + 1
        residues3 = [3**c, 2 * 3**c]
    else:
        digits = int(unit_atom["digits"])
        k3 = c + digits
        residues3 = [3**c * int(unit_atom["residue"])]
    h_atom = next((atom for atom in clause["atoms"] if atom["kind"] == "h_mod2"), None)
    if h_atom is not None and int(h_atom["bits"]) > k2:
        if int(h_atom["residue"]) % 2**k2 != r2:
            return []
        k2 = int(h_atom["bits"])
        r2 = int(h_atom["residue"])
    modulus2 = 2**k2
    modulus3 = 3**k3
    result: list[int] = []
    for r3 in residues3:
        lift = ((r3 - r2) * pow(modulus2, -1, modulus3)) % modulus3
        residue = r2 + modulus2 * lift
        modulus = modulus2 * modulus3
        if residue == 0:
            residue = modulus
        if clause_member(residue, clause):
            result.extend([residue, residue + modulus])
    return result


def bounded_audit(
    candidate: dict[str, Any],
    positives: list[int],
    maximum_charge: int,
    maximum_family_parameter: int,
    maximum_shortcut_steps: int,
) -> dict[str, Any]:
    tested: set[int] = set(positives)
    bounded_members = 0
    for charge in range(1, maximum_charge + 1, 2):
        if predicate_member(charge, candidate):
            tested.add(charge)
            bounded_members += 1
    family_members = 0
    for family in candidate["families"]:
        domain = family["domain"]
        for parameter in range(int(domain["t_min"]), maximum_family_parameter + 1):
            charge = family_value(str(family["kind"]), parameter)
            if member_family(charge, family):
                tested.add(charge)
                family_members += 1
    for clause in candidate["clauses"]:
        tested.update(clause_representatives(clause))

    unknowns: list[dict[str, Any]] = []
    traces = 0
    for charge in sorted(tested):
        if not predicate_member(charge, candidate):
            continue
        transition = exact_recharge(charge, maximum_shortcut_steps)
        traces += 1
        if transition["status"] == "unknown_frontier":
            unknowns.append(recharge_public_record(transition))
            continue
        if transition["status"] != "defined":
            return {
                "bounded_status": "rejected",
                "first_failure": failure_record(
                    charge, transition, "R_undefined", candidate
                ),
                "unknown_frontiers": unknowns,
                "coverage": {
                    "exact_R_evaluations": traces,
                    "odd_H_exhaustive_bound": maximum_charge,
                    "bounded_members": bounded_members,
                    "family_parameter_bound": maximum_family_parameter,
                    "family_members_before_dedup": family_members,
                    "distinct_test_points": len(tested),
                },
            }
        output = int(transition["output"])
        if not predicate_member(output, candidate):
            return {
                "bounded_status": "rejected",
                "first_failure": failure_record(
                    charge, transition, "closure_failure", candidate
                ),
                "unknown_frontiers": unknowns,
                "coverage": {
                    "exact_R_evaluations": traces,
                    "odd_H_exhaustive_bound": maximum_charge,
                    "bounded_members": bounded_members,
                    "family_parameter_bound": maximum_family_parameter,
                    "family_members_before_dedup": family_members,
                    "distinct_test_points": len(tested),
                },
            }
    return {
        "bounded_status": "survived_displayed_tests",
        "first_failure": None,
        "unknown_frontiers": unknowns,
        "coverage": {
            "exact_R_evaluations": traces,
            "odd_H_exhaustive_bound": maximum_charge,
            "bounded_members": bounded_members,
            "family_parameter_bound": maximum_family_parameter,
            "family_members_before_dedup": family_members,
            "distinct_test_points": len(tested),
        },
    }


def symbolic_periodic_closure(
    candidate: dict[str, Any], maximum_progression_period: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    if candidate["families"]:
        return {
            "universal_closed": False,
            "decision": "unsupported_recursive_family_without_transition_rule",
            "obligations": [
                "supply an all-parameter source-family to target-family identity",
                "prove integrality and Presburger/residue-domain inclusion",
            ],
        }
    if not candidate["clauses"] or any(
        clause.get("step") is None for clause in candidate["clauses"]
    ):
        return {
            "universal_closed": False,
            "decision": "unsupported_clause_without_branch_homogeneous_step_cell",
            "obligations": [
                "partition every clause into legal first-passage step cells",
                "prove the partition covers the whole predicate",
            ],
        }

    target_k2 = max(
        int(clause["step"]["source_modulus_power"])
        for clause in candidate["clauses"]
    )
    target_k3 = 1
    for clause in candidate["clauses"]:
        c = int(next(atom["value"] for atom in clause["atoms"] if atom["kind"] == "v3_eq"))
        unit_atom = next(
            (atom for atom in clause["atoms"] if atom["kind"] == "unit_mod3"), None
        )
        target_k3 = max(target_k3, c + (int(unit_atom["digits"]) if unit_atom else 1))
        h_atom = next((atom for atom in clause["atoms"] if atom["kind"] == "h_mod2"), None)
        if h_atom is not None:
            target_k2 = max(target_k2, int(h_atom["bits"]))
    target_modulus = 2**target_k2 * 3**target_k3
    progression_rows: list[dict[str, Any]] = []
    least_failure: tuple[int, dict[str, Any]] | None = None
    for clause_index, clause in enumerate(candidate["clauses"]):
        step = clause["step"]
        representatives = clause_representatives(clause)[::2]
        if not representatives:
            continue
        c = int(next(atom["value"] for atom in clause["atoms"] if atom["kind"] == "v3_eq"))
        unit_atom = next(
            (atom for atom in clause["atoms"] if atom["kind"] == "unit_mod3"), None
        )
        source_k3 = c + (int(unit_atom["digits"]) if unit_atom else 1)
        source_k2 = int(step["source_modulus_power"])
        h_atom = next((atom for atom in clause["atoms"] if atom["kind"] == "h_mod2"), None)
        if h_atom is not None:
            source_k2 = max(source_k2, int(h_atom["bits"]))
        source_modulus = 2**source_k2 * 3**source_k3
        division_power = int(step["division_power"])
        delta_numerator = 3 ** (int(step["a"]) + int(step["O"])) * source_modulus
        if delta_numerator % 2**division_power:
            raise AssertionError("source cylinder lacks enough division precision")
        output_delta = delta_numerator // 2**division_power
        period = target_modulus // math.gcd(target_modulus, output_delta)
        if period > maximum_progression_period:
            return {
                "universal_closed": False,
                "decision": "symbolic_period_budget_exhausted",
                "required_period": period,
                "maximum_progression_period": maximum_progression_period,
                "progressions_completed": progression_rows,
            }
        for base in representatives:
            base_output = (
                3 ** int(step["a"])
                * (3 ** int(step["O"]) * base + int(step["e"]))
                // 2**division_power
            )
            row = {
                "source_clause": clause_index,
                "source_base": str(base),
                "source_stride": str(source_modulus),
                "output_base": str(base_output),
                "output_stride": str(output_delta),
                "membership_period_in_parameter": period,
            }
            progression_rows.append(row)
            for parameter in range(period):
                output = base_output + output_delta * parameter
                if predicate_member(output, candidate):
                    continue
                charge = base + source_modulus * parameter
                transition = exact_recharge(charge, maximum_shortcut_steps)
                if transition["status"] != "defined" or int(transition["output"]) != output:
                    raise AssertionError("symbolic progression failed literal replay")
                failure = failure_record(charge, transition, "closure_failure", candidate)
                if least_failure is None or charge < least_failure[0]:
                    least_failure = (charge, failure)
    if least_failure is not None:
        return {
            "universal_closed": False,
            "decision": "exact_symbolic_closure_failure",
            "first_failure": least_failure[1],
            "progressions": progression_rows,
        }
    return {
        "universal_closed": True,
        "decision": "complete_periodic_progression_enumeration",
        "progressions": progression_rows,
        "certificate_scope": (
            "every source clause is one or more exact arithmetic progressions; "
            "R is affine on each and target membership is periodic in its parameter"
        ),
    }


def witness_integer(failure: dict[str, Any] | None) -> int | None:
    return None if failure is None else int(failure["H"])


def choose_first_failure(*failures: dict[str, Any] | None) -> dict[str, Any] | None:
    present = [failure for failure in failures if failure is not None]
    return min(present, key=lambda row: (int(row["H"]), row["kind"])) if present else None


def run_architecture(
    architecture: Architecture,
    anchor: int,
    args: argparse.Namespace,
) -> dict[str, Any]:
    positives = [anchor]
    negatives: set[int] = set()
    transition_cache: dict[int, dict[str, Any]] = {}
    rounds: list[dict[str, Any]] = []
    smallest_failure: dict[str, Any] | None = None
    final_status = "cegis_round_limit"
    final_candidate: dict[str, Any] | None = None
    final_symbolic: dict[str, Any] | None = None

    def synthesize_for(
        trial_positives: list[int], trial_negatives: set[int]
    ) -> tuple[dict[str, Any] | None, dict[str, Any]]:
        for trial_charge in trial_positives:
            transition_cache.setdefault(
                trial_charge,
                exact_recharge(trial_charge, args.maximum_shortcut_steps),
            )
        return synthesize_candidate(
            architecture,
            trial_positives,
            trial_negatives,
            transition_cache,
            args.maximum_unit3_digits,
            args.maximum_dyadic_bits,
            args.maximum_family_parameter_bits,
        )

    for iteration in range(args.maximum_cegis_rounds):
        candidate, synthesis = synthesize_for(positives, negatives)
        if candidate is None:
            final_status = "architecture_cannot_separate_accumulated_examples"
            rounds.append(
                {
                    "iteration": iteration,
                    "synthesis": synthesis,
                    "candidate": None,
                    "refinement": "reject_architecture",
                }
            )
            break
        final_candidate = candidate
        bounded = bounded_audit(
            candidate,
            positives,
            args.maximum_charge,
            args.maximum_family_parameter,
            args.maximum_shortcut_steps,
        )
        symbolic = symbolic_periodic_closure(
            candidate,
            args.maximum_symbolic_progression_period,
            args.maximum_shortcut_steps,
        )
        final_symbolic = symbolic
        failure = choose_first_failure(
            bounded["first_failure"], symbolic.get("first_failure")
        )
        smallest_failure = choose_first_failure(smallest_failure, failure)
        round_record = {
            "iteration": iteration,
            "positive_examples": len(positives),
            "negative_examples": len(negatives),
            "synthesis": synthesis,
            "candidate": candidate,
            "bounded_audit": bounded,
            "symbolic_closure": symbolic,
            "cegis_counterexample": failure,
        }
        if failure is None:
            if symbolic["universal_closed"] and not bounded["unknown_frontiers"]:
                final_status = "universal_closure_certificate_found"
                round_record["refinement"] = None
            else:
                final_status = "bounded_survivor_only"
                round_record["refinement"] = None
            rounds.append(round_record)
            break
        witness = int(failure["H"])
        transition = exact_recharge(witness, args.maximum_shortcut_steps)
        if witness in positives:
            if transition["status"] != "defined":
                final_status = "reachable_positive_has_undefined_R"
                round_record["refinement"] = "reject_architecture_at_required_positive"
                rounds.append(round_record)
                break
            output = int(transition["output"])
            if output in positives:
                raise AssertionError("positive closure witness did not enlarge examples")
            positives.append(output)
            round_record["refinement"] = {
                "kind": "add_required_reachable_output",
                "output_bits": output.bit_length(),
                "output_sha256": integer_sha256(output),
            }
        else:
            exclusion_negatives = set(negatives)
            exclusion_negatives.add(witness)
            exclusion_candidate, exclusion_synthesis = synthesize_for(
                positives, exclusion_negatives
            )
            inclusion_candidate: dict[str, Any] | None = None
            inclusion_synthesis: dict[str, Any] | None = None
            output: int | None = None
            if transition["status"] == "defined":
                output = int(transition["output"])
                if output not in positives:
                    inclusion_candidate, inclusion_synthesis = synthesize_for(
                        positives + [output], negatives
                    )

            choices: list[tuple[tuple[Any, ...], str]] = []
            if exclusion_candidate is not None:
                complexity = exclusion_candidate["description_complexity"]
                choices.append(
                    ((int(complexity["scalar"]), complexity["kappa"], 0), "exclude")
                )
            if inclusion_candidate is not None:
                complexity = inclusion_candidate["description_complexity"]
                choices.append(
                    ((int(complexity["scalar"]), complexity["kappa"], 1), "include")
                )
            if not choices:
                final_status = "architecture_cannot_refine_exact_witness"
                round_record["refinement"] = {
                    "kind": "reject_architecture",
                    "exclude_synthesis": exclusion_synthesis,
                    "include_synthesis": inclusion_synthesis,
                }
                rounds.append(round_record)
                break
            choices.sort(key=lambda row: row[0])
            choice = choices[0][1]
            if choice == "exclude":
                negatives = exclusion_negatives
                round_record["refinement"] = {
                    "kind": "exclude_spurious_source",
                    "H": str(witness),
                    "next_description_complexity": exclusion_candidate[
                        "description_complexity"
                    ],
                    "alternative_include_feasible": inclusion_candidate is not None,
                }
            else:
                if output is None:
                    raise AssertionError("include refinement lacks a defined target")
                positives.append(output)
                round_record["refinement"] = {
                    "kind": "include_target_of_spurious_source",
                    "output_bits": output.bit_length(),
                    "output_sha256": integer_sha256(output),
                    "next_description_complexity": inclusion_candidate[
                        "description_complexity"
                    ],
                    "alternative_exclude_feasible": exclusion_candidate is not None,
                }
        rounds.append(round_record)
    ordinary = {
        "kind": "explicit_ordinary_anchor",
        "H0": str(anchor),
        "H0_bits": anchor.bit_length(),
        "H0_sha256": integer_sha256(anchor),
        "x0_equals_3H0_minus_1": str(3 * anchor - 1),
        "anchor_membership_in_final_candidate": (
            predicate_member(anchor, final_candidate) if final_candidate is not None else False
        ),
        "recharge_equivalence_reference": (
            "KontoroC.OutwardInvariantBridge."
            "partialMap_invariant_gives_not_collatz, with hsound supplied by "
            "OutwardBoundaryRenewal.recharge_then_drain_properties"
        ),
        "coherent_dyadic_carry_obligation": "not_applicable_to_explicit_H0",
    }
    return {
        "architecture": architecture.name,
        "status": final_status,
        "rounds": rounds,
        "smallest_closure_or_definedness_failure": smallest_failure,
        "final_candidate_sha256": (
            final_candidate["canonical_sha256"] if final_candidate is not None else None
        ),
        "final_universal_closed": (
            bool(final_symbolic["universal_closed"]) if final_symbolic is not None else False
        ),
        "ordinary_seed_obligation": ordinary,
    }


def grammar_record() -> dict[str, Any]:
    grammar = {
        "version": GRAMMAR_VERSION,
        "predicate": "finite DNF of clauses, optionally union named recursive families",
        "clause": "Cell(w,a) optional AND arithmetic atoms",
        "step_cell": {
            "conditions": [
                "3H-1 == r_w (mod 2^S)",
                "v2(3^O*H+e_w) == S+a",
            ],
            "legal_map": "R(H)=3^a*(3^O*H+e_w)/2^(S+a)",
        },
        "atom_catalog": [
            "v3(H)=q",
            "v3(H)>=q",
            "v3(H)=r (mod 2^j)",
            "H=r (mod 2^k)",
            "primitive(H)=r (mod 2^k)",
            "primitive(H)=s (mod 3^ell)",
            "primitive(H)=alpha*3^v3(H)+beta (mod 2^k)",
            "primitive(H)=alpha*2^v3(H)+beta (mod 3^ell)",
        ],
        "implemented_synthesis_atoms": ["v3(H)=q", "H mod 2^k", "primitive mod 3^ell"],
        "recursive_family": (
            "T0(t,z)=z; T{i+1}(t,z)=(alpha_i*3^(m_i*t+r_i)*Ti+beta_i)/2^d_i"
        ),
        "implemented_family_instances": [
            "3^t",
            "3*(2^17*3^t-7)",
        ],
        "complexity_order": [
            "recursive_depth",
            "parameter_dimension",
            "family_clauses",
            "DNF_clauses",
            "atoms",
            "modulus_budget",
            "coefficient_bitlength",
            "threshold_bitlength",
        ],
    }
    grammar["sha256"] = hashlib.sha256(canonical_json(grammar)).hexdigest()
    return grammar


def exact_cegis(args: argparse.Namespace) -> dict[str, Any]:
    for name in (
        "maximum_charge",
        "maximum_shortcut_steps",
        "maximum_cegis_rounds",
        "maximum_unit3_digits",
        "maximum_dyadic_bits",
        "maximum_family_parameter_bits",
        "maximum_family_parameter",
        "maximum_symbolic_progression_period",
    ):
        if int(getattr(args, name)) < 1:
            raise ValueError(f"{name} must be positive")
    anchor = family_value("resonant", args.anchor_resonant_parameter)
    architectures = [
        run_architecture(architecture, anchor, args) for architecture in ARCHITECTURES
    ]
    any_universal = any(row["final_universal_closed"] for row in architectures)
    return {
        "meaning": "bounded exact invariant-CEGIS over the partial odd-charge recharge map R",
        "grammar": grammar_record(),
        "bounds": {
            "maximum_charge": args.maximum_charge,
            "maximum_shortcut_steps": args.maximum_shortcut_steps,
            "maximum_cegis_rounds": args.maximum_cegis_rounds,
            "maximum_unit3_digits": args.maximum_unit3_digits,
            "maximum_dyadic_bits": args.maximum_dyadic_bits,
            "maximum_family_parameter_bits": args.maximum_family_parameter_bits,
            "maximum_family_parameter": args.maximum_family_parameter,
            "maximum_symbolic_progression_period": args.maximum_symbolic_progression_period,
            "anchor_resonant_parameter": args.anchor_resonant_parameter,
        },
        "anchor": {
            "theorem_driven_family": "H_L=3*(2^17*3^L-7) -> 3^(L+12)",
            "L": args.anchor_resonant_parameter,
            "H0": str(anchor),
            "H0_bits": anchor.bit_length(),
            "H0_sha256": integer_sha256(anchor),
            "ordinary_seed_x0": str(3 * anchor - 1),
        },
        "architectures": architectures,
        "separation_of_claims": {
            "bounded_survival": "only survived the explicitly displayed finite domains",
            "symbolic_closure": "true only after complete periodic progression enumeration",
            "ordinary_seed": "explicit H0 avoids a merely 2-adic inverse limit",
            "carry_growth": (
                "projective candidates would additionally require one coherent dyadic path "
                "with eventual-zero or sub-2 carry; none is promoted here"
            ),
            "unboundedness": (
                "OutwardInvariantBridge.invariant_set_not_bddAbove proves every "
                "nonempty recharge-closed invariant must be unbounded; finite tables cannot qualify"
            ),
            "actual_collatz_counterexample": False,
        },
        "universal_candidate_found": any_universal,
        "counterexample": None,
        "claim_scope": (
            "exact bounded CEGIS failures and, where completed, finite periodic symbolic "
            "closure checks; no unbounded recursive-family closure and no nonterminating orbit"
        ),
    }


def build_artifact(args: argparse.Namespace) -> dict[str, Any]:
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": exact_cegis(args),
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "anchor_bits": audit["anchor"]["H0_bits"],
        "architectures": [
            {
                "architecture": row["architecture"],
                "status": row["status"],
                "rounds": len(row["rounds"]),
                "smallest_failure_H": (
                    row["smallest_closure_or_definedness_failure"]["H"]
                    if row["smallest_closure_or_definedness_failure"] is not None
                    else None
                ),
                "universal_closed": row["final_universal_closed"],
            }
            for row in audit["architectures"]
        ],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported invariant-CEGIS schema")
    args = argparse.Namespace(**stored["audit"]["bounds"])
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("invariant-CEGIS artifact failed exact reconstruction")
    return report(stored)


def selftest() -> None:
    resonant = family_value("resonant", 0)
    first = exact_recharge(resonant, 10_000)
    if first["status"] != "defined" or int(first["output"]) != 3**12:
        raise AssertionError("resonant recharge regression changed")
    step = transition_step(first)
    if not step_cell_holds(resonant, step):
        raise AssertionError("step-cell regression changed")
    short = exact_recharge(5, 10_000)
    step_architecture = next(
        architecture
        for architecture in ARCHITECTURES
        if architecture.name == "step+valuation"
    )
    short_clause = make_clause(5, short, step_architecture, 0, 0)
    if short_clause is None:
        raise AssertionError("defined short recharge lost its clause")
    short_candidate = finalize_candidate(
        step_architecture,
        [short_clause],
        [],
        {"unit3_digits": 0, "dyadic_bits": 0, "family_parameter_bits": 0},
    )
    symbolic = symbolic_periodic_closure(short_candidate, 100, 10_000)
    if symbolic["decision"] != "exact_symbolic_closure_failure":
        raise AssertionError("periodic symbolic closure selftest changed")
    if int(symbolic["first_failure"]["H"]) != 5:
        raise AssertionError("symbolic checker lost the least closure witness")
    args = argparse.Namespace(
        maximum_charge=501,
        maximum_shortcut_steps=10_000,
        maximum_cegis_rounds=4,
        maximum_unit3_digits=2,
        maximum_dyadic_bits=3,
        maximum_family_parameter_bits=2,
        maximum_family_parameter=16,
        maximum_symbolic_progression_period=2_000,
        anchor_resonant_parameter=0,
    )
    audit = exact_cegis(args)
    if audit["counterexample"] is not None:
        raise AssertionError("bounded invariant CEGIS overclaimed")
    if len(audit["architectures"]) != len(ARCHITECTURES):
        raise AssertionError("architecture catalog changed")


def add_bounds(command: argparse.ArgumentParser) -> None:
    command.add_argument("--maximum-charge", type=int, default=200_001)
    command.add_argument("--maximum-shortcut-steps", type=int, default=250_000)
    command.add_argument("--maximum-cegis-rounds", type=int, default=64)
    command.add_argument("--maximum-unit3-digits", type=int, default=4)
    command.add_argument("--maximum-dyadic-bits", type=int, default=8)
    command.add_argument("--maximum-family-parameter-bits", type=int, default=8)
    command.add_argument("--maximum-family-parameter", type=int, default=800)
    command.add_argument("--maximum-symbolic-progression-period", type=int, default=1_000_000)
    command.add_argument("--anchor-resonant-parameter", type=int, default=688)


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
        print("outward charge invariant CEGIS selftest: PASS")
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

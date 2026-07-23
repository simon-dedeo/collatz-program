#!/usr/bin/env python3
"""Exact coherent-cylinder CEGIS for alternating writer--decoder cells.

The cell starts with the first-passage writer ``010111``.  Its exact drain
selects a counter ``c >= 2``.  It is followed by the resonant decoder
``0^(2*3^c) 1^o`` and by a prescribed decoder drain ``b >= 0``.  For every
finite sequence of symbols ``(c,b)`` the worker constructs the unique nested
2-adic cylinder of root exponents and checks the coefficient identities and
all exact dyadic valuations symbolically.

Finite cylinder existence is deliberately *not* treated as survival: an
ordinary root exponent exists only if the canonical exponent addresses
eventually stop carrying.  The beam is therefore ranked by exact exponent
carry, canonical-address growth, and schedule description complexity.  It
also replays canonical representatives and stores their first failure.  The
artifact always records ``universal_invariant: null`` and
``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from outward_charge_invariant_cegis import integer_sha256
from outward_primitive_invariant_cegis import minimal_terminal_ones


SCHEMA = "collatz-outward-writer-decoder-cegis-v1"
ROOT_WORD = "010111"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def exact_v2_affine_power3(
    exponent: int,
    coefficient: int,
    constant: int,
    known_lower_bound: int = 0,
) -> int:
    """Return v2(coefficient*3^exponent+constant) without expanding 3^exponent."""

    if exponent < 0 or coefficient <= 0 or constant < 0:
        raise ValueError("positive affine-power data required")
    if known_lower_bound < 0:
        raise ValueError("valuation lower bound must be nonnegative")
    if (
        coefficient * pow(3, exponent, 2**known_lower_bound) + constant
    ) % 2**known_lower_bound:
        raise ValueError("claimed valuation lower bound is false")
    power = known_lower_bound
    while (
        coefficient * pow(3, exponent, 2 ** (power + 1)) + constant
    ) % 2 ** (power + 1) == 0:
        power += 1
    return power


def lift_base3_exponent(
    target: int,
    modulus_power: int,
    initial_exponent: int,
    initial_precision: int,
) -> int | None:
    """Lift 3^E=target mod 2^M from E mod 2^K in linear-many squarings."""

    if modulus_power < 3 or initial_precision < 0:
        raise ValueError("invalid base-three lift precision")
    modulus = 2**modulus_power
    target %= modulus
    if initial_precision == 0:
        if target % 8 == 1:
            exponent = 0
        elif target % 8 == 3:
            exponent = 1
        else:
            return None
        precision = 1
    else:
        exponent = initial_exponent % 2**initial_precision
        precision = initial_precision
        small_modulus = 2 ** (precision + 2)
        if pow(3, exponent, small_modulus) != target % small_modulus:
            return None

    current = pow(3, exponent, modulus)
    toggle = pow(3, 2**precision, modulus)
    target_precision = modulus_power - 2
    while precision < target_precision:
        mask = 2 ** (precision + 3) - 1
        if current & mask != target & mask:
            exponent += 2**precision
            current = current * toggle % modulus
        toggle = toggle * toggle % modulus
        precision += 1
    if pow(3, exponent, modulus) != target:
        raise AssertionError("base-three Hensel reconstruction failed")
    return exponent


@dataclass(frozen=True)
class Cell:
    c: int
    b: int
    z: int
    o: int
    S: int
    d: int
    Bg: int
    Dg: int


def make_cell(c: int, b: int) -> Cell:
    if c < 2 or b < 0:
        raise ValueError("writer--decoder cells require c>=2 and b>=0")
    z = 2 * 3**c
    o = minimal_terminal_ones(z)
    S = z + o
    numerator = 2**z - 1
    d = numerator // 3 ** (c + 1)
    if numerator != 3 ** (c + 1) * d or d % 2 == 0 or d % 3 == 0:
        raise AssertionError("resonant decoder LTE identity failed")
    if not (3 ** (o - 1) <= 2 ** (S - 1) and 3**o > 2**S):
        raise AssertionError("decoder is not first passage")
    Bg = 7 + 2 ** (c + 4) * d
    Dg = S + c + 4 + b
    if not 3 ** (c + o + b + 2) > 2**Dg:
        raise AssertionError("composite cell is not outward")
    return Cell(c, b, z, o, S, d, Bg, Dg)


@dataclass(frozen=True)
class ChartState:
    A: int
    B: int
    D: int
    C: int
    K: int
    path: tuple[tuple[int, int], ...]
    carries: tuple[int, ...]
    zero_carry_suffix: int


ROOT = ChartState(0, 0, 0, 0, 0, (), (), 0)


def verify_state(state: ChartState) -> None:
    if state.D == 0:
        if state != ROOT:
            raise AssertionError("only the root chart has depth zero")
        return
    if state.K != state.D - 1 or not 0 <= state.C < 2**state.K:
        raise AssertionError("noncanonical exponent address")
    modulus = 2 ** (state.D + 1)
    numerator = (pow(3, state.C + state.A, modulus) + state.B) % modulus
    if numerator != 2**state.D:
        raise AssertionError("chart does not represent an odd integer cylinder")


def extend_state(state: ChartState, cell: Cell) -> tuple[ChartState, int | None]:
    """Construct and verify the unique coherent child cylinder."""

    verify_state(state)
    modulus_power = state.D + cell.Dg + 1
    modulus = 2**modulus_power
    inverse_nine = pow(9, -1, modulus)
    target = inverse_nine * (
        2 ** (state.D + cell.Dg)
        - 9 * state.B
        - 2**state.D * cell.Bg
    ) % modulus
    exponent = lift_base3_exponent(
        target,
        modulus_power,
        state.C + state.A,
        state.K,
    )
    if exponent is None:
        raise AssertionError("coherent writer--decoder child unexpectedly absent")
    new_K = modulus_power - 2
    new_C = (exponent - state.A) % 2**new_K
    if state.K and new_C % 2**state.K != state.C:
        raise AssertionError("child exponent cylinder does not extend its parent")
    carry = None if state.K == 0 else (new_C - state.C) // 2**state.K
    if carry is not None and carry < 0:
        raise AssertionError("canonical exponent carry is negative")

    new_A = state.A + cell.c + cell.o + cell.b + 2
    new_B = 3 ** (cell.c + cell.o + cell.b) * (
        9 * state.B + 2**state.D * cell.Bg
    )
    new_D = state.D + cell.Dg
    new_state = ChartState(
        new_A,
        new_B,
        new_D,
        new_C,
        new_K,
        state.path + ((cell.c, cell.b),),
        state.carries + (() if carry is None else (carry,)),
        state.zero_carry_suffix + 1 if carry == 0 else 0,
    )

    # Exact symbolic valuation checks at the canonical representative.  The
    # same congruences hold throughout its new exponent cylinder.
    old_numerator_modulus = 2 ** (state.D + 1)
    old_numerator = (
        pow(3, new_C + state.A, old_numerator_modulus) + state.B
    ) % old_numerator_modulus
    if state.D and old_numerator != 2**state.D:
        raise AssertionError("child lost the parent odd chart")
    writer_power = state.D + cell.c + 5
    writer_modulus = 2**writer_power
    writer_numerator = (
        9 * (pow(3, new_C + state.A, writer_modulus) + state.B)
        + 7 * 2**state.D
    ) % writer_modulus
    if writer_numerator != 2 ** (state.D + cell.c + 4):
        raise AssertionError("writer drain counter is not exact")
    pair_numerator = (
        9 * (pow(3, new_C + state.A, modulus) + state.B)
        + 2**state.D * cell.Bg
    ) % modulus
    if pair_numerator != 2 ** (state.D + cell.Dg):
        raise AssertionError("decoder drain counter is not exact")
    verify_state(new_state)
    return new_state, carry


def least_period(path: tuple[tuple[int, int], ...]) -> int:
    if not path:
        return 0
    for period in range(1, len(path) + 1):
        if all(path[index] == path[index % period] for index in range(len(path))):
            return period
    raise AssertionError("finite word has no period")


def factor_complexity(path: tuple[tuple[int, int], ...], width: int) -> int:
    if width < 1 or width > len(path):
        return 0
    return len({path[index : index + width] for index in range(len(path) - width + 1)})


def description_cost(path: tuple[tuple[int, int], ...]) -> int:
    if not path:
        return 0
    period = least_period(path)
    distinct = len(set(path))
    turns = sum(path[index] != path[index - 1] for index in range(1, len(path)))
    return 4 * period + 2 * distinct + turns


def state_score(state: ChartState) -> tuple[int, int, int, int, tuple[tuple[int, int], ...]]:
    last_carry = state.carries[-1] if state.carries else 0
    return (
        -state.zero_carry_suffix,
        last_carry,
        state.C.bit_length(),
        description_cost(state.path),
        state.path,
    )


def state_summary(state: ChartState, carry: int | None = None) -> dict[str, Any]:
    shown_carry = state.carries[-1] if carry is None and state.carries else carry
    widths = range(1, min(5, len(state.path)) + 1)
    return {
        "path": [[c, b] for c, b in state.path],
        "path_sha256": hashlib.sha256(canonical_json(state.path)).hexdigest(),
        "path_description_cost": description_cost(state.path),
        "least_prefix_period": least_period(state.path),
        "factor_complexity_through_5": {
            str(width): factor_complexity(state.path, width) for width in widths
        },
        "A": state.A,
        "B_bits": state.B.bit_length(),
        "B_sha256": integer_sha256(state.B),
        "D": state.D,
        "canonical_C": str(state.C),
        "canonical_C_bits": state.C.bit_length(),
        "exponent_precision_K": state.K,
        "last_exponent_carry": None if shown_carry is None else str(shown_carry),
        "last_exponent_carry_bits": (
            None if shown_carry is None else shown_carry.bit_length()
        ),
        "zero_carry_suffix": state.zero_carry_suffix,
        "nonzero_carries": sum(carry_value != 0 for carry_value in state.carries),
    }


def canonical_replay(state: ChartState, args: argparse.Namespace) -> dict[str, Any]:
    """Replay the canonical natural exponent and return its first exact failure."""

    verify_state(state)
    fixed_C = state.C
    current = state
    rows: list[dict[str, Any]] = []
    failure: dict[str, Any] | None = None
    for replay_depth in range(args.maximum_canonical_replay_steps):
        exponent = fixed_C + current.A
        writer_constant = 9 * current.B + 7 * 2**current.D
        writer_numerator_v2 = exact_v2_affine_power3(
            exponent,
            9,
            writer_constant,
            current.D + 1,
        )
        writer_value_v2 = writer_numerator_v2 - current.D
        c = writer_value_v2 - 4
        if c < 2:
            failure = {
                "replay_depth": replay_depth,
                "kind": "writer_not_in_010111_counter_family",
                "v2_9H_plus_7": writer_value_v2,
                "derived_c": c,
            }
            break
        if c > args.maximum_canonical_replay_counter:
            failure = {
                "replay_depth": replay_depth,
                "kind": "derived_counter_above_replay_bound",
                "v2_9H_plus_7": writer_value_v2,
                "derived_c": c,
                "maximum_canonical_replay_counter": (
                    args.maximum_canonical_replay_counter
                ),
            }
            break

        base_cell = make_cell(c, 0)
        pair_constant = 9 * current.B + 2**current.D * base_cell.Bg
        guaranteed_power = current.D + c + 4
        pair_numerator_v2 = exact_v2_affine_power3(
            exponent,
            9,
            pair_constant,
            guaranteed_power,
        )
        pair_value_v2 = pair_numerator_v2 - current.D
        base_decoder_power = base_cell.S + c + 4
        if pair_value_v2 < base_decoder_power:
            failure = {
                "replay_depth": replay_depth,
                "kind": "resonant_decoder_address_shortfall",
                "derived_c": c,
                "v2_9H_plus_Bg": pair_value_v2,
                "required_at_least": base_decoder_power,
                "shortfall": base_decoder_power - pair_value_v2,
            }
            break
        b = pair_value_v2 - base_decoder_power
        if b > args.maximum_canonical_replay_drain:
            failure = {
                "replay_depth": replay_depth,
                "kind": "derived_decoder_drain_above_replay_bound",
                "derived_c": c,
                "derived_b": b,
                "maximum_canonical_replay_drain": (
                    args.maximum_canonical_replay_drain
                ),
            }
            break

        cell = make_cell(c, b)
        child, carry = extend_state(current, cell)
        if carry != 0 or child.C != fixed_C:
            raise AssertionError("canonical exact replay did not have zero address carry")
        rows.append(
            {
                "replay_depth": replay_depth,
                "symbol": [c, b],
                "D_before": current.D,
                "D_after": child.D,
                "A_after": child.A,
                "B_after_bits": child.B.bit_length(),
                "B_after_sha256": integer_sha256(child.B),
                "exact_zero_exponent_carry": True,
            }
        )
        current = child

    if failure is None:
        failure = {
            "replay_depth": args.maximum_canonical_replay_steps,
            "kind": "bounded_replay_frontier",
        }
    return {
        "prefix_path": [[c, b] for c, b in state.path],
        "fixed_canonical_C": str(fixed_C),
        "fixed_canonical_C_bits": fixed_C.bit_length(),
        "ordinary_seed_encoding": f"3^({fixed_C + 1})-1",
        "successful_zero_carry_cells": len(rows),
        "rows": rows,
        "first_failure": failure,
        "claim_scope": (
            "exact symbolic replay of one ordinary exponent through the displayed "
            "cells; a bounded replay frontier is not nontermination"
        ),
    }


def bounded_beam(args: argparse.Namespace) -> dict[str, Any]:
    alphabet = [
        make_cell(c, b)
        for c in range(args.minimum_counter, args.maximum_counter + 1)
        for b in range(args.maximum_decoder_drain + 1)
    ]
    beam = [ROOT]
    rows: list[dict[str, Any]] = []
    all_previous_states_retained = True
    edge_hasher = hashlib.sha256()
    smallest_nonzero_failure: dict[str, Any] | None = None
    for depth in range(1, args.maximum_depth + 1):
        candidates: list[ChartState] = []
        zero_edges = 0
        minimum_nonzero: tuple[int, ChartState] | None = None
        for state in beam:
            for cell in alphabet:
                child, carry = extend_state(state, cell)
                candidates.append(child)
                edge_record = {
                    "parent_path": state.path,
                    "symbol": (cell.c, cell.b),
                    "child_C": str(child.C),
                    "child_K": child.K,
                    "carry": carry,
                }
                edge_hasher.update(canonical_json(edge_record) + b"\n")
                if carry == 0:
                    zero_edges += 1
                elif carry is not None and (
                    minimum_nonzero is None or carry < minimum_nonzero[0]
                ):
                    minimum_nonzero = (carry, child)
        candidates.sort(key=state_score)
        tested_edges = len(candidates)
        exhaustive = all_previous_states_retained
        if minimum_nonzero is not None:
            witness = state_summary(minimum_nonzero[1], minimum_nonzero[0])
            if smallest_nonzero_failure is None or (
                int(witness["canonical_C"]), witness["path"]
            ) < (
                int(smallest_nonzero_failure["canonical_C"]),
                smallest_nonzero_failure["path"],
            ):
                smallest_nonzero_failure = witness
        rows.append(
            {
                "depth": depth,
                "parents_expanded": len(beam),
                "alphabet_size": len(alphabet),
                "tested_edges": tested_edges,
                "exhaustive_over_full_alphabet_at_this_depth": exhaustive,
                "zero_exponent_carry_edges": zero_edges,
                "minimum_nonzero_carry": (
                    None if minimum_nonzero is None else str(minimum_nonzero[0])
                ),
                "minimum_nonzero_carry_bits": (
                    None
                    if minimum_nonzero is None
                    else minimum_nonzero[0].bit_length()
                ),
                "champions": [
                    state_summary(candidate)
                    for candidate in candidates[: args.champions_per_depth]
                ],
            }
        )
        retained = min(args.beam_width, len(candidates))
        all_previous_states_retained = exhaustive and retained == len(candidates)
        beam = candidates[:retained]
    replay_states = beam[: args.canonical_replay_candidates]
    canonical_replays = [canonical_replay(state, args) for state in replay_states]
    return {
        "alphabet": [
            {
                "c": cell.c,
                "b": cell.b,
                "z": cell.z,
                "o": cell.o,
                "S": cell.S,
                "d": str(cell.d),
                "Bg": str(cell.Bg),
                "Dg": cell.Dg,
            }
            for cell in alphabet
        ],
        "depth_rows": rows,
        "tested_edges_sha256": edge_hasher.hexdigest(),
        "smallest_nonzero_address_failure": smallest_nonzero_failure,
        "canonical_replays": canonical_replays,
        "canonical_replay_failure_counts": {
            kind: sum(
                row["first_failure"]["kind"] == kind for row in canonical_replays
            )
            for kind in sorted(
                {row["first_failure"]["kind"] for row in canonical_replays}
            )
        },
        "maximum_successful_zero_carry_replay_cells": max(
            (row["successful_zero_carry_cells"] for row in canonical_replays),
            default=0,
        ),
        "final_beam": [
            state_summary(state) for state in beam[: args.final_beam_witnesses]
        ],
        "bounded_verdict": (
            "no exact zero-carry edge in the explored coherent cylinders"
            if all(row["zero_exponent_carry_edges"] == 0 for row in rows)
            else "finite exact zero-carry events found; eventual stabilization unproved"
        ),
    }


def theorem_record() -> dict[str, Any]:
    return {
        "cell_semantics": {
            "writer_output": "3^c*q, q=(9H+7)/2^(c+4)",
            "decoder_data": (
                "z=2*3^c, d=(2^z-1)/3^(c+1), "
                "v2(q+d)=S+b"
            ),
            "gate": "v2(9H+Bg)=Dg=S+c+4+b",
            "chart_update": {
                "A_prime": "A+c+o+b+2",
                "B_prime": "3^(c+o+b)*(9B+2^D*Bg)",
                "D_prime": "D+Dg",
            },
        },
        "address_carry_law": {
            "precision": "K_n=D_n-1 after the first cell",
            "recurrence": "rho_(n+1)=rho_n+2^(D_n-1)*ell_n, ell_n>=0",
            "ordinary_gate": (
                "one natural exponent C forces ell_n=0 whenever "
                "D_n>floor(log2(C))+1"
            ),
            "nonzero_carry_lower_bound": "C>=2^(D_n-1)",
            "minimum_cell_depth": 55,
            "uniform_finite_consequence": (
                "a nonzero carry after n completed cells requires C>=2^(55*n-1)"
            ),
            "status": "research derivation; companion Lean request QM166",
        },
        "selector_complexity": {
            "eventually_periodic_symbols": (
                "universally impossible: a period composes to "
                "(3^P*H+K)/2^L with 3^P>2^L and K>0"
            ),
            "kernel_checked_support": (
                "ShortcutParityPeriodicNoGo already excludes periodic and ultimately "
                "periodic concatenations of outward shortcut blocks"
            ),
            "bounded_aperiodic_symbols": (
                "not excluded; Morse-Hedlund forces factor complexity p(k)>=k+1"
            ),
            "counter_growth_scope": (
                "c_n or b_n need not tend to infinity; what must grow is runtime "
                "chart depth, and a bounded selector must retain unbounded word complexity"
            ),
        },
    }


def architecture_record(beam: dict[str, Any]) -> list[dict[str, Any]]:
    replay_failures = [
        {
            "fixed_canonical_C": row["fixed_canonical_C"],
            "prefix_path": row["prefix_path"],
            "successful_zero_carry_cells": row["successful_zero_carry_cells"],
            "first_failure": row["first_failure"],
        }
        for row in beam["canonical_replays"]
    ]
    least_replay_failure = min(
        replay_failures,
        key=lambda row: (int(row["fixed_canonical_C"]), row["prefix_path"]),
        default=None,
    )
    return [
        {
            "architecture": "fixed_or_eventually_periodic_(c,b)",
            "description_complexity": "finite period",
            "status": "universally_rejected",
            "smallest_closure_failure": (
                "positive affine period would require (3^P-2^L)H+K=0"
            ),
        },
        {
            "architecture": "bounded_aperiodic_(c,b)_with_growing_chart_depth",
            "description_complexity": "factor complexity at least k+1",
            "status": "bounded_CEGIS_only",
            "smallest_closure_failure": least_replay_failure,
        },
        {
            "architecture": "unbounded_arithmetic_counter_selector",
            "description_complexity": "pending parametric recurrence",
            "status": "not_rejected_and_not_certified",
            "smallest_closure_failure": None,
        },
    ]


def build_audit(args: argparse.Namespace) -> dict[str, Any]:
    if args.minimum_counter < 2 or args.maximum_counter < args.minimum_counter:
        raise ValueError("invalid counter interval")
    if args.maximum_decoder_drain < 0 or args.maximum_depth < 1:
        raise ValueError("invalid drain or depth bound")
    if args.beam_width < 1 or args.champions_per_depth < 1:
        raise ValueError("beam and witness bounds must be positive")
    if args.canonical_replay_candidates < 1 or args.maximum_canonical_replay_steps < 1:
        raise ValueError("canonical replay bounds must be positive")
    if args.maximum_canonical_replay_counter < 2:
        raise ValueError("canonical replay counter bound must be at least two")
    if args.maximum_canonical_replay_drain < 0:
        raise ValueError("canonical replay drain bound must be nonnegative")
    beam = bounded_beam(args)
    return {
        "meaning": (
            "bounded exact arithmetic CEGIS on coherent nested exponent cylinders "
            "for alternating writer--resonant-decoder cells"
        ),
        "bounds": {
            "minimum_counter": args.minimum_counter,
            "maximum_counter": args.maximum_counter,
            "maximum_decoder_drain": args.maximum_decoder_drain,
            "maximum_depth": args.maximum_depth,
            "beam_width": args.beam_width,
            "champions_per_depth": args.champions_per_depth,
            "final_beam_witnesses": args.final_beam_witnesses,
            "canonical_replay_candidates": args.canonical_replay_candidates,
            "maximum_canonical_replay_steps": args.maximum_canonical_replay_steps,
            "maximum_canonical_replay_counter": (
                args.maximum_canonical_replay_counter
            ),
            "maximum_canonical_replay_drain": args.maximum_canonical_replay_drain,
        },
        "exact_semantics_and_theorems": theorem_record(),
        "coherent_cylinder_beam": beam,
        "selector_architecture_outer_loop": architecture_record(beam),
        "symbolic_transition_algebra_closed": True,
        "unbounded_invariant_closed": False,
        "universal_invariant": None,
        "counterexample": None,
        "claim_scope": (
            "every displayed edge is an exact all-members cylinder identity; the beam "
            "coverage is exhaustive only where explicitly marked, and finite cylinder "
            "existence is not ordinary nontermination"
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
    beam = audit["coherent_cylinder_beam"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "depth": audit["bounds"]["maximum_depth"],
        "alphabet_size": len(beam["alphabet"]),
        "zero_carry_edges_by_depth": [
            row["zero_exponent_carry_edges"] for row in beam["depth_rows"]
        ],
        "bounded_verdict": beam["bounded_verdict"],
        "canonical_replay_failure_counts": beam[
            "canonical_replay_failure_counts"
        ],
        "maximum_successful_zero_carry_replay_cells": beam[
            "maximum_successful_zero_carry_replay_cells"
        ],
        "universal_invariant": audit["universal_invariant"],
        "counterexample": audit["counterexample"],
    }


def verify_artifact(path: Path) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported writer--decoder CEGIS schema")
    args = argparse.Namespace(**stored["audit"]["bounds"])
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("writer--decoder artifact failed exact reconstruction")
    return report(stored)


def selftest() -> None:
    for c in range(2, 5):
        for b in range(3):
            cell = make_cell(c, b)
            if cell.Dg < 55 or cell.Bg % 2 != 1:
                raise AssertionError("cell regression changed")
    # Check the fast lift against literal exponentiation on small precisions.
    for modulus_power in range(3, 18):
        period = 2 ** (modulus_power - 2)
        for exponent in range(min(period, 32)):
            target = pow(3, exponent, 2**modulus_power)
            rebuilt = lift_base3_exponent(target, modulus_power, 0, 0)
            if rebuilt != exponent % period:
                raise AssertionError("base-three lift selftest failed")
    args = argparse.Namespace(
        minimum_counter=2,
        maximum_counter=3,
        maximum_decoder_drain=1,
        maximum_depth=3,
        beam_width=16,
        champions_per_depth=2,
        final_beam_witnesses=2,
        canonical_replay_candidates=2,
        maximum_canonical_replay_steps=2,
        maximum_canonical_replay_counter=5,
        maximum_canonical_replay_drain=16,
    )
    audit = build_audit(args)
    if audit["counterexample"] is not None or audit["universal_invariant"] is not None:
        raise AssertionError("bounded writer--decoder audit overclaimed")
    if not audit["symbolic_transition_algebra_closed"]:
        raise AssertionError("exact cell algebra was not checked")


def add_bounds(command: argparse.ArgumentParser) -> None:
    command.add_argument("--minimum-counter", type=int, default=2)
    command.add_argument("--maximum-counter", type=int, default=4)
    command.add_argument("--maximum-decoder-drain", type=int, default=2)
    command.add_argument("--maximum-depth", type=int, default=10)
    command.add_argument("--beam-width", type=int, default=128)
    command.add_argument("--champions-per-depth", type=int, default=5)
    command.add_argument("--final-beam-witnesses", type=int, default=12)
    command.add_argument("--canonical-replay-candidates", type=int, default=12)
    command.add_argument("--maximum-canonical-replay-steps", type=int, default=4)
    command.add_argument("--maximum-canonical-replay-counter", type=int, default=6)
    command.add_argument("--maximum-canonical-replay-drain", type=int, default=64)


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
        print("outward writer--decoder CEGIS selftest: PASS")
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

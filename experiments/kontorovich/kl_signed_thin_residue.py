#!/usr/bin/env python3
"""Exact bounded audit of a thin signed-controller reset language.

The reset modes in this worker are literal pairs ``(c, N)`` with a negative
signed Syracuse controller state ``c`` and a shortcut shadow length ``N``.
For a positive reset state

    x = c + 2**N * m,

the first ``N`` shortcut parity choices agree with those of ``c``.  If ``O``
of those sources are odd and ``c_end = T**N(c)``, exact subtraction gives

    T**N(x) = c_end + 3**O * m.

Resetting to ``(c_next, N_next)`` therefore requires

    2**N_next * m_next = 3**O * m + c_end - c_next.

For fixed current mode, ``m -> c_end + 3**O*m`` is a 2-adic affine
homeomorphism.  A complete cover by universally outward next-mode parity
cylinders would consequently be a complete outward prefix code, which is the
already-closed Two-Kraft architecture.  This worker does not retry it.

Instead, inside the explicit box ``-center_bound <= c < 0`` and
``1 <= N <= max_controller_depth``, it extracts the proper prefix-free
language of minimal outward next modes, checks its exact dyadic and tilted
Kraft masses, and checks every affine pullback at precision ``2**B``.  It
then enumerates finite concatenations of this proper code and records the
canonical extension lifts

    R_(u v) = R_u + 2**|u| * lift(u,v).

An ordinary infinite reset program would need these lifts eventually to be
zero.  Finite depth cannot decide that tail property, so the artifact always
contains ``counterexample: null``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


SCHEMA = "collatz-kl-signed-thin-residue-v1"


def signed_syracuse(x: int) -> int:
    """The literal shortcut Syracuse map on all integers."""

    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


@dataclass(frozen=True)
class Trace:
    start: int
    depth: int
    parity_word: tuple[int, ...]
    endpoint: int
    odd_count: int
    affine_offset: int

    @property
    def numerator(self) -> int:
        return 3**self.odd_count

    @property
    def denominator(self) -> int:
        return 1 << self.depth

    @property
    def outward(self) -> bool:
        return self.denominator < self.numerator


def signed_trace(start: int, depth: int) -> Trace:
    if start >= 0 or depth < 1:
        raise ValueError("a controller trace needs start < 0 and depth >= 1")
    value = start
    word: list[int] = []
    odd_count = 0
    offset = 0
    for source_index in range(depth):
        bit = value & 1
        word.append(bit)
        if bit:
            odd_count += 1
            offset = 3 * offset + (1 << source_index)
        value = signed_syracuse(value)
    trace = Trace(start, depth, tuple(word), value, odd_count, offset)
    if trace.denominator * trace.endpoint != (
        trace.numerator * trace.start + trace.affine_offset
    ):
        raise AssertionError("signed shortcut affine identity failed")
    return trace


def replay_word(start: int, word: tuple[int, ...]) -> int:
    value = start
    for expected in word:
        if (value & 1) != expected:
            raise AssertionError("literal shortcut replay missed its parity word")
        value = signed_syracuse(value)
    return value


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def parity_residue(word: tuple[int, ...]) -> int:
    """Unique starting residue modulo ``2**len(word)`` for a parity word."""

    modulus = 1 << len(word)
    hits = []
    for residue in range(modulus):
        value = residue
        actual = []
        for _ in word:
            actual.append(value & 1)
            value = signed_syracuse(value)
        if tuple(actual) == word:
            hits.append(residue)
    if len(hits) != 1:
        raise AssertionError("shortcut parity coding was not bijective")
    return hits[0]


def is_prefix(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    return len(left) <= len(right) and right[: len(left)] == left


def check_prefix_free(words: tuple[tuple[int, ...], ...]) -> None:
    for index, left in enumerate(words):
        for right_index, right in enumerate(words):
            if index != right_index and is_prefix(left, right):
                raise AssertionError("controller code is not prefix-free")


def fraction_row(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "fraction": f"{value.numerator}/{value.denominator}",
    }


@dataclass(frozen=True)
class PrefixState:
    residue: int
    bits: int
    multiplier: int
    endpoint: int
    zero_run: int
    path_index: int


def decode_path(path_index: int, depth: int, alphabet_size: int) -> list[int]:
    answer = [0] * depth
    for index in range(depth - 1, -1, -1):
        answer[index] = path_index % alphabet_size
        path_index //= alphabet_size
    return answer


def extend_prefix(
    state: PrefixState,
    code_word: tuple[int, ...],
    code_residue: int,
    code_index: int,
    alphabet_size: int,
) -> tuple[PrefixState, int, int]:
    """Append one code word and return state, lift, and block source."""

    block_bits = len(code_word)
    block_modulus = 1 << block_bits
    lift = (
        (code_residue - state.endpoint)
        * pow(state.multiplier, -1, block_modulus)
    ) % block_modulus
    residue = state.residue + (1 << state.bits) * lift
    if not (0 <= residue < (1 << (state.bits + block_bits))):
        raise AssertionError("canonical extended residue left its range")

    block_source = state.endpoint + state.multiplier * lift
    if block_source <= 0:
        raise AssertionError("finite admissible code produced a nonpositive source")
    block_endpoint = replay_word(block_source, code_word)
    if block_endpoint <= block_source:
        raise AssertionError("minimal outward code failed literal state growth")

    next_state = PrefixState(
        residue=residue,
        bits=state.bits + block_bits,
        multiplier=state.multiplier * 3 ** sum(code_word),
        endpoint=block_endpoint,
        zero_run=state.zero_run + 1 if lift == 0 else 0,
        path_index=state.path_index * alphabet_size + code_index,
    )
    return next_state, lift, block_source


def replay_code_path(
    path: list[int],
    code: tuple[tuple[int, ...], ...],
    residues: dict[tuple[int, ...], int],
) -> dict[str, Any]:
    state = PrefixState(0, 0, 1, 0, 0, 0)
    lifts: list[int] = []
    for code_index in path:
        state, lift, _ = extend_prefix(
            state,
            code[code_index],
            residues[code[code_index]],
            code_index,
            len(code),
        )
        lifts.append(lift)

    # The incremental construction above uses a different canonical
    # representative at each horizon.  Literal replay must instead begin at
    # the final representative and run the whole fixed word from that one
    # ordinary integer.
    literal_value = state.residue
    reset_states = [literal_value]
    for code_index in path:
        next_value = replay_word(literal_value, code[code_index])
        if next_value <= literal_value:
            raise AssertionError("final canonical representative did not grow")
        reset_states.append(next_value)
        literal_value = next_value
    return {
        "code_words": [word_string(code[index]) for index in path],
        "extension_lifts": lifts,
        "canonical_initial_residue": state.residue,
        "written_bits": state.bits,
        "literal_reset_states": reset_states,
        "terminal_zero_lift_run": state.zero_run,
    }


def prefix_state_for_path(
    path: list[int],
    code: tuple[tuple[int, ...], ...],
    residues: dict[tuple[int, ...], int],
) -> PrefixState:
    state = PrefixState(0, 0, 1, 0, 0, 0)
    for code_index in path:
        state, _, _ = extend_prefix(
            state,
            code[code_index],
            residues[code[code_index]],
            code_index,
            len(code),
        )
    return state


def zero_lift_lookahead(
    path: list[int],
    code: tuple[tuple[int, ...], ...],
    residues: dict[tuple[int, ...], int],
    limit: int = 64,
) -> dict[str, Any]:
    """Follow the unique zero-lift continuation until it stops or hits a cap."""

    state = prefix_state_for_path(path, code, residues)
    continuation: list[int] = []
    for _ in range(limit):
        zero_children = []
        for code_index, code_word in enumerate(code):
            child, lift, _ = extend_prefix(
                state,
                code_word,
                residues[code_word],
                code_index,
                len(code),
            )
            if lift == 0:
                zero_children.append((code_index, child))
        if len(zero_children) > 1:
            raise AssertionError("prefix-free code had two zero-lift continuations")
        if not zero_children:
            return {
                "additional_zero_lift_words": [
                    word_string(code[index]) for index in continuation
                ],
                "additional_zero_lift_count": len(continuation),
                "extended_terminal_zero_lift_run": state.zero_run,
                "stopped_with_no_zero_lift_extension": True,
            }
        code_index, state = zero_children[0]
        continuation.append(code_index)
    return {
        "additional_zero_lift_words": [
            word_string(code[index]) for index in continuation
        ],
        "additional_zero_lift_count": len(continuation),
        "extended_terminal_zero_lift_run": state.zero_run,
        "stopped_with_no_zero_lift_extension": False,
    }


def finite_depth_rows(
    code: tuple[tuple[int, ...], ...],
    residues: dict[tuple[int, ...], int],
    max_depth: int,
    p_mass: Fraction,
    q_mass: Fraction,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    states = [PrefixState(0, 0, 1, 0, 0, 0)]
    rows: list[dict[str, Any]] = []
    global_best: tuple[int, int, PrefixState] | None = None

    for depth in range(1, max_depth + 1):
        next_states: list[PrefixState] = []
        zero_edges = 0
        terminal_positive_runs = 0
        best: PrefixState | None = None
        for state in states:
            for code_index, code_word in enumerate(code):
                child, lift, _ = extend_prefix(
                    state,
                    code_word,
                    residues[code_word],
                    code_index,
                    len(code),
                )
                next_states.append(child)
                if lift == 0:
                    zero_edges += 1
                if child.zero_run:
                    terminal_positive_runs += 1
                if best is None or (child.zero_run, -child.residue) > (
                    best.zero_run,
                    -best.residue,
                ):
                    best = child
        states = next_states
        if best is None:
            raise AssertionError("nonempty code generated no finite prefixes")
        if global_best is None or (best.zero_run, depth, -best.residue) > (
            global_best[0],
            global_best[1],
            -global_best[2].residue,
        ):
            global_best = (best.zero_run, depth, best)
        rows.append(
            {
                "block_depth": depth,
                "admissible_preloaded_prefixes": len(states),
                "minimum_shortcut_steps": depth * min(map(len, code)),
                "maximum_shortcut_steps": depth * max(map(len, code)),
                "ordinary_mass": fraction_row(p_mass**depth),
                "tilted_mass": fraction_row(q_mass**depth),
                "zero_lift_extensions": zero_edges,
                "prefixes_ending_in_zero_lift": terminal_positive_runs,
                "maximum_terminal_zero_lift_run": best.zero_run,
            }
        )

    if global_best is None:
        raise AssertionError("missing strongest finite prefix")
    _, best_depth, best_state = global_best
    best_path = decode_path(best_state.path_index, best_depth, len(code))
    strongest = replay_code_path(best_path, code, residues)
    strongest["zero_lift_lookahead"] = zero_lift_lookahead(
        best_path, code, residues
    )
    return rows, strongest


def source_modes(center_bound: int, max_controller_depth: int) -> list[Trace]:
    return [
        signed_trace(center, depth)
        for center in range(-center_bound, 0)
        for depth in range(1, max_controller_depth + 1)
    ]


def extract_code(traces: list[Trace]) -> tuple[tuple[int, ...], ...]:
    outward_words = {trace.parity_word for trace in traces if trace.outward}
    minimal = tuple(
        sorted(
            (
                word
                for word in outward_words
                if not any(
                    other != word and is_prefix(other, word)
                    for other in outward_words
                )
            ),
            key=lambda word: (len(word), word),
        )
    )
    check_prefix_free(minimal)
    for word in outward_words:
        if not any(is_prefix(leaf, word) for leaf in minimal):
            raise AssertionError("minimal code does not cover every outward mode")
    return minimal


def least_payload_for_positive_state(
    center: int, depth: int, residue: int, modulus: int
) -> int:
    threshold = (-center) // (1 << depth) + 1
    lift = max(0, (threshold - residue + modulus - 1) // modulus)
    payload = residue + lift * modulus
    if payload < threshold:
        raise AssertionError("failed to enter the positive reset-state domain")
    return payload


def audit(
    *,
    center_bound: int = 96,
    max_controller_depth: int = 8,
    precision_bits: int = 8,
    max_block_depth: int = 9,
) -> dict[str, Any]:
    if not (
        center_bound >= 1
        and 1 <= max_controller_depth <= precision_bits
        and max_block_depth >= 1
    ):
        raise ValueError("invalid controller-language bounds")

    traces = source_modes(center_bound, max_controller_depth)
    outward_traces = [trace for trace in traces if trace.outward]
    outward_words = {trace.parity_word for trace in outward_traces}
    code = extract_code(traces)
    residues = {word: parity_residue(word) for word in code}

    code_rows = []
    for word in code:
        residue = residues[word]
        negative_representative = residue - (1 << len(word))
        representative_trace = signed_trace(negative_representative, len(word))
        if representative_trace.parity_word != word:
            raise AssertionError("negative code representative has wrong parity word")
        if not (-center_bound <= negative_representative < 0):
            raise AssertionError("minimal code representative left the stated box")
        code_rows.append(
            {
                "parity_word": word_string(word),
                "shortcut_steps": len(word),
                "odd_sources": sum(word),
                "dyadic_residue": residue,
                "negative_representative": negative_representative,
                "signed_endpoint": representative_trace.endpoint,
                "three_pow_odd": 3 ** sum(word),
                "two_pow_steps": 1 << len(word),
                "strict_slope_margin": 3 ** sum(word) - (1 << len(word)),
            }
        )

    p_mass = sum((Fraction(1, 1 << len(word)) for word in code), Fraction())
    q_mass = sum(
        (Fraction(3 ** sum(word), 4 ** len(word)) for word in code),
        Fraction(),
    )
    if not (p_mass < 1 and q_mass <= 1):
        raise AssertionError("proper code violated its exact Kraft bounds")
    for word in code:
        if not Fraction(1, 1 << len(word)) < Fraction(
            3 ** sum(word), 4 ** len(word)
        ):
            raise AssertionError("outward leaf did not increase tilted weight")

    modulus = 1 << precision_bits
    target_residues: set[int] = set()
    target_owner: dict[int, tuple[int, ...]] = {}
    for word in code:
        stride = 1 << len(word)
        for residue in range(residues[word], modulus, stride):
            if residue in target_owner:
                raise AssertionError("prefix-free target cylinders overlapped")
            target_owner[residue] = word
            target_residues.add(residue)
    expected_target_count = p_mass * modulus
    if expected_target_count.denominator != 1:
        raise AssertionError("precision does not resolve every code cylinder")
    if len(target_residues) != expected_target_count.numerator:
        raise AssertionError("dyadic cover count disagrees with Kraft mass")

    pullback_count_histogram: dict[int, int] = {}
    growing_pullback_count_histogram: dict[int, int] = {}
    reset_transition_checks = 0
    for trace in traces:
        pullback = {
            payload_residue
            for payload_residue in range(modulus)
            if (trace.endpoint + trace.numerator * payload_residue) % modulus
            in target_residues
        }
        pullback_count_histogram[len(pullback)] = (
            pullback_count_histogram.get(len(pullback), 0) + 1
        )
        if len(pullback) != len(target_residues):
            raise AssertionError("odd affine pullback was not a permutation")
        if not trace.outward:
            continue
        growing_pullback_count_histogram[len(pullback)] = (
            growing_pullback_count_histogram.get(len(pullback), 0) + 1
        )
        for payload_residue in pullback:
            payload = least_payload_for_positive_state(
                trace.start,
                trace.depth,
                payload_residue,
                modulus,
            )
            source_state = trace.start + trace.denominator * payload
            endpoint = replay_word(source_state, trace.parity_word)
            if endpoint != trace.endpoint + trace.numerator * payload:
                raise AssertionError("signed-controller difference law failed")
            if not (0 < source_state < endpoint):
                raise AssertionError("universal actual-state growth failed")

            target_word = target_owner[endpoint % modulus]
            target_depth = len(target_word)
            target_center = residues[target_word] - (1 << target_depth)
            delta = trace.endpoint - target_center
            numerator = trace.numerator * payload + delta
            if numerator % (1 << target_depth):
                raise AssertionError("reset cylinder divisibility failed")
            next_payload = numerator // (1 << target_depth)
            if endpoint != target_center + (1 << target_depth) * next_payload:
                raise AssertionError("target reset normalization failed")
            if next_payload <= 0:
                raise AssertionError("positive endpoint produced nonpositive payload")
            reset_transition_checks += 1

    finite_rows, strongest_zero_run = finite_depth_rows(
        code, residues, max_block_depth, p_mass, q_mass
    )

    return {
        "schema": SCHEMA,
        "arithmetic": "exact_python_integers_and_fractions",
        "claim_scope": (
            "bounded exact specialization of the signed-Syracuse reset "
            "recurrence; finite-depth admissible preloaded language only, "
            "not an invariant ordinary orbit and not a Collatz counterexample"
        ),
        "bounds": {
            "negative_center_min": -center_bound,
            "negative_center_max": -1,
            "current_shadow_depth_min": 1,
            "current_shadow_depth_max": max_controller_depth,
            "dyadic_precision_bits": precision_bits,
            "finite_preloaded_block_depth": max_block_depth,
        },
        "mode_counts": {
            "controller_modes": len(traces),
            "universally_outward_modes": len(outward_traces),
            "distinct_outward_parity_words": len(outward_words),
        },
        "minimal_outward_prefix_code": code_rows,
        "code_masses": {
            "ordinary_p": fraction_row(p_mass),
            "tilted_q": fraction_row(q_mass),
            "resolved_outward_target_residues": len(target_residues),
            "ambient_residues": modulus,
            "missing_target_residues": modulus - len(target_residues),
            "is_total_cover": len(target_residues) == modulus,
        },
        "affine_pullback_audit": {
            "all_mode_cover_count_histogram": {
                str(key): value
                for key, value in sorted(pullback_count_histogram.items())
            },
            "outward_mode_cover_count_histogram": {
                str(key): value
                for key, value in sorted(
                    growing_pullback_count_histogram.items()
                )
            },
            "literal_reset_transition_checks": reset_transition_checks,
            "identity": (
                "2^Nnext*mnext = 3^O*m + "
                "signedSyracuse^[N](c) - cnext"
            ),
            "total_cover_reduction": (
                "for fixed current mode, m -> cEnd+3^O*m is a permutation "
                "modulo 2^B; a total outward next-mode cover would normalize "
                "to the already-closed complete outward prefix-code case"
            ),
        },
        "finite_depth_admissible_preloaded_language": finite_rows,
        "strongest_finite_zero_lift_run": strongest_zero_run,
        "eventual_zero_address_tail": {
            "decided": False,
            "reason": (
                "finite block depth cannot decide whether one nested "
                "canonical address has zero extension lifts from some point on"
            ),
            "required_extension_relation": (
                "R_(u v)=R_u+2^len(u)*ell, where "
                "ell=(R_v-T^len(u)(R_u))*3^(-odd(u)) mod 2^len(v)"
            ),
            "ordinary_promotion_gate": (
                "an infinite compatible controller schedule must have "
                "ell=0 eventually, then pass positivity and literal replay"
            ),
        },
        "counterexample": None,
        "verifier_sha256": source_sha256(),
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(**kwargs: int) -> dict[str, Any]:
    return audit(**kwargs)


def verify_artifact(data: dict[str, Any]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported signed thin-residue schema")
    bounds = data["bounds"]
    expected = build_certificate(
        center_bound=-int(bounds["negative_center_min"]),
        max_controller_depth=int(bounds["current_shadow_depth_max"]),
        precision_bits=int(bounds["dyadic_precision_bits"]),
        max_block_depth=int(bounds["finite_preloaded_block_depth"]),
    )
    if data != expected:
        raise ValueError("signed thin-residue artifact failed reconstruction")


def render(data: dict[str, Any]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def selftest() -> None:
    assert signed_syracuse(-1) == -1
    assert signed_syracuse(-5) == -7
    assert signed_trace(-5, 2).parity_word == (1, 1)

    result = audit(max_block_depth=3)
    words = [row["parity_word"] for row in result["minimal_outward_prefix_code"]]
    assert words == ["1", "011", "001111", "010111"]
    assert result["mode_counts"] == {
        "controller_modes": 768,
        "universally_outward_modes": 246,
        "distinct_outward_parity_words": 82,
    }
    assert result["code_masses"]["ordinary_p"]["fraction"] == "21/32"
    assert result["code_masses"]["tilted_q"]["fraction"] == "1905/2048"
    assert result["code_masses"]["resolved_outward_target_residues"] == 168
    assert result["affine_pullback_audit"]["literal_reset_transition_checks"] == 41328
    depth_rows = result["finite_depth_admissible_preloaded_language"]
    assert [row["zero_lift_extensions"] for row in depth_rows] == [0, 0, 8]
    assert depth_rows[-1]["maximum_terminal_zero_lift_run"] == 1
    assert result["counterexample"] is None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")

    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--center-bound", type=int, default=96)
    build.add_argument("--max-controller-depth", type=int, default=8)
    build.add_argument("--precision-bits", type=int, default=8)
    build.add_argument("--max-block-depth", type=int, default=9)

    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)

    args = parser.parse_args()
    if args.command == "selftest":
        selftest()
        print("KL signed thin-residue selftest: PASS")
    elif args.command == "build":
        data = build_certificate(
            center_bound=args.center_bound,
            max_controller_depth=args.max_controller_depth,
            precision_bits=args.precision_bits,
            max_block_depth=args.max_block_depth,
        )
        args.output.write_text(render(data))
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("KL signed thin-residue artifact: PASS")


if __name__ == "__main__":
    main()

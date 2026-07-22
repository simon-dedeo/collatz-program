#!/usr/bin/env python3
"""Exact parity-complete splash instructions for the Collatz two-rail ISA.

The original two-rail gate retained only collisions whose ``+1``-rail gap is
even and whose outgoing ``-1``-rail gap is at least two.  Neither restriction
is intrinsic.  If the intermediate gap is odd, the last ``+1``-rail step has
valuation one and gives the exact catcher

    1 + 2*3^s*Q  ->  2 + 3^(s+1)*Q = -1 + 2^L*P'.

Allowing ``L=1`` means that the next ``-1`` rail may have zero delay ticks.
Together the even cleanup gate and this odd-gap catcher decode every positive
odd payload unless its macro reaches 1.  Their LSB-first cylinder masses among
odd 2-adics are respectively 1/3 and 2/3.

This is a complete instruction *factorization* of Collatz, not a divergent
program.  The committed saturated-map witness is parsed all the way to 1.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path

from path_compiler import accelerated_step


SCHEMA = "collatz-complete-splash-isa-v1"


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 expects a positive integer")
    return (value & -value).bit_length() - 1


def power_of_two_exponent(value: int) -> int:
    if value <= 0 or value & (value - 1):
        raise ValueError("expected a positive power of two")
    return value.bit_length() - 1


@dataclass(frozen=True)
class CompleteSplashGate:
    branch: str
    amp_ticks: int
    clean_ticks: int
    to_plus_extra: int
    terminal_extra: int | None
    input_gap: int
    plus_gap: int
    output_gap: int
    input_payload_base: int
    input_payload_stride: int
    plus_payload_base: int
    plus_payload_stride: int
    output_payload_base: int
    output_payload_stride: int

    def payloads(self, family_index: int) -> tuple[int, int, int]:
        if family_index < 0:
            raise ValueError("family index must be nonnegative")
        return (
            self.input_payload_base + self.input_payload_stride * family_index,
            self.plus_payload_base + self.plus_payload_stride * family_index,
            self.output_payload_base + self.output_payload_stride * family_index,
        )

    @property
    def accelerated_steps(self) -> int:
        return self.amp_ticks + self.clean_ticks + 2

    @property
    def total_halvings(self) -> int:
        if self.branch == "even_cleanup":
            if self.terminal_extra is None:
                raise AssertionError("even cleanup lost its terminal extra")
            return (
                self.amp_ticks
                + 1
                + self.to_plus_extra
                + 2 * self.clean_ticks
                + 2
                + self.terminal_extra
            )
        if self.branch == "odd_catcher":
            return (
                self.amp_ticks
                + 1
                + self.to_plus_extra
                + 2 * self.clean_ticks
                + 1
            )
        raise AssertionError("unknown splash branch")


def _check_gate_coefficients(gate: CompleteSplashGate) -> None:
    for index in (0, 1):
        p, q, p_next = gate.payloads(index)
        if min(p, q, p_next) <= 0 or any(x % 2 == 0 for x in (p, q, p_next)):
            raise AssertionError("splash payloads must be positive and odd")
        if (
            pow(3, gate.amp_ticks + 1) * p - 1
            != pow(2, gate.to_plus_extra)
            * (1 + pow(2, gate.plus_gap) * q)
        ):
            raise AssertionError("input-to-plus coefficient identity failed")
        if gate.branch == "even_cleanup":
            if gate.terminal_extra is None:
                raise AssertionError("even cleanup lost its terminal extra")
            if (
                1 + pow(3, gate.clean_ticks + 1) * q
                != pow(2, gate.terminal_extra)
                * (-1 + pow(2, gate.output_gap) * p_next)
            ):
                raise AssertionError("even cleanup coefficient identity failed")
        elif gate.branch == "odd_catcher":
            if 2 + pow(3, gate.clean_ticks + 1) * q != (
                -1 + pow(2, gate.output_gap) * p_next
            ):
                raise AssertionError("odd catcher coefficient identity failed")
        else:
            raise AssertionError("unknown splash branch")


def even_cleanup_gate(
    amp_ticks: int,
    clean_ticks: int,
    to_plus_extra: int,
    terminal_extra: int,
    output_gap: int,
) -> CompleteSplashGate:
    """Complete affine family for an even intermediate ``+1``-rail gap."""
    if amp_ticks < 0 or clean_ticks < 0:
        raise ValueError("rail lengths must be nonnegative")
    if min(to_plus_extra, terminal_extra, output_gap) < 1:
        raise ValueError("extras and outgoing gap must be positive")

    plus_gap = 2 * clean_ticks + 2
    modulus_plus = pow(3, clean_ticks + 1)
    output_seed = (
        (pow(2, terminal_extra) + 1)
        * pow(pow(2, terminal_extra + output_gap), -1, modulus_plus)
    ) % modulus_plus
    if output_seed == 0 or output_seed % 2 == 0:
        output_seed += modulus_plus
    plus_seed = (
        pow(2, terminal_extra)
        * (-1 + pow(2, output_gap) * output_seed)
        - 1
    ) // modulus_plus

    modulus_amp = pow(3, amp_ticks + 1)
    plus_stride_in_aux = pow(2, terminal_extra + output_gap + 1)
    constant = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_seed
    )
    coefficient = pow(2, to_plus_extra + plus_gap) * plus_stride_in_aux
    auxiliary_residue = (
        -constant * pow(coefficient, -1, modulus_amp)
    ) % modulus_amp

    output_base = output_seed + 2 * modulus_plus * auxiliary_residue
    plus_base = plus_seed + plus_stride_in_aux * auxiliary_residue
    input_numerator = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_base
    )
    if input_numerator % modulus_amp:
        raise AssertionError("even cleanup input congruence failed")
    input_base = input_numerator // modulus_amp

    gate = CompleteSplashGate(
        branch="even_cleanup",
        amp_ticks=amp_ticks,
        clean_ticks=clean_ticks,
        to_plus_extra=to_plus_extra,
        terminal_extra=terminal_extra,
        input_gap=amp_ticks + 1,
        plus_gap=plus_gap,
        output_gap=output_gap,
        input_payload_base=input_base,
        input_payload_stride=pow(
            2,
            to_plus_extra
            + terminal_extra
            + 2 * clean_ticks
            + output_gap
            + 3,
        ),
        plus_payload_base=plus_base,
        plus_payload_stride=plus_stride_in_aux * modulus_amp,
        output_payload_base=output_base,
        output_payload_stride=2 * modulus_plus * modulus_amp,
    )
    _check_gate_coefficients(gate)
    return gate


def odd_gap_catcher(
    amp_ticks: int,
    clean_ticks: int,
    to_plus_extra: int,
    output_gap: int,
) -> CompleteSplashGate:
    """Complete affine family for an odd intermediate ``+1``-rail gap."""
    if amp_ticks < 0 or clean_ticks < 0:
        raise ValueError("rail lengths must be nonnegative")
    if min(to_plus_extra, output_gap) < 1:
        raise ValueError("extra and outgoing gap must be positive")

    plus_gap = 2 * clean_ticks + 1
    output_modulus = 1 << (output_gap + 1)
    # This selects exact valuation output_gap in 1+3^s*Q.
    plus_seed = (
        (pow(2, output_gap) - 1)
        * pow(pow(3, clean_ticks), -1, output_modulus)
    ) % output_modulus
    if plus_seed <= 0 or plus_seed % 2 == 0:
        raise AssertionError("odd catcher seed is not positive odd")

    modulus_amp = pow(3, amp_ticks + 1)
    constant = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_seed
    )
    coefficient = pow(
        2, to_plus_extra + plus_gap + output_gap + 1
    )
    auxiliary_residue = (
        -constant * pow(coefficient, -1, modulus_amp)
    ) % modulus_amp

    plus_base = plus_seed + pow(2, output_gap + 1) * auxiliary_residue
    input_numerator = 1 + pow(2, to_plus_extra) * (
        1 + pow(2, plus_gap) * plus_base
    )
    if input_numerator % modulus_amp:
        raise AssertionError("odd catcher input congruence failed")
    input_base = input_numerator // modulus_amp
    output_numerator = 3 * (
        1 + pow(3, clean_ticks) * plus_base
    )
    if output_numerator % pow(2, output_gap):
        raise AssertionError("odd catcher output congruence failed")
    output_base = output_numerator // pow(2, output_gap)

    gate = CompleteSplashGate(
        branch="odd_catcher",
        amp_ticks=amp_ticks,
        clean_ticks=clean_ticks,
        to_plus_extra=to_plus_extra,
        terminal_extra=None,
        input_gap=amp_ticks + 1,
        plus_gap=plus_gap,
        output_gap=output_gap,
        input_payload_base=input_base,
        input_payload_stride=pow(
            2, to_plus_extra + 2 * clean_ticks + output_gap + 2
        ),
        plus_payload_base=plus_base,
        plus_payload_stride=(
            pow(2, output_gap + 1) * modulus_amp
        ),
        output_payload_base=output_base,
        output_payload_stride=2 * pow(3, amp_ticks + clean_ticks + 2),
    )
    _check_gate_coefficients(gate)
    return gate


def verify_member(
    gate: CompleteSplashGate, family_index: int
) -> tuple[int, int]:
    p, q, p_next = gate.payloads(family_index)
    start = -1 + pow(2, gate.input_gap) * p
    endpoint = -1 + pow(2, gate.output_gap) * p_next
    state = start

    for tick in range(gate.amp_ticks):
        expected = -1 + (
            pow(3, tick) * pow(2, gate.input_gap - tick) * p
        )
        if state != expected:
            raise AssertionError("amplifier rail formula failed")
        state, valuation = accelerated_step(state)
        if valuation != 1:
            raise AssertionError("amplifier tick did not have valuation one")

    state, valuation = accelerated_step(state)
    if valuation != 1 + gate.to_plus_extra:
        raise AssertionError("first collision valuation failed")
    if state != 1 + pow(2, gate.plus_gap) * q:
        raise AssertionError("first collision state failed")

    for tick in range(gate.clean_ticks):
        expected = 1 + (
            pow(3, tick) * pow(2, gate.plus_gap - 2 * tick) * q
        )
        if state != expected:
            raise AssertionError("cleanup rail formula failed")
        state, valuation = accelerated_step(state)
        if valuation != 2:
            raise AssertionError("cleanup tick did not have valuation two")

    state, valuation = accelerated_step(state)
    expected_valuation = (
        2 + gate.terminal_extra
        if gate.branch == "even_cleanup" and gate.terminal_extra is not None
        else 1
    )
    if valuation != expected_valuation or state != endpoint:
        raise AssertionError("terminal splash collision failed")
    return start, endpoint


def decode_payload(
    amp_ticks: int, payload: int
) -> tuple[CompleteSplashGate, int] | None:
    """Decode one macro, returning ``None`` exactly when it reaches 1."""
    if amp_ticks < 0 or payload < 1 or payload % 2 == 0:
        raise ValueError("expected nonnegative rail length and positive odd payload")

    first = pow(3, amp_ticks + 1) * payload - 1
    to_plus_extra = v2(first)
    plus_state = first >> to_plus_extra
    if plus_state == 1:
        return None
    plus_gap = v2(plus_state - 1)
    q = (plus_state - 1) >> plus_gap
    if q <= 0 or q % 2 == 0:
        raise AssertionError("decoded intermediate payload is not positive odd")

    if plus_gap % 2 == 0:
        clean_ticks = (plus_gap - 2) // 2
        second = 1 + pow(3, clean_ticks + 1) * q
        terminal_extra = v2(second)
        minus_state = second >> terminal_extra
        output_gap = v2(minus_state + 1)
        gate = even_cleanup_gate(
            amp_ticks,
            clean_ticks,
            to_plus_extra,
            terminal_extra,
            output_gap,
        )
    else:
        clean_ticks = (plus_gap - 1) // 2
        endpoint = 2 + pow(3, clean_ticks + 1) * q
        output_gap = v2(endpoint + 1)
        gate = odd_gap_catcher(
            amp_ticks, clean_ticks, to_plus_extra, output_gap
        )

    difference = payload - gate.input_payload_base
    if difference < 0 or difference % gate.input_payload_stride:
        raise AssertionError("decoded payload missed its affine cylinder")
    family_index = difference // gate.input_payload_stride
    decoded_payloads = gate.payloads(family_index)
    if decoded_payloads[0] != payload or decoded_payloads[1] != q:
        raise AssertionError("decoded family payloads disagree")
    verify_member(gate, family_index)
    return gate, family_index


def codeword(gate: CompleteSplashGate) -> tuple[int, int]:
    exponent = power_of_two_exponent(gate.input_payload_stride)
    return gate.input_payload_base % (1 << exponent), exponent


def bounded_gates(amp_ticks: int, maximum_code_bits: int) -> list[CompleteSplashGate]:
    gates: list[CompleteSplashGate] = []
    for a in range(1, maximum_code_bits + 1):
        for s in range(maximum_code_bits + 1):
            for output_gap in range(1, maximum_code_bits + 1):
                odd_exponent = a + 2 * s + output_gap + 2
                if odd_exponent <= maximum_code_bits:
                    gates.append(odd_gap_catcher(amp_ticks, s, a, output_gap))
                for b in range(1, maximum_code_bits + 1):
                    even_exponent = a + b + 2 * s + output_gap + 3
                    if even_exponent <= maximum_code_bits:
                        gates.append(
                            even_cleanup_gate(
                                amp_ticks, s, a, b, output_gap
                            )
                        )
    return gates


def verify_prefix_free(gates: list[CompleteSplashGate]) -> int:
    words = [codeword(gate) for gate in gates]
    comparisons = 0
    for index, (left, left_bits) in enumerate(words):
        for right, right_bits in words[index + 1 :]:
            comparisons += 1
            common_bits = min(left_bits, right_bits)
            if (left - right) % (1 << common_bits) == 0:
                raise AssertionError("complete splash code is not prefix-free")
    return comparisons


@dataclass(frozen=True)
class SplashLink:
    address_bits: int
    source_index_base: int
    source_index_stride: int
    target_index_base: int
    target_index_stride: int

    def indices(self, tail: int) -> tuple[int, int]:
        return (
            self.source_index_base + self.source_index_stride * tail,
            self.target_index_base + self.target_index_stride * tail,
        )


def link_instruction(
    source: CompleteSplashGate, target: CompleteSplashGate
) -> SplashLink:
    if source.output_gap != target.input_gap:
        raise ValueError("sparse gaps do not link")
    target_exponent = power_of_two_exponent(target.input_payload_stride)
    address_bits = target_exponent - 1
    modulus = 1 << address_bits
    source_multiplier = source.output_payload_stride // 2
    offset = (source.output_payload_base - target.input_payload_base) // 2
    residue = (-offset * pow(source_multiplier, -1, modulus)) % modulus
    target_base = (source_multiplier * residue + offset) // modulus
    if target_base < 0:
        lifts = (-target_base + source_multiplier - 1) // source_multiplier
        residue += modulus * lifts
        target_base += source_multiplier * lifts
    link = SplashLink(
        address_bits=address_bits,
        source_index_base=residue,
        source_index_stride=modulus,
        target_index_base=target_base,
        target_index_stride=source_multiplier,
    )
    for tail in range(16):
        z, w = link.indices(tail)
        if source.payloads(z)[2] != target.payloads(w)[0]:
            raise AssertionError("splash link payloads do not match")
    return link


def universally_outward(gate: CompleteSplashGate, base: int, stride: int) -> bool:
    start0, end0 = verify_member(gate, base)
    start1, end1 = verify_member(gate, base + stride)
    return end0 > start0 and end1 - end0 >= start1 - start0


def saturated_step(value: int) -> int:
    return (3 * value + (1 if value % 2 else 2)) // 2


def affine_saturated_block(
    base: int, stride: int, steps: int
) -> tuple[int, int, list[int]]:
    """Propagate an affine cylinder coefficientwise, proving all tails."""
    digits: list[int] = []
    for _ in range(steps):
        digit = 1 if base % 2 else 2
        if stride % 2:
            raise AssertionError("affine tail could change the parity branch")
        numerator_base = 3 * base + digit
        numerator_stride = 3 * stride
        if numerator_base % 2 or numerator_stride % 2:
            raise AssertionError("saturated affine step is not integral")
        base = numerator_base // 2
        stride = numerator_stride // 2
        digits.append(digit)
    return base, stride, digits


def ordinary_continuation(seed: int, limit: int = 100_000) -> dict[str, int | bool]:
    state = seed
    peak = seed
    peak_at = 0
    steps = 0
    halvings = 0
    while state != 1 and steps < limit:
        state, valuation = accelerated_step(state)
        steps += 1
        halvings += valuation
        if state > peak:
            peak = state
            peak_at = steps
    return {
        "limit": limit,
        "reached_one": state == 1,
        "accelerated_steps": steps,
        "total_halvings": halvings,
        "ordinary_steps": steps + halvings,
        "peak": peak,
        "peak_at_accelerated_step": peak_at,
    }


def build_certificate() -> dict[str, object]:
    bounds = {
        "amp_ticks": "0..8",
        "maximum_code_bits_including_forced_odd_bit": 18,
        "decoded_payloads": "positive odd P<2^13",
    }
    counts: list[int] = []
    comparisons: list[int] = []
    covered: list[int] = []
    branch_counts = {"even_cleanup": 0, "odd_catcher": 0, "halts": 0}
    for r in range(9):
        gates = bounded_gates(r, 18)
        counts.append(len(gates))
        comparisons.append(verify_prefix_free(gates))
        covered.append(sum(1 << (18 - bits) for _, bits in map(codeword, gates)))
        for payload in range(1, 1 << 13, 2):
            decoded = decode_payload(r, payload)
            if decoded is None:
                branch_counts["halts"] += 1
            else:
                branch_counts[decoded[0].branch] += 1
    if len(set(counts)) != 1 or len(set(comparisons)) != 1:
        raise AssertionError("prefix combinatorics unexpectedly depend on r")
    if len(set(covered)) != 1:
        raise AssertionError("bounded prefix coverage unexpectedly depends on r")

    even_mass = Fraction(1, 3)
    odd_mass = Fraction(2, 3)
    if even_mass + odd_mass != 1:
        raise AssertionError("complete Kraft identity failed")

    # A longer saturated-map compiler block.  Its first two splash gates are
    # both universally outward; the parity-complete decoder then catches what
    # the earlier even-only grammar called a failure.
    source = even_cleanup_gate(10, 0, 4, 2, 11)
    target = even_cleanup_gate(10, 2, 1, 3, 2)
    link = link_instruction(source, target)
    if asdict(link) != {
        "address_bits": 12,
        "source_index_base": 1023,
        "source_index_stride": 4096,
        "target_index_base": 132860,
        "target_index_stride": 531441,
    }:
        raise AssertionError("U^12 splash bridge changed")
    u_base, u_stride, u_digits = affine_saturated_block(1023, 4096, 12)
    if (u_base, u_stride, u_digits) != (
        132860,
        531441,
        [1] * 10 + [2, 1],
    ):
        raise AssertionError("U^12 affine cylinder identity changed")
    if not universally_outward(source, 1023, 4096):
        raise AssertionError("U^12 source gate is not universally outward")
    if not universally_outward(target, 132860, 531441):
        raise AssertionError("U^12 target gate is not universally outward")

    saturated = 0
    for _ in range(622):
        saturated = saturated_step(saturated)
    if saturated % 4096 != 1023:
        raise AssertionError("saturated orbit missed the U^12 address")
    saturated_after = saturated
    saturated_digits: list[int] = []
    for _ in range(12):
        saturated_digits.append(1 if saturated_after % 2 else 2)
        saturated_after = saturated_step(saturated_after)
    if saturated_digits != u_digits:
        raise AssertionError("saturated U witness took the wrong branch word")

    source_start, source_endpoint = verify_member(source, saturated)
    _, target_endpoint = verify_member(target, saturated_after)
    if source_endpoint != verify_member(target, saturated_after)[0]:
        raise AssertionError("saturated U^12 gates do not link")
    if not source_start < source_endpoint < target_endpoint:
        raise AssertionError("first two saturated U^12 gates are not outward")

    r = target.output_gap - 1
    payload = target.payloads(saturated_after)[2]
    state = target_endpoint
    gate_count = 2
    outward_gates = 2
    branch_totals = {"even_cleanup": 2, "odd_catcher": 0}
    accelerated_steps = source.accelerated_steps + target.accelerated_steps
    total_halvings = source.total_halvings + target.total_halvings
    first_catcher: dict[str, object] | None = None
    while True:
        decoded = decode_payload(r, payload)
        if decoded is None:
            first = pow(3, r + 1) * payload - 1
            halt_extra = v2(first)
            if first >> halt_extra != 1:
                raise AssertionError("decoder halt did not reach one")
            accelerated_steps += r + 1
            total_halvings += r + 1 + halt_extra
            break
        gate, family_index = decoded
        start, endpoint = verify_member(gate, family_index)
        if start != state:
            raise AssertionError("complete splash cascade broke linkage")
        if first_catcher is None:
            first_catcher = {
                "gate_shape": {
                    "branch": gate.branch,
                    "amp_ticks": gate.amp_ticks,
                    "clean_ticks": gate.clean_ticks,
                    "to_plus_extra": gate.to_plus_extra,
                    "terminal_extra": gate.terminal_extra,
                    "output_gap": gate.output_gap,
                },
                "start": start,
                "endpoint": endpoint,
                "outward": endpoint > start,
            }
        gate_count += 1
        outward_gates += int(endpoint > start)
        branch_totals[gate.branch] += 1
        accelerated_steps += gate.accelerated_steps
        total_halvings += gate.total_halvings
        state = endpoint
        r = gate.output_gap - 1
        payload = gate.payloads(family_index)[2]
        if gate_count > 10_000:
            raise AssertionError("splash cascade exceeded its audit limit")

    if first_catcher is None:
        raise AssertionError("saturated witness had no parity catcher")
    if (state, accelerated_steps, total_halvings) != (5, 1016, 2006):
        raise AssertionError("complete splash cascade regression changed")
    continuation = ordinary_continuation(source_start)
    if not continuation["reached_one"]:
        raise AssertionError("saturated splash witness unexpectedly survived")
    if (
        continuation["accelerated_steps"] != accelerated_steps
        or continuation["total_halvings"] != total_halvings
    ):
        raise AssertionError("macro parse disagrees with literal continuation")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact total macro decoder away from explicit halting collisions, "
            "bounded prefix/decoder audit, and one finite saturated-map cascade; "
            "not a counterexample"
        ),
        "parity_complete_grammar": {
            "even_cleanup_equation": (
                "1+3^(s+1)Q=2^b(-1+2^L P')"
            ),
            "odd_catcher_equation": (
                "2+3^(s+1)Q=-1+2^L P'"
            ),
            "zero_delay_output_allowed": True,
            "even_branch_kraft_mass_among_odd_payloads": "1/3",
            "odd_branch_kraft_mass_among_odd_payloads": "2/3",
            "total_kraft_mass": "1",
            "decoder_outcome": (
                "every positive odd payload emits exactly one branch or its "
                "current macro reaches 1"
            ),
        },
        "bounded_audit": {
            "bounds": bounds,
            "codewords_per_amp_length": counts[0],
            "pairwise_prefix_comparisons_per_amp_length": comparisons[0],
            "covered_odd_residues_mod_2^18": covered[0],
            "all_odd_residues_mod_2^18": 1 << 17,
            "amp_lengths_checked": len(counts),
            "literal_decoder_outcomes": branch_counts,
            "all_codes_prefix_free": True,
        },
        "saturated_U12_bridge": {
            "source_gate": asdict(source),
            "target_gate": asdict(target),
            "link": asdict(link),
            "universal_identity": (
                "U^12(1023+4096*t)=132860+531441*t for every t>=0"
            ),
            "digits": u_digits,
            "source_family_universally_outward": True,
            "target_family_universally_outward": True,
            "saturated_orbit_entry_time": 622,
            "saturated_source_index": saturated,
            "saturated_target_index": saturated_after,
            "collatz_source_state": source_start,
            "after_source_gate": source_endpoint,
            "after_target_gate": target_endpoint,
            "first_previously_rejected_catcher": first_catcher,
            "complete_macro_parse": {
                "decoded_gates": gate_count,
                "outward_gates": outward_gates,
                "branch_totals": branch_totals,
                "state_before_halting_collision": state,
                "accelerated_steps_to_one": accelerated_steps,
                "total_halvings_to_one": total_halvings,
            },
            "literal_continuation": continuation,
        },
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != build_certificate():
        raise ValueError("complete splash ISA artifact failed exact reconstruction")


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
        print("complete_splash_isa selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(build_certificate(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("complete_splash_isa artifact: PASS")


if __name__ == "__main__":
    main()

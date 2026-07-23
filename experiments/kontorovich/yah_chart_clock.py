#!/usr/bin/env python3
"""Exact scale clock and third restorative edge for the YAH chart machine.

Queue macros decouple into two pieces.  Their terminal carries update the
integer register, while their head widths update a normalized leading scale
``rho``.  A zero head consumes one shortcut sweep and a nonzero head consumes
two, so at macro boundaries

    rho' = 3*rho/2       for head 0,
    rho' = 3*rho/4       for head 1 or 2.

Starting at the returned restorative chart, ``rho=269001/262144``.  The
unique head whose ternary interval contains ``rho`` therefore generates an
unbounded public clock.  The first symbols are ``010202101021...``.  A
periodic tail would force a positive power of three to equal a power of two.

The abstract leading clock is aperiodic.  Identifying its entire infinite head
word with the literal YAH itinerary additionally requires a Diophantine gap
bound showing that the additive correction never crosses a head boundary;
this worker proves that bridge only for the five macros below.

The worker uses the clock to certify the next collision after the second
restorative edge.  On ``w=249 mod 256`` the second-edge register ``T`` obeys
``T=221 mod 256``.  Five macros with heads ``0,1,0,2,1`` and carries
``[0],[1,1],[1],[1,1],[1,1]`` return to a head-zero seven-reservoir chart:

    256*U = 3^7*T + 1.

They gain two cells.  The output is again a two-adic isometric register and
its low bit equals the remaining source parameter bit.

Finally, an exact scale identity shows why the search must remain aperiodic.
For a segment of M macros, S shortcut sweeps, J odd sweeps, and space gain
G=J-M, its affine register slope is

    3^J/2^S = 3^G * rho_end/rho_start.

Since every clock value lies in [1,2), positive space gain forces slope
strictly above 3/2.  Thus no positive-space nonexpanding edge exists.  This
does not rule out an aperiodic expanding dispatcher and is not a Collatz
counterexample.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

import yah_context_loop as yah
import yah_queue_macro as queue
import yah_returned_burst as burst


SCHEMA = "yah_chart_clock_v1"
INITIAL_SCALE = Fraction(269001, 262144)
SECOND_PHASE = 7
THIRD_SOURCE_BASE = 249
THIRD_SOURCE_STRIDE = 256
THIRD_SOURCE_REGISTER = 221
THIRD_HEADS = (0, 1, 0, 2, 1)
THIRD_CARRIES = ((0,), (1, 1), (1,), (1, 1), (1, 1))
BASE_ATOM_LENGTH = 65536
TOTAL_SWEEPS = 19


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def head_for_scale(scale: Fraction) -> int:
    if not Fraction(1) <= scale < 2:
        raise ValueError("scale left the canonical ternary interval")
    if scale < Fraction(4, 3):
        return 0
    if scale < Fraction(5, 3):
        return 1
    return 2


def next_scale(scale: Fraction, head: int) -> Fraction:
    if head not in {0, 1, 2}:
        raise ValueError("invalid head")
    result = scale * Fraction(3, 2 if head == 0 else 4)
    if not Fraction(1) <= result < 2:
        raise AssertionError("head clock failed to renormalize")
    return result


def clock(count: int) -> tuple[list[Fraction], list[int]]:
    if count < 1:
        raise ValueError("clock length must be positive")
    scales: list[Fraction] = []
    heads: list[int] = []
    scale = INITIAL_SCALE
    for _ in range(count):
        head = head_for_scale(scale)
        scales.append(scale)
        heads.append(head)
        scale = next_scale(scale, head)
    scales.append(scale)
    return scales, heads


def second_register_mod(parameter: int, bits: int) -> int:
    """Return the second-edge register T(w) modulo ``2^bits`` exactly."""

    if parameter < 0 or bits < 0:
        raise ValueError("invalid second-register query")
    incoming = burst.returned_register_mod(35 + 2048 * parameter, 11 + bits)
    numerator = 3**10 * incoming + 8
    if numerator % (1 << 11):
        raise AssertionError("second restorative division failed")
    return (numerator >> 11) % (1 << bits)


def third_register_mod(parameter: int, bits: int) -> int:
    """Return U(z) modulo ``2^bits`` on ``w=249+256z``."""

    if parameter < 0 or bits < 0:
        raise ValueError("invalid third-register query")
    source = second_register_mod(
        THIRD_SOURCE_BASE + THIRD_SOURCE_STRIDE * parameter, 8 + bits
    )
    numerator = 3**7 * source + 1
    if numerator % (1 << 8):
        raise AssertionError("third restorative division failed")
    return (numerator >> 8) % (1 << bits)


def v2_nonzero(value: int) -> int:
    if value == 0:
        raise ValueError("valuation requires a nonzero integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def head_interval(head: int) -> tuple[Fraction, Fraction]:
    return {
        0: (Fraction(1), Fraction(4, 3)),
        1: (Fraction(4, 3), Fraction(5, 3)),
        2: (Fraction(5, 3), Fraction(2)),
    }[head]


def check_corrected_head(
    scale: Fraction, correction: Fraction, head: int, length_lower_bound: int
) -> dict[str, Any]:
    """Prove the additive finite correction cannot change the leading head.

    At a macro boundary the exact defect has form

        D = scale * 3^L + correction,

    so the represented integer is ``D-1``.  The leading scale is strictly
    inside one ternary head interval.  Replacing ``3^L`` by the smaller
    ``3^length_lower_bound`` gives a sufficient exact gap certificate.
    """

    lower, upper = head_interval(head)
    if not lower < scale < upper:
        raise AssertionError("leading scale does not select the claimed head")
    power = 3**length_lower_bound
    lower_gap = (scale - lower) * power + correction - 1
    upper_gap = (upper - scale) * power - correction + 1
    if lower_gap <= 0 or upper_gap <= 0:
        raise AssertionError("finite correction can cross a head boundary")
    return {
        "head": head,
        "scale": fraction_record(scale),
        "correction": fraction_record(correction),
        "length_lower_bound": length_lower_bound,
        "lower_gap_at_bound": fraction_record(lower_gap),
        "upper_gap_at_bound": fraction_record(upper_gap),
    }


def third_edge_certificate() -> dict[str, Any]:
    roots = [
        parameter
        for parameter in range(THIRD_SOURCE_STRIDE)
        if (3**7 * second_register_mod(parameter, 8) + 1) % (1 << 8) == 0
    ]
    if roots != [THIRD_SOURCE_BASE]:
        raise AssertionError("third restorative address is not unique")
    source_mod = second_register_mod(THIRD_SOURCE_BASE, 8)
    if source_mod != THIRD_SOURCE_REGISTER:
        raise AssertionError("third source register residue changed")

    scales, heads = clock(32)
    if tuple(heads[SECOND_PHASE : SECOND_PHASE + len(THIRD_HEADS)]) != THIRD_HEADS:
        raise AssertionError("third edge disagrees with the scale clock")

    # Exact formula at the output of the second edge:
    # D = scale*3^L + correction, L >= 20 on the whole source cylinder.
    constant = 3**10 * 4669 + 2**21
    correction = Fraction(3**7 * constant, 2**29)
    defect = 3**7 * source_mod
    shortcut_steps = 0
    odd_steps = 0
    net_space = 0
    stage_records: list[dict[str, Any]] = []
    for offset, (expected_head, expected_carries) in enumerate(
        zip(THIRD_HEADS, THIRD_CARRIES, strict=True)
    ):
        phase = SECOND_PHASE + offset
        head_check = check_corrected_head(scales[phase], correction, expected_head, 20)
        observed: list[int] = []
        for _ in range(1 if expected_head == 0 else 2):
            shortcut_steps += 1
            if defect % 2 == 0:
                defect = 3 * defect // 2
                correction *= Fraction(3, 2)
                odd_steps += 1
                observed.append(1)
            else:
                defect = (defect + 1) // 2
                correction = (correction + 1) / 2
                observed.append(0)
        if tuple(observed) != expected_carries:
            raise AssertionError("third edge carry schedule failed")
        net_space += sum(observed) - 1
        stage_records.append(
            {
                "phase": phase,
                "head_check": head_check,
                "terminal_carries": observed,
                "representative_defect": defect,
                "space_delta": sum(observed) - 1,
            }
        )

    output, remainder = divmod(defect, 3**7)
    if remainder or output % 3 == 0:
        raise AssertionError("third edge failed to restore exactly seven trits")
    if (shortcut_steps, odd_steps, net_space, output) != (8, 7, 2, 1888):
        raise AssertionError("third edge ledger changed")
    if (1 << 8) * output != 3**7 * source_mod + 1:
        raise AssertionError("third affine register map failed")

    # Bounded independent audit of the inherited isometry and exact low bit.
    registers = [third_register_mod(parameter, 16) for parameter in range(33)]
    for left in range(len(registers)):
        if registers[left] % 2 != left % 2:
            raise AssertionError("third register does not expose its source bit")
        for right in range(left + 1, len(registers)):
            difference = (registers[right] - registers[left]) % (1 << 16)
            if v2_nonzero(difference) != v2_nonzero(right - left):
                raise AssertionError("third-register isometry regression failed")

    return {
        "source_parameter": "w=249+256*z",
        "source_residue": THIRD_SOURCE_BASE,
        "source_modulus": THIRD_SOURCE_STRIDE,
        "source_register_mod_256": source_mod,
        "heads": list(THIRD_HEADS),
        "terminal_carries": [list(value) for value in THIRD_CARRIES],
        "shortcut_steps": shortcut_steps,
        "odd_steps": odd_steps,
        "net_space_charge": net_space,
        "endpoint_reservoir": 7,
        "register_map": "256*U=3^7*T+1",
        "representative_output_register": output,
        "stages": stage_records,
        "output_register_mod_256": registers[:16],
        "output_low_bit": "U(z) mod 2 = z mod 2",
        "isometry_scope": "all-parameter algebra; bounded pair replay for z=0,...,32",
    }


def block_value_mod(block: str, modulus: int) -> int:
    queue.validate_trit_word(block)
    value = 0
    for trit in block:
        value = (3 * value + int(trit)) % modulus
    return value


def cascade_block(block: str, start_state: int, layers: int) -> tuple[str, int]:
    """Apply ``layers`` quotient sweeps to one atom in a single pass.

    Bit ``i`` of the state is the carry entering sweep layer ``i`` at the
    current atom boundary.  Summing the layer equations with weights ``2^i``
    gives the exact invariant

        3*state + digit = 2^layers*output_digit + next_state.
    """

    if layers < 1 or not 0 <= start_state < 1 << layers:
        raise ValueError("invalid cascade state")
    queue.validate_trit_word(block)
    state = start_state
    output: list[str] = []
    for trit in block:
        digit = trit
        next_state = state
        for layer in range(layers):
            carry = (state >> layer) & 1
            quotient, next_carry = queue.SWEEP_TRANSITION[carry, digit]
            if next_carry:
                next_state |= 1 << layer
            else:
                next_state &= ~(1 << layer)
            digit = quotient
        output.append(digit)
        state = next_state
    return "".join(output), state


def counter_write_no_go_certificate() -> dict[str, Any]:
    """Prove the tempting atom-pair counter write does not occur.

    The multiplier has order two, but it is ``1+2^18`` rather than ``-1``.
    Because the block translation is odd, two atom transitions give a
    translation of exact valuation one.  Every affine carry-state orbit
    therefore has the full period ``2^19``.  The third nominal block uses one
    whole state cycle and has no smaller atom-aligned repetition.
    """

    base = burst.returned_explicit_lasso().block
    if len(base) != BASE_ATOM_LENGTH:
        raise AssertionError("returned base atom length changed")
    modulus = 1 << TOTAL_SWEEPS
    multiplier = pow(3, BASE_ATOM_LENGTH, modulus)
    if multiplier != 1 + (1 << 18):
        raise AssertionError("unexpected base-atom multiplier")
    translation = block_value_mod(base, modulus)
    if translation % 2 != 1:
        raise AssertionError("base-atom translation must be odd")

    def transition(state: int) -> int:
        return (multiplier * state + translation) % modulus

    two_step_translation = (multiplier + 1) * translation % modulus
    if v2_nonzero(two_step_translation) != 1:
        raise AssertionError("two-step translation lacks exact valuation one")

    # For even k=2j, f^k(r)=r+j*c, so the least return has j=2^18 and
    # k=2^19.  Odd iterates cannot return because (f^(2j+1)(r)-r) is odd.
    # Exhaust four complete representative orbits independently.
    representative_periods: dict[str, int] = {}
    for state in (0, 1, 12345, modulus - 1):
        current = state
        for period in range(1, modulus + 1):
            current = transition(current)
            if current == state:
                break
        if period != modulus:
            raise AssertionError("affine carry orbit had a short period")
        representative_periods[str(state)] = period

    # Two explicit atoms validate the cascade/state formula.  They do not
    # return to the initial state, which is precisely the failed reblocking.
    first, middle = cascade_block(base, 0, TOTAL_SWEEPS)
    second, after_two = cascade_block(base, middle, TOTAL_SWEEPS)
    if middle != transition(0):
        raise AssertionError("explicit cascade disagrees with affine state law")
    if after_two != transition(middle) or after_two != two_step_translation:
        raise AssertionError("explicit two-atom cascade state law failed")

    source_atoms = (1 << 11) * (1 << 8)
    if source_atoms != 1 << TOTAL_SWEEPS or source_atoms % 2:
        raise AssertionError("third restriction has the wrong atom count")
    nominal_block_length = source_atoms * BASE_ATOM_LENGTH
    return {
        "cascade_layers": TOTAL_SWEEPS,
        "state_modulus": modulus,
        "base_atom_length": BASE_ATOM_LENGTH,
        "atom_multiplier_mod_state": multiplier,
        "atom_translation_mod_state": translation,
        "universal_state_law": "r_next=3^65536*r+blockValue (mod 2^19)",
        "multiplier_order": 2,
        "two_step_translation": two_step_translation,
        "two_step_translation_v2": 1,
        "universal_period": modulus,
        "period_proof": (
            "even iterates translate by j*c with v2(c)=1; odd return "
            "differences are odd; hence the least return is 2^19"
        ),
        "representative_periods": representative_periods,
        "first_atom_sha256_at_state_zero": yah.sha256_bytes(first.encode()),
        "second_atom_sha256_at_state_zero": yah.sha256_bytes(second.encode()),
        "two_atom_block_sha256_at_state_zero": yah.sha256_bytes((first + second).encode()),
        "two_atoms_distinct_at_state_zero": first != second,
        "state_after_first_atom_from_zero": middle,
        "state_after_two_atoms_from_zero": after_two,
        "source_atoms_per_nominal_block": source_atoms,
        "nominal_block_length": nominal_block_length,
        "atom_aligned_primitive_period": source_atoms,
        "counter_update": None,
        "written_zero_bits": 0,
        "scope": (
            "the third output block traverses a full 2^19 carry-state cycle; "
            "the order-two multiplier does not yield a two-atom reblocking"
        ),
    }


def full_cycle_lasso_gate(max_layers: int) -> dict[str, Any]:
    """Audit the universal fixed-sweep lasso information gate.

    For modulus ``2^s`` the atom-boundary carry map is the mixed congruential
    generator ``r -> 3^m*r+b``.  Here ``m`` is even and ``b`` is odd, so the
    multiplier is one modulo four and the translation is coprime to the
    modulus.  The power-of-two full-period criterion gives one cycle of size
    ``2^s``.  We exhaust the cycles through layer 18 and check the algebraic
    hypotheses through ``max_layers``.
    """

    if max_layers < TOTAL_SWEEPS:
        raise ValueError("full-cycle audit must include the live 19-layer chart")
    base = burst.returned_explicit_lasso().block
    if len(base) != BASE_ATOM_LENGTH or BASE_ATOM_LENGTH % 2:
        raise AssertionError("base atom must have positive even length")
    rows: list[dict[str, Any]] = []
    for layers in range(1, max_layers + 1):
        modulus = 1 << layers
        multiplier = pow(3, BASE_ATOM_LENGTH, modulus)
        translation = block_value_mod(base, modulus)
        if translation % 2 != 1:
            raise AssertionError("atom translation stopped being odd")
        if layers >= 2 and multiplier % 4 != 1:
            raise AssertionError("atom multiplier stopped being one modulo four")
        exhausted_period = None
        if layers <= 18:
            state = 0
            for period in range(1, modulus + 1):
                state = (multiplier * state + translation) % modulus
                if state == 0:
                    break
            if period != modulus:
                raise AssertionError("bounded affine carry map was not full-cycle")
            exhausted_period = period
        rows.append(
            {
                "layers": layers,
                "modulus": modulus,
                "multiplier": multiplier,
                "translation": translation,
                "multiplier_mod_4": multiplier % 4,
                "translation_mod_2": translation % 2,
                "exhausted_period": exhausted_period,
            }
        )
    if not BASE_ATOM_LENGTH >= max_layers:
        raise AssertionError("output-atom injectivity size bound failed")
    return {
        "max_layers": max_layers,
        "base_atom_length": BASE_ATOM_LENGTH,
        "base_atom_even": True,
        "base_atom_value_odd": True,
        "rows": rows,
        "exhaustive_cycle_layers": 18,
        "full_period_schema_to_formalize": (
            "for every s>=1, odd b and a=3^m=1 mod 4 give one affine "
            "carry-state cycle of length 2^s"
        ),
        "formal_status": (
            "the universal LCG/reblocking theorem is requested from Lean; "
            "this artifact checks its hypotheses through layer 24 and "
            "exhausts the cycles through layer 18"
        ),
        "output_atom_injectivity": (
            "3^m>2^s makes the quotient output block injective in its "
            "incoming carry state"
        ),
        "lasso_information_law": (
            "after canonical reblocking, every fixed finite pipeline of s "
            "quotient sweeps updates t=a+2^s*t_next and consumes s bits"
        ),
        "conditional_design_implication": (
            "no fixed-macro letter-to-letter lasso edge can increase its "
            "ordinary repetition parameter once the displayed full-period "
            "schema is kernel-checked; contextual/nonuniform pipelines remain open"
        ),
    }


def slope_space_audit(scales: list[Fraction], heads: list[int]) -> dict[str, Any]:
    checks = 0
    minimum_positive = None
    samples: list[dict[str, Any]] = []
    for start in range(32):
        sweeps = 0
        for count in range(1, 33):
            head = heads[start + count - 1]
            sweeps += 1 if head == 0 else 2
            for odd in range(sweeps + 1):
                gain = odd - count
                direct = Fraction(3**odd, 2**sweeps)
                gain_factor = (
                    Fraction(3**gain) if gain >= 0 else Fraction(1, 3 ** (-gain))
                )
                factored = gain_factor * scales[start + count] / scales[start]
                if direct != factored:
                    raise AssertionError("slope-space factorization failed")
                if gain > 0:
                    if direct <= Fraction(3, 2):
                        raise AssertionError("positive-space edge was not expanding")
                    minimum_positive = (
                        direct
                        if minimum_positive is None
                        else min(minimum_positive, direct)
                    )
                checks += 1
            if start in {0, 7, 12} and count in {1, 5, 12}:
                samples.append(
                    {
                        "start_phase": start,
                        "macro_count": count,
                        "sweeps": sweeps,
                        "scale_ratio": fraction_record(scales[start + count] / scales[start]),
                    }
                )
    if minimum_positive is None:
        raise AssertionError("slope audit did not test a positive-space segment")
    return {
        "finite_identity_checks": checks,
        "minimum_positive_slope_in_audit": fraction_record(minimum_positive),
        "universal_identity": "3^J/2^S=3^(J-M)*rho_(n+M)/rho_n",
        "universal_consequence": (
            "rho in [1,2) implies every segment with J-M>=1 has slope >3/2"
        ),
        "samples": samples,
    }


def build_audit(clock_length: int) -> dict[str, Any]:
    if clock_length < 80:
        raise ValueError("clock audit must include at least 80 macros")
    scales, heads = clock(clock_length)
    sweep_prefix = [0]
    for head in heads:
        sweep_prefix.append(sweep_prefix[-1] + (1 if head == 0 else 2))
    for index, scale in enumerate(scales):
        expected = INITIAL_SCALE * Fraction(3**index, 2 ** sweep_prefix[index])
        if scale != expected or not Fraction(1) <= scale < 2:
            raise AssertionError("closed scale formula failed")
    return {
        "clock_length": clock_length,
        "initial_scale": fraction_record(INITIAL_SCALE),
        "head_word": "".join(map(str, heads)),
        "zero_heads": heads.count(0),
        "one_heads": heads.count(1),
        "two_heads": heads.count(2),
        "sweep_prefix_final": sweep_prefix[-1],
        "closed_scale_law": "rho_n=rho_0*3^n/2^S_n in [1,2)",
        "aperiodicity_schema": (
            "an eventually periodic head tail would repeat one sweep count q "
            "over p macros; bounded rho forces 3^p=2^q, impossible for p>0"
        ),
        "third_restorative_edge": third_edge_certificate(),
        "counter_write_no_go": counter_write_no_go_certificate(),
        "full_cycle_lasso_gate": full_cycle_lasso_gate(24),
        "slope_space": slope_space_audit(scales, heads),
        "closure_status": {
            "counterexample": None,
            "achieved": (
                "an abstract scale clock, a correction-bridged third edge, and "
                "exact positive-space and counter-reblocking no-go certificates"
            ),
            "closed_lane": "a positive-space nonexpanding chart edge cannot exist",
            "missing": (
                "a contextual opcode which genuinely increases or nonlinearly "
                "rewrites the lasso counter instead of restricting it"
            ),
        },
    }


def worker_sha256() -> str:
    return yah.sha256_bytes(Path(__file__).read_bytes())


def build_artifact(clock_length: int) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "worker_sha256": worker_sha256(),
        "burst_worker_sha256": yah.sha256_bytes(Path(burst.__file__).read_bytes()),
        "audit": build_audit(clock_length),
    }
    payload = dict(data)
    data["artifact_sha256"] = yah.sha256_bytes(yah.canonical_json(payload))
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    required = {
        "schema", "generated_at_utc", "worker_sha256", "burst_worker_sha256",
        "audit", "artifact_sha256",
    }
    if set(data) != required or data["schema"] != SCHEMA:
        raise ValueError("artifact schema mismatch")
    if data["worker_sha256"] != worker_sha256():
        raise ValueError("worker hash mismatch")
    if data["burst_worker_sha256"] != yah.sha256_bytes(Path(burst.__file__).read_bytes()):
        raise ValueError("burst worker hash mismatch")
    payload = dict(data)
    advertised = payload.pop("artifact_sha256")
    if advertised != yah.sha256_bytes(yah.canonical_json(payload)):
        raise ValueError("artifact self-hash mismatch")
    count = data["audit"]["clock_length"]
    if data["audit"] != build_audit(count):
        raise ValueError("chart-clock audit replay mismatch")
    edge = data["audit"]["third_restorative_edge"]
    return {
        "artifact_sha256": advertised,
        "worker_sha256": data["worker_sha256"],
        "clock_length": count,
        "third_source_residue": edge["source_residue"],
        "third_register_map": edge["register_map"],
        "counterexample": None,
    }


def selftest() -> None:
    scales, heads = clock(20)
    if "".join(map(str, heads)) != "01020210102101020210":
        raise AssertionError("scale-clock prefix changed")
    if scales[7] != Fraction(588305187, 536870912):
        raise AssertionError("second-edge output phase changed")
    third_edge_certificate()


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--clock-length", type=int, default=128)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "selftest":
        selftest()
        print("selftest: ok")
        return 0
    if args.command == "build":
        selftest()
        artifact = build_artifact(args.clock_length)
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())

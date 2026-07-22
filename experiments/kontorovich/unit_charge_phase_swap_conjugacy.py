#!/usr/bin/env python3
"""Exact two-opcode phase-swap conjugacies in the public cofactor language.

For fixed ``L,d,h0,h1`` define the linked two-step word

    W_r = [(r,h0,L-r), (L-r,h1,r+d)].

The next word ``W_(r+d)`` differs at its three phase boundaries by
``(+d,-d,+d)``.  Consequently the two composite maps have exactly the same
binary and ternary exponents.  This is a word-level way for two opcode charts
to cross and recover their original separation; it evades the one-cell
``2622 -> 2618`` separation loss.

This worker compiles the nested source cylinders exactly and constructs an
integral affine conjugacy between consecutive word *maps* when the composite
constant passes the same gcd criterion as a one-step parallel conjugacy.  The
default artifact checks both parallel comparisons in the smallest phase line

    W_1 : 1 -> 3 -> 2,
    W_2 : 2 -> 2 -> 3,
    W_3 : 3 -> 1 -> 4.

The artifact also checks the decisive *conjugacy-selected* handoff inequality:
the embedded source of the next word lies strictly above the current word's
output, and its tail coefficient grows faster.  Hence these conjugacy squares
do not themselves chain into an orbit.

This does not mean that the two word-rays are disjoint.  Coprimality of their
binary and ternary strides gives a different direct handoff progression.  The
worker constructs and replays that progression too.  It is one more selected
dyadic cylinder, not a conjugacy, a turnaround, an infinite ordinary orbit, a
universal literal Collatz theorem, or a counterexample.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

from unit_charge_public_cofactor import branch, replay_branch_member


SCHEMA = "collatz-unit-charge-phase-swap-conjugacy-v2"


def phase_swap_word(
    r: int, L: int, d: int, h0: int, h1: int
) -> list[dict[str, int | str | bool]]:
    """Return the two public branches in ``W_r``."""
    if min(r, d, h0, h1) < 1 or L - r < 1:
        raise ValueError("phase-swap parameters must keep every opcode positive")
    return [
        branch(r, h0, L - r),
        branch(L - r, h1, r + d),
    ]


def compile_two_word(
    rows: list[dict[str, int | str | bool]],
) -> dict[str, Any]:
    """Compile two linked branch cylinders into one exact affine map."""
    if len(rows) != 2:
        raise ValueError("the phase-swap compiler expects exactly two branches")
    first, second = rows
    p0 = int(first["P"])
    p1 = int(second["P"])
    q0 = int(first["Q"])
    q1 = int(second["Q"])
    rho0 = int(first["source_tail_residue"])
    sigma0 = int(first["target_tail_base"])
    rho1 = int(second["source_tail_residue"])
    sigma1 = int(second["target_tail_base"])

    # The first output must land in the second source cylinder.  Since 3 is
    # odd, this selects one exact surviving-tail class modulo 2^p1.
    u0 = (
        (rho1 - sigma0)
        * pow(pow(3, q0), -1, 1 << p1)
    ) % (1 << p1)
    source_residue = rho0 + (1 << p0) * u0
    middle_tail = sigma0 + pow(3, q0) * u0
    if (middle_tail - rho1) % (1 << p1):
        raise AssertionError("two-word middle cylinder did not link")
    second_surviving_base = (middle_tail - rho1) // (1 << p1)
    target_base = sigma1 + pow(3, q1) * second_surviving_base

    p = p0 + p1
    q = q0 + q1
    kappa = (1 << p) * target_base - pow(3, q) * source_residue
    expected_kappa = (
        pow(3, q1) * int(first["kappa"])
        + (1 << p0) * int(second["kappa"])
    )
    if kappa != expected_kappa:
        raise AssertionError("two-word affine constant composition failed")
    return {
        "rows": rows,
        "P": p,
        "Q": q,
        "kappa": kappa,
        "source_tail_residue": source_residue,
        "target_tail_base": target_base,
        "first_surviving_base": u0,
        "second_surviving_base": second_surviving_base,
    }


def replay_composite_member(compiled: dict[str, Any], tail: int) -> dict[str, int]:
    """Replay both arithmetic bouncer branches for one composite tail."""
    if tail < 0:
        raise ValueError("surviving tail must be nonnegative")
    first, second = compiled["rows"]
    p1 = int(second["P"])
    q0 = int(first["Q"])
    first_tail = int(compiled["first_surviving_base"]) + (1 << p1) * tail
    second_tail = int(compiled["second_surviving_base"]) + pow(3, q0) * tail
    first_replay = replay_branch_member(first, first_tail)
    second_replay = replay_branch_member(second, second_tail)
    if int(first_replay["target_tail"]) != int(second_replay["source_tail"]):
        raise AssertionError("arithmetic bouncer replays did not link")
    source_tail = int(compiled["source_tail_residue"]) + (
        1 << int(compiled["P"])
    ) * tail
    target_tail = int(compiled["target_tail_base"]) + pow(
        3, int(compiled["Q"])
    ) * tail
    if source_tail != int(first_replay["source_tail"]):
        raise AssertionError("compiled source tail disagreed with replay")
    if target_tail != int(second_replay["target_tail"]):
        raise AssertionError("compiled target tail disagreed with replay")

    return {
        "source_tail": source_tail,
        "target_tail": target_tail,
        "source_y": int(first_replay["input_y"]),
        "target_y": int(second_replay["output_y"]),
    }


def least_positive_conjugacy(
    first: dict[str, Any], second: dict[str, Any]
) -> tuple[int, int, int, int]:
    """Return ``(s,c,v0,g)`` for a composite source-cylinder embedding."""
    if first["P"] != second["P"] or first["Q"] != second["Q"]:
        raise ValueError("composite conjugacy requires equal total gains")
    p = int(first["P"])
    q = int(first["Q"])
    binary = 1 << p
    ternary = pow(3, q)
    gap = ternary - binary
    if gap <= 0:
        raise ValueError("selected composite is not outward")
    kappa_a = int(first["kappa"])
    kappa_b = int(second["kappa"])
    divisor = math.gcd(abs(kappa_a), gap)
    if kappa_b % divisor:
        raise ValueError("composite constants fail the conjugacy gcd criterion")
    modulus = gap // divisor
    slope = (
        (kappa_b // divisor)
        * pow((kappa_a // divisor) % modulus, -1, modulus)
    ) % modulus
    if slope == 0:
        slope = modulus

    def values(candidate: int) -> tuple[int, int]:
        numerator = candidate * kappa_a - kappa_b
        if numerator % gap:
            raise AssertionError("composite conjugacy congruence failed")
        intercept = numerator // gap
        cylinder_numerator = (
            candidate * int(first["source_tail_residue"])
            + intercept
            - int(second["source_tail_residue"])
        )
        if cylinder_numerator % binary:
            raise AssertionError("composite conjugacy missed its source cylinder")
        return intercept, cylinder_numerator // binary

    intercept, surviving_base = values(slope)
    while intercept < 0 or surviving_base < 0:
        slope += modulus
        intercept, surviving_base = values(slope)
    return slope, intercept, surviving_base, divisor


def conjugacy_record(r: int, L: int, d: int, h0: int, h1: int) -> dict[str, Any]:
    """Build and exactly replay ``W_r -> W_(r+d)``."""
    first = compile_two_word(phase_swap_word(r, L, d, h0, h1))
    second = compile_two_word(phase_swap_word(r + d, L, d, h0, h1))
    if first["P"] != second["P"] or first["Q"] != second["Q"]:
        raise AssertionError("phase swap lost its equal total exponents")
    slope, intercept, surviving_base, divisor = least_positive_conjugacy(
        first, second
    )
    p = int(first["P"])
    q = int(first["Q"])
    binary = 1 << p
    ternary = pow(3, q)
    if (
        (ternary - binary) * intercept
        != slope * int(first["kappa"]) - int(second["kappa"])
    ):
        raise AssertionError("composite affine conjugacy identity failed")
    if (
        slope * int(first["source_tail_residue"]) + intercept
        != int(second["source_tail_residue"]) + binary * surviving_base
    ):
        raise AssertionError("composite source-cylinder embedding failed")
    if (
        slope * int(first["target_tail_base"]) + intercept
        != int(second["target_tail_base"]) + ternary * surviving_base
    ):
        raise AssertionError("composite target-tail embedding failed")

    # A parallel conjugacy is not automatically an orbit handoff.  The current output is
    # sigma_a+3^Q*u, whereas the conjugacy-selected next input is
    # rho_b+2^P*(v0+s*u).  Both the constant and slope differences are
    # strictly positive in the two certified cells.
    orbit_constant_gap = (
        int(second["source_tail_residue"])
        + binary * surviving_base
        - int(first["target_tail_base"])
    )
    orbit_slope_gap = binary * slope - ternary
    if orbit_constant_gap <= 0 or orbit_slope_gap <= 0:
        raise AssertionError("certified phase swap lost its no-handoff inequality")

    # The failure above is specific to the advertised conjugacy embedding.
    # Independently, the two rays always have a direct CRT handoff because
    # gcd(3^Q,2^P)=1.  Solve
    #
    #   sigma_a+3^Q*u = rho_b+2^P*v
    #
    # in the least nonnegative u residue and shift the full solution lattice
    # until v is nonnegative as well.
    direct_delta = int(second["source_tail_residue"]) - int(
        first["target_tail_base"]
    )
    direct_current_base = (
        direct_delta * pow(ternary, -1, binary)
    ) % binary
    direct_next_base = (
        ternary * direct_current_base - direct_delta
    ) // binary
    if direct_next_base < 0:
        shift = (-direct_next_base + ternary - 1) // ternary
        direct_current_base += binary * shift
        direct_next_base += ternary * shift
    if direct_current_base < 0 or direct_next_base < 0:
        raise AssertionError("direct handoff progression is not nonnegative")
    if (
        int(first["target_tail_base"]) + ternary * direct_current_base
        != int(second["source_tail_residue"]) + binary * direct_next_base
    ):
        raise AssertionError("direct handoff base equation failed")

    direct_samples: list[dict[str, int]] = []
    for tail in (0, 1):
        current_tail = direct_current_base + binary * tail
        next_tail = direct_next_base + ternary * tail
        current = replay_composite_member(first, current_tail)
        next_member = replay_composite_member(second, next_tail)
        if current["target_tail"] != next_member["source_tail"]:
            raise AssertionError("direct handoff sample did not link")
        direct_samples.append(
            {
                "residual_tail": tail,
                "current_surviving_tail_bits": current_tail.bit_length(),
                "next_surviving_tail_bits": next_tail.bit_length(),
                "linked_public_tail_bits": current["target_tail"].bit_length(),
                "arithmetic_bouncer_steps_replayed": 4,
            }
        )

    samples: list[dict[str, int]] = []
    for tail in (0, 1):
        a = replay_composite_member(first, tail)
        b_tail = surviving_base + slope * tail
        b = replay_composite_member(second, b_tail)
        if b["source_tail"] != slope * a["source_tail"] + intercept:
            raise AssertionError("sample source tails missed conjugacy")
        if b["target_tail"] != slope * a["target_tail"] + intercept:
            raise AssertionError("sample target tails missed conjugacy")
        samples.append(
            {
                "source_surviving_tail": tail,
                "target_surviving_tail": b_tail,
                "source_y_bits": a["source_y"].bit_length(),
                "source_endpoint_y_bits": a["target_y"].bit_length(),
                "target_y_bits": b["source_y"].bit_length(),
                "target_endpoint_y_bits": b["target_y"].bit_length(),
                "arithmetic_bouncer_steps_replayed": 4,
            }
        )

    def triples(compiled: dict[str, Any]) -> list[list[int]]:
        return [
            [int(row["m"]), int(row["h"]), int(row["next_m"])]
            for row in compiled["rows"]
        ]

    return {
        "parameters": {"r": r, "L": L, "d": d, "h0": h0, "h1": h1},
        "source_word": triples(first),
        "target_word": triples(second),
        "boundary_phase_differences": [d, -d, d],
        "P": p,
        "Q": q,
        "composite_kappa_source": str(first["kappa"]),
        "composite_kappa_target": str(second["kappa"]),
        "kappa_gcd_with_gain_gap": divisor,
        "embedding_slope": str(slope),
        "embedding_intercept": str(intercept),
        "surviving_tail_base": str(surviving_base),
        "equal_total_gains_checked": True,
        "nested_source_cylinders_checked": True,
        "affine_conjugacy_checked": True,
        "orbit_handoff_constant_gap": str(orbit_constant_gap),
        "orbit_handoff_slope_gap": str(orbit_slope_gap),
        "no_nonnegative_tail_conjugacy_handoff_checked": True,
        "direct_handoff_current_tail_base": str(direct_current_base),
        "direct_handoff_next_tail_base": str(direct_next_base),
        "direct_handoff_current_stride_power_of_two": p,
        "direct_handoff_next_stride_power_of_three": q,
        "direct_handoff_base_equation_checked": True,
        "direct_handoff_samples": direct_samples,
        "samples": samples,
    }


def build_record() -> dict[str, Any]:
    records = [conjugacy_record(r, 4, 1, 1, 1) for r in (1, 2)]
    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact arithmetic construction of the two consecutive composite "
            "conjugacies W_1->W_2 and W_2->W_3 in the L=4,d=1,h0=h1=1 "
            "phase-swap line, the exact no-conjugacy-handoff inequalities, "
            "and distinct direct finite handoff progressions"
        ),
        "non_claims": (
            "the direct progressions are fresh dyadic cylinder selections, "
            "not a conjugacy, turnaround, self-reproducing linked glider, "
            "infinite ordinary orbit, universal literal Collatz compiler, "
            "or counterexample"
        ),
        "records": records,
    }


def verify_record(record: dict[str, Any]) -> None:
    if record.get("schema") != SCHEMA:
        raise ValueError("unsupported phase-swap conjugacy schema")
    if record != build_record():
        raise ValueError("phase-swap conjugacy artifact failed reconstruction")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    build = sub.add_parser("build")
    build.add_argument("output", type=Path)
    verify = sub.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        verify_record(build_record())
        print("unit charge phase-swap conjugacy selftest: PASS")
    elif args.command == "build":
        record = build_record()
        args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_record(json.loads(args.artifact.read_text()))
        print("unit charge phase-swap conjugacy artifact: PASS")


if __name__ == "__main__":
    main()

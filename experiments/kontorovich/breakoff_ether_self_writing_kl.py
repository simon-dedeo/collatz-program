#!/usr/bin/env python3
"""Exact self-writing KL coordinate for the returning ether glider.

For every genuine returning-glider packet put

    Z = 3^(6*n) * u = Z0 + (473*2^20) * q.

The complete EC17 transition then collapses to the fixed determinant identity

    3^11 * Z(q) + 17 = 2^20 * W(q),
    W(q) = 83499104 + (473*3^11) * q.

The current branch is written in ``v3(Z)``.  The next branch is read from
``v2(W)`` and written back as the same multiple of six in ``v3(Z')``.  This
is an exact deterministic search coordinate, not an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from math import gcd
from pathlib import Path

from breakoff_ether_counter import REGISTER_OFFSET, REGISTER_STRIDE
from breakoff_ether_glider import glider_macro, link_macros


SCHEMA = "collatz-breakoff-ether-self-writing-kl-v2"
Z0 = 494_251_421
Z_STRIDE = 473 * (1 << 20)
W0 = 83_499_104
W_STRIDE = 473 * 3**11
RETURN_BITS = 20
R0 = 1_044_929


def vprime(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("zero has no finite valuation")
    result = 0
    value = abs(value)
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def normalized_core(ether_cells: int, packet: int) -> int:
    register = REGISTER_STRIDE * packet + REGISTER_OFFSET
    denominator = 3 * (1 << (8 * ether_cells - 5))
    if register <= 0 or register % denominator:
        raise AssertionError("packet has no positive normalized core")
    core = register // denominator
    if core % 2 != 1 or core % 3 != 1:
        raise AssertionError("packet core left the EC17 unit class")
    return core


def packet_q(ether_cells: int, packet: int) -> int:
    core = normalized_core(ether_cells, packet)
    packet_scale = (1 << (8 * ether_cells - 5)) * core
    if (packet_scale + 291_427) % 473:
        raise AssertionError("packet left the invariant color zero")
    z = 3 ** (6 * ether_cells) * core
    difference = z - Z0
    if difference < 0 or difference % Z_STRIDE:
        raise AssertionError("packet left the fixed self-writing cylinder")
    q = difference // Z_STRIDE
    if vprime(z, 3) != 6 * ether_cells:
        raise AssertionError("packet branch is not written in the ternary rail")
    return q


def accepted_step(q: int) -> tuple[int, int, int]:
    """Return current branch, next branch, and q' for one accepted state."""

    if q < 0:
        raise ValueError("self-writing payload must be nonnegative")
    z = Z0 + Z_STRIDE * q
    ternary = vprime(z, 3)
    if ternary < 6 or ternary % 6:
        raise ValueError("current ternary rail is not a positive branch")
    current = ternary // 6
    core = z // 3**ternary
    if core % 3 != 1:
        raise ValueError("initial packet is in the wrong ternary unit class")

    w = W0 + W_STRIDE * q
    binary = vprime(w, 2)
    if binary < 3 or (binary + 5) % 8:
        raise ValueError("binary delay does not encode a target branch")
    target = (binary + 5) // 8
    next_core = w >> binary
    numerator = 729**target * next_core - Z0
    if numerator < 0 or numerator % Z_STRIDE:
        raise ValueError("fixed 20-bit return cylinder failed")
    q_next = numerator // Z_STRIDE

    z_next = Z0 + Z_STRIDE * q_next
    if z_next != 729**target * next_core:
        raise AssertionError("next ternary rail reconstruction failed")
    if vprime(z_next, 3) != 6 * target or next_core % 3 != 1:
        raise AssertionError("binary delay was not written back ternarily")
    if q_next <= q:
        raise AssertionError("accepted self-writing step was not outward")
    return current, target, q_next


def crt_pair(a: int, modulus_a: int, b: int, modulus_b: int) -> int:
    if modulus_a <= 0 or modulus_b <= 0:
        raise ValueError("CRT moduli must be positive")
    if modulus_a % 2 == 0 or modulus_b != 1 << RETURN_BITS:
        raise ValueError("unexpected CRT modulus shape")
    return a + modulus_a * (
        (b - a) * pow(modulus_a, -1, modulus_b) % modulus_b
    )


def target_family(target: int) -> dict[str, object]:
    """The complete dyadic source cylinder for one prescribed next branch."""

    if target < 1:
        raise ValueError("target branch must be positive")
    binary = 8 * target - 5
    odd_residue = W0 * pow(2, -binary, W_STRIDE) % W_STRIDE
    return_residue = Z0 * pow(729, -target, 1 << RETURN_BITS) % (
        1 << RETURN_BITS
    )
    core_base = crt_pair(
        odd_residue, W_STRIDE, return_residue, 1 << RETURN_BITS
    )
    core_stride = W_STRIDE * (1 << RETURN_BITS)

    # Move to the first nonnegative source and target in this complete class.
    def source_of(lift: int) -> int:
        value = (1 << binary) * (core_base + core_stride * lift) - W0
        if value % W_STRIDE:
            raise AssertionError("CRT core did not reconstruct an integer source")
        return value // W_STRIDE

    def output_of(lift: int) -> int:
        value = 729**target * (core_base + core_stride * lift) - Z0
        if value % Z_STRIDE:
            raise AssertionError("CRT core missed the return cylinder")
        return value // Z_STRIDE

    lift = 0
    if source_of(lift) < 0 or output_of(lift) < 0:
        source_gain = 1 << (binary + RETURN_BITS)
        output_gain = 3 ** (6 * target + 11)
        lift = max(
            (-source_of(0) + source_gain - 1) // source_gain,
            (-output_of(0) + output_gain - 1) // output_gain,
        )
    core_base += core_stride * lift
    source_base = source_of(0) if lift == 0 else (
        ((1 << binary) * core_base - W0) // W_STRIDE
    )
    output_base = output_of(0) if lift == 0 else (
        (729**target * core_base - Z0) // Z_STRIDE
    )
    source_stride = 1 << (8 * target + 15)
    output_stride = 3 ** (6 * target + 11)

    for tail in range(3):
        q = source_base + source_stride * tail
        h = core_base + core_stride * tail
        w = W0 + W_STRIDE * q
        if w != (1 << binary) * h or vprime(w, 2) != binary:
            raise AssertionError("target family lost its exact binary delay")
        q_next = output_base + output_stride * tail
        if Z0 + Z_STRIDE * q_next != 729**target * h:
            raise AssertionError("target family lost its ternary writeback")

    return {
        "target_branch": target,
        "binary_delay": binary,
        "odd_core_base": str(core_base),
        "odd_core_stride": str(core_stride),
        "source_q_base": str(source_base),
        "source_q_stride": str(source_stride),
        "target_q_base": str(output_base),
        "target_q_stride": str(output_stride),
        "return_residue_mod_2^20": return_residue,
    }


def verify_affine_theorems() -> dict[str, object]:
    if 3**11 * Z0 + 17 != (1 << 20) * W0:
        raise AssertionError("two-rail constant identity failed")
    if 3**11 * Z_STRIDE != (1 << 20) * W_STRIDE:
        raise AssertionError("two-rail slope identity failed")
    if Z0 != 473 * R0 + 4:
        raise AssertionError("R/q centering constant changed")

    # D and E are represented as affine pairs (slope, intercept).
    d = (Fraction(3**11, 1 << 15), Fraction(1221, 1 << 15))
    e = (Fraction(729, 256), Fraction(4, 256))
    if 3**11 * (473 * R0 + 4) + 17 != (1 << 15) * (
        473 * (d[0] * R0 + d[1]) + 4
    ):
        raise AssertionError("D conjugacy identity failed")
    if 256 * (473 * (e[0] * R0 + e[1]) + 4) != 729 * (
        473 * R0 + 4
    ):
        raise AssertionError("E conjugacy identity failed")

    boundary = (1 << 18) * R0 + 2215
    e_boundary = (729 * boundary + 881) / 256
    conjugate = (1 << 18) * (e[0] * R0 + e[1]) + 2215
    if e_boundary != conjugate:
        raise AssertionError("KL ether conjugacy failed")
    d_boundary = (3**11 * boundary + 278339) / (1 << 15)
    d_conjugate = (1 << 18) * (d[0] * R0 + d[1]) + 2215
    if d_boundary != d_conjugate:
        raise AssertionError("KL recharge conjugacy failed")

    if not (3 ** (6 + 11) > 2 ** (8 + 15)):
        raise AssertionError("base outward separator failed")

    # For s=2^(8n-5)u, EC17 induces s' = 316s+138 mod 473.
    # Its unique fixed point is -291427, so chi=s+291427 multiplies by 316.
    if 3**6 % 473 != (1 << 8) % 473:
        raise AssertionError("473 resonance changed")
    color_slope = 3**11 * pow(2, -15, 473) % 473
    color_intercept = 17 * pow(2, -20, 473) % 473
    color_fixed = -291_427 % 473
    if (color_slope, color_intercept, color_fixed) != (316, 138, 414):
        raise AssertionError("packet-color constants changed")
    if (color_slope * color_fixed + color_intercept) % 473 != color_fixed:
        raise AssertionError("packet color zero is not invariant")
    if gcd(color_slope - 1, 473) != 1:
        raise AssertionError("packet color fixed point is not unique")
    return {
        "two_rail_identity": "3^11*Z(q)+17=2^20*W(q)",
        "center_coordinate": "Z=473*R+4, R=1044929+2^20*q",
        "recharge_map": "D(R)=(3^11*R+1221)/2^15",
        "ether_map": "E(R)=(729*R+4)/256",
        "transition": "R'=E^m(D(R))",
        "kl_boundary": "C=2^18*R+2215",
        "kl_ether_conjugate": "C |-> (729*C+881)/256",
        "kl_recharge_conjugate": "C |-> (3^11*C+278339)/2^15",
        "outward_separator": "3^(6m+11)>2^(8m+15) for m>=1",
        "packet_color": "chi=2^(8n-5)u+291427 (mod 473); chi'=316*chi",
        "packet_color_zero_is_unique_fixed_color": True,
    }


def promotion_gate_theorems() -> dict[str, object]:
    """Exact algebra reducing full packet promotion to one odd checksum.

    For a positive bare EC17 step

        2^(8m+15) u' = 3^(6n+11) u + 17,

    subtraction of the determinant identity forces

        3^11 (3^(6n)u-Z0) = 2^20 (2^(8m-5)u'-W0).

    Thus the dyadic factor in the affine Z rail is automatic.  Packet color
    zero is exactly the remaining factor 473, and the narrow inequality
    ``0 < Z0 < 473*2^20`` turns divisibility into positive rail height.
    """

    if not 0 < Z0 < Z_STRIDE:
        raise AssertionError("promotion height window changed")
    if Z0 % 3 == 0:
        raise AssertionError("zero affine height became a positive branch")
    if (Z0 + 32 * 291_427) % 473:
        raise AssertionError("packet color is not the 473 rail checksum")
    if 3**11 * Z0 + 17 != (1 << 20) * W0:
        raise AssertionError("promotion determinant identity failed")
    return {
        "automatic_dyadic_rail": (
            "every positive bare EC17 step n->m satisfies "
            "2^20 | 3^(6n)u-Z0"
        ),
        "subtraction_identity": (
            "3^11*(3^(6n)u-Z0)="
            "2^20*(2^(8m-5)u'-W0)"
        ),
        "color_equivalence": (
            "473 | 3^(6n)u-Z0 iff "
            "2^(8n-5)u+291427=0 (mod 473)"
        ),
        "height_gate": "0<Z0<473*2^20 and 3 does not divide Z0",
        "promotion_reduction": (
            "a positive bare EC17 ray plus packet color zero at one state "
            "lies on the full nonnegative Z rail at every state and promotes "
            "to the self-writing packet map"
        ),
        "remaining_bare_core_gate": (
            "eventual zero canonical bare-core carry plus one color-zero seed"
        ),
        "preferred_public_payload_gate": (
            "for 2^(8m+15)q'=3^(6m+11)q+delta_m, eventual-zero "
            "canonical public carry constructs a shifted self-writing tail"
        ),
    }


def bare_promotion_regression(maximum_branch: int) -> dict[str, object]:
    """Construct one color-zero positive bare step for every bounded n,m."""

    if maximum_branch < 1:
        raise ValueError("branch bound must be positive")
    digest = hashlib.sha256()
    checks = 0
    for source in range(1, maximum_branch + 1):
        for target in range(1, maximum_branch + 1):
            odd_exponent = 6 * source + 11
            binary_exponent = 8 * target + 15
            binary_modulus = 1 << binary_exponent
            core_base = (
                -17 * pow(3**odd_exponent, -1, binary_modulus)
            ) % binary_modulus

            # Choose the affine lift simultaneously in the core unit class
            # u=1 mod3 and in packet color zero mod473.
            lift_mod_three = (
                (1 - core_base) * pow(binary_modulus, -1, 3)
            ) % 3
            color_core = (
                -291_427 * pow(1 << (8 * source - 5), -1, 473)
            ) % 473
            lift_mod_473 = (
                (color_core - core_base)
                * pow(binary_modulus, -1, 473)
            ) % 473
            lift = lift_mod_three + 3 * (
                (lift_mod_473 - lift_mod_three) * pow(3, -1, 473) % 473
            )
            core = core_base + binary_modulus * lift
            numerator = 3**odd_exponent * core + 17
            if numerator % binary_modulus:
                raise AssertionError("constructed bare step is not integral")
            core_next = numerator // binary_modulus
            if (
                core <= 0
                or core_next <= 0
                or core % 3 != 1
                or core_next % 3 != 1
            ):
                raise AssertionError(
                    "constructed bare step left the positive unit class"
                )

            excess = 3 ** (6 * source) * core - Z0
            if excess <= 0 or excess % Z_STRIDE:
                raise AssertionError("color-zero bare step did not promote")
            q = excess // Z_STRIDE
            if Z0 + Z_STRIDE * q != 3 ** (6 * source) * core:
                raise AssertionError("promoted source missed the Z rail")
            if W0 + W_STRIDE * q != (1 << (8 * target - 5)) * core_next:
                raise AssertionError("promoted target missed the W rail")
            digest.update(
                f"{source},{target},{core},{core_next},{q}\n".encode()
            )
            checks += 1
    return {
        "branch_bounds": [1, maximum_branch],
        "color_zero_positive_bare_steps_promoted": checks,
        "row_sha256": digest.hexdigest(),
    }


def linked_regression(maximum_branch: int, lifts: int) -> dict[str, object]:
    digest = hashlib.sha256()
    checks = 0
    for source in range(1, maximum_branch + 1):
        previous = glider_macro(source)
        for target in range(1, maximum_branch + 1):
            current = glider_macro(target)
            previous_tail, current_tail = link_macros(previous, current)
            family = target_family(target)
            source_base = int(family["source_q_base"])
            source_stride = int(family["source_q_stride"])
            target_base = int(family["target_q_base"])
            target_stride = int(family["target_q_stride"])
            for lift in range(lifts):
                tail = previous_tail + (
                    1 << current.input_packet_stride_exponent
                ) * lift
                next_tail = current_tail + previous.output_packet_stride * lift
                packet, output_packet = previous.member(tail)
                next_packet, _ = current.member(next_tail)
                if output_packet != next_packet:
                    raise AssertionError("compiled macro link failed")
                q = packet_q(source, packet)
                q_next = packet_q(target, next_packet)
                current_branch, next_branch, reconstructed = accepted_step(q)
                if (current_branch, next_branch, reconstructed) != (
                    source,
                    target,
                    q_next,
                ):
                    raise AssertionError("self-writing recurrence missed a packet link")
                if (q - source_base) % source_stride:
                    raise AssertionError("linked source missed target dyadic cylinder")
                family_tail = (q - source_base) // source_stride
                if q_next != target_base + target_stride * family_tail:
                    raise AssertionError("target family affine replay failed")
                digest.update(
                    f"{source},{target},{lift},{q},{q_next}\n".encode()
                )
                checks += 1
    return {
        "bounds": {
            "source_branch": [1, maximum_branch],
            "target_branch": [1, maximum_branch],
            "affine_lifts_per_pair": lifts,
        },
        "checks": checks,
        "row_sha256": digest.hexdigest(),
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_certificate(maximum_branch: int, lifts: int) -> dict[str, object]:
    if maximum_branch < 1 or lifts < 1:
        raise ValueError("audit bounds must be positive")
    families = [target_family(m) for m in range(1, maximum_branch + 1)]
    regression = linked_regression(maximum_branch, lifts)
    return {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "scope": (
            "universal exact affine identities, complete fixed-target CRT "
            "families through the displayed branch bound, and bounded literal "
            "packet-link replay; no infinite accepted q orbit and no Collatz "
            "counterexample"
        ),
        "constants": {
            "Z(q)": f"{Z0}+{Z_STRIDE}*q",
            "W(q)": f"{W0}+{W_STRIDE}*q",
            "return_modulus": str(Z_STRIDE),
        },
        "theorems": verify_affine_theorems(),
        "promotion_gate": promotion_gate_theorems(),
        "bare_promotion_regression": bare_promotion_regression(maximum_branch),
        "decoder": (
            "n=v3(Z)/6; m=(v2(W)+5)/8; h=W/2^(8m-5); "
            "q'=(729^m*h-Z0)/(473*2^20)"
        ),
        "ordinary_gate": (
            "one initial packet unit condition, then exact branch valuations "
            "and the fixed q' return cylinder"
        ),
        "finite_link_theorem": (
            "for fixed target m, CRT gives q=a_m+2^(8m+15)t and "
            "q'=b_m+3^(6m+11)t; the source ternary rail is a further "
            "coprime class, so every finite n->m link exists"
        ),
        "target_families": families,
        "literal_link_regression": regression,
        "strict_payload_growth": True,
        "counterexample": None,
    }


def render(value: dict[str, object]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def selftest() -> None:
    verify_affine_theorems()
    promotion_gate_theorems()
    bare_promotion_regression(2)
    first = target_family(1)
    if int(first["source_q_stride"]) != 1 << 23:
        raise AssertionError("first target-family source stride changed")
    linked_regression(2, 2)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-branch", type=int, default=32)
    build.add_argument("--lifts", type=int, default=4)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        selftest()
        print("breakoff ether self-writing KL selftest: PASS")
    elif args.command == "build":
        certificate = build_certificate(args.maximum_branch, args.lifts)
        args.output.write_text(render(certificate))
        print(f"wrote {args.output}")
    else:
        expected = json.loads(args.artifact.read_text())
        if expected.get("schema") != SCHEMA:
            raise ValueError("unexpected artifact schema")
        bounds = expected["literal_link_regression"]["bounds"]
        actual = build_certificate(
            int(bounds["source_branch"][1]),
            int(bounds["affine_lifts_per_pair"]),
        )
        if actual != expected:
            raise AssertionError("artifact differs from exact recomputation")
        print("breakoff ether self-writing KL artifact: PASS")


if __name__ == "__main__":
    main()

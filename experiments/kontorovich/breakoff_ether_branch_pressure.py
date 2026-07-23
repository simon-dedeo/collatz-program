#!/usr/bin/env python3
"""Exact branch-code pressure and the invariant EC1 unit slice.

The self-writing returning-glider map has one source cylinder for every target
branch ``m >= 1``.  Put

    P_m = 8*m + 15,       Q_m = 6*m + 11.

On the complete target cylinder the map is

    q = a_m + 2^P_m*t  ->  q' = b_m + 3^Q_m*t,

or, equivalently,

    2^P_m*q' = 3^Q_m*q + delta_m.

The target cylinders are disjoint (they have different exact valuations of
``W(q)``).  Consequently prescribed target schedules form an LSB-first
variable-length code with lengths ``23,31,39,...``.  Its exact Kraft mass is

    sum_m 2^(-P_m) = 1/(255*2^15),

and the number of schedule cylinders of cost ``S`` has generating function

    (1-x^8)/(1-x^8-x^23).

This is the pressure/Bowen object suggested by the Krasikov--Lagarias
thermodynamic formalism.  It measures the full 2-adic schedule set; it does
not turn a 2-adic schedule into an ordinary natural seed.

There is also an invariant arithmetic slice that removes the collision
particle.  Both affine offsets are divisible by 17.  Thus ``q=17*r`` gives

    Zbar(r) = 29073613 + 495976448*r,
    Wbar(r) =  4911712 +  83790531*r,
    3^11*Zbar(r) + 1 = 2^20*Wbar(r).

Every accepted step starting with ``17 | q`` again has ``17 | q'``.  In core
coordinates this is the irreducible unit law

    2^(8*m+15)*v' = 3^(6*n+11)*v + 1,    v = 2 (mod 3).

Higher powers of 17 expose a precise branch checksum.  A standard LTE/order
calculation reduces preservation of ``17^s | q`` to one target residue modulo
``8*17^(s-2)``.  The executable audit constructs the unique Hensel lifts and
checks the equivalence at finite precision.  None of these statements supplies
an infinite accepted orbit or a Collatz counterexample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from functools import cache
from pathlib import Path
from typing import Any, Sequence

from breakoff_ether_self_writing_kl import (
    W0,
    W_STRIDE,
    Z0,
    Z_STRIDE,
    target_family,
)


SCHEMA = "collatz-breakoff-ether-branch-pressure-v1"
COLLISION = 17
RESONANCE = 473
MINIMUM_CODE_BITS = 23
CODE_PERIOD_BITS = 8
UNIT_Z0 = Z0 // COLLISION
UNIT_W0 = W0 // COLLISION


def vprime(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("zero has no finite valuation")
    value = abs(value)
    result = 0
    while value % prime == 0:
        value //= prime
        result += 1
    return result


def branch_bits(target: int) -> int:
    if target < 1:
        raise ValueError("target branch must be positive")
    return 8 * target + 15


def branch_trits(target: int) -> int:
    if target < 1:
        raise ValueError("target branch must be positive")
    return 6 * target + 11


def branch_delta(target: int) -> int:
    """The positive additive constant in the q-coordinate branch map."""

    binary = 8 * target - 5
    numerator = 3 ** (6 * target) * W0 - 2**binary * Z0
    if numerator % RESONANCE:
        raise AssertionError("branch delta lost its factor 473")
    result = numerator // RESONANCE
    if result <= 0:
        raise AssertionError("branch delta is not positive")
    return result


@cache
def branch_row(target: int) -> dict[str, int]:
    family = target_family(target)
    source = int(family["source_q_base"])
    output = int(family["target_q_base"])
    bits = branch_bits(target)
    trits = branch_trits(target)
    delta = branch_delta(target)
    if not 0 <= source < 1 << bits:
        raise AssertionError("source representative is not canonical")
    if (1 << bits) * output != 3**trits * source + delta:
        raise AssertionError("affine branch identity failed")
    return {
        "target": target,
        "bits": bits,
        "trits": trits,
        "source": source,
        "output": output,
        "delta": delta,
    }


@dataclass(frozen=True)
class Prefix:
    schedule: tuple[int, ...]
    initial_residue: int
    source_bits: int
    endpoint: int
    ternary_exponent: int
    address_digits: tuple[int, ...]

    @staticmethod
    def root() -> "Prefix":
        return Prefix((), 0, 0, 0, 0, ())

    def extend(self, target: int) -> "Prefix":
        row = branch_row(target)
        bits = row["bits"]
        modulus = 1 << bits
        multiplier_mod = pow(3, self.ternary_exponent, modulus)
        digit = (
            (row["source"] - self.endpoint)
            * pow(multiplier_mod, -1, modulus)
        ) % modulus
        adjusted_endpoint = self.endpoint + 3**self.ternary_exponent * digit
        difference = adjusted_endpoint - row["source"]
        if difference < 0 or difference % modulus:
            raise AssertionError("prefix address did not enter its branch cylinder")
        tail = difference // modulus
        following = row["output"] + 3 ** row["trits"] * tail
        result = Prefix(
            schedule=self.schedule + (target,),
            initial_residue=(
                self.initial_residue + (1 << self.source_bits) * digit
            ),
            source_bits=self.source_bits + bits,
            endpoint=following,
            ternary_exponent=self.ternary_exponent + row["trits"],
            address_digits=self.address_digits + (digit,),
        )
        result.replay()
        return result

    def replay(self) -> None:
        value = self.initial_residue
        for target in self.schedule:
            row = branch_row(target)
            difference = value - row["source"]
            modulus = 1 << row["bits"]
            if difference < 0 or difference % modulus:
                raise AssertionError("canonical prefix missed a target cylinder")
            value = row["output"] + 3 ** row["trits"] * (
                difference // modulus
            )
        if value != self.endpoint:
            raise AssertionError("prefix closed form disagrees with replay")
        if not 0 <= self.initial_residue < 1 << self.source_bits:
            raise AssertionError("prefix residue left its canonical range")


def schedule_counts(bit_budget: int) -> list[int]:
    """Count ordered target schedules by their exact total source-bit cost."""

    if bit_budget < 0:
        raise ValueError("bit budget must be nonnegative")
    counts = [0] * (bit_budget + 1)
    counts[0] = 1
    for cost in range(1, bit_budget + 1):
        counts[cost] = sum(
            counts[cost - part]
            for part in range(MINIMUM_CODE_BITS, cost + 1, CODE_PERIOD_BITS)
        )

    # (1-x^8-x^23) A(x) = 1-x^8.
    for cost, count in enumerate(counts):
        expected = (1 if cost == 0 else 0) - (1 if cost == 8 else 0)
        if cost >= 8:
            expected += counts[cost - 8]
        if cost >= 23:
            expected += counts[cost - 23]
        if count != expected:
            raise AssertionError("schedule generating-function recurrence failed")
    return counts


def exhaustive_prefix_regression(bit_budget: int) -> dict[str, Any]:
    """Construct every code cylinder through a modest exact bit budget."""

    counts = schedule_counts(bit_budget)
    stack = [Prefix.root()]
    seen: dict[tuple[int, int], tuple[int, ...]] = {(0, 0): ()}
    by_cost = [0] * (bit_budget + 1)
    by_cost[0] = 1
    maximum_depth = 0
    maximum_height_slack = 0
    packet_valid_canonical_sources = 0
    while stack:
        prefix = stack.pop()
        maximum_depth = max(maximum_depth, len(prefix.schedule))
        if prefix.schedule:
            maximum_height_slack = max(
                maximum_height_slack,
                prefix.source_bits - prefix.initial_residue.bit_length(),
            )
            z = Z0 + Z_STRIDE * prefix.initial_residue
            ternary = vprime(z, 3)
            if ternary >= 6 and ternary % 6 == 0:
                core = z // 3**ternary
                if core % 3 == 1:
                    packet_valid_canonical_sources += 1
        for target in range(1, (bit_budget - prefix.source_bits - 15) // 8 + 1):
            child = prefix.extend(target)
            key = (child.source_bits, child.initial_residue)
            if key in seen:
                raise AssertionError(
                    "distinct target schedules produced the same code cylinder"
                )
            seen[key] = child.schedule
            by_cost[child.source_bits] += 1
            stack.append(child)
    if by_cost != counts:
        raise AssertionError("constructed code tree disagrees with recurrence")
    return {
        "bit_budget": bit_budget,
        "schedule_cylinders_including_root": len(seen),
        "maximum_schedule_depth": maximum_depth,
        "maximum_canonical_height_slack_bits": maximum_height_slack,
        "packet_valid_canonical_sources": packet_valid_canonical_sources,
        "nonzero_exact_cost_counts": {
            str(cost): count for cost, count in enumerate(counts) if count
        },
        "distinct_cylinders_checked": True,
    }


def pressure_certificate() -> dict[str, Any]:
    # Exact rational bounds for the root x in (0,1) of x^8+x^23=1.
    # The Hausdorff/entropy dimension is d=-log_2(x); only the root bracket is
    # part of the executable exact-arithmetic certificate.
    lower = Fraction(952_202_755, 1_000_000_000)
    upper = Fraction(952_202_756, 1_000_000_000)

    def polynomial(value: Fraction) -> Fraction:
        return value**8 + value**23 - 1

    if not polynomial(lower) < 0 < polynomial(upper):
        raise AssertionError("pressure-root rational bracket failed")
    kraft = sum(
        Fraction(1, 1 << branch_bits(target)) for target in range(1, 256)
    )
    tail = Fraction(1, (1 << branch_bits(256)) * 255) * 256
    if kraft + tail != Fraction(1, 255 * (1 << 15)):
        raise AssertionError("infinite Kraft sum failed")
    return {
        "code_lengths": "P_m=8m+15, m>=1",
        "kraft_mass": "1/(255*2^15)",
        "schedule_generating_function": "(1-x^8)/(1-x^8-x^23)",
        "pressure_equation": "x^8+x^23=1; dimension d=-log_2(x)",
        "root_x_exact_rational_bracket": [str(lower), str(upper)],
        "dimension_decimal_diagnostic": "0.07065929109419928758...",
        "dimension_interpretation": (
            "standard countable-prefix-code pressure consequence; the artifact "
            "certifies the code, recurrence, Kraft sum, and root bracket, not a "
            "standalone formal proof of the Hausdorff-dimension theorem"
        ),
    }


def unit_slice_theorems(maximum_branch: int) -> dict[str, Any]:
    if Z0 % COLLISION or W0 % COLLISION:
        raise AssertionError("the affine offsets lost their factor 17")
    if 3**11 * UNIT_Z0 + 1 != (1 << 20) * UNIT_W0:
        raise AssertionError("unit determinant constant identity failed")
    if 3**11 * Z_STRIDE != (1 << 20) * W_STRIDE:
        raise AssertionError("unit determinant slope identity failed")

    rows: list[dict[str, Any]] = []
    residue_transport_checks = 0
    previous_delta = None
    for target in range(1, maximum_branch + 1):
        row = branch_row(target)
        delta = row["delta"]
        if delta % COLLISION:
            raise AssertionError("q=17r is not invariant")
        unit_delta = delta // COLLISION
        if previous_delta is not None:
            earlier = previous_delta
            m = target - 1
            if delta != 256 * earlier + 3 ** (6 * m) * W0:
                raise AssertionError("first delta recurrence failed")
            if delta != 729 * earlier + 2 ** (8 * m - 5) * Z0:
                raise AssertionError("second delta recurrence failed")
        previous_delta = delta

        # Intersect the complete target cylinder with q=0 mod 17 and replay
        # the reduced branch affine identity on two members.
        bits = row["bits"]
        tail0 = -row["source"] * pow(1 << bits, -1, COLLISION) % COLLISION
        q0 = row["source"] + (1 << bits) * tail0
        for lift in range(2):
            q = q0 + (1 << bits) * COLLISION * lift
            if q % COLLISION:
                raise AssertionError("unit-slice source missed q=0 mod 17")
            tail = (q - row["source"]) >> bits
            q_next = row["output"] + 3 ** row["trits"] * tail
            if q_next % COLLISION:
                raise AssertionError("unit-slice target missed q'=0 mod 17")
            r = q // COLLISION
            r_next = q_next // COLLISION
            if (1 << bits) * r_next != 3 ** row["trits"] * r + unit_delta:
                raise AssertionError("reduced unit branch identity failed")

        # Complete mod-17 transport.  In the unit component, source and
        # successor cores have a second factor 17 exactly at source residues
        # r=14 and r=1 respectively.  The displayed affine transport makes
        # those two events mutually exclusive on every accepted step.
        for source_residue in range(COLLISION):
            target_residue = (
                (3 ** row["trits"] * source_residue + unit_delta)
                * pow(1 << bits, -1, COLLISION)
            ) % COLLISION
            expected = (
                14
                + 6
                * pow(-2, target - 1, COLLISION)
                * (source_residue - 1)
            ) % COLLISION
            if target_residue != expected:
                raise AssertionError("unit-slice color transport failed")
            current_core_deep = source_residue == 14
            successor_core_deep = source_residue == 1
            if current_core_deep and successor_core_deep:
                raise AssertionError("adjacent unit cores both gained 17^2")
            if (target_residue == 14) != successor_core_deep:
                raise AssertionError("successor deep-core residue was not exact")
            residue_transport_checks += 1
        rows.append(
            {
                "target": target,
                "P": bits,
                "Q": row["trits"],
                "delta_over_17": str(unit_delta),
                "unit_source_q": str(q0),
            }
        )
    return {
        "reduced_coordinates": {
            "Zbar(r)": f"{UNIT_Z0}+{Z_STRIDE}*r",
            "Wbar(r)": f"{UNIT_W0}+{W_STRIDE}*r",
            "determinant": "3^11*Zbar(r)+1=2^20*Wbar(r)",
        },
        "packet_unit_law": (
            "if Zbar=3^(6n)v and Wbar=2^(8m-5)v', then "
            "2^(8m+15)v'=3^(6n+11)v+1; v,v' are odd and 2 mod 3"
        ),
        "invariant_slice": "17|q implies 17|q' on every accepted branch",
        "mod_17_transport": "r'-14 = 6*(-2)^(m-1)*(r-1) (mod 17)",
        "adjacent_deep_core_theorem": (
            "for every accepted unit-slice step, min(v17(u),v17(u'))=1; "
            "equivalently consecutive normalized cores cannot both be "
            "divisible by 17^2"
        ),
        "deep_core_density_bound": "at most one half along every finite or infinite orbit",
        "residue_transport_checks": residue_transport_checks,
        "branch_rows": rows,
    }


def hensel_branch_clock(precision: int) -> dict[str, Any]:
    """Construct the unique target residue preserving higher 17-adic slices."""

    if precision < 1:
        raise ValueError("17-adic precision must be positive")
    # R=(3^6)/(2^8), C=2^-5*UNIT_Z0/UNIT_W0.  The condition
    # 17^k | delta_m/17 is exactly R^m=C (mod 17^k).
    if vprime(3**48 - 2**64, COLLISION) != 1:
        raise AssertionError("R^8 lost its primitive 17-adic lift")
    if vprime(UNIT_Z0 - 32 * UNIT_W0, COLLISION) != 1:
        raise AssertionError("C lost its primitive 17-adic displacement")

    residue = 0
    period = 8
    rows: list[dict[str, Any]] = []
    for level in range(1, precision + 1):
        modulus = COLLISION**level
        if level > 1:
            candidates = [residue + digit * period for digit in range(COLLISION)]
            good = []
            for candidate in candidates:
                left = pow(3, 6 * candidate, modulus) * UNIT_W0
                right = pow(2, 8 * candidate - 5, modulus) * UNIT_Z0
                if (left - right) % modulus == 0:
                    good.append(candidate)
            if len(good) != 1:
                raise AssertionError("17-adic branch checksum did not lift uniquely")
            residue = good[0]
            period *= COLLISION
        left = pow(3, 6 * residue, modulus) * UNIT_W0
        right = pow(2, 8 * residue - 5, modulus) * UNIT_Z0
        if (left - right) % modulus:
            raise AssertionError("17-adic branch checksum failed")
        rows.append(
            {
                "delta_over_17_precision": level,
                "target_residue": str(residue),
                "target_modulus": str(period),
            }
        )
    return {
        "clock_equation": (
            "(3^6/2^8)^m = 2^-5*(29073613/4911712) in Z_17"
        ),
        "primitive_checks": {
            "v17(3^48-2^64)": 1,
            "v17(29073613-32*4911712)": 1,
        },
        "lifts": rows,
        "preservation_rule": (
            "given 17^s|q on an accepted target-m branch, 17^s|q' iff "
            "17^s|delta_m; for s>=2 this is the unique displayed target "
            "class at precision s-1"
        ),
    }


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def build_audit(
    maximum_branch: int, prefix_bit_budget: int, hensel_precision: int
) -> dict[str, Any]:
    return {
        "branch_affine_law": (
            "2^(8m+15)q'=3^(6m+11)q+delta_m, "
            "delta_m=(3^(6m)W0-2^(8m-5)Z0)/473>0"
        ),
        "pressure": pressure_certificate(),
        "prefix_regression": exhaustive_prefix_regression(prefix_bit_budget),
        "unit_slice": unit_slice_theorems(maximum_branch),
        "higher_17_adic_clock": hensel_branch_clock(hensel_precision),
        "claim_scope": (
            "universal algebraic branch/unit-slice identities, exact finite "
            "prefix-tree regression at the stated bit budget, and exact "
            "17-adic Hensel lifts through the stated precision; no infinite "
            "accepted orbit and no Collatz counterexample"
        ),
        "counterexample": None,
    }


def build_artifact(
    maximum_branch: int, prefix_bit_budget: int, hensel_precision: int
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "bounds": {
            "maximum_branch": maximum_branch,
            "prefix_bit_budget": prefix_bit_budget,
            "hensel_precision": hensel_precision,
        },
        "audit": build_audit(maximum_branch, prefix_bit_budget, hensel_precision),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected artifact schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    bounds = expected["bounds"]
    actual = build_artifact(
        int(bounds["maximum_branch"]),
        int(bounds["prefix_bit_budget"]),
        int(bounds["hensel_precision"]),
    )
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("finite branch-pressure artifact claims a counterexample")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": expected["worker_sha256"],
        "prefix_cylinders": expected["audit"]["prefix_regression"][
            "schedule_cylinders_including_root"
        ],
        "hensel_precision": bounds["hensel_precision"],
        "counterexample": None,
    }


def selftest() -> None:
    branch_row(1)
    unit_slice_theorems(3)
    hensel_branch_clock(4)
    regression = exhaustive_prefix_regression(80)
    if regression["schedule_cylinders_including_root"] != 28:
        raise AssertionError("tiny prefix census changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-branch", type=int, default=64)
    build.add_argument("--prefix-bit-budget", type=int, default=160)
    build.add_argument("--hensel-precision", type=int, default=12)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("breakoff ether branch-pressure selftest: PASS")
        return 0
    if args.command == "build":
        artifact = build_artifact(
            args.maximum_branch, args.prefix_bit_budget, args.hensel_precision
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), sort_keys=True))
        return 0
    print(json.dumps(verify_artifact(args.artifact), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

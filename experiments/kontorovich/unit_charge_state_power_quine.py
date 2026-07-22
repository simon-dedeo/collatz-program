#!/usr/bin/env python3
"""Exact public-state perfect-power closure interface for the charge bouncer.

Write the public state as ``y=s^23``.  If a legal bouncer transition has
recharge count ``h=23*ell`` and odd collision quotient ``q=t^23``, its output is

    y' = A^(23*ell)*q = (A^ell*t)^23.

Thus the public data type reproduces automatically.  The remaining transition
equation is

    C^m*(s^23+1) = D^m*(1+(B^ell*t)^23).          (SPQ)

Exact input valuation is ``v2(s+1)=23m`` by odd-exponent LTE.  When ``m=23k``,
SPQ is an equal-sums-of-two-23rd-powers equation.  A short size argument rules
out that residue class: the input valuation makes ``s`` exponentially too
large for the difference between the two adjacent power packets.

There is also a proposed global, ineffective obstruction.  In every nonzero coefficient
class SPQ gives a rational approximation to ``alpha=3^(e/23)`` with error
strictly below ``alpha/s^23``.  Since a reduced denominator is at most
``X=U*s<s^2``, this is eventually better than denominator exponent 11.  Once
the universal elementary bridge is kernel-checked, Roth's theorem would permit
only finitely many such transitions in each class; the output root is strictly
larger than the input root, so the pure public type could not run forever.
The proposed implication uses Roth externally.  This worker
checks the exact algebraic bridge, the concrete inequalities, and literal
bouncer semantics for any supplied candidate; Lean receives the universal
elementary bridge separately.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

from breakoff_delay_gate import v2
from unit_charge_bouncer import A, B, C, D, F, bouncer_step, constants
from unit_charge_power_quine import exact_factorization_of_F


SCHEMA = "collatz-unit-charge-state-power-quine-v1"


def vp(value: int, prime: int) -> int:
    if value == 0:
        raise ValueError("valuation of zero is not used")
    exponent = 0
    value = abs(value)
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def state_power_equation(m: int, ell: int, s: int, t: int) -> bool:
    if min(m, ell, s, t) < 1:
        raise ValueError("state-power parameters must be positive")
    return pow(C, m) * (pow(s, 23) + 1) == pow(D, m) * (
        1 + pow(pow(B, ell) * t, 23)
    )


def literal_candidate_check(
    m: int, ell: int, s: int, t: int
) -> dict[str, object]:
    """Replay a proposed SPQ transition through the public bouncer map."""
    y = pow(s, 23)
    equation = state_power_equation(m, ell, s, t)
    record: dict[str, object] = {
        "m": m,
        "ell": ell,
        "recharge_h": 23 * ell,
        "s": s,
        "t": t,
        "state_power_equation_holds": equation,
        "input_v2_s_plus_one": v2(s + 1),
        "input_public_state": y,
    }
    if not equation:
        record["literal_bouncer_replay_attempted"] = False
        return record

    expected_input_valuation = 23 * m
    if v2(s + 1) != expected_input_valuation:
        record["literal_bouncer_replay_attempted"] = False
        record["rejection"] = "input valuation is not exactly 23m"
        return record
    if t % 2 == 0:
        record["literal_bouncer_replay_attempted"] = False
        record["rejection"] = "collision quotient root is even"
        return record

    expected_output = pow(pow(A, ell) * t, 23)
    values = constants()
    if y % values["M"] or (y + 1) % F:
        record["literal_bouncer_replay_attempted"] = False
        record["rejection"] = "input public state missed the fixed register"
        return record
    if expected_output % values["M"] or (expected_output + 1) % F:
        record["literal_bouncer_replay_attempted"] = False
        record["rejection"] = "output public state missed the fixed register"
        return record
    output_valuation = v2(expected_output + 1)
    if output_valuation < 23 or output_valuation % 23:
        record["literal_bouncer_replay_attempted"] = False
        record["rejection"] = "output public state has no next defect opcode"
        return record

    step = bouncer_step(y)
    if step.input_defect_cells != m + 1:
        raise AssertionError("SPQ replay read the wrong input defect")
    if step.background_cells != 23 * ell - 1:
        raise AssertionError("SPQ replay did not read h=23*ell")
    if step.output_y != expected_output:
        raise AssertionError("SPQ replay did not reproduce the public power")
    record.update(
        {
            "literal_bouncer_replay_attempted": True,
            "literal_bouncer_replay_passed": True,
            "output_public_state": step.output_y,
            "output_root": pow(A, ell) * t,
            "output_is_23rd_power": True,
        }
    )
    return record


def build_record() -> dict[str, object]:
    values = constants()
    factors = exact_factorization_of_F()
    if A != pow(3, 114) or B != pow(2, 154):
        raise AssertionError("recharge constants changed")
    if C != pow(3, 17) or D != pow(2, 23):
        raise AssertionError("defect constants changed")

    # Every prime factor p of F has gcd(23,p-1)=1.  Hence x -> x^23 is a
    # bijection modulo F, and the register equation s^23=-1 forces s=-1 mod F.
    root_rows: list[dict[str, int]] = []
    for prime in factors:
        exponent_gcd = gcd(23, prime - 1)
        if exponent_gcd != 1:
            raise AssertionError("F acquired a nonunique 23rd-power root")
        if pow(prime - 1, 23, prime) != prime - 1:
            raise AssertionError("-1 stopped being its own 23rd root")
        root_rows.append(
            {
                "prime": prime,
                "prime_mod_23": prime % 23,
                "gcd_23_prime_minus_one": exponent_gcd,
            }
        )

    output_root_rows: list[dict[str, int]] = []
    for ell in (1, 2, 23, 146):
        output_root_residue = (-pow(pow(A, ell), -1, F)) % F
        if pow(pow(A, ell) * output_root_residue, 23, F) != F - 1:
            raise AssertionError("output root register residue failed")
        output_root_rows.append(
            {"ell": ell, "forced_t_mod_F": output_root_residue}
        )

    # Exact coefficient checks behind the elementary m=23k contradiction.
    if not C > D > 1:
        raise AssertionError("taxicab packet ordering changed")
    if not pow(3, 17) < pow(2, 34):
        raise AssertionError("ternary upper bound failed")
    if not 528 * 22 > 34:
        raise AssertionError("valuation-growth separator failed")
    if not pow(2, 529) - 1 > pow(2, 528):
        raise AssertionError("input valuation lower bound failed at k=1")

    # The exact one-step bridge to Roth.  For m=23*k+r one may absorb every
    # complete 23rd power into U and leave e=17*m (mod 23):
    #
    #   Y^23 - 3^e X^23 = C^m-D^m,
    #   X=U*s, Y=2^m*B^ell*t, U=3^floor(17m/23).
    #
    # If alpha^23=3^e, factorization gives
    # 0 < Y/X-alpha < alpha/s^23.  The rows below check all integer identities
    # and the coarse U<s bound; the real-algebraic inequality is requested in
    # Lean and Roth remains an explicitly external theorem.
    approximation_rows: list[dict[str, int | bool]] = []
    for m in range(1, 24):
        a, e = divmod(17 * m, 23)
        u = pow(3, a)
        approximation_rows.append(
            {
                "m": m,
                "a": a,
                "e": e,
                "coefficient_reconstruction": pow(3, e) * pow(u, 23)
                == pow(C, m),
                "binary_reconstruction_ell_1": pow(pow(2, m) * B, 23)
                == pow(D, m) * pow(B, 23),
                "U_lt_minimum_positive_s": u < pow(D, m) - 1,
                "nonzero_class": e != 0,
            }
        )
    if not all(
        row["coefficient_reconstruction"]
        and row["binary_reconstruction_ell_1"]
        and row["U_lt_minimum_positive_s"]
        for row in approximation_rows
    ):
        raise AssertionError("Roth normalization audit failed")
    if sum(not row["nonzero_class"] for row in approximation_rows) != 1:
        raise AssertionError("expected exactly one rational coefficient class")

    # Algebraic normalization is checked at several exact k, including a
    # nontrivial large exponent.  It is an identity in k; Lean receives the
    # universal statement separately.
    normalization_rows: list[dict[str, int | bool]] = []
    for k in (1, 2, 23, 146):
        m = 23 * k
        u = pow(3, 17 * k)
        z = pow(2, 23 * k)
        normalization_rows.append(
            {
                "k": k,
                "m": m,
                "C^m_equals_U^23": pow(C, m) == pow(u, 23),
                "D^m_equals_Z^23": pow(D, m) == pow(z, 23),
                "input_divisibility_exponent": 23 * m,
                "input_divisibility_exponent_equals_529k": 23 * m == 529 * k,
            }
        )
    if not all(
        row["C^m_equals_U^23"]
        and row["D^m_equals_Z^23"]
        and row["input_divisibility_exponent_equals_529k"]
        for row in normalization_rows
    ):
        raise AssertionError("m=23k taxicab normalization failed")

    sanity = literal_candidate_check(1, 1, 1, 1)
    if sanity["state_power_equation_holds"]:
        raise AssertionError("negative SPQ sanity tuple unexpectedly closed")

    return {
        "schema": SCHEMA,
        "verifier_sha256": source_sha256(),
        "claim_scope": (
            "exact public-state 23rd-power reproduction reduction for every "
            "h=23*ell; Lean proves the m-divisible-by-23 one-step no-go; the "
            "a proposed all-class no-infinite-run conclusion would use "
            "Roth's theorem externally after an elementary approximation "
            "bridge which is still awaiting Lean"
        ),
        "constants": {
            "A": A,
            "B": B,
            "C": C,
            "D": D,
            "F": F,
            "M": values["M"],
        },
        "public_state_type": "y=s^23",
        "recharge_type": "h=23*ell, ell>=1",
        "collision_quotient_type": "q=t^23",
        "reproduced_output": "y'=A^(23*ell)*t^23=(A^ell*t)^23",
        "necessary_and_semantically_sufficient_equation_with_side_conditions": (
            "C^m*(s^23+1)=D^m*(1+(B^ell*t)^23), "
            "v2(s+1)=23m, t odd, and input/output register conditions"
        ),
        "odd_exponent_lte": [
            "v2(s^23+1)=v2(s+1) for odd s",
            "v3((B*t)^23+1)=v3(B*t+1) when 3 divides B*t+1",
        ],
        "register_23rd_root_audit": root_rows,
        "forced_input_root_mod_F": "s=-1 mod F",
        "forced_output_t_mod_F_samples": output_root_rows,
        "m_multiple_23": {
            "taxicab_equation": (
                "(3^(17k)*s)^23+(3^(17k))^23="
                "(2^(23k+154)*t)^23+(2^(23k))^23"
            ),
            "normalization_rows": normalization_rows,
            "proof_schema": [
                "taxicab equality and C>D force 0<Y^23-X^23<U^23",
                "integrality forces Y^23-X^23>=X^22, hence s^22<U",
                "2^(529k)|(s+1) forces s>2^(528k)",
                "U=3^(17k)<2^(34k), but s^22>2^(11616k)>2^(34k)",
            ],
            "status": "elementary universal no-go kernel-checked in Lean commit 4c56925",
        },
        "nonzero_coefficient_classes": {
            "normalization_rows": approximation_rows,
            "exact_approximation": (
                "for alpha=3^(e/23), 0<Y/X-alpha<alpha/s^23"
            ),
            "denominator_bound": (
                "for reduced p/q=Y/X, q<=X=U*s<s^2, hence eventually "
                "0<p/q-alpha<q^-11"
            ),
            "growth": "B^ell*t>s and A^ell*t>B^ell*t, so the next root exceeds s",
            "status": (
                "if the elementary bridge is kernel-checked, Roth would imply "
                "finitely many transitions per class and no infinite "
                "pure-state run; external theorem, bridge sent to Lean"
            ),
        },
        "negative_sanity_tuple": sanity,
        "checks": {
            "public_output_type_reproduces_algebraically": True,
            "register_root_mod_F_is_unique": True,
            "taxicab_normalization_exact": True,
            "valuation_growth_separator_exact": True,
            "all_class_no_infinite_run_claim_depends_on_external_Roth": True,
        },
    }


def source_sha256() -> str:
    sources = [
        Path(__file__),
        Path(__file__).with_name("unit_charge_bouncer.py"),
        Path(__file__).with_name("unit_charge_power_quine.py"),
    ]
    return hashlib.sha256(b"".join(path.read_bytes() for path in sources)).hexdigest()


def canonical_json(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def verify_certificate(path: Path) -> None:
    stored = json.loads(path.read_text())
    expected = json.loads(canonical_json(build_record()))
    if stored != expected:
        raise AssertionError("state-power quine artifact does not reconstruct")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    args = parser.parse_args()

    if args.command == "selftest":
        build_record()
        print("unit charge state-power quine selftest: PASS")
    elif args.command == "build":
        args.output.write_text(canonical_json(build_record()))
        print(f"wrote {args.output}")
    elif args.command == "verify":
        verify_certificate(args.artifact)
        print("unit charge state-power quine artifact: PASS")
    else:
        raise AssertionError("unreachable command")


if __name__ == "__main__":
    main()

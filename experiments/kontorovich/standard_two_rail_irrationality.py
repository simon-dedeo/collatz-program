#!/usr/bin/env python3
"""Exact hypothesis audit for the Väänänen--Wallisser obstruction.

This checker does not reprove their 1989 linear-independence theorem.  It
checks, without floating point, the parameter substitution and the two strict
inequalities needed to apply that published theorem to the standard two-rail
partial-theta candidate.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


SCHEMA = "collatz-standard-two-rail-irrationality-audit-v1"


def choose2(value: int) -> int:
    if value < 0:
        raise ValueError("value must be nonnegative")
    return value * (value - 1) // 2


def f_term(q: Fraction, alpha: Fraction, n: int) -> Fraction:
    """Term of VW's f_q(alpha)=sum q^(-n(n+1)/2) alpha^n."""
    return q ** (-(n * (n + 1) // 2)) * alpha**n


def partial_theta_term(q_inverse: Fraction, z: Fraction, n: int) -> Fraction:
    return q_inverse ** choose2(n) * z**n


def exact_audit() -> dict[str, object]:
    q = Fraction(3, 2)
    q_inverse = Fraction(2, 3)
    z = Fraction(2**13, 3**9)
    alpha = q * z
    if alpha != Fraction(2**12, 3**8):
        raise AssertionError("partial-theta argument reduction failed")

    coefficient_checks = 64
    for n in range(coefficient_checks):
        if f_term(q, alpha, n) != partial_theta_term(q_inverse, z, n):
            raise AssertionError("VW function and partial theta disagree")

    # VW's size parameter is
    # gamma = 1 - log(2)/log(3), while for l=1,sigma=0 their threshold is
    # Gamma = (3-sqrt(5))/2.  The exact rational separator 3/8 proves
    # gamma < 3/8 < Gamma:
    #   log(2)/log(3) > 5/8  from 2^8 > 3^5;
    #   sqrt(5) < 9/4        from 5*4^2 < 9^2.
    log_ratio_power_left = 2**8
    log_ratio_power_right = 3**5
    sqrt_bound_left = 5 * 4**2
    sqrt_bound_right = 9**2
    if not log_ratio_power_left > log_ratio_power_right:
        raise AssertionError("log-ratio separator failed")
    if not sqrt_bound_left < sqrt_bound_right:
        raise AssertionError("square-root separator failed")

    return {
        "schema": SCHEMA,
        "claim_scope": (
            "exact parameter and strict-inequality audit for a published "
            "linear-independence theorem; the external theorem itself is "
            "cited, not reproved"
        ),
        "source": {
            "authors": "K. Vaananen and R. Wallisser",
            "title": (
                "Zu einem Satz von Skolem ueber lineare Unabhaengigkeit "
                "von Werten gewisser Thetareihen"
            ),
            "journal": "Manuscripta Mathematica 65 (1989), 199-212",
            "digitized_full_text": (
                "https://gdz.sub.uni-goettingen.de/download/pdf/"
                "PPN365956996_0065/LOG_0016.pdf"
            ),
            "theorem_parameters": {"ell": 1, "sigma": 0, "p": 2},
        },
        "function_mapping": {
            "vw_function": "f_q(x)=sum_(n>=0) q^(-n(n+1)/2) x^n",
            "vw_q": "3/2",
            "partial_theta": (
                "F(2/3,z)=sum_(n>=0) (2/3)^(n(n-1)/2) z^n"
            ),
            "z": "8192/19683",
            "alpha_equals_q_times_z": "4096/6561",
            "identity": "F(2/3,8192/19683)=f_(3/2)(4096/6561)",
            "coefficients_checked_exactly": coefficient_checks,
        },
        "elementary_hypotheses": {
            "q_reduced": True,
            "q_numerator_absolute_greater_than_one": True,
            "alpha_nonzero_rational": True,
            "distinct_alpha_ratio_conditions": "vacuous_for_ell_1",
            "two_adic_convergence": "abs_2(3/2)=2>1",
        },
        "strict_size_condition": {
            "gamma": "1-log(2)/log(3)",
            "Gamma": "(3-sqrt(5))/2",
            "rational_separator": "3/8",
            "gamma_less_than_separator_from": "2^8=256 > 243=3^5",
            "separator_less_than_Gamma_from": "5*4^2=80 < 81=9^2",
            "integer_checks": {
                "2^8": log_ratio_power_left,
                "3^5": log_ratio_power_right,
                "5*4^2": sqrt_bound_left,
                "9^2": sqrt_bound_right,
            },
        },
        "conclusion_using_published_theorem": (
            "F(2/3,8192/19683) is irrational in Q_2; hence the standard "
            "two-rail candidate cannot be a positive rational integer"
        ),
    }


def verify_artifact(data: dict[str, object]) -> None:
    if data.get("schema") != SCHEMA:
        raise ValueError("unsupported artifact schema")
    if data != exact_audit():
        raise ValueError("irrationality audit failed exact reconstruction")


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
        exact_audit()
        print("standard_two_rail_irrationality selftest: PASS")
    elif args.command == "build":
        args.output.write_text(json.dumps(exact_audit(), indent=2) + "\n")
        print(f"wrote {args.output}")
    else:
        verify_artifact(json.loads(args.artifact.read_text()))
        print("standard_two_rail_irrationality artifact: PASS")


if __name__ == "__main__":
    main()

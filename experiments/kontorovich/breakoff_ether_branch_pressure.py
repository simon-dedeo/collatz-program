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

The blocks recorded by ``Prefix.address_digits`` are also the canonical carry
digits of the exact public-payload reset program.  Lean commit ``d4a8edf``
proves the sharp ordinary gate: eventual-zero public carry constructs a
shifted self-writing orbit, while every supplied orbit has eventual-zero
public carry.  Thus these are the primary construction digits, not merely a
coding diagnostic.

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
checks the equivalence at finite precision.

At exact 17-adic depth one, the mod-17 transport has a finite safe graph.  It
is strongly connected and, more usefully, contains eight constant-residue
rails: for each target class ``m=j (mod 8)`` there is a shallow residue fixed
by every such branch.  Restricting the branch alphabet to one rail changes the
pressure equation to

    x^64 + x^(8*j+15) = 1.

The audit certifies the graph, all eight rails, their Kraft masses, and exact
rational brackets for these pressure roots.  None of these statements supplies
an infinite accepted orbit or a Collatz counterexample.

The standard nonlinear rail schedule ``m_n=j+8*v17(n+1)`` has an exact
digit-sum Mahler function.  Version 5 audits the hypotheses of Wang's 2006
p-adic value theorem, which excludes all eight such schedules after the
natural-boundary argument recorded in the artifact.  The theorem is cited,
not reproved; the artifact itself remains an exact hypothesis checker and
records no counterexample.

Version 6 isolates the next place-value ruler
``m_n=j+8*17^v17(n+1)`` as a genuinely bivariate Mahler system.  It checks
the exact block/digit laws, the defective-Jordan iterates, and the rank-two
rational specializations.  This identifies a multivariate 2-adic value
theorem as a precise open seam; it does not assert such a theorem.

Version 7 adds the exact valuation formula and an executable eventual
monomial-separation algorithm along every one of the eight specialized
Jordan orbits.  This is the finite-polynomial zero-estimate input suggested
by a KL-style auxiliary argument.  It proves no special-value theorem by
itself.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
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


SCHEMA = "collatz-breakoff-ether-branch-pressure-v7"
COLLISION = 17
RESONANCE = 473
MINIMUM_CODE_BITS = 23
CODE_PERIOD_BITS = 8
UNIT_Z0 = Z0 // COLLISION
UNIT_W0 = W0 // COLLISION
PUBLIC_A = Fraction(W0, W_STRIDE)
PUBLIC_B = Fraction(Z0, Z_STRIDE)
PUBLIC_EPSILON = PUBLIC_A - PUBLIC_B


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


def branch_ratio(target: int) -> Fraction:
    """Real-contracting and 2-adically contracting inverse branch ratio."""

    return Fraction(1 << branch_bits(target), 3 ** branch_trits(target))


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
    public_theta_identities = 0
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
            verify_public_theta_prefix(child)
            public_theta_identities += 1
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
        "public_theta_prefix_identities": public_theta_identities,
        "nonzero_exact_cost_counts": {
            str(cost): count for cost, count in enumerate(counts) if count
        },
        "distinct_cylinders_checked": True,
    }


def verify_public_theta_prefix(prefix: Prefix) -> None:
    """Check the exact finite telescoping form of the public address."""

    if not prefix.schedule:
        return
    ratio = Fraction(1)
    inner_sum = Fraction(0)
    last_index = len(prefix.schedule) - 1
    for index, target in enumerate(prefix.schedule):
        ratio *= branch_ratio(target)
        if index < last_index:
            inner_sum += ratio
    left = prefix.initial_residue + PUBLIC_A + PUBLIC_EPSILON * inner_sum
    right = ratio * (prefix.endpoint + PUBLIC_B)
    if left != right:
        raise AssertionError("public theta prefix identity failed")


def public_theta_certificate() -> dict[str, Any]:
    """The one-series KL/Tschakaloff form of an arbitrary branch schedule."""

    expected_epsilon = Fraction(
        17, RESONANCE * (1 << 20) * 3**11
    )
    if PUBLIC_EPSILON != expected_epsilon:
        raise AssertionError("public theta determinant gap changed")
    if not all(0 < branch_ratio(target) < 1 for target in range(1, 65)):
        raise AssertionError("public inverse branch stopped contracting over R")
    return {
        "inverse_branch_ratio": (
            "alpha_m=2^(8m+15)/3^(6m+11)="
            "(2^15/3^11)*(2^8/3^6)^m"
        ),
        "determinant_gap": (
            "A=W0/(473*3^11), B=Z0/(473*2^20), "
            "epsilon=A-B=17/(473*2^20*3^11)"
        ),
        "finite_telescoping_identity": (
            "q0+A+epsilon*sum_(1<=j<N)R_j=R_N*(q_N+B), "
            "R_j=product_(i<j)alpha_(m_i)"
        ),
        "infinite_two_adic_address": (
            "q0=-A-epsilon*Theta, Theta=sum_(j>=1)R_j"
        ),
        "ordinary_seed_target": (
            "Theta=-2^20*W(q0)/17 for an ordinary public payload q0"
        ),
        "unit_slice_target": (
            "if q0=17r, then Theta=-2^20*Wbar(r), a negative ordinary "
            "integer; the eight shallow rails add the certified branch-clock "
            "residue constraints to this integer target"
        ),
        "tail_functional_equation": (
            "Theta_t=alpha_(m_t)*(1+Theta_(t+1)); "
            "v2(Theta_t)=8m_t+15"
        ),
        "interpretation": (
            "the counterexample problem is a variable-exponent one-series "
            "2-adic theta rationality problem; fixed-rate schedules are the "
            "already-closed partial-theta special case, while nonlinear "
            "payload-written exponent positions remain open"
        ),
    }


def public_theta_pressure_certificate() -> dict[str, Any]:
    """Exact two-place height gate for a negative integral theta value.

    This records the finite arithmetic behind the universal implication.  If
    ``Theta=-K`` with ``K>0``, write the first ``N`` terms as
    ``A_N/3^D_N``.  The first omitted term has exact dyadic valuation
    ``V_(N+1)``, while the real partial sum lies in ``(0,1)``.  Therefore

        2^V_(N+1) <= K*3^D_N+A_N < (K+1)*3^D_N.

    The checker does not assume that an integral theta value exists.
    """

    if not 2 * (1 << 23) < 3**17:
        raise AssertionError("alpha_1 stopped being less than one half")
    if not 3**41 < 1 << 65:
        raise AssertionError("dyadic/ternary separator changed")
    if not 3**6 % RESONANCE == 2**8 % RESONANCE:
        raise AssertionError("mod-473 ether resonance changed")
    if not (32 * UNIT_W0 - UNIT_Z0) % RESONANCE == 0:
        raise AssertionError("reduced lattice resonance changed")

    # Audit the exponent elimination independently over a nontrivial exact
    # box.  The identity itself is polynomial, so these checks are regression
    # witnesses rather than the proof of its universal quantifiers.
    identities_checked = 0
    for count in range(1, 65):
        for cumulative in range(count, count + 65):
            for fresh in (1, count, cumulative, cumulative + 17):
                d_n = 11 * count + 6 * cumulative
                v_next = 15 * (count + 1) + 8 * (cumulative + fresh)
                excess = 41 * v_next - 65 * d_n
                expected = 328 * fresh - 62 * cumulative - 100 * count + 615
                if excess != expected:
                    raise AssertionError("fresh-branch pressure identity failed")
                identities_checked += 1

    # If m_N >= M_N and M_N >= N, the ratio in the height gate is bounded
    # below by 2^15*(2^31/3^17)^N.  Its base is already strictly greater than
    # one, so such indices cannot occur cofinally for one fixed K.
    if not 2**31 > 3**17:
        raise AssertionError("superincreasing lower-bound base stopped growing")

    return {
        "negative_integer_height_gate": (
            "if Theta=-K with K>0, M_N=sum_(i<N)m_i, "
            "D_N=11N+6M_N, and V_N=15N+8M_N, then "
            "2^V_(N+1) <= K*3^D_N+A_N < (K+1)*3^D_N"
        ),
        "exact_tail_valuation": (
            "v2(Theta-sum_(1<=j<=N)R_j)=V_(N+1)"
        ),
        "real_partial_sum_gate": (
            "0<sum_(1<=j<=N)R_j<1 because alpha_m<=alpha_1<1/2"
        ),
        "separator": "3^41<2^65",
        "fresh_branch_excess": (
            "41V_(N+1)-65D_N=328m_N-62M_N-100N+615"
        ),
        "exclusion": (
            "an unbounded positive fresh-branch excess cannot hit a fixed "
            "negative integer; in particular schedules with m_N>=M_N "
            "at arbitrarily late indices are excluded"
        ),
        "superincreasing_lower_bound": (
            "2^V_(N+1)/3^D_N >= 2^15*(2^31/3^17)^N when "
            "m_N>=M_N>=N"
        ),
        "unit_lattice_sufficiency_constants": {
            "3^6_mod_473": pow(3, 6, RESONANCE),
            "2^8_mod_473": pow(2, 8, RESONANCE),
            "32Wbar0_minus_Zbar0_div_473": (
                32 * UNIT_W0 - UNIT_Z0
            ) // RESONANCE,
            "interpretation": (
                "a negative theta hit -2^20*Wbar(r) recursively produces "
                "integer suffixes and the reduced affine lattice; this is "
                "the converse construction target, not an existence claim"
            ),
        },
        "exponent_identity_regressions": identities_checked,
        "scope": (
            "slow valuation/place-value ruler schedules can satisfy this "
            "height gate; the standard valuation ruler is separately closed "
            "by the Wang application below, while more general adaptive "
            "schedules require other input"
        ),
    }


def valuation_factorial(n: int, prime: int) -> int:
    """Legendre valuation of ``n!`` in exact integer arithmetic."""

    if n < 0:
        raise ValueError("factorial index must be nonnegative")
    result = 0
    quotient = n
    while quotient:
        quotient //= prime
        result += quotient
    return result


def digit_sum(n: int, base: int) -> int:
    """Sum the base-``base`` digits of a nonnegative integer."""

    if n < 0 or base < 2:
        raise ValueError("invalid digit-sum query")
    result = 0
    while n:
        result += n % base
        n //= base
    return result


def ruler_mahler_certificate() -> dict[str, Any]:
    """Certify the exact 17-ruler/Mahler reduction coefficient by coefficient."""

    prime = COLLISION
    coefficient_checks = 0
    digit_sum_checks = 0
    for n in range(prime**3):
        base = valuation_factorial(n, prime)
        if 16 * base != n - digit_sum(n, prime):
            raise AssertionError("17-ruler Legendre digit-sum identity failed")
        digit_sum_checks += 1
        for remainder in range(prime):
            if valuation_factorial(prime * n + remainder, prime) != n + base:
                raise AssertionError("17-ruler Legendre block identity failed")
            coefficient_checks += 1

    a = Fraction(1 << 15, 3**11)
    b = Fraction(1 << 8, 3**6)
    c = b**8
    kappa = Fraction(16, 27)
    if kappa**16 != c:
        raise AssertionError("Mahler rescaling constant changed")
    if not 17 < 17**2:
        raise AssertionError("Wang degree condition changed")

    rail_points: list[dict[str, Any]] = []
    for rail in range(1, 9):
        z = a * b**rail
        x = kappa * z
        expected_x = Fraction(1 << (19 + 8 * rail), 3 ** (14 + 6 * rail))
        if x != expected_x:
            raise AssertionError("17-ruler Mahler point identity failed")
        if vprime(x.numerator, 2) != 19 + 8 * rail:
            raise AssertionError("17-ruler point lost its 2-adic size")
        rail_points.append(
            {
                "rail_representative": rail,
                "z": str(z),
                "rescaled_x": str(x),
            }
        )

    # The amplified ruler is a theorem-driven negative control for the height
    # gate.  At N=17^k-1 the closed Legendre sum makes its fresh branch larger
    # than all preceding branches combined.
    amplified_checks = 0
    for depth in range(1, 9):
        boundary = prime**depth
        closed_sum = prime ** (depth - 1) * (boundary - 1)
        if depth <= 4:
            exact_sum = sum(
                prime ** (2 * vprime(t, prime)) for t in range(1, boundary)
            )
            if exact_sum != closed_sum:
                raise AssertionError("amplified-ruler valuation sum changed")
        else:
            exact_sum = closed_sum
        index = boundary - 1
        for rail in range(1, 9):
            cumulative = rail * index + 8 * exact_sum
            fresh = rail + 8 * prime ** (2 * depth)
            if fresh <= cumulative:
                raise AssertionError("amplified ruler stopped being superincreasing")
            amplified_checks += 1

    return {
        "schedule": "m_n=j+8*v17(n+1), 1<=j<=8",
        "series_parameters": {
            "a": str(a),
            "b": str(b),
            "c": str(c),
            "kappa": str(kappa),
        },
        "legendre_block_identity": (
            "v17((17n+r)!)=n+v17(n!) for 0<=r<17"
        ),
        "mahler_function": (
            "F_c(z)=sum_(n>=0)c^v17(n!)*z^n; "
            "F_c(z)=(1+z+...+z^16)*F_c(c*z^17)"
        ),
        "theta_specialization": "1+Theta=F_c(a*b^j)",
        "standard_rescaling": (
            "G(x)=F_c(x/kappa), G(x)=P_17(x/kappa)*G(x^17)"
        ),
        "digit_sum_form": (
            "G(x)=sum_(n>=0)kappa^(-s_17(n))*x^n="
            "product_(k>=0)P_17(x^(17^k)/kappa)"
        ),
        "target": "G(x_j)=1-2^20*Wbar(r)",
        "rail_points": rail_points,
        "coefficient_identity_regressions": coefficient_checks,
        "digit_sum_identity_regressions": digit_sum_checks,
        "wang_theorem_application": {
            "source": (
                "T. Q. Wang, p-adic Transcendence and p-adic "
                "Transcendence Measures for the Values of Mahler Type "
                "Functions, Acta Math. Sinica 22 (2006), Theorem 1"
            ),
            "parameters": {
                "p": 2,
                "rho": 17,
                "functional_degree_N": 1,
                "Q0(z,u)": "P_17(z/kappa)",
                "Q1(z,u)": "-u",
                "elimination_polynomial_g(z)": "P_17(z/kappa)",
                "m0": 1,
                "M0": 17,
            },
            "numerical_condition": "M0*N^2=17<17^2=rho^2",
            "argument_condition": (
                "x_j is nonzero and |x_j|_2=2^(-(19+8j))<1"
            ),
            "nonvanishing": (
                "P_17(x_j^(17^k)/kappa)>0 in the real embedding for all k"
            ),
            "function_transcendence": (
                "the product zeros x^(17^k)=kappa*zeta, "
                "zeta^17=1 and zeta!=1, accumulate densely at the complex "
                "unit circle, giving a natural boundary; rational-coefficient "
                "scalar descent transfers transcendence to C_2(z)"
            ),
            "published_theorem_conclusion": (
                "G(x_j) is transcendental in Q_2 for every 1<=j<=8, so it "
                "cannot equal the ordinary integer 1-2^20*Wbar(r)"
            ),
        },
        "amplified_negative_control": {
            "schedule": "m_n=j+8*17^(2*v17(n+1))",
            "closed_sum": (
                "sum_(1<=t<17^k)17^(2v17(t))=17^(k-1)*(17^k-1)"
            ),
            "superincreasing_cases_checked": amplified_checks,
            "consequence": "excluded by the public theta height gate",
        },
        "scope": (
            "the functional equation, digit-sum form, specializations, and "
            "elementary Wang hypotheses are checked exactly; the universal "
            "special-value conclusion invokes the cited published theorem "
            "and the displayed natural-boundary/scalar-descent argument"
        ),
    }


def place_value_mahler_certificate() -> dict[str, Any]:
    """Exact bivariate system for the surviving place-value 17-ruler."""

    prime = COLLISION
    bound = prime**4
    prefix = [0] * (bound + 1)
    digit_formula_checks = 0
    for n in range(1, bound + 1):
        prefix[n] = prefix[n - 1] + prime ** vprime(n, prime)

    for n in range(bound):
        digits = []
        value = n
        while value:
            digits.append(value % prime)
            value //= prime
        candidate = digits[0] if digits else 0
        candidate += sum(
            digit * prime ** (index - 1) * (prime + 16 * index)
            for index, digit in enumerate(digits[1:], start=1)
        )
        if prefix[n] != candidate:
            raise AssertionError("place-value ruler digit formula failed")
        digit_formula_checks += 1

    block_checks = 0
    for n in range(prime**3):
        for remainder in range(prime):
            if prefix[prime * n + remainder] != (
                prime * prefix[n] + 16 * n + remainder
            ):
                raise AssertionError("place-value ruler block law failed")
            block_checks += 1

    iterate_checks = 0
    iterates: list[dict[str, Any]] = []
    c_exponent = 1
    z_c_exponent = 0
    z_exponent = 1
    for depth in range(65):
        expected_c = prime**depth
        expected_z_c = 0 if depth == 0 else 16 * depth * prime ** (depth - 1)
        expected_z = prime**depth
        if (c_exponent, z_c_exponent, z_exponent) != (
            expected_c,
            expected_z_c,
            expected_z,
        ):
            raise AssertionError("bivariate Mahler iterate formula failed")
        if depth < 8:
            iterates.append(
                {
                    "depth": depth,
                    "C_coordinate_C_exponent": str(c_exponent),
                    "Z_coordinate_C_exponent": str(z_c_exponent),
                    "Z_coordinate_Z_exponent": str(z_exponent),
                }
            )
        c_exponent *= prime
        z_c_exponent = 16 * expected_c + prime * z_c_exponent
        z_exponent *= prime
        iterate_checks += 1

    rank_checks = []
    for rail in range(1, 9):
        c_vector = (64, -48)
        z_vector = (15 + 8 * rail, -(11 + 6 * rail))
        determinant = (
            c_vector[0] * z_vector[1] - c_vector[1] * z_vector[0]
        )
        if determinant != 16:
            raise AssertionError("place-value rational parameters lost rank two")
        rank_checks.append(
            {
                "rail_representative": rail,
                "prime_exponent_determinant": determinant,
            }
        )

    boundary_checks = []
    for depth in range(1, 9):
        boundary = prime**depth
        closed = 16 * depth * prime ** (depth - 1)
        if depth <= 4 and prefix[boundary - 1] != closed:
            raise AssertionError("place-value boundary sum failed")
        for rail in range(1, 9):
            cumulative = rail * (boundary - 1) + 8 * closed
            fresh = rail + 8 * boundary
            if fresh >= cumulative:
                raise AssertionError("place-value spike unexpectedly superincreasing")
        boundary_checks.append(
            {
                "depth": depth,
                "A_(17^k-1)": str(closed),
                "all_eight_fresh_spikes_below_history": True,
            }
        )

    return {
        "schedule": "m_n=j+8*17^v17(n+1), 1<=j<=8",
        "prefix_weight": "A_n=sum_(1<=t<=n)17^v17(t)",
        "block_law": "A_(17n+r)=17*A_n+16*n+r for 0<=r<17",
        "digit_formula": (
            "if n=sum_i d_i*17^i, then "
            "A_n=d_0+sum_(i>=1)d_i*17^(i-1)*(17+16i)"
        ),
        "theta_value": (
            "1+Theta=H(c,z_j), H(C,Z)=sum_(n>=0)C^A_n*Z^n"
        ),
        "functional_equation": (
            "H(C,Z)=P_17(CZ)*H(C^17,C^16*Z^17)"
        ),
        "mahler_map": "T(C,Z)=(C^17,C^16*Z^17)",
        "iterate_formula": (
            "T^k(C,Z)=(C^(17^k),C^(16k17^(k-1))*Z^(17^k))"
        ),
        "product": (
            "H(C,Z)=product_(k>=0)P_17("
            "C^(17^k+16k17^(k-1))*Z^(17^k))"
        ),
        "finite_checks": {
            "digit_formula": digit_formula_checks,
            "block_law": block_checks,
            "iterate_formula": iterate_checks,
            "sample_iterates": iterates,
            "boundary_rows": boundary_checks,
        },
        "rank_two_parameters": {
            "c_prime_vector": "(v2,v3)=(64,-48)",
            "z_j_prime_vector": "(15+8j,-11-6j)",
            "determinants": rank_checks,
            "interpretation": (
                "determinant 16 for every rail; the rational parameters "
                "cannot both be powers of one rational base"
            ),
        },
        "theorem_boundary": (
            "the defective Jordan map is genuinely bivariate and does not "
            "reduce to the univariate Wang theorem; the exact height gate is "
            "asymptotically slack because cumulative k*17^k depth dominates "
            "each fresh 17^k spike"
        ),
        "live_target": (
            "a multivariate 2-adic Mahler value theorem for the Jordan map, "
            "or a direct auxiliary-function proof; no rationality or orbit "
            "claim is made"
        ),
    }


def jordan_monomial_separation_certificate() -> dict[str, Any]:
    """Exact 2-adic monomial separation on the place-value Jordan orbit.

    A term is represented by ``(p, q, v)`` for a coefficient of 2-adic
    valuation ``v`` multiplying ``C^p Z^q``.  For a finite support, the
    lexicographically least pair ``(q, p)`` is eventually the unique term of
    least valuation.  The loop below computes a rigorous witness depth using
    only integer arithmetic.
    """

    def term_valuation(
        rail: int, depth: int, p_exponent: int, q_exponent: int, coefficient_v2: int
    ) -> int:
        c_coordinate_v2 = 64 * COLLISION**depth
        z_coordinate_v2 = (
            1024 * depth * COLLISION ** (depth - 1)
            if depth > 0
            else 0
        ) + (15 + 8 * rail) * COLLISION**depth
        return (
            coefficient_v2
            + p_exponent * c_coordinate_v2
            + q_exponent * z_coordinate_v2
        )

    def witness_depth(rail: int, terms: Sequence[tuple[int, int, int]]) -> int:
        if not terms:
            raise ValueError("a polynomial support must be nonempty")
        if len({(p, q) for p, q, _ in terms}) != len(terms):
            raise ValueError("combine equal monomials before separation")
        chosen = min(terms, key=lambda term: (term[1], term[0]))
        depth = 0
        while True:
            chosen_value = term_valuation(rail, depth, *chosen)
            if all(
                chosen_value < term_valuation(rail, depth, *term)
                for term in terms
                if term != chosen
            ):
                # Once the affine bracket in k is positive, its slope is
                # nonnegative for every competitor because chosen has least
                # q and then least p.  The exponentially increasing factor
                # 17^(k-1) then preserves strictness.  Check the next 64
                # depths as an independent regression of that derivation.
                for later in range(depth, depth + 65):
                    chosen_later = term_valuation(rail, later, *chosen)
                    if not all(
                        chosen_later < term_valuation(rail, later, *term)
                        for term in terms
                        if term != chosen
                    ):
                        break
                else:
                    return depth
            depth += 1
            if depth > 10_000:
                raise AssertionError("Jordan monomial separation did not terminate")

    # Bare monomial collisions have a particularly transparent exact law.
    # For k>=1 the valuation difference, after removing coefficient
    # valuations, is
    #
    #   17^(k-1) * (17*(64*dp+(15+8j)*dq) + 1024*k*dq).
    #
    # If dq=0 it never vanishes for distinct monomials; if dq!=0 the affine
    # bracket has at most one integer root.  Exhaust a nontrivial box as a
    # regression against the direct valuation implementation.
    pair_checks = 0
    for rail in range(1, 9):
        monomials = [(p, q) for p in range(9) for q in range(9)]
        for left_index, (p_left, q_left) in enumerate(monomials):
            for p_right, q_right in monomials[left_index + 1 :]:
                direct_collisions = []
                formula_collisions = []
                for depth in range(1, 65):
                    direct_difference = term_valuation(
                        rail, depth, p_right, q_right, 0
                    ) - term_valuation(rail, depth, p_left, q_left, 0)
                    dp = p_right - p_left
                    dq = q_right - q_left
                    formula_difference = COLLISION ** (depth - 1) * (
                        COLLISION * (64 * dp + (15 + 8 * rail) * dq)
                        + 1024 * depth * dq
                    )
                    if direct_difference != formula_difference:
                        raise AssertionError("Jordan valuation-difference formula failed")
                    if direct_difference == 0:
                        direct_collisions.append(depth)
                    if formula_difference == 0:
                        formula_collisions.append(depth)
                if direct_collisions != formula_collisions or len(direct_collisions) > 1:
                    raise AssertionError("Jordan monomials collided more than once")
                pair_checks += 1

    adversarial_support = (
        (0, 0, 100_000),
        (1, 0, -100_000),
        (0, 1, -1_000_000),
        (8, 1, 50_000),
        (0, 2, -10_000_000),
    )
    witness_rows = []
    for rail in range(1, 9):
        depth = witness_depth(rail, adversarial_support)
        chosen = min(adversarial_support, key=lambda term: (term[1], term[0]))
        chosen_value = term_valuation(rail, depth, *chosen)
        margin = min(
            term_valuation(rail, depth, *term) - chosen_value
            for term in adversarial_support
            if term != chosen
        )
        if margin <= 0:
            raise AssertionError("Jordan separation witness has no strict margin")
        witness_rows.append(
            {
                "rail": rail,
                "witness_depth": depth,
                "least_support_pair_(q,p)": [chosen[1], chosen[0]],
                "strict_v2_margin": str(margin),
            }
        )

    return {
        "orbit": (
            "T^k(c,z_j)=(c^(17^k),c^(16k17^(k-1))*z_j^(17^k))"
        ),
        "term_valuation": (
            "v2(a*C_k^p*Z_k^q)=v2(a)+64p*17^k+"
            "q*((15+8j)*17^k+1024k*17^(k-1))"
        ),
        "pair_difference_for_k_ge_1": (
            "17^(k-1)*(17*(64*dp+(15+8j)*dq)+1024*k*dq), "
            "before the coefficient-valuation difference"
        ),
        "eventual_separator": (
            "for every nonzero finite rational polynomial, the support term "
            "with lexicographically least (q,p) is eventually the unique "
            "term of least 2-adic valuation; hence evaluation along the "
            "Jordan orbit is eventually nonzero"
        ),
        "finite_regression": {
            "bare_pairs_checked": pair_checks,
            "depths_per_pair": 64,
            "adversarial_support": [list(term) for term in adversarial_support],
            "all_eight_witnesses": witness_rows,
        },
        "scope": (
            "exact finite-polynomial orbit separation only; functional "
            "transcendence plus this zero estimate still require a new "
            "multivariate 2-adic auxiliary-value theorem before any ruler "
            "or orbit conclusion"
        ),
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


def unit_residue_transition(source: int, target_class: int) -> int:
    """Transport r modulo 17 for a target branch m=target_class (mod 8)."""

    if not 0 <= source < COLLISION:
        raise ValueError("source residue must be modulo 17")
    if not 1 <= target_class <= 8:
        raise ValueError("target class must use representatives 1,...,8")
    return (
        14
        + 6
        * pow(-2, target_class - 1, COLLISION)
        * (source - 1)
    ) % COLLISION


def unit_transition_mod(source: int, target: int, precision: int) -> int:
    """Exact reduced affine transition modulo ``17^precision``."""

    if precision < 1:
        raise ValueError("17-adic precision must be positive")
    row = branch_row(target)
    unit_delta = row["delta"] // COLLISION
    modulus = COLLISION**precision
    return (
        (3 ** row["trits"] * source + unit_delta)
        * pow(1 << row["bits"], -1, modulus)
    ) % modulus


def pressure_root_bracket(first_length: int, period: int = 64) -> tuple[Fraction, Fraction]:
    """Exact dyadic bracket for x^period+x^first_length=1 in (0,1)."""

    lower = Fraction(0)
    upper = Fraction(1)
    for _ in range(96):
        middle = (lower + upper) / 2
        value = middle**period + middle**first_length - 1
        if value < 0:
            lower = middle
        elif value > 0:
            upper = middle
        else:
            return middle, middle
    if not lower**period + lower**first_length < 1:
        raise AssertionError("restricted pressure lower bracket failed")
    if not upper**period + upper**first_length > 1:
        raise AssertionError("restricted pressure upper bracket failed")
    return lower, upper


def unit_residue_rails() -> dict[str, Any]:
    """Certify the shallow mod-17 graph and its eight invariant rails."""

    # r=14 means that the current normalized core has a second factor 17;
    # r=1 maps to r'=14 on every branch.  Remove both to obtain the graph in
    # which consecutive cores stay at exact 17-adic depth one.
    safe_states = tuple(residue for residue in range(COLLISION) if residue not in (1, 14))
    safe_set = set(safe_states)
    adjacency: dict[int, list[tuple[int, int]]] = {}
    reverse: dict[int, set[int]] = {residue: set() for residue in safe_states}
    for source in safe_states:
        edges = []
        for target_class in range(1, 9):
            target = unit_residue_transition(source, target_class)
            if target in safe_set:
                edges.append((target_class, target))
                reverse[target].add(source)
        if len(edges) not in (7, 8):
            raise AssertionError("unexpected shallow-graph out-degree")
        adjacency[source] = edges

    def reachable(start: int, neighbors: dict[int, set[int]]) -> set[int]:
        visited: set[int] = set()
        stack = [start]
        while stack:
            state = stack.pop()
            if state in visited:
                continue
            visited.add(state)
            stack.extend(neighbors[state] - visited)
        return visited

    forward = {
        source: {target for _, target in edges}
        for source, edges in adjacency.items()
    }
    anchor = safe_states[0]
    if reachable(anchor, forward) != safe_set or reachable(anchor, reverse) != safe_set:
        raise AssertionError("shallow residue graph is not strongly connected")

    fixed_residues = {1: 12, 2: 2, 3: 13, 4: 3, 5: 15, 6: 6, 7: 9, 8: 0}
    expected_second_digits = {
        1: (6, 10, 13),
        2: (5, 9, 3),
        3: (7, 5, 8),
        4: (3, 4, 0),
        5: (11, 12, 16),
        6: (12, 6, 12),
        7: (10, 8, 10),
        8: (14, 2, 0),
    }
    rails: list[dict[str, Any]] = []
    for target_class, fixed in fixed_residues.items():
        if fixed not in safe_set:
            raise AssertionError("rail is not at exact 17-adic depth one")
        if unit_residue_transition(fixed, target_class) != fixed:
            raise AssertionError("claimed unit-residue rail is not invariant")
        # The transition depends only on m modulo 8, so check several literal
        # positive branches against the complete affine map as well.
        for target in (target_class, target_class + 8, target_class + 16):
            row = branch_row(target)
            unit_delta = row["delta"] // COLLISION
            direct = (
                (3 ** row["trits"] * fixed + unit_delta)
                * pow(1 << row["bits"], -1, COLLISION)
            ) % COLLISION
            if direct != fixed:
                raise AssertionError("literal branch left its residue rail")

        # Lift one digit.  Write r=fixed+17*s and m=target_class+8*j.
        # The next digit is affine, s'=A*s+B*j+C (mod 17), and B is a
        # unit.  Hence the next payload digit can decode/choose the next
        # branch-clock digit; the shallow rail does not become stationary.
        def next_second_digit(source_digit: int, branch_digit: int) -> int:
            source = fixed + COLLISION * source_digit
            target = target_class + 8 * branch_digit
            following = unit_transition_mod(source, target, 2)
            if (following - fixed) % COLLISION:
                raise AssertionError("second-digit lift left the base rail")
            return ((following - fixed) // COLLISION) % COLLISION

        constant = next_second_digit(0, 0)
        source_coefficient = (next_second_digit(1, 0) - constant) % COLLISION
        branch_coefficient = (next_second_digit(0, 1) - constant) % COLLISION
        formula = (source_coefficient, branch_coefficient, constant)
        if formula != expected_second_digits[target_class]:
            raise AssertionError("second-digit rail formula changed")
        if branch_coefficient == 0:
            raise AssertionError("branch digit stopped being decodable")
        for source_digit in range(COLLISION):
            for branch_digit in range(COLLISION):
                expected_digit = (
                    source_coefficient * source_digit
                    + branch_coefficient * branch_digit
                    + constant
                ) % COLLISION
                if next_second_digit(source_digit, branch_digit) != expected_digit:
                    raise AssertionError("second-digit affine law failed")

        first_length = branch_bits(target_class)
        kraft = Fraction(1, 1 << first_length) / (
            1 - Fraction(1, 1 << 64)
        )
        lower, upper = pressure_root_bracket(first_length)
        root_midpoint = float((lower + upper) / 2)
        rails.append(
            {
                "target_class_mod_8": target_class % 8,
                "positive_representative": target_class,
                "fixed_r_mod_17": fixed,
                "second_digit_transport": (
                    f"s'={source_coefficient}*s+{branch_coefficient}*j+"
                    f"{constant} (mod 17), for r={fixed}+17s and "
                    f"m={target_class}+8j"
                ),
                "branch_digit_coefficient_is_unit": True,
                "branch_lengths": f"{first_length}+64k, k>=0",
                "kraft_mass": str(kraft),
                "schedule_generating_function": (
                    f"(1-x^64)/(1-x^64-x^{first_length})"
                ),
                "pressure_equation": f"x^64+x^{first_length}=1",
                "root_x_exact_dyadic_bracket": [str(lower), str(upper)],
                "dimension_decimal_diagnostic": format(
                    -math.log2(root_midpoint), ".18g"
                ),
            }
        )

    return {
        "safe_states_r_mod_17": list(safe_states),
        "excluded_residues": {
            "14": "current core is divisible by 17^2",
            "1": "successor core is divisible by 17^2",
        },
        "safe_graph_strongly_connected": True,
        "safe_graph_out_degrees": {
            str(source): len(edges) for source, edges in adjacency.items()
        },
        "labeled_safe_adjacency": {
            str(source): [
                {"target_class_representative": label, "target_r": target}
                for label, target in edges
            ]
            for source, edges in adjacency.items()
        },
        "invariant_rails": rails,
        "higher_digit_clock": {
            "coordinate_law": (
                "for x=Zbar(r), x'=(729/256)^m*(3^11*x+1)/2^15 "
                "in Z_17"
            ),
            "primitive_lte_input": "v17(3^48-2^64)=1",
            "branch_decoder": (
                "at precision k, consecutive shallow r residues determine "
                "m modulo 8*17^(k-1); changing m by 8d changes the output "
                "at exact valuation 1+v17(d)"
            ),
            "consequence": (
                "a stationary all-depth 17-adic rail forces stationary "
                "branch data and is incompatible with a positive fixed-branch "
                "orbit; evolving higher 17-adic digits remain a live counter "
                "channel"
            ),
        },
        "interpretation": (
            "each rail permits arbitrary positive target branches in one "
            "class modulo 8 while every normalized core has exactly one "
            "factor 17; this is an arithmetic selector, not an existence "
            "proof for an ordinary infinite orbit"
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
        "ordinary_address_gate": {
            "canonical_digits": (
                "Prefix.address_digits are the successive carry digits of "
                "the public reset program with instruction (P_m,Q_m,delta_m)"
            ),
            "eventual_zero_meaning": (
                "kernel-checked in companion commit d4a8edf: sufficient for "
                "a shifted self-writing tail and necessary for every "
                "supplied self-writing orbit"
            ),
        },
        "pressure": pressure_certificate(),
        "public_theta": public_theta_certificate(),
        "public_theta_pressure": public_theta_pressure_certificate(),
        "ruler_mahler": ruler_mahler_certificate(),
        "place_value_mahler": place_value_mahler_certificate(),
        "jordan_monomial_separation": jordan_monomial_separation_certificate(),
        "prefix_regression": exhaustive_prefix_regression(prefix_bit_budget),
        "unit_slice": unit_slice_theorems(maximum_branch),
        "unit_residue_rails": unit_residue_rails(),
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
    rails = unit_residue_rails()
    if len(rails["invariant_rails"]) != 8:
        raise AssertionError("unit-residue rail census changed")
    hensel_branch_clock(4)
    jordan_monomial_separation_certificate()
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

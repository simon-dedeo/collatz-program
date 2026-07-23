#!/usr/bin/env python3
"""Exact first-passage code for the minimal outward shortcut system.

For a shortcut parity word ``w``, let ``S`` be its length and ``O`` its
number of odd source states.  Its affine slope is ``3^O/2^S``.  The minimal
outward code consists of all words for which

    3^O > 2^S

for the first time at the final letter.  It is prefix-free.  Concatenating
its words gives strict multiplicative growth without invoking the YAH/tag
compiler.  An ordinary positive integer admitting infinitely many such
blocks would therefore be a Collatz counterexample.

The second audit follows every positive source through a stated bound to the
terminal 1--2 cycle.  Increasing-source exhaustion then computes the exact
minimum ordinary address ``h_n`` for every block depth reached and a strict
lower bound for the next one.  This directly measures the atomic construction
gate; it is not an unstructured search for long stopping times.

This worker counts the first-passage code by ``(S,O)`` rather than enumerating
its exponentially many words.  Under fair binary parity measure it certifies
the two exact stopped-mass identities

    P_N + A_N = 1,
    Q_N + R_N = 1,

where ``P`` is ordinary Kraft mass, ``A`` is uncrossed mass, ``Q`` is tilted
mass ``sum 3^O/4^S`` of words crossing by depth ``N``, and ``R`` is the
remaining tilted mass.  The second equality is the stopped martingale
identity: an even extension has weight factor ``1/4`` and an odd extension
has factor ``3/4``.

The infinite tilted mass is therefore critical, not supercritical.  Standard
negative-drift/optional-stopping reasoning gives ``R_N -> 0`` and total
tilted mass one; the artifact checks the exact finite identities and records
the residual at a stated bound.  It does not infer an ordinary survivor.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-outward-first-passage-v3"


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def decimal_ratio(numerator: int, denominator: int, digits: int = 18) -> str:
    integer, remainder = divmod(numerator, denominator)
    places = []
    for _ in range(digits):
        remainder *= 10
        digit, remainder = divmod(remainder, denominator)
        places.append(str(digit))
    return f"{integer}." + "".join(places)


def accelerated_odd_step(value: int) -> int:
    if value <= 0 or value % 2 == 0:
        raise ValueError("accelerated odd step requires a positive odd input")
    value = 3 * value + 1
    while value % 2 == 0:
        value //= 2
    return value


def v2(value: int) -> int:
    """Exact 2-adic valuation of a positive integer."""

    if value <= 0:
        raise ValueError("v2 requires a positive integer")
    return (value & -value).bit_length() - 1


def v3(value: int) -> int:
    """Exact 3-adic valuation of a positive integer."""

    if value <= 0:
        raise ValueError("v3 requires a positive integer")
    exponent = 0
    while value % 3 == 0:
        value //= 3
        exponent += 1
    return exponent


def word_affine_constant(word: str) -> int:
    """Return A_w in 2^S T^S(x)=3^O x+A_w for a parity word."""

    constant = 0
    length = 0
    for bit in word:
        if bit == "1":
            constant = 3 * constant + 2**length
        elif bit != "0":
            raise ValueError("parity words must contain only 0 and 1")
        length += 1
    return constant


def source_profile(
    source: int, maximum_shortcut_steps: int, keep_boundaries: bool = False
) -> dict[str, Any]:
    """Count complete first-passage blocks on one ordinary shortcut orbit.

    Reaching 1 or 2 is handled exactly rather than by an arbitrary orbit
    horizon.  At state 1 there can be at most one final crossing: the next
    odd letter multiplies the pending slope by 3/2, after which the 1--2
    cycle has two-letter multiplier 3/4.  At state 2 no future crossing is
    possible because the first new letter is even.
    """

    if source <= 0:
        raise ValueError("source must be positive")
    if maximum_shortcut_steps < 1:
        raise ValueError("shortcut step limit must be positive")

    value = source
    block_length = 0
    block_odds = 0
    block_count = 0
    shortcut_steps = 0
    accelerated_steps = 0
    block_word: list[str] = []
    boundaries: list[dict[str, Any]] = []
    stabilization: dict[str, int] | None = None

    def record_boundary() -> None:
        nonlocal stabilization
        if stabilization is None and source < 2**shortcut_steps:
            stabilization = {
                "block_depth": block_count,
                "shortcut_steps": shortcut_steps,
                "accelerated_steps": accelerated_steps,
                "state": value,
            }
        if keep_boundaries:
            row = {
                "block_depth": block_count,
                "shortcut_steps": shortcut_steps,
                "accelerated_steps": accelerated_steps,
                "state": value,
                "block_length": block_length,
                "block_odd_count": block_odds,
                "word": "".join(block_word),
            }
            boundaries.append(row)

    def result() -> dict[str, Any]:
        stabilization_depth = (
            int(stabilization["block_depth"]) if stabilization is not None else None
        )
        return {
            "source": source,
            "first_passage_blocks": block_count,
            "shortcut_steps_to_terminal_cycle": shortcut_steps,
            "accelerated_steps_to_terminal_cycle": accelerated_steps,
            "terminal_cycle_state": value,
            "address_stabilization": stabilization,
            "post_address_first_passage_extensions": (
                block_count - stabilization_depth
                if stabilization_depth is not None
                else 0
            ),
            "boundaries": boundaries,
        }

    while shortcut_steps < maximum_shortcut_steps:
        if value == 1:
            if 3 ** (block_odds + 1) > 2 ** (block_length + 1):
                block_length += 1
                block_odds += 1
                block_word.append("1")
                shortcut_steps += 1
                accelerated_steps += 1
                value = 2
                block_count += 1
                record_boundary()
            return result()
        if value == 2:
            return result()

        odd = value % 2
        block_word.append(str(odd))
        block_length += 1
        shortcut_steps += 1
        if odd:
            block_odds += 1
            accelerated_steps += 1
            value = (3 * value + 1) // 2
        else:
            value //= 2

        if 3**block_odds > 2**block_length:
            block_count += 1
            record_boundary()
            block_length = 0
            block_odds = 0
            block_word = []

    raise AssertionError(
        f"source {source} did not reach the terminal cycle within "
        f"{maximum_shortcut_steps} shortcut steps"
    )


def minimum_address_regression(
    maximum_seed: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    """Exhaust the exact monotone minimum-address sequence below a seed cap."""

    if maximum_seed < 1:
        raise ValueError("maximum seed must be positive")

    record_rows: list[dict[str, Any]] = []
    post_address_record_rows: list[dict[str, int]] = []
    certified_h: list[dict[str, int]] = []
    survivor_counts = [0]
    record_depth = 0
    post_address_record = -1
    for source in range(1, maximum_seed + 1):
        profile = source_profile(source, maximum_shortcut_steps)
        depth = int(profile["first_passage_blocks"])
        while len(survivor_counts) <= depth:
            survivor_counts.append(0)
        for block_depth in range(1, depth + 1):
            survivor_counts[block_depth] += 1

        extensions = int(profile["post_address_first_passage_extensions"])
        if extensions > post_address_record:
            stabilization = profile["address_stabilization"]
            if stabilization is None:
                raise AssertionError("post-address record has no stabilization row")
            post_address_record_rows.append(
                {
                    "source": source,
                    "post_address_first_passage_extensions": extensions,
                    "first_passage_blocks": depth,
                    "address_stabilization_block_depth": int(
                        stabilization["block_depth"]
                    ),
                    "address_stabilization_shortcut_steps": int(
                        stabilization["shortcut_steps"]
                    ),
                }
            )
            post_address_record = extensions

        if depth > record_depth:
            record_rows.append(
                {
                    "source": source,
                    "first_passage_blocks": depth,
                    "shortcut_steps_to_terminal_cycle": int(
                        profile["shortcut_steps_to_terminal_cycle"]
                    ),
                    "accelerated_steps_to_terminal_cycle": int(
                        profile["accelerated_steps_to_terminal_cycle"]
                    ),
                }
            )
            for block_depth in range(record_depth + 1, depth + 1):
                certified_h.append(
                    {"block_depth": block_depth, "minimum_address": source}
                )
            record_depth = depth

    previous_words: list[str] | None = None
    previous_source: int | None = None
    for row in record_rows:
        profile = source_profile(int(row["source"]), maximum_shortcut_steps, True)
        words = [str(boundary["word"]) for boundary in profile["boundaries"]]
        common = 0
        if previous_words is not None:
            for left, right in zip(previous_words, words):
                if left != right:
                    break
                common += 1
        row["previous_record_source"] = previous_source
        row["common_first_passage_prefix_blocks"] = common
        previous_words = words
        previous_source = int(row["source"])

    champion = source_profile(
        int(record_rows[-1]["source"]), maximum_shortcut_steps, True
    )
    odd_boundaries = [
        row for row in champion["boundaries"] if int(row["state"]) % 2 == 1
    ]
    if not odd_boundaries:
        raise AssertionError("record seed has no odd first-passage boundary")
    visual = odd_boundaries[-1]
    replay = int(champion["source"])
    for _ in range(int(visual["accelerated_steps"])):
        replay = accelerated_odd_step(replay)
    if replay != int(visual["state"]):
        raise AssertionError("accelerated visualizer witness did not replay")

    stabilization = champion["address_stabilization"]
    if stabilization is None:
        raise AssertionError("record seed never reached its canonical address")
    post_address_visual = [
        row
        for row in odd_boundaries
        if int(row["block_depth"]) > int(stabilization["block_depth"])
    ][-1]
    replay = int(stabilization["state"])
    post_address_accelerated_steps = int(
        post_address_visual["accelerated_steps"]
    ) - int(stabilization["accelerated_steps"])
    for _ in range(post_address_accelerated_steps):
        replay = accelerated_odd_step(replay)
    if replay != int(post_address_visual["state"]):
        raise AssertionError("post-address visualizer witness did not replay")

    survivor_rows = [
        {
            "block_depth": depth,
            "survivors": (
                survivor_counts[depth] if depth < len(survivor_counts) else 0
            ),
            "density_decimal_diagnostic": decimal_ratio(
                survivor_counts[depth] if depth < len(survivor_counts) else 0,
                maximum_seed,
                12,
            ),
        }
        for depth in range(1, record_depth + 2)
    ]

    triadic_slice_rows: list[dict[str, int]] = []
    for row in certified_h:
        block_depth = int(row["block_depth"])
        minimum = int(row["minimum_address"])
        if minimum % 2 != 1:
            raise AssertionError("a certified minimum address is not odd")
        minimum_profile = source_profile(
            minimum, maximum_shortcut_steps, True
        )
        first_boundary = minimum_profile["boundaries"][0]
        target = (3 * minimum + 1) // 2
        if str(first_boundary["word"]) != "1" or int(
            first_boundary["state"]
        ) != target:
            raise AssertionError("odd minimum did not begin with forced word 1")
        if target % 3 != 2:
            raise AssertionError("first-block target is not in class 2 mod 3")
        target_profile = source_profile(target, maximum_shortcut_steps)
        if int(target_profile["first_passage_blocks"]) < block_depth - 1:
            raise AssertionError("triadic target lost a required block")
        if 3 * minimum != 2 * target - 1:
            raise AssertionError("triadic slice recurrence failed")
        triadic_slice_rows.append(
            {
                "block_depth": block_depth,
                "minimum_address": minimum,
                "target_depth": block_depth - 1,
                "least_survivor_congruent_2_mod_3": target,
            }
        )

    return {
        "meaning": (
            "h_n is the least positive ordinary seed completing n successive "
            "first-passage blocks; exhaustive increasing-seed replay certifies "
            "every displayed minimum"
        ),
        "maximum_seed": maximum_seed,
        "maximum_shortcut_steps_per_seed": maximum_shortcut_steps,
        "all_scanned_sources_reached_terminal_cycle": True,
        "record_rows": record_rows,
        "certified_h_values": certified_h,
        "survivor_counts_by_depth": survivor_rows,
        "triadic_min_plus_reduction": {
            "identity": (
                "h_(n+1)=(2*m_n-1)/3 where m_n is the least member of "
                "E_n congruent to 2 mod 3"
            ),
            "proof_boundary": (
                "a least source is odd because deleting initial even steps "
                "cannot reduce its first-passage record count; its forced "
                "first word is 1 and bijects odd sources with targets 2 mod 3"
            ),
            "certified_rows": triadic_slice_rows,
        },
        "greatest_certified_block_depth": record_depth,
        "next_minimum_address_strict_lower_bound": {
            "block_depth": record_depth + 1,
            "strictly_greater_than": maximum_seed,
        },
        "visualizer_prefix": {
            "collatz_source": int(champion["source"]),
            "collatz_target": int(visual["state"]),
            "accelerated_steps": int(visual["accelerated_steps"]),
            "first_passage_blocks": int(visual["block_depth"]),
            "shortcut_steps": int(visual["shortcut_steps"]),
            "scope": (
                "exact finite prefix of the record minimum-address seed; "
                "the complete ordinary orbit reaches the 1--2 cycle"
            ),
        },
        "post_address_renewal": {
            "meaning": (
                "after source<2^L, the accumulated parity cylinder has the "
                "displayed source as its canonical residue; later completed "
                "blocks are literal zero-carry renewals rather than preloaded "
                "address bits"
            ),
            "record_rows": post_address_record_rows,
            "champion": {
                "source": int(champion["source"]),
                "address_stabilization": stabilization,
                "post_address_first_passage_extensions": int(
                    champion["post_address_first_passage_extensions"]
                ),
            },
            "visualizer_post_address_prefix": {
                "collatz_source": int(stabilization["state"]),
                "collatz_target": int(post_address_visual["state"]),
                "accelerated_steps": post_address_accelerated_steps,
                "first_passage_extensions": int(
                    post_address_visual["block_depth"]
                )
                - int(stabilization["block_depth"]),
                "scope": (
                    "exact finite prefix beginning only after the canonical "
                    "ordinary address has stabilized; the full orbit dies"
                ),
            },
        },
    }


def charge_recurrence_audit(profile: dict[str, Any]) -> dict[str, Any]:
    """Audit the canonical odd-charge compression of one literal orbit."""

    boundaries = profile["boundaries"]
    if not boundaries:
        raise ValueError("charge audit requires retained first-passage boundaries")
    for row in boundaries:
        if int(row["state"]) % 3 != 2:
            raise AssertionError("completed first-passage boundary is not 2 mod 3")

    transitions: list[dict[str, Any]] = []
    recharges: list[dict[str, Any]] = []
    for index in range(len(boundaries) - 1):
        current = boundaries[index]
        following = boundaries[index + 1]
        charge = (int(current["state"]) + 1) // 3
        next_charge = (int(following["state"]) + 1) // 3
        word = str(following["word"])
        if charge % 2 == 0:
            if word != "1" or 2 * next_charge != 3 * charge:
                raise AssertionError("even charge did not take its forced 1 drain")
            transitions.append(
                {
                    "input_charge": charge,
                    "kind": "forced_1_drain",
                    "word": word,
                    "output_charge": next_charge,
                }
            )
            continue

        length = len(word)
        odds = word.count("1")
        constant = word_affine_constant(word)
        defect_numerator = constant + 2**length - 3**odds
        if defect_numerator <= 0 or defect_numerator % 3:
            raise AssertionError("nontrivial recharge defect is not positive /3")
        defect = defect_numerator // 3
        if word == "1" or not word.startswith("0") or not word.endswith("11"):
            raise AssertionError("odd charge did not take a nontrivial 0...11 word")
        numerator = 3**odds * charge + defect
        if numerator % 2**length:
            raise AssertionError("recharge branch failed its dyadic legality test")
        endpoint_charge = numerator // 2**length
        if endpoint_charge != next_charge or endpoint_charge % 3:
            raise AssertionError("recharge endpoint identity failed")

        drain = v2(endpoint_charge)
        terminal_index = index + 1 + drain
        if terminal_index >= len(boundaries):
            raise AssertionError("literal orbit omitted a forced charge drain")
        for offset in range(drain):
            if str(boundaries[index + 2 + offset]["word"]) != "1":
                raise AssertionError("recharge drain contains a non-1 block")
        odd_output = (
            int(boundaries[terminal_index]["state"]) + 1
        ) // 3
        expected_output = 3**drain * endpoint_charge // 2**drain
        if odd_output != expected_output or odd_output % 2 != 1:
            raise AssertionError("compressed odd-charge output identity failed")
        if odd_output <= charge or v3(odd_output) < drain + 1:
            raise AssertionError("charge growth or ternary recharge bound failed")

        recharge = {
            "input_block_depth": int(current["block_depth"]),
            "input_charge": charge,
            "input_v3": v3(charge),
            "word": word,
            "length": length,
            "odd_count": odds,
            "affine_constant": constant,
            "recharge_defect": defect,
            "pre_drain_charge": endpoint_charge,
            "forced_1_blocks": drain,
            "output_charge": odd_output,
            "output_v3": v3(odd_output),
            "first_passage_blocks_consumed": 1 + drain,
            "shortcut_steps_consumed": length + drain,
        }
        recharges.append(recharge)
        transitions.append({"kind": "nontrivial_recharge", **recharge})

    shallow_rows: list[dict[str, int]] = []
    for row in recharges:
        if row["word"] != "011":
            continue
        charge = int(row["input_charge"])
        odd_output = int(row["output_charge"])
        c = v3(charge)
        c_prime = int(row["forced_1_blocks"]) + 1
        primitive = charge // 3**c
        next_primitive = odd_output // 3**c_prime
        if (
            2 ** (c_prime + 2) * next_primitive
            != 3 ** (c + 1) * primitive + 1
        ):
            raise AssertionError("011 primitive two-counter recurrence failed")
        shallow_rows.append(
            {
                "c": c,
                "u": primitive,
                "next_c": c_prime,
                "next_u": next_primitive,
            }
        )

    final_charge = (int(boundaries[-1]["state"]) + 1) // 3
    return {
        "source": int(profile["source"]),
        "boundary_coordinate": "x=3H-1",
        "all_completed_boundaries_are_2_mod_3": True,
        "transition_rows": transitions,
        "recharge_rows": recharges,
        "shallow_011_rows": shallow_rows,
        "final_odd_charge_with_undefined_next_recharge": final_charge,
        "theorem_boundary": (
            "an infinite ordinary first-passage execution exists iff the "
            "partial compressed recharge map has an infinite orbit on positive "
            "odd H; this artifact checks finite literal instances only"
        ),
        "counterexample": None,
    }


def renewal_calibration(
    audit: dict[str, Any], regression: dict[str, Any]
) -> dict[str, Any]:
    """Exact finite calibration of the defective renewal and address records."""

    bracket = audit["full_ordinary_kraft_bracket"]
    lower = Fraction(str(bracket["lower"]))
    upper = Fraction(str(bracket["upper"]))
    depth = int(regression["greatest_certified_block_depth"])
    minimum_address = int(regression["certified_h_values"][-1]["minimum_address"])
    scaled_lower = minimum_address * lower**depth
    scaled_upper = minimum_address * upper**depth
    expected_lower = int(regression["maximum_seed"]) * lower**depth
    expected_upper = int(regression["maximum_seed"]) * upper**depth
    doob_max_lower = 1 / (2 * upper)
    doob_max_upper = 1 / (2 * lower)

    return {
        "defective_geometric_law": (
            "under fair parity, disjoint prefix cylinders give p(F^n)=P^n "
            "and p(exactly n completed blocks)=(1-P)P^n"
        ),
        "record_depth": depth,
        "record_minimum_address": minimum_address,
        "minimum_address_times_P_to_depth_bracket": {
            "exact_lower_expression": (
                f"{minimum_address}*({bracket['lower']})^{depth}"
            ),
            "exact_upper_expression": (
                f"{minimum_address}*({bracket['upper']})^{depth}"
            ),
            "lower_decimal_diagnostic": decimal_ratio(
                scaled_lower.numerator, scaled_lower.denominator, 12
            ),
            "upper_decimal_diagnostic": decimal_ratio(
                scaled_upper.numerator, scaled_upper.denominator, 12
            ),
        },
        "maximum_seed_times_P_to_depth_bracket": {
            "exact_lower_expression": (
                f"{regression['maximum_seed']}*({bracket['lower']})^{depth}"
            ),
            "exact_upper_expression": (
                f"{regression['maximum_seed']}*({bracket['upper']})^{depth}"
            ),
            "lower_decimal_diagnostic": decimal_ratio(
                expected_lower.numerator, expected_lower.denominator, 12
            ),
            "upper_decimal_diagnostic": decimal_ratio(
                expected_upper.numerator, expected_upper.denominator, 12
            ),
        },
        "classical_survival_conditioning": {
            "block_law": "p_hat(w)=p(w)/P",
            "largest_single_block_probability": "1/(2P)",
            "largest_probability_bracket": {
                "lower": str(doob_max_lower),
                "upper": str(doob_max_upper),
                "lower_decimal_diagnostic": decimal_ratio(
                    doob_max_lower.numerator, doob_max_lower.denominator, 12
                ),
                "upper_decimal_diagnostic": decimal_ratio(
                    doob_max_upper.numerator, doob_max_upper.denominator, 12
                ),
            },
            "diffuseness_bound": (
                "for each fixed B, the conditioned product law obeys "
                "nu{rho_n<=B}<=B*(1/(2P))^n"
            ),
        },
        "scope": (
            "P^n is a fixed-depth asymptotic density law, not a uniform "
            "short-interval estimate when depth grows with the seed bound; "
            "the displayed finite survivor counts are the exact comparison"
        ),
    }


def first_passage_audit(maximum_length: int) -> dict[str, Any]:
    if maximum_length < 1:
        raise ValueError("maximum word length must be positive")

    # alive[O] counts length-(depth-1) words that have never yet had outward
    # slope.  The state is sufficient because the slope test depends only on
    # length and odd count.
    alive = {0: 1}
    crossing_by_length: list[dict[str, Any]] = []
    crossing_rows: list[tuple[int, int, int]] = []

    for depth in range(1, maximum_length + 1):
        following: dict[int, int] = {}
        crossing_count = 0
        crossing_odd_histogram: dict[int, int] = {}
        for odd_count, count in alive.items():
            # Even extension.
            following[odd_count] = following.get(odd_count, 0) + count

            # Odd extension.  This is the only way to cross the outward
            # boundary, because an even extension strictly decreases slope.
            next_odd = odd_count + 1
            if 3**next_odd > 2**depth:
                crossing_count += count
                crossing_odd_histogram[next_odd] = (
                    crossing_odd_histogram.get(next_odd, 0) + count
                )
                crossing_rows.append((depth, next_odd, count))
            else:
                following[next_odd] = following.get(next_odd, 0) + count
        alive = following
        if crossing_count or depth <= 6:
            crossing_by_length.append(
                {
                    "length": depth,
                    "first_passage_words": str(crossing_count),
                    "odd_count_histogram": {
                        str(odd): str(count)
                        for odd, count in sorted(crossing_odd_histogram.items())
                    },
                }
            )

    ordinary_denominator = 2**maximum_length
    ordinary_cross_numerator = sum(
        count * 2 ** (maximum_length - depth)
        for depth, _odd, count in crossing_rows
    )
    ordinary_alive_numerator = sum(alive.values())
    if ordinary_cross_numerator + ordinary_alive_numerator != ordinary_denominator:
        raise AssertionError("ordinary stopped-mass identity failed")

    tilted_denominator = 4**maximum_length
    tilted_cross_numerator = sum(
        count * 3**odd * 4 ** (maximum_length - depth)
        for depth, odd, count in crossing_rows
    )
    tilted_alive_numerator = sum(
        count * 3**odd for odd, count in alive.items()
    )
    if tilted_cross_numerator + tilted_alive_numerator != tilted_denominator:
        raise AssertionError("tilted stopped-martingale identity failed")

    # Under the tilted cylinder law q(w)=3^O/4^S, odd bits have probability
    # 3/4 and the log-slope drift is positive.  Thus a first passage occurs
    # almost surely.  A first-passage word overshoots from slope <=1 by one
    # odd factor 3/2, so its final slope lies in (1,3/2].  Consequently its
    # ordinary mass p=q/slope lies between (2/3)q and q.  The live tilted
    # residual therefore gives an exact bracket for the full ordinary Kraft
    # mass without enumerating the infinite tail.
    ordinary_partial = Fraction(
        ordinary_cross_numerator, ordinary_denominator
    )
    tilted_residual = Fraction(tilted_alive_numerator, tilted_denominator)
    ordinary_limit_lower = ordinary_partial + Fraction(2, 3) * tilted_residual
    ordinary_limit_upper = ordinary_partial + tilted_residual
    if not ordinary_limit_lower < ordinary_limit_upper < 1:
        raise AssertionError("ordinary first-passage limit bracket failed")

    # The bounded signed-controller code already in the repository is
    # exactly the first three nonempty layers of this canonical code.
    first_nonempty = [
        (int(row["length"]), int(row["first_passage_words"]))
        for row in crossing_by_length
        if int(row["first_passage_words"])
    ][:3]
    if first_nonempty != [(1, 1), (3, 1), (6, 2)]:
        raise AssertionError("minimal four-word outward code changed")

    return {
        "definition": (
            "all parity words w with 3^odd(w)>2^len(w) and "
            "3^odd(u)<=2^len(u) for every proper prefix u"
        ),
        "prefix_free": True,
        "maximality": (
            "every outward parity word has a unique first-passage prefix, "
            "so replacing it by that prefix shows this code dominates every "
            "outward prefix-free code in both ordinary and tilted mass"
        ),
        "minimal_layers": {
            "length_word_counts": [[1, 1], [3, 1], [6, 2]],
            "literal_words": ["1", "011", "001111", "010111"],
            "ordinary_kraft_mass": "21/32",
            "tilted_mass": "1905/2048",
        },
        "bound": maximum_length,
        "crossing_by_length": crossing_by_length,
        "ordinary_stopped_mass": {
            "crossed_numerator": str(ordinary_cross_numerator),
            "alive_numerator": str(ordinary_alive_numerator),
            "denominator": str(ordinary_denominator),
            "identity": "P_N+A_N=1",
            "crossed_decimal_diagnostic": decimal_ratio(
                ordinary_cross_numerator, ordinary_denominator
            ),
        },
        "tilted_stopped_mass": {
            "crossed_numerator": str(tilted_cross_numerator),
            "alive_numerator": str(tilted_alive_numerator),
            "denominator": str(tilted_denominator),
            "identity": "Q_N+R_N=1",
            "crossed_decimal_diagnostic": decimal_ratio(
                tilted_cross_numerator, tilted_denominator
            ),
            "alive_decimal_diagnostic": decimal_ratio(
                tilted_alive_numerator, tilted_denominator
            ),
        },
        "full_ordinary_kraft_bracket": {
            "lower": str(ordinary_limit_lower),
            "upper": str(ordinary_limit_upper),
            "lower_decimal_diagnostic": decimal_ratio(
                ordinary_limit_lower.numerator,
                ordinary_limit_lower.denominator,
            ),
            "upper_decimal_diagnostic": decimal_ratio(
                ordinary_limit_upper.numerator,
                ordinary_limit_upper.denominator,
            ),
            "proof": (
                "the unobserved tilted tail has mass R_N; first-passage "
                "overshoot gives 1<slope<=3/2 and hence (2/3)q<=p<q"
            ),
        },
        "infinite_theorem_boundary": (
            "the fair-parity slope is a nonnegative martingale; on uncrossed "
            "paths it is at most one and tends to zero almost surely by the "
            "negative log drift, so dominated convergence gives total tilted "
            "first-passage mass exactly one"
        ),
        "mass_to_atom_gate": (
            "branching criticality alone does not give an ordinary seed; a "
            "coherent path with rho_n=o(2^n) suffices, since every nonzero "
            "extension carry makes rho_(n+1)>=2^n; measure-theoretically, "
            "sum_n E[rho_(n+1)]/2^n<infinity forces eventual zero carry"
        ),
        "carry_growth_criterion": {
            "identity": "rho_(n+1)=rho_n+2^L_n*ell_n, ell_n>=0, L_n>=n",
            "nonzero_carry_bound": "ell_n>0 implies rho_(n+1)>=2^n",
            "deterministic_sufficient_conditions": [
                "rho_n=o(2^n)",
                "limsup rho_n^(1/n)<2",
            ],
            "measure_sufficient_condition": (
                "sum_n E[rho_(n+1)]/2^n<infinity; Markov plus "
                "Borel-Cantelli then gives eventual zero carry almost surely"
            ),
            "formalization_status": "requested from the companion Lean worker",
        },
        "claim_scope": (
            "exact finite first-passage and stopped-mass identities at the "
            "stated bound; no infinite ordinary survivor and no Collatz "
            "counterexample"
        ),
        "counterexample": None,
    }


def build_artifact(
    maximum_length: int, maximum_seed: int, maximum_shortcut_steps: int
) -> dict[str, Any]:
    audit = first_passage_audit(maximum_length)
    regression = minimum_address_regression(
        maximum_seed, maximum_shortcut_steps
    )
    champion_source = int(regression["record_rows"][-1]["source"])
    champion_profile = source_profile(
        champion_source, maximum_shortcut_steps, True
    )
    shallow_profile = source_profile(159_487, 10_000, True)
    data = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": audit,
        "minimum_address_regression": regression,
        "renewal_calibration": renewal_calibration(audit, regression),
        "odd_charge_recurrence": {
            "record_champion": charge_recurrence_audit(champion_profile),
            "shallow_011_record": charge_recurrence_audit(shallow_profile),
        },
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected outward first-passage schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    regression = expected["minimum_address_regression"]
    actual = build_artifact(
        int(expected["audit"]["bound"]),
        int(regression["maximum_seed"]),
        int(regression["maximum_shortcut_steps_per_seed"]),
    )
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if expected["audit"]["counterexample"] is not None:
        raise AssertionError("first-passage artifact claims a counterexample")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": expected["worker_sha256"],
        "bound": expected["audit"]["bound"],
        "maximum_seed": regression["maximum_seed"],
        "greatest_certified_block_depth": regression[
            "greatest_certified_block_depth"
        ],
        "counterexample": None,
    }


def selftest() -> None:
    tiny = first_passage_audit(6)
    if tiny["ordinary_stopped_mass"]["crossed_numerator"] != "42":
        raise AssertionError("tiny ordinary first-passage mass changed")
    if tiny["tilted_stopped_mass"]["crossed_numerator"] != "3810":
        raise AssertionError("tiny tilted first-passage mass changed")
    addresses = minimum_address_regression(100, 1_000)
    if addresses["greatest_certified_block_depth"] != 15:
        raise AssertionError("tiny minimum-address depth changed")
    if addresses["certified_h_values"][4] != {
        "block_depth": 5,
        "minimum_address": 27,
    }:
        raise AssertionError("tiny minimum-address record changed")
    if addresses["post_address_renewal"]["champion"][
        "post_address_first_passage_extensions"
    ] != 12:
        raise AssertionError("tiny post-address renewal record changed")
    shallow = charge_recurrence_audit(source_profile(159_487, 10_000, True))
    cycle_prefix = [
        (row["c"], row["next_c"]) for row in shallow["shallow_011_rows"][:3]
    ]
    if cycle_prefix != [(7, 2), (2, 12), (12, 7)]:
        raise AssertionError("shallow 011 exponent prefix changed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--maximum-length", type=int, default=256)
    build.add_argument("--maximum-seed", type=int, default=300_000)
    build.add_argument("--maximum-shortcut-steps", type=int, default=10_000)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward first-passage selftest: PASS")
        return 0
    if args.command == "build":
        artifact = build_artifact(
            args.maximum_length, args.maximum_seed, args.maximum_shortcut_steps
        )
        args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.output), indent=2, sort_keys=True))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_artifact(args.artifact), indent=2, sort_keys=True))
        return 0
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    raise SystemExit(main())

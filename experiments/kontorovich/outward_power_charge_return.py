#!/usr/bin/env python3
"""Exact exponent search after the resonant odd-charge recharge.

The kernel-checked resonant family sends

    H_L = 3 * (2^17 * 3^L - 7)  |->  3^(L+12).

This worker studies only the theorem-mandated landing family ``H=3^C``.  It
iterates the deterministic compressed odd-charge map until the next outward
recharge is undefined, or until it reaches a pure power of three / the input
resonant family again.  It is not a generic Collatz seed sweep.  A finite
return is only a candidate edge; it is not an infinite orbit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
from collections import Counter
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "collatz-outward-power-charge-return-v1"
RESONANT_LENGTH = 17
RESONANT_SHIFT = 12


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def integer_sha256(value: int) -> str:
    if value < 0:
        raise ValueError("integer hash requires a nonnegative value")
    width = max(1, (value.bit_length() + 7) // 8)
    return hashlib.sha256(value.to_bytes(width, "big")).hexdigest()


def valuation(value: int, prime: int) -> tuple[int, int]:
    if value <= 0 or prime <= 1:
        raise ValueError("valuation requires positive value and prime")
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent, value


def power_of_three_exponent(value: int) -> int | None:
    exponent, unit = valuation(value, 3)
    return exponent if unit == 1 else None


def resonant_parameter(value: int) -> int | None:
    """Return L when value=3*(2^17*3^L-7), and otherwise None."""

    if value % 3:
        return None
    shifted = value // 3 + 7
    modulus = 1 << RESONANT_LENGTH
    if shifted % modulus:
        return None
    return power_of_three_exponent(shifted // modulus)


def shallow_hensel_audit(maximum_depth: int = 64) -> dict[str, Any]:
    """Construct the unique 2-adic drain tower for the 010111 cylinder.

    Put C=12+16n and f(n)=3^(14+16n)+7.  The returned r_k is the
    unique residue modulo 2^k for which 2^(6+k) divides f(r_k).  LTE for
    g=3^16 makes the lift binary and unique; all checks below use modular
    exponentiation, so even the depth-64 row is exact and small.
    """

    if maximum_depth < 1:
        raise ValueError("Hensel depth must be positive")
    generator = 3**16
    residue = 0
    rows: list[dict[str, Any]] = []
    for depth in range(maximum_depth + 1):
        modulus = 1 << (6 + depth)
        exponent = 14 + 16 * residue
        if (pow(3, exponent, modulus) + 7) % modulus:
            raise AssertionError("Hensel residue lost its advertised divisibility")
        exponent_residue = 12 + 16 * residue
        rows.append(
            {
                "drain_at_least": depth,
                "n_residue_mod_2_pow_depth": str(residue),
                "n_residue_hex": hex(residue),
                "C_residue_mod_2_pow_depth_plus_4": str(exponent_residue),
                "C_residue_hex": hex(exponent_residue),
            }
        )
        if depth == maximum_depth:
            break

        next_modulus = 1 << (7 + depth)
        value_mod_next = (pow(3, exponent, next_modulus) + 7) % next_modulus
        epsilon = (value_mod_next >> (6 + depth)) & 1
        alternative = residue + (1 << depth)
        delta = (
            pow(generator, 1 << depth, next_modulus) - 1
        ) % next_modulus
        if delta % (1 << (6 + depth)):
            raise AssertionError("LTE lift difference lost divisibility")
        if delta % (1 << (7 + depth)) == 0:
            raise AssertionError("LTE lift difference gained an extra factor")
        children = [residue, alternative]
        good_children = [
            child
            for child in children
            if (pow(3, 14 + 16 * child, next_modulus) + 7) % next_modulus == 0
        ]
        if len(good_children) != 1:
            raise AssertionError("Hensel lift is not unique")
        residue = residue + epsilon * (1 << depth)
        if residue != good_children[0]:
            raise AssertionError("Hensel lift bit formula selected the wrong child")
        rows[-1]["next_lift_bit"] = epsilon

    e_star_modulus = 1 << (maximum_depth + 4)
    e_star = (14 + 16 * residue) % e_star_modulus
    if maximum_depth >= 64 and hex(e_star) != "0x5d9f1db0034c04ae":
        raise AssertionError("depth-64 2-adic exponent regression changed")
    return {
        "parameterization": "C=12+16*n; f(n)=3^(14+16*n)+7",
        "exact_lte_law": "v2((3^16)^(2^k)-1)=6+k",
        "lift_law": (
            "a(C)>=k iff C=12+16*r_k mod 2^(k+4), where "
            "2^(6+k) divides f(r_k)"
        ),
        "maximum_lift_depth": maximum_depth,
        "two_adic_E_star_mod_2_pow_depth_plus_4": str(e_star),
        "two_adic_E_star_hex": hex(e_star),
        "rows": rows,
        "interpretation": (
            "arbitrarily large finite drains occupy one nested exponent "
            "cylinder; this is not one natural exponent with an infinite orbit"
        ),
    }


def compressed_recharge(charge: int, maximum_shortcut_steps: int) -> dict[str, Any] | None:
    """Execute one nontrivial first-passage recharge and its forced drain."""

    if charge <= 0 or charge % 2 == 0:
        raise ValueError("compressed recharge requires a positive odd charge")
    state = 3 * charge - 1
    slope_three = 1
    slope_two = 1
    odd_count = 0
    word: list[str] = []
    for _ in range(maximum_shortcut_steps):
        if state in (1, 2):
            return None
        odd = state % 2
        word.append("1" if odd else "0")
        slope_two *= 2
        if odd:
            state = (3 * state + 1) // 2
            slope_three *= 3
            odd_count += 1
        else:
            state //= 2
        if slope_three <= slope_two:
            continue

        if state % 3 != 2:
            raise AssertionError("first-passage endpoint left class 2 mod 3")
        pre_drain = (state + 1) // 3
        drain, odd_part = valuation(pre_drain, 2)
        output = 3**drain * odd_part
        output_v3, output_unit = valuation(output, 3)
        if output % 2 == 0 or output <= charge:
            raise AssertionError("compressed recharge lost oddness or growth")
        if output_v3 < drain + 1:
            raise AssertionError("compressed recharge lost its ternary bound")
        return {
            "input": charge,
            "pre_drain": pre_drain,
            "output": output,
            "word": "".join(word),
            "length": len(word),
            "odd_count": odd_count,
            "forced_one_blocks": drain,
            "output_v3": output_v3,
            "output_unit": output_unit,
        }
    raise AssertionError(
        "recharge did not cross or terminate within the advertised step limit"
    )


def orbit_summary(
    exponent: int,
    maximum_recharges: int,
    maximum_shortcut_steps: int,
    keep_trace: bool = False,
) -> dict[str, Any]:
    if exponent < 1:
        raise ValueError("power exponent must be positive")
    charge = 3**exponent
    maximum_word_length = 0
    maximum_charge_bits = charge.bit_length()
    trace: list[dict[str, Any]] = []
    for depth in range(1, maximum_recharges + 1):
        transition = compressed_recharge(charge, maximum_shortcut_steps)
        if transition is None:
            return {
                "exponent": exponent,
                "status": "terminal_before_next_recharge",
                "completed_recharges": depth - 1,
                "maximum_word_length": maximum_word_length,
                "maximum_charge_bits": maximum_charge_bits,
                "return": None,
                "trace": trace if keep_trace else None,
            }
        output = int(transition["output"])
        maximum_word_length = max(maximum_word_length, int(transition["length"]))
        maximum_charge_bits = max(maximum_charge_bits, output.bit_length())
        if keep_trace:
            trace.append(
                {
                    "recharge_depth": depth,
                    "input_bits": charge.bit_length(),
                    "input_sha256": integer_sha256(charge),
                    "word": transition["word"],
                    "length": transition["length"],
                    "odd_count": transition["odd_count"],
                    "forced_one_blocks": transition["forced_one_blocks"],
                    "output_bits": output.bit_length(),
                    "output_sha256": integer_sha256(output),
                    "output_v3": transition["output_v3"],
                }
            )

        pure_exponent = power_of_three_exponent(output)
        resonant = resonant_parameter(output)
        if pure_exponent is not None:
            return {
                "exponent": exponent,
                "status": "pure_power_return",
                "completed_recharges": depth,
                "maximum_word_length": maximum_word_length,
                "maximum_charge_bits": maximum_charge_bits,
                "return": {
                    "kind": "pure_power",
                    "exponent": pure_exponent,
                    "exponent_gain": pure_exponent - exponent,
                },
                "trace": trace if keep_trace else None,
            }
        if resonant is not None:
            return {
                "exponent": exponent,
                "status": "resonant_family_return",
                "completed_recharges": depth,
                "maximum_word_length": maximum_word_length,
                "maximum_charge_bits": maximum_charge_bits,
                "return": {"kind": "resonant_family", "parameter": resonant},
                "trace": trace if keep_trace else None,
            }
        charge = output

    return {
        "exponent": exponent,
        "status": "recharge_limit",
        "completed_recharges": maximum_recharges,
        "maximum_word_length": maximum_word_length,
        "maximum_charge_bits": maximum_charge_bits,
        "return": None,
        "trace": trace if keep_trace else None,
    }


def scan_chunk(arguments: tuple[int, int, int, int]) -> list[dict[str, Any]]:
    lower, upper, maximum_recharges, maximum_shortcut_steps = arguments
    return [
        orbit_summary(exponent, maximum_recharges, maximum_shortcut_steps)
        for exponent in range(lower, upper)
    ]


def exact_scan(
    minimum_exponent: int,
    maximum_exponent: int,
    maximum_recharges: int,
    maximum_shortcut_steps: int,
    processes: int,
    chunk_size: int,
) -> dict[str, Any]:
    if not 1 <= minimum_exponent <= maximum_exponent:
        raise ValueError("invalid exponent interval")
    if maximum_recharges < 1 or maximum_shortcut_steps < 1:
        raise ValueError("search limits must be positive")
    if processes < 1 or chunk_size < 1:
        raise ValueError("parallelization settings must be positive")
    chunks = [
        (
            lower,
            min(lower + chunk_size, maximum_exponent + 1),
            maximum_recharges,
            maximum_shortcut_steps,
        )
        for lower in range(minimum_exponent, maximum_exponent + 1, chunk_size)
    ]
    if processes == 1:
        pieces = [scan_chunk(chunk) for chunk in chunks]
    else:
        with mp.Pool(processes) as pool:
            pieces = pool.map(scan_chunk, chunks)
    rows = [row for piece in pieces for row in piece]
    if len(rows) != maximum_exponent - minimum_exponent + 1:
        raise AssertionError("exponent scan did not cover its interval")

    status_histogram = Counter(str(row["status"]) for row in rows)
    recharge_histogram = Counter(int(row["completed_recharges"]) for row in rows)
    maximum_depth = max(int(row["completed_recharges"]) for row in rows)
    champion_exponents = [
        int(row["exponent"])
        for row in rows
        if int(row["completed_recharges"]) == maximum_depth
    ]
    records: list[dict[str, int]] = []
    record_depth = -1
    for row in rows:
        depth = int(row["completed_recharges"])
        if depth > record_depth:
            records.append({"exponent": int(row["exponent"]), "recharges": depth})
            record_depth = depth
    returns = [
        {
            "initial_exponent": int(row["exponent"]),
            "recharge_depth": int(row["completed_recharges"]),
            **dict(row["return"]),
        }
        for row in rows
        if row["return"] is not None
    ]

    eligibility_residues = [
        residue
        for residue in range(16)
        if pow(3, residue + 1, 64) == 19
    ]
    if eligibility_residues != [12]:
        raise AssertionError("010111 exponent cylinder changed")
    shallow_drains: Counter[int] = Counter()
    shallow_maximum_drain = -1
    shallow_maximum_rows: list[dict[str, int]] = []
    shallow_count = 0
    first_shallow = minimum_exponent + ((12 - minimum_exponent) % 16)
    for exponent in range(first_shallow, maximum_exponent + 1, 16):
        transition = compressed_recharge(3**exponent, maximum_shortcut_steps)
        if transition is None or transition["word"] != "010111":
            raise AssertionError("010111 exponent cylinder lost its word")
        numerator = 3 ** (exponent + 2) + 7
        numerator_v2, odd_quotient = valuation(numerator, 2)
        drain = int(transition["forced_one_blocks"])
        if numerator_v2 < 6 or drain != numerator_v2 - 6:
            raise AssertionError("010111 Hensel drain law failed")
        if int(transition["pre_drain"]) != 9 * numerator // 64:
            raise AssertionError("010111 pre-drain formula failed")
        if int(transition["output"]) != 3 ** (drain + 2) * odd_quotient:
            raise AssertionError("010111 output charge formula failed")
        shallow_count += 1
        shallow_drains[drain] += 1
        row = {"exponent": exponent, "forced_one_blocks": drain}
        if drain > shallow_maximum_drain:
            shallow_maximum_drain = drain
            shallow_maximum_rows = [row]
        elif drain == shallow_maximum_drain:
            shallow_maximum_rows.append(row)
    champion = orbit_summary(
        champion_exponents[0],
        maximum_recharges,
        maximum_shortcut_steps,
        True,
    )
    if int(champion["completed_recharges"]) != maximum_depth:
        raise AssertionError("champion replay changed its recharge depth")

    return {
        "meaning": (
            "exact deterministic compressed-recharge scan of H=3^C, the "
            "kernel-checked landing family of the resonant outward word"
        ),
        "minimum_exponent": minimum_exponent,
        "maximum_exponent": maximum_exponent,
        "maximum_recharges_per_exponent": maximum_recharges,
        "maximum_shortcut_steps_per_recharge": maximum_shortcut_steps,
        "exponents_checked": len(rows),
        "status_histogram": dict(sorted(status_histogram.items())),
        "recharge_count_histogram": {
            str(depth): count for depth, count in sorted(recharge_histogram.items())
        },
        "record_rows": records,
        "maximum_completed_recharges": maximum_depth,
        "champion_tie_count": len(champion_exponents),
        "champion_exponents_first_twenty": champion_exponents[:20],
        "champion": champion,
        "maximum_word_length_observed": max(int(row["maximum_word_length"]) for row in rows),
        "maximum_charge_bits_observed": max(int(row["maximum_charge_bits"]) for row in rows),
        "return_rows": returns,
        "shallow_010111_exponent_cylinder": {
            "word": "010111",
            "word_data": {"S": 6, "O": 4, "source_residue": 18, "defect": 63},
            "eligibility": "C=12 mod 16",
            "eligibility_residues_mod_16": eligibility_residues,
            "charge_formula": (
                "K=9*(3^(C+2)+7)/64; a=v2(3^(C+2)+7)-6; "
                "R=3^(a+2)*(3^(C+2)+7)/2^(a+6)"
            ),
            "members_checked_in_interval": shallow_count,
            "drain_histogram": {
                str(drain): count for drain, count in sorted(shallow_drains.items())
            },
            "maximum_forced_one_blocks": shallow_maximum_drain,
            "maximum_rows": shallow_maximum_rows,
            "hensel_tower": shallow_hensel_audit(),
            "direct_resonant_return_impossible": (
                "output v3 is a+2>=2, whereas every resonant-family input has v3=1"
            ),
            "direct_pure_power_return_equation": "3^(C+2)+7=2^(6+a)",
        },
        "all_exponents_resolved_before_limits": status_histogram["recharge_limit"] == 0,
        "counterexample": None,
        "claim_scope": (
            "finite exponent interval after one exact resonant edge; a finite "
            "return row would still require a parametric closure theorem"
        ),
    }


def build_artifact(args: argparse.Namespace) -> dict[str, Any]:
    result = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": exact_scan(
            args.minimum_exponent,
            args.maximum_exponent,
            args.maximum_recharges,
            args.maximum_shortcut_steps,
            args.processes,
            args.chunk_size,
        ),
    }
    result["artifact_sha256"] = hashlib.sha256(canonical_json(result)).hexdigest()
    return result


def verify_artifact(path: Path, processes: int, chunk_size: int) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    if stored.get("schema") != SCHEMA:
        raise ValueError("unsupported power-charge return schema")
    audit = stored["audit"]
    args = argparse.Namespace(
        minimum_exponent=int(audit["minimum_exponent"]),
        maximum_exponent=int(audit["maximum_exponent"]),
        maximum_recharges=int(audit["maximum_recharges_per_exponent"]),
        maximum_shortcut_steps=int(audit["maximum_shortcut_steps_per_recharge"]),
        processes=processes,
        chunk_size=chunk_size,
    )
    rebuilt = build_artifact(args)
    if rebuilt != stored:
        raise AssertionError("power-charge return artifact failed reconstruction")
    return report(stored)


def report(artifact: dict[str, Any]) -> dict[str, Any]:
    audit = artifact["audit"]
    return {
        "artifact_sha256": artifact["artifact_sha256"],
        "worker_sha256": artifact["worker_sha256"],
        "exponent_interval": [audit["minimum_exponent"], audit["maximum_exponent"]],
        "maximum_completed_recharges": audit["maximum_completed_recharges"],
        "returns_found": len(audit["return_rows"]),
        "all_exponents_resolved_before_limits": audit["all_exponents_resolved_before_limits"],
        "counterexample": audit["counterexample"],
    }


def selftest() -> None:
    tower = shallow_hensel_audit()
    if tower["rows"][32]["n_residue_hex"] != "0x34c04a":
        raise AssertionError("depth-32 Hensel residue changed")
    row = compressed_recharge(3**12, 100_000)
    if row is None or row["word"] != "010111":
        raise AssertionError("C=12 shallow power recharge changed")
    if row["forced_one_blocks"] != 1 or row["output_v3"] != 3:
        raise AssertionError("C=12 charge output changed")
    audit = exact_scan(12, 1000, 100, 100_000, 1, 100)
    if audit["maximum_completed_recharges"] != 11:
        raise AssertionError("small exponent champion changed")
    if audit["champion_exponents_first_twenty"][0] != 700:
        raise AssertionError("small exponent champion location changed")
    if audit["return_rows"] or not audit["all_exponents_resolved_before_limits"]:
        raise AssertionError("small exponent return/termination classification changed")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--processes", type=int, default=1)
    result.add_argument("--chunk-size", type=int, default=100)
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("selftest")
    probe = sub.add_parser("probe")
    build = sub.add_parser("build")
    verify = sub.add_parser("verify")
    for command in (probe, build):
        command.add_argument("--minimum-exponent", type=int, default=12)
        command.add_argument("--maximum-exponent", type=int, default=1000)
        command.add_argument("--maximum-recharges", type=int, default=100)
        command.add_argument("--maximum-shortcut-steps", type=int, default=100_000)
    build.add_argument("artifact", type=Path)
    verify.add_argument("artifact", type=Path)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward power-charge return selftest: PASS")
        return 0
    if args.command == "probe":
        artifact = build_artifact(args)
        print(json.dumps(report(artifact), indent=2, sort_keys=True))
        return 0
    if args.command == "build":
        artifact = build_artifact(args)
        args.artifact.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(json.dumps(verify_artifact(args.artifact, args.processes, args.chunk_size), indent=2, sort_keys=True))
        return 0
    print(json.dumps(verify_artifact(args.artifact, args.processes, args.chunk_size), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

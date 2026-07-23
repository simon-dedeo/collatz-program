#!/usr/bin/env python3
"""Exact finite-height audit of the triadic min-plus renewal operator.

Let E_n be the positive sources completing n outward first-passage blocks and

    m_n(k,a) = min {x in E_n : x = a (mod 3^k)}.

For a first-passage word w, every execution has dual-residue form

    (x,y) = (r_w + 2^S t, b_w + 3^O t).

Fixing the source phase modulo 3^k fixes t modulo 3^k and hence the target
phase modulo 3^(O+k).  This gives an exact min-plus update for m_(n+1).
The worker below checks the update against literal shortcut execution for all
phases and depths in a stated finite box.  It does not claim that a fixed
triadic precision closes the unbounded inverse limit; in fact the word `1`
already raises the required precision from k to k+1.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Sequence

try:
    from .outward_first_passage import (
        canonical_json,
        source_profile,
        word_affine_constant,
    )
except ImportError:
    from outward_first_passage import (
        canonical_json,
        source_profile,
        word_affine_constant,
    )


SCHEMA = "collatz-outward-minplus-profile-v1"


def source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def first_word_data(source: int, maximum_shortcut_steps: int) -> dict[str, Any] | None:
    profile = source_profile(source, maximum_shortcut_steps, True)
    if not profile["boundaries"]:
        return None
    boundary = profile["boundaries"][0]
    word = str(boundary["word"])
    length = len(word)
    odds = word.count("1")
    residue = source % 2**length
    if residue == 0:
        raise AssertionError("an outward first-passage word has zero residue")
    constant = word_affine_constant(word)
    numerator = 3**odds * residue + constant
    if numerator % 2**length:
        raise AssertionError("canonical target is not integral")
    target = numerator // 2**length
    if not 0 <= target < 3**odds:
        raise AssertionError("canonical target left its triadic range")
    parameter = (source - residue) // 2**length
    if int(boundary["state"]) != target + 3**odds * parameter:
        raise AssertionError("dual-residue word family failed")
    return {
        "word": word,
        "length": length,
        "odd_count": odds,
        "source_residue": residue,
        "target_residue": target,
        "affine_constant": constant,
    }


def complete_word_table(
    source_bound: int, maximum_shortcut_steps: int
) -> list[dict[str, Any]]:
    """Enumerate W_B={w in F:r_w<=B} by their injective source residues."""

    table: dict[str, dict[str, Any]] = {}
    for source in range(1, source_bound + 1):
        row = first_word_data(source, maximum_shortcut_steps)
        if row is None:
            continue
        word = str(row["word"])
        previous = table.get(word)
        if previous is not None and previous != row:
            raise AssertionError("one word acquired inconsistent dual data")
        table[word] = row
    rows = sorted(table.values(), key=lambda row: int(row["source_residue"]))
    if len({int(row["source_residue"]) for row in rows}) != len(rows):
        raise AssertionError("canonical source residue is not injective on W_B")
    for row in rows:
        residue = int(row["source_residue"])
        if residue > source_bound:
            raise AssertionError("word table exceeded its source bound")
        replay = first_word_data(residue, maximum_shortcut_steps)
        if replay != row:
            raise AssertionError("canonical residue did not reproduce its word")
    return rows


def target_bound(source_bound: int, table: list[dict[str, Any]]) -> int:
    maximum = 0
    for row in table:
        length = int(row["length"])
        odds = int(row["odd_count"])
        residue = int(row["source_residue"])
        target = int(row["target_residue"])
        parameter = (source_bound - residue) // 2**length
        maximum = max(maximum, target + 3**odds * parameter)
    return maximum


def block_counts(bound: int, maximum_shortcut_steps: int) -> list[int]:
    return [
        0,
        *(
            int(source_profile(source, maximum_shortcut_steps)["first_passage_blocks"])
            for source in range(1, bound + 1)
        ),
    ]


def phase_minimum(
    counts: list[int], depth: int, exponent: int, residue: int
) -> int | None:
    modulus = 3**exponent
    residue %= modulus
    for source in range(1, len(counts)):
        if counts[source] >= depth and source % modulus == residue:
            return source
    return None


def minplus_candidate(
    counts_at_target_bound: list[int],
    depth: int,
    phase_exponent: int,
    phase_residue: int,
    source_bound: int,
    table: list[dict[str, Any]],
) -> int | None:
    best: int | None = None
    source_modulus = 3**phase_exponent
    for row in table:
        length = int(row["length"])
        odds = int(row["odd_count"])
        source_residue = int(row["source_residue"])
        target_residue = int(row["target_residue"])
        inverse = pow(2**length, -1, source_modulus)
        parameter_phase = (
            (phase_residue - source_residue) * inverse
        ) % source_modulus
        lifted_target_residue = target_residue + 3**odds * parameter_phase
        target = phase_minimum(
            counts_at_target_bound,
            depth,
            odds + phase_exponent,
            lifted_target_residue,
        )
        if target is None:
            continue
        difference = target - target_residue
        if difference < 0 or difference % 3**odds:
            raise AssertionError("target phase did not give an integral parameter")
        candidate = source_residue + 2**length * (difference // 3**odds)
        if candidate > source_bound or candidate % source_modulus != (
            phase_residue % source_modulus
        ):
            continue
        if best is None or candidate < best:
            best = candidate
    return best


def audit(
    source_bound: int,
    maximum_depth: int,
    maximum_phase_exponent: int,
    maximum_shortcut_steps: int,
) -> dict[str, Any]:
    if source_bound < 1 or maximum_depth < 1 or maximum_phase_exponent < 0:
        raise ValueError("audit bounds must be nonnegative and nontrivial")
    table = complete_word_table(source_bound, maximum_shortcut_steps)
    bound = target_bound(source_bound, table)
    source_counts = block_counts(source_bound, maximum_shortcut_steps)
    target_counts = block_counts(bound, maximum_shortcut_steps)

    checks = 0
    rows: list[dict[str, Any]] = []
    for depth in range(maximum_depth):
        for exponent in range(maximum_phase_exponent + 1):
            for residue in range(3**exponent):
                direct = phase_minimum(
                    source_counts, depth + 1, exponent, residue
                )
                computed = minplus_candidate(
                    target_counts,
                    depth,
                    exponent,
                    residue,
                    source_bound,
                    table,
                )
                if direct != computed:
                    raise AssertionError(
                        "triadic min-plus update disagrees with literal execution"
                    )
                checks += 1
                if direct is not None:
                    rows.append(
                        {
                            "input_depth": depth,
                            "output_depth": depth + 1,
                            "phase_exponent": exponent,
                            "phase_residue": residue,
                            "minimum": direct,
                        }
                    )

    nonzero_carry_checks = 0
    zero_carry_target_maximum = 0
    for row in table:
        length = int(row["length"])
        odds = int(row["odd_count"])
        source_residue = int(row["source_residue"])
        target_residue = int(row["target_residue"])
        maximum_parameter = (source_bound - source_residue) // 2**length
        zero_carry_target_maximum = max(zero_carry_target_maximum, target_residue)
        for parameter in range(1, maximum_parameter + 1):
            source = source_residue + 2**length * parameter
            target = target_residue + 3**odds * parameter
            if source > source_bound or target > 3 * source_bound - 1:
                raise AssertionError("nonzero-carry target bound failed")
            nonzero_carry_checks += 1

    return {
        "definition": (
            "m_n(k,a) is the least positive source <=B completing n blocks "
            "and congruent to a modulo 3^k, with null for an empty phase"
        ),
        "source_bound": source_bound,
        "maximum_depth": maximum_depth,
        "maximum_phase_exponent": maximum_phase_exponent,
        "maximum_shortcut_steps_per_source": maximum_shortcut_steps,
        "complete_word_table": table,
        "word_table_size": len(table),
        "target_bound_C_of_B": bound,
        "minplus_equalities_checked": checks,
        "nonzero_carry_target_bounds_checked": nonzero_carry_checks,
        "zero_carry_target_maximum": zero_carry_target_maximum,
        "nonzero_carry_target_upper_bound": 3 * source_bound - 1,
        "nonempty_profile_rows": rows,
        "finite_closure": (
            "at height C choose K with 3^K>C; the level-K profile is the "
            "exact membership bitmap and answers every higher-phase query"
        ),
        "unbounded_obstruction": (
            "no fixed phase depth closes the unbounded operator: word 1 "
            "requires input precision k+1 to update output precision k"
        ),
        "claim_scope": (
            "exact finite word-table completeness and min-plus equality in "
            "the stated box; no bounded inverse-limit profile or orbit"
        ),
        "counterexample": None,
    }


def build_artifact(
    source_bound: int,
    maximum_depth: int,
    maximum_phase_exponent: int,
    maximum_shortcut_steps: int,
) -> dict[str, Any]:
    data = {
        "schema": SCHEMA,
        "worker_sha256": source_sha256(),
        "audit": audit(
            source_bound,
            maximum_depth,
            maximum_phase_exponent,
            maximum_shortcut_steps,
        ),
    }
    data["artifact_sha256"] = hashlib.sha256(canonical_json(data)).hexdigest()
    return data


def verify_artifact(path: Path) -> dict[str, Any]:
    expected = json.loads(path.read_text())
    if expected.get("schema") != SCHEMA:
        raise ValueError("unexpected outward min-plus schema")
    if expected.get("worker_sha256") != source_sha256():
        raise ValueError("worker hash mismatch")
    payload = dict(expected)
    advertised = payload.pop("artifact_sha256")
    if advertised != hashlib.sha256(canonical_json(payload)).hexdigest():
        raise ValueError("artifact self-hash mismatch")
    audit_data = expected["audit"]
    actual = build_artifact(
        int(audit_data["source_bound"]),
        int(audit_data["maximum_depth"]),
        int(audit_data["maximum_phase_exponent"]),
        int(audit_data["maximum_shortcut_steps_per_source"]),
    )
    if actual != expected:
        raise AssertionError("artifact differs from exact recomputation")
    if audit_data["counterexample"] is not None:
        raise AssertionError("min-plus artifact claims a counterexample")
    return {
        "artifact_sha256": advertised,
        "worker_sha256": expected["worker_sha256"],
        "source_bound": audit_data["source_bound"],
        "target_bound": audit_data["target_bound_C_of_B"],
        "minplus_equalities_checked": audit_data["minplus_equalities_checked"],
        "counterexample": None,
    }


def selftest() -> None:
    result = audit(20, 3, 2, 10_000)
    if int(result["minplus_equalities_checked"]) != 39:
        raise AssertionError("tiny min-plus check count changed")
    if int(result["word_table_size"]) < 2:
        raise AssertionError("tiny first-passage word table collapsed")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("selftest")
    build = subparsers.add_parser("build")
    build.add_argument("output", type=Path)
    build.add_argument("--source-bound", type=int, default=50)
    build.add_argument("--maximum-depth", type=int, default=6)
    build.add_argument("--maximum-phase-exponent", type=int, default=3)
    build.add_argument("--maximum-shortcut-steps", type=int, default=100_000)
    verify = subparsers.add_parser("verify")
    verify.add_argument("artifact", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.command == "selftest":
        selftest()
        print("outward min-plus profile selftest: PASS")
        return 0
    if args.command == "build":
        artifact = build_artifact(
            args.source_bound,
            args.maximum_depth,
            args.maximum_phase_exponent,
            args.maximum_shortcut_steps,
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

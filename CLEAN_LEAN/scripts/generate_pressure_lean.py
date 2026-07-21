#!/usr/bin/env python3
"""Compile the portable Lemma-5 JSON into Lean adjacency-list data.

The generated theorem checks only positivity and the exact tilted pressure
rows.  State/edge semantics and irrational endpoint domination remain separate
soundness obligations, just as documented in the JSON predicate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path


def rat(text: str | Fraction) -> Fraction:
    return text if isinstance(text, Fraction) else Fraction(text)


def lean_rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : ℚ)"
    return f"({value.numerator} / {value.denominator} : ℚ)"


def lean_vector(name: str, codomain: str, values: list[str]) -> str:
    body = ",\n    ".join(values)
    return f"def {name} : Fin {len(values)} → {codomain} :=\n  ![{body}]\n"


def camel(name: str) -> str:
    chunks = name.replace("-", "_").split("_")
    return chunks[0] + "".join(chunk.capitalize() for chunk in chunks[1:])


def compile_certificate(cert: dict) -> str:
    prefix = camel(cert["name"])
    states = cert["states"]
    residues = [int(state["q"]) for state in states]
    index = {q: i for i, q in enumerate(residues)}
    if len(index) != len(residues):
        raise ValueError(f"duplicate state in {cert['name']}")

    h_values = [lean_rat(rat(state["h"])) for state in states]
    output = [lean_vector(f"{prefix}H", "ℚ", h_values)]
    output.append(lean_vector(f"{prefix}Residue", "ℕ", [str(q) for q in residues]))

    z = rat(cert["z"])
    pieces = cert["pieces"]
    edges = cert["edges"]
    for piece_number in range(len(pieces)):
        grouped: dict[int, list[tuple[int, Fraction]]] = {q: [] for q in residues}
        for edge in edges:
            if int(edge["piece"]) != piece_number:
                continue
            src = int(edge["src"])
            tgt = int(edge["tgt"])
            if src not in index or tgt not in index:
                raise ValueError(f"edge outside state set in {cert['name']}")
            effective_weight = rat(edge["w"]) * (z ** int(edge["b"]))
            grouped[src].append((index[tgt], effective_weight))

        adjacency = []
        for q in residues:
            row = grouped[q]
            if not row:
                raise ValueError(f"empty row {q} in {cert['name']} piece {piece_number}")
            entries = ", ".join(
                f"({target}, {lean_rat(weight)})" for target, weight in row
            )
            adjacency.append(f"[{entries}]")
        edge_name = f"{prefix}Edges{piece_number}"
        output.append(lean_vector(edge_name, f"List (Fin {len(states)} × ℚ)", adjacency))

    output.append(f"def {prefix}R : ℚ := {lean_rat(rat(cert['R']))}\n")
    output.append(
        f"set_option maxRecDepth 100000 in\n"
        f"theorem {prefix}_h_pos : ∀ q, 0 < {prefix}H q := by decide +kernel\n"
    )
    output.append(
        f"set_option maxRecDepth 100000 in\n"
        f"theorem {prefix}_one_le_h : ∀ q, 1 ≤ {prefix}H q := by decide +kernel\n"
    )
    for piece_number in range(len(pieces)):
        edge_name = f"{prefix}Edges{piece_number}"
        output.append(
            "set_option maxHeartbeats 0 in\n"
            "-- Exact reduction of the portable rational row table.\n"
            "set_option maxRecDepth 100000 in\n"
            f"theorem {prefix}_piece{piece_number}_rows :\n"
            "    checkAdjacencyPressureCertificateRat "
            f"{edge_name} {prefix}H {prefix}R = true := by\n"
            "  decide +kernel\n"
        )
        output.append(
            f"theorem {prefix}_piece{piece_number}_real_rows :\n"
            f"    (∀ q r, 0 ≤ (listKernelRat ({edge_name} q) r : ℝ)) ∧\n"
            f"      ∀ q, (∑ r, (listKernelRat ({edge_name} q) r : ℝ) *\n"
            f"        ({prefix}H r : ℝ)) ≤ ({prefix}R : ℝ) * ({prefix}H q : ℝ) :=\n"
            f"  real_pressureCertificate_of_checkAdjacencyRat {edge_name}\n"
            f"    {prefix}H {prefix}R {prefix}_piece{piece_number}_rows\n"
        )
        output.append(
            f"theorem {prefix}_piece{piece_number}_pressureMass_le :\n"
            f"    ∀ n q, pressureMass\n"
            f"      (fun q r => (listKernelRat ({edge_name} q) r : ℝ)) n q ≤\n"
            f"        ({prefix}R : ℝ) ^ n * ({prefix}H q : ℝ) := by\n"
            f"  apply pressureMass_le_of_checkAdjacencyRat {edge_name}\n"
            f"    {prefix}H {prefix}R {prefix}_piece{piece_number}_rows\n"
            f"    {prefix}_one_le_h\n"
            f"  norm_num [{prefix}R]\n"
        )
    return "\n".join(output)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("json_path", type=Path)
    parser.add_argument("output_path", type=Path)
    args = parser.parse_args()

    raw = args.json_path.read_bytes()
    document = json.loads(raw)
    declared_hash = document["sha256_payload"]
    payload = dict(document)
    payload.pop("sha256_payload")
    actual_hash = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    if actual_hash != declared_hash:
        raise ValueError("portable payload SHA-256 mismatch")

    modules = "\n\n".join(compile_certificate(cert) for cert in document["certificates"])
    generated = f"""/-
Copyright (c) 2026 Simon DeDeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon DeDeo, OpenAI Codex
-/
import CleanLean.KL.PressureCertificate

/-!
# Portable Lemma-5 pressure-certificate data

This file is generated by `scripts/generate_pressure_lean.py` from
`experiments/pressure-cert/lemma5_exact_cert.json`.
Payload SHA-256: `{declared_hash}`.
-/

set_option linter.style.longLine false

namespace CleanLean.KL.PortablePressureData

{modules}

end CleanLean.KL.PortablePressureData
"""
    args.output_path.write_text(generated)


if __name__ == "__main__":
    main()

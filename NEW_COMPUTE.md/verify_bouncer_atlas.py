#!/usr/bin/env python3
"""Independent exact replay and small-box census for bouncer_atlas output."""

import math
import pathlib
import re
import sys


def fields(line):
    return dict(re.findall(r"(\w+)=([^\s]+)", line))


def v2(n):
    assert n
    return (n & -n).bit_length() - 1


def invmod(a, modulus):
    old_r, r, old_s, s = modulus, a % modulus, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
    assert old_r == 1
    return old_s % modulus


def compose(a, b):
    ai, asi, ao, aso = a
    bi, bsi, bo, bso = b
    d = bi - ao
    g = math.gcd(aso, bsi)
    if d % g:
        return None
    aa, bb, dg = aso // g, bsi // g, d // g
    t = 0 if bb == 1 else (dg * invmod(aa, bb)) % bb
    u = (aso * t - d) // bsi
    if u < 0:
        k = (-u + aa - 1) // aa
        t += bb * k
        u += aa * k
    assert ao + aso * t == bi + bsi * u
    return ai + asi * t, asi * bb, bo + bso * u, bso * aa


def main(path):
    lines = path.read_text().splitlines()
    head = fields(lines[0])
    mb, hb, depth = map(int, (head["m_bound"], head["h_bound"], head["depth"]))
    assert depth == 2
    A, B, C, D = 3**114, 2**154, 3**17, 2**23
    F, M = (A - B) // 5, 3**33 * (C - D)
    edges = {}
    for line in lines:
        if not line.startswith("EDGE\t"):
            continue
        row = fields(line)
        key = tuple(map(int, (row["m"], row["h"], row["next_m"])))
        edge = tuple(map(int, (row["input_base"], row["input_stride"], row["output_base"], row["output_stride"])))
        edges[key] = edge
        m, h, nxt = key
        for tail in (0, 1):
            y = edge[0] + edge[1] * tail
            out = edge[2] + edge[3] * tail
            assert y > 0 and y & 1 and y % M == 0 and (y + 1) % F == 0
            assert v2(y + 1) == 23 * m
            collision = C**m * (y + 1) - D**m
            assert v2(collision) == 23 * m + 154 * h
            assert A**h * (collision >> (23 * m + 154 * h)) == out
            assert out % M == 0 and (out + 1) % F == 0 and v2(out + 1) == 23 * nxt
    assert len(edges) == mb * hb * mb

    paths = failures = stable = decreased = nonoutward = 0
    minimum = minimum_code = delta = delta_code = None
    alphabet = hb * mb
    for code in range(mb * alphabet * alphabet):
        q = code
        m0 = q % mb + 1
        q //= mb
        s0 = q % alphabet
        q //= alphabet
        s1 = q % alphabet
        h0, m1 = s0 // mb + 1, s0 % mb + 1
        h1, m2 = s1 // mb + 1, s1 % mb + 1
        parent = edges[m0, h0, m1]
        child = compose(parent, edges[m1, h1, m2])
        if child is None:
            failures += 1
            continue
        paths += 1
        if child[2] <= child[0]:
            nonoutward += 1
        change = child[0] - parent[0]
        stable += change == 0
        decreased += change < 0
        change = abs(change)
        if minimum is None or child[0] < minimum:
            minimum, minimum_code = child[0], code
        if delta is None or change < delta:
            delta, delta_code = change, code

    rows = [fields(x) for x in lines if x.startswith("DEPTH\tdepth=2\t")]
    row = rows[-1]
    expected = {
        "paths": paths,
        "link_failures": failures,
        "stabilizations": stable,
        "decreases": decreased,
        "nonoutward": nonoutward,
        "min_root": minimum,
        "min_root_code": minimum_code,
        "min_increment": delta,
        "min_increment_code": delta_code,
    }
    for key, value in expected.items():
        assert int(row[key]) == value, (key, row[key], value)
    result = fields(next(x for x in lines if x.startswith("RESULT\t")))
    assert result["status"] == "complete"
    assert int(result["processed_prefix_tasks"]) == mb * alphabet * alphabet
    print(f"verified exact bouncer atlas: {len(edges)} edges, {paths} linked paths, {failures} failures")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: verify_bouncer_atlas.py OUTPUT.tsv")
    main(pathlib.Path(sys.argv[1]))

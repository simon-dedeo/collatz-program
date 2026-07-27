#!/usr/bin/env python3
"""Independent small regressions for the six native workers."""
import pathlib, re, sys

root = pathlib.Path(sys.argv[1])

soft = (root / "kl-soft.tsv").read_text()
m = re.search(r"RESULT\t8\t2187\t[^\n]+", soft)
assert m, "missing soft result"
fields = m.group(0).split("\t")
rho = float(fields[5])
assert abs(rho - 0.9832936961) < 2e-8, rho

fr = (root / "kl-frustration.tsv").read_text()
assert "k=14" in fr and "SUMMARY" in fr and fr.count("CURVATURE") == 6

carry = (root / "carry.tsv").read_text()
assert carry.count("WORD\t") == 3
assert "DEPTH\t9\t1\t8" in carry
assert "RESULT\tdeepest_nonempty=9\tfirst_empty=10\tstatus=exhausted" in carry

minplus = (root / "minplus.tsv").read_text()
expected = {1: 1, 2: 3, 3: 7, 4: 15, 5: 27, 6: 27, 7: 27, 8: 27}
for depth, h in expected.items():
    assert f"SLICE\tdepth={depth}\th={h}\t" in minplus, (depth, h)

champ = (root / "zero-champion.tsv").read_text()
assert "prefix_depth=8" in champ and "counterexample=null" in champ
assert "CHAMPION\ttotal_survival=27\tbeyond_prefix=19\tseed=1166377457" in champ

hensel = (root / "hensel.tsv").read_text()
assert "two_link_hits=0" in hensel and "three_link_hits=0" in hensel
print("six-worker smoke verification: PASS")

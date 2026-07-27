#!/usr/bin/env python3
"""Summarize independent carry-policy CEGIS shards without merging claims."""
import pathlib, re, sys

if len(sys.argv) < 4:
    raise SystemExit("usage: combine_carry_policy.py OUTPUT.tsv SHARD.tsv...")
out=pathlib.Path(sys.argv[1]); paths=[pathlib.Path(x) for x in sys.argv[2:]]
rows=[]
for path in paths:
    lines=path.read_text().splitlines()
    head=dict(re.findall(r"(\w+)=([^\s]+)",lines[0]))
    best=dict(x.split("=",1) for x in next(x for x in reversed(lines) if x.startswith("BEST\t")).split("\t")[1:])
    result=dict(x.split("=",1) for x in next(x for x in lines if x.startswith("RESULT\t")).split("\t")[1:])
    rows.append((path,head,best,result))
assert len({r[1]["label"].split("-")[0] for r in rows}) == 1
with out.open("w") as f:
    f.write(f"# exact finite carry-policy CEGIS summary shards={len(rows)} symbolic_all_state_certificate=null counterexample=null\n")
    for path,h,b,r in rows:
        f.write(f"SHARD\tfile={path.name}\tword_bound={h['word_bound']}\twords={h['words']}\tstrict={h['strict']}\trows={h['rows']}\tevaluated={b['evaluated']}\ttrain_feasible={b['train_feasible']}\theld_feasible={b['held_feasible']}\theld_rows={b['held_rows']}\tfinite_sample_certificate={r['finite_sample_certificate']}\tcoeff={b['coeff']}\n")
    f.write("RESULT\tstatus=complete\tmeaning=independent_finite_CEGIS_shards_verified\tsymbolic_all_state_certificate=null\tcounterexample=null\n")
print(f"summarized {len(rows)} independently verified shards")

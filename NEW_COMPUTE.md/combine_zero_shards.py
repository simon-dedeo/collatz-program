#!/usr/bin/env python3
"""Combine a complete disjoint zero-carry shard family exactly."""
import pathlib
import re
import sys

if len(sys.argv) < 4:
    raise SystemExit("usage: combine_zero_shards.py OUTPUT.tsv SHARD.tsv...")
out = pathlib.Path(sys.argv[1])
paths = [pathlib.Path(p) for p in sys.argv[2:]]
headers = []
hist = {}
champion = None
for path in paths:
    lines = path.read_text().splitlines()
    fields = dict(re.findall(r"(\w+)=([^\s]+)", lines[0]))
    headers.append(fields)
    for line in lines[1:]:
        parts = line.split("\t")
        if parts[0] == "HIST":
            row = dict(x.split("=", 1) for x in parts[1:])
            d = int(row["total_survival"])
            hist[d] = hist.get(d, 0) + int(row["count"])
        elif parts[0] == "CHAMPION":
            row = dict(x.split("=", 1) for x in parts[1:])
            candidate = (int(row["total_survival"]), -int(row["seed"]), int(row["seed"]), int(row["prefix_endpoint"]))
            if champion is None or candidate[:2] > champion[:2]:
                champion = candidate

keys = ("prefix_depth", "total_schedules", "shard_count", "replay_cap", "arithmetic_bits")
for key in keys:
    assert len({h[key] for h in headers}) == 1, (key, headers)
depth = int(headers[0]["prefix_depth"])
total = int(headers[0]["total_schedules"])
count = int(headers[0]["shard_count"])
cap = int(headers[0]["replay_cap"])
assert len(paths) == count
assert {int(h["shard_index"]) for h in headers} == set(range(count))
assert sum(int(h["shard_schedules"]) for h in headers) == total == 3**depth
positive = sum(int(h["positive_representatives"]) for h in headers)
overflow = sum(int(h["overflowed_replays"]) for h in headers)
assert sum(hist.values()) == positive
assert champion is not None
survival, _, seed, endpoint = champion
with out.open("w") as f:
    f.write(f"# exact combined zero-carry canonical-cylinder census prefix_depth={depth} schedules={total} shards={count} positive_representatives={positive} replay_cap={cap} overflowed_replays={overflow} arithmetic_bits={headers[0]['arithmetic_bits']}\n")
    for d in sorted(hist):
        f.write(f"HIST\ttotal_survival={d}\tbeyond_prefix={max(0,d-depth)}\tcount={hist[d]}\n")
    f.write(f"CHAMPION\ttotal_survival={survival}\tbeyond_prefix={max(0,survival-depth)}\tseed={seed}\tprefix_endpoint={endpoint}\tcounterexample=null\n")

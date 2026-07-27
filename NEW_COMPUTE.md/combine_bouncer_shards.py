#!/usr/bin/env python3
"""Combine exact complete or partial bouncer-atlas shards without overclaiming."""

import pathlib
import re
import sys


def fields(line):
    return dict(re.findall(r"(\w+)=([^\s]+)", line))


def tagged(lines, tag):
    return [line for line in lines if line.startswith(tag + "\t")]


if len(sys.argv) < 4:
    raise SystemExit("usage: combine_bouncer_shards.py OUTPUT.tsv SHARD.tsv...")
out = pathlib.Path(sys.argv[1])
paths = [pathlib.Path(p) for p in sys.argv[2:]]
documents = [path.read_text().splitlines() for path in paths]
headers = [fields(lines[0]) for lines in documents]

constant = ("m_bound", "h_bound", "depth", "total_prefix_tasks", "shards", "label")
for key in constant:
    assert len({header[key] for header in headers}) == 1, (key, headers)
shards = int(headers[0]["shards"])
assert len(paths) == shards
assert {int(header["shard"]) for header in headers} == set(range(shards))
total = int(headers[0]["total_prefix_tasks"])
assert sum(int(header["shard_tasks"]) for header in headers) == total

edge_sections = [tagged(lines, "EDGE") for lines in documents]
assert all(section == edge_sections[0] for section in edge_sections[1:])
results = [fields(tagged(lines, "RESULT")[-1]) for lines in documents]
processed = sum(int(result["processed_prefix_tasks"]) for result in results)
assigned = sum(int(result["shard_tasks"]) for result in results)
assert assigned == total
assert all(int(result["processed_prefix_tasks"]) <= int(result["shard_tasks"]) for result in results)
status = "complete" if processed == total and all(result["status"] == "complete" for result in results) else "partial"

depth = int(headers[0]["depth"])
combined = {}
for d in range(2, depth + 1):
    rows = []
    for lines in documents:
        candidates = [fields(line) for line in tagged(lines, "DEPTH") if fields(line)["depth"] == str(d)]
        assert candidates
        rows.append(candidates[-1])
    sums = {}
    for key in ("paths", "link_failures", "stabilizations", "decreases", "nonoutward"):
        sums[key] = sum(int(row[key]) for row in rows)
    roots = [(int(row["min_root"]), int(row["min_root_code"])) for row in rows if row["min_root"] != "null"]
    deltas = [(int(row["min_increment"]), int(row["min_increment_code"])) for row in rows if row["min_increment"] != "null"]
    combined[d] = (sums, min(roots, default=None), min(deltas, default=None))

with out.open("w") as handle:
    handle.write(
        f"# exact combined bouncer backward-cylinder atlas m_bound={headers[0]['m_bound']} "
        f"h_bound={headers[0]['h_bound']} depth={depth} shards={shards} "
        f"processed_prefix_tasks={processed} total_prefix_tasks={total} status={status} "
        f"label={headers[0]['label']}\n"
    )
    for line in edge_sections[0]:
        handle.write(line + "\n")
    for d in range(2, depth + 1):
        sums, root, delta = combined[d]
        root_value, root_code = root if root else ("null", 0)
        delta_value, delta_code = delta if delta else ("null", 0)
        root_bits = int(root_value).bit_length() if root else 0
        delta_bits = int(delta_value).bit_length() if delta else 0
        handle.write(
            f"DEPTH\tdepth={d}\tprocessed_prefix_tasks={processed}\ttotal_prefix_tasks={total}"
            f"\tpaths={sums['paths']}\tlink_failures={sums['link_failures']}"
            f"\tstabilizations={sums['stabilizations']}\tdecreases={sums['decreases']}"
            f"\tnonoutward={sums['nonoutward']}\tmin_root_bits={root_bits}\tmin_root={root_value}"
            f"\tmin_root_code={root_code}\tmin_increment_bits={delta_bits}\tmin_increment={delta_value}"
            f"\tmin_increment_code={delta_code}\n"
        )
    handle.write(
        f"RESULT\tstatus={status}\tprocessed_prefix_tasks={processed}\ttotal_prefix_tasks={total}"
        f"\tfinite_stabilizations={combined[depth][0]['stabilizations']}"
        "\tinvariant=null\tcounterexample=null\n"
    )
print(f"combined {shards} shards: {processed}/{total} prefix tasks, status={status}")

#!/usr/bin/env python3
"""Watch counterexample-search artifacts and alert the visualizer.

The monitor is intentionally conservative.  It fingerprints research-facing
files, reports changes through the generated block in VISUALIZER_COMMENTS.md,
and auto-renders only JSON objects that carry a complete, exactly replayable
``collatz_source``/``collatz_target``/``accelerated_steps`` triple.  Automatic
renders live under IMAGES/AUTO until a visualizer reviews and promotes them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator

from render_collatz import exact_trace, render_spec


ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "IMAGES"
STATE = HERE / ".visualizer_monitor_state.json"
REPORT = HERE / ".visualizer_monitor_report.json"
COMMENTS = ROOT / "VISUALIZER_COMMENTS.md"
AUTO = HERE / "AUTO"
START = "<!-- visualizer-monitor:start -->"
END = "<!-- visualizer-monitor:end -->"
KEYWORDS = (
    "counterexample",
    "ordinary orbit",
    "accelerated",
    "self-writing",
    "seed",
    "cycle",
    "escape",
    "carry",
    "ruler",
    "mahler",
)


def monitored_paths() -> list[Path]:
    paths = [
        ROOT / "README.md",
        ROOT / "NEW_RESUME.md",
        ROOT / "docs" / "FOR_CLEAN_LEAN.md",
        ROOT / "CLEAN_LEAN" / "FOR_FABLE.md",
    ]
    experiment_dir = ROOT / "experiments" / "kontorovich"
    paths.extend(experiment_dir.glob("*.py"))
    paths.extend(experiment_dir.glob("*.json"))
    return sorted(path for path in paths if path.is_file())


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def snapshot() -> dict[str, str]:
    return {str(path.relative_to(ROOT)): digest(path) for path in monitored_paths()}


def walk_objects(value: Any, pointer: str = "") -> Iterator[tuple[str, dict[str, Any]]]:
    if isinstance(value, dict):
        yield pointer or "/", value
        for key, child in value.items():
            escaped = str(key).replace("~", "~0").replace("/", "~1")
            yield from walk_objects(child, f"{pointer}/{escaped}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk_objects(child, f"{pointer}/{index}")


def exact_candidates(path: Path) -> list[dict[str, Any]]:
    if path.suffix != ".json" or path.stat().st_size > 20_000_000:
        return []
    try:
        document = json.loads(path.read_text())
    except (UnicodeDecodeError, json.JSONDecodeError):
        return []
    candidates: list[dict[str, Any]] = []
    for pointer, value in walk_objects(document):
        if not {"collatz_source", "collatz_target", "accelerated_steps"} <= value.keys():
            continue
        try:
            seed = int(value["collatz_source"])
            target = int(value["collatz_target"])
            steps = int(value["accelerated_steps"])
            exact_trace(seed, target, max(steps, 1), steps)
        except (TypeError, ValueError):
            continue
        if seed <= 0 or target <= seed or steps < 6:
            continue
        signature = hashlib.sha256(
            f"{path.relative_to(ROOT)}#{pointer}:{seed}:{target}:{steps}".encode()
        ).hexdigest()[:16]
        candidates.append(
            {
                "id": f"auto_{signature}",
                "seed": str(seed),
                "stop_at": str(target),
                "expected_steps": steps,
                "construction_prefix_steps": steps,
                "provenance": f"{path.relative_to(ROOT)}#{pointer}",
                "scope": (
                    "Machine-discovered exact finite outward prefix. It has not "
                    "been reviewed as an interesting construction and is not an "
                    "infinite-orbit claim."
                ),
            }
        )
    return candidates


def keyword_hits(path: Path, limit: int = 8) -> list[str]:
    if path.suffix not in {".md", ".py", ".json"} or path.stat().st_size > 5_000_000:
        return []
    hits: list[str] = []
    try:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            lowered = line.lower()
            if any(keyword in lowered for keyword in KEYWORDS):
                compact = " ".join(line.strip().split())
                if compact:
                    hits.append(f"{number}: {compact[:180]}")
            if len(hits) >= limit:
                break
    except UnicodeDecodeError:
        return []
    return hits


def replace_monitor_block(body: str) -> None:
    if START in body and END in body:
        prefix, rest = body.split(START, 1)
        _, suffix = rest.split(END, 1)
        updated = prefix.rstrip() + "\n\n" + body + suffix
    else:
        updated = body.rstrip() + "\n"
    COMMENTS.write_text(updated)


def update_comments(
    scanned_at: str,
    changed: list[str],
    rendered: list[str],
    hits: dict[str, list[str]],
) -> None:
    if COMMENTS.exists():
        current = COMMENTS.read_text()
    else:
        current = "# Visualizer comments\n"
    lines = [
        START,
        "## Automated monitor status",
        "",
        f"Last change scan: `{scanned_at}`. This block is a machine alert, not a research result.",
        "",
    ]
    if not changed:
        lines.append("No monitored file changed since the previous scan.")
    else:
        lines.append("Changed monitored files:")
        lines.append("")
        lines.extend(f"- `{name}`" for name in changed)
        if rendered:
            lines.extend(["", "New exact unreviewed renders:", ""])
            lines.extend(f"- `{name}`" for name in rendered)
        if hits:
            lines.extend(["", "Keyword alerts for visual review:", ""])
            for name, rows in hits.items():
                lines.append(f"- `{name}`: " + " | ".join(rows[:3]))
    lines.extend(["", END])
    block = "\n".join(lines)
    if START in current and END in current:
        prefix, rest = current.split(START, 1)
        _, suffix = rest.split(END, 1)
        updated = prefix.rstrip() + "\n\n" + block + suffix
    else:
        updated = current.rstrip() + "\n\n" + block + "\n"
    COMMENTS.write_text(updated)


def scan(initialize: bool = False) -> dict[str, Any]:
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    current = snapshot()
    previous: dict[str, str] = {}
    if STATE.exists():
        previous = json.loads(STATE.read_text()).get("files", {})
    changed = [] if initialize else sorted(
        name for name, value in current.items() if previous.get(name) != value
    )
    removed = [] if initialize else sorted(set(previous) - set(current))
    rendered: list[str] = []
    hits: dict[str, list[str]] = {}
    for name in changed:
        path = ROOT / name
        path_hits = keyword_hits(path)
        if path_hits:
            hits[name] = path_hits
        for spec in exact_candidates(path):
            AUTO.mkdir(parents=True, exist_ok=True)
            png_path = AUTO / f"{spec['id']}.png"
            if not png_path.exists():
                render_spec(spec, AUTO)
                rendered.append(str(png_path.relative_to(ROOT)))
    record = {
        "schema": "collatz-visualizer-monitor-v1",
        "scanned_at_utc": now,
        "changed": changed,
        "removed": removed,
        "rendered": rendered,
        "keyword_hits": hits,
    }
    STATE.write_text(json.dumps({"files": current}, indent=2, sort_keys=True) + "\n")
    REPORT.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    if not initialize and (changed or removed):
        update_comments(now, changed + [f"REMOVED: {name}" for name in removed], rendered, hits)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--initialize", action="store_true")
    parser.add_argument("--watch", action="store_true")
    parser.add_argument("--interval", type=float, default=60.0)
    args = parser.parse_args()
    if args.interval < 5:
        parser.error("--interval must be at least 5 seconds")
    if args.watch:
        if not STATE.exists():
            scan(initialize=True)
        while True:
            time.sleep(args.interval)
            record = scan()
            if record["changed"] or record["removed"]:
                print(json.dumps(record, sort_keys=True), flush=True)
    else:
        print(json.dumps(scan(initialize=args.initialize), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

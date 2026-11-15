#!/usr/bin/env python3
"""Time-boxed batch runner.

Source of truth for a batch's status is its own frontmatter in queue/*.md.
state.json holds only the clock of the batch that is currently running, so an
interrupted run can be closed out afterwards with `close --force`.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / "queue"
STATE = ROOT / "state.json"
LEDGER = ROOT / "LEDGER.md"
FRONT = re.compile(r"\A---\n(.*?)\n---\n", re.S)
STATUSES = ("pending", "running", "done", "blocked", "abandoned")


def parse(path: Path) -> dict | None:
    m = FRONT.match(path.read_text())
    if not m:
        return None
    fm: dict = {}
    for line in m.group(1).splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        key, _, value = line.partition(":")
        fm[key.strip()] = value.strip().strip('"').strip("'")
    fm["_path"] = str(path)
    fm["_id"] = path.name.split("-")[0]
    return fm


def batches() -> list[dict]:
    return [b for p in sorted(QUEUE.glob("*.md"))
            if not p.name.startswith("_") and (b := parse(p))]


def find(batch_id: str) -> dict:
    for b in batches():
        if b["_id"] == batch_id or b.get("id") == batch_id:
            return b
    sys.exit(f"no batch {batch_id!r} in {QUEUE}")


def set_field(path: str, key: str, value: str) -> None:
    p = Path(path)
    text = p.read_text()
    m = FRONT.match(text)
    lines = m.group(1).splitlines()
    for i, line in enumerate(lines):
        if line.partition(":")[0].strip() == key:
            lines[i] = f"{key}: {value}"
            break
    else:
        lines.append(f"{key}: {value}")
    p.write_text("---\n" + "\n".join(lines) + "\n---\n" + text[m.end():])


def state() -> dict:
    return json.loads(STATE.read_text()) if STATE.exists() else {}


def hm(seconds: float) -> str:
    sign = "-" if seconds < 0 else ""
    seconds = abs(int(seconds))
    return f"{sign}{seconds // 60}m{seconds % 60:02d}s"


def cmd_status(_: argparse.Namespace) -> int:
    running = state()
    print(f"{'id':4} {'state':9} {'budget':7} {'used':8} title")
    for b in batches():
        budget = int(b.get("budget_s", 0))
        used = ""
        if running.get("id") in (b["_id"], b.get("id")):
            used = hm(time.time() - running["started_at"])
        print(f"{b['_id']:4} {b.get('state', 'pending'):9} {hm(budget):7} {used:8} {b.get('title', '')}")
    if running:
        print(f"\nrunning: {running['id']}  remaining {hm(running['deadline'] - time.time())}")
    return 0


def cmd_next(_: argparse.Namespace) -> int:
    for b in batches():
        if b.get("state", "pending") == "pending":
            print(f"{b['_id']}\t{b.get('budget_s', '0')}\t{b.get('title', '')}")
            return 0
    print("queue empty", file=sys.stderr)
    return 5


def cmd_start(args: argparse.Namespace) -> int:
    live = state()
    if live:
        sys.exit(f"{live['id']} is still open ({hm(live['deadline'] - time.time())} remaining), close it first")
    b = find(args.id)
    now = time.time()
    budget = int(b.get("budget_s", 0))
    if budget <= 0:
        sys.exit(f"batch {args.id} has no budget_s. A batch without a budget is not a batch")
    STATE.write_text(json.dumps({
        "id": b["_id"], "title": b.get("title", ""), "path": b["_path"],
        "started_at": now, "budget_s": budget, "deadline": now + budget,
    }, indent=2))
    set_field(b["_path"], "state", "running")
    print(f"{b['_id']} started  deadline {hm(budget)} from now  ({time.strftime('%H:%M:%S', time.localtime(now + budget))})")
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    live = state()
    if not live:
        print("nothing running", file=sys.stderr)
        return 4
    remaining = live["deadline"] - time.time()
    if args.json:
        print(json.dumps({"id": live["id"], "remaining_s": round(remaining, 1),
                          "remaining_ms": max(0, int(remaining * 1000)),
                          "over": remaining <= 0}))
    else:
        print(f"{live['id']}  remaining {hm(remaining)}  ({int(remaining)}s)")
    return 3 if remaining <= 0 else 0


def cmd_extend(args: argparse.Namespace) -> int:
    live = state()
    if not live:
        sys.exit("nothing running")
    if args.minutes <= 0:
        sys.exit("Extension must be a positive number of minutes")
    live["deadline"] += args.minutes * 60
    live.setdefault("extensions", []).append({"minutes": args.minutes, "at": time.time(), "why": args.why})
    STATE.write_text(json.dumps(live, indent=2))
    print(f"{live['id']} extended by {args.minutes}m. Remaining {hm(live['deadline'] - time.time())}")
    return 0


def cmd_close(args: argparse.Namespace) -> int:
    b = find(args.id)
    live = state()
    if live and live["id"] == b["_id"]:
        elapsed = time.time() - live["started_at"]
        budget = live["budget_s"]
        ext = sum(e["minutes"] for e in live.get("extensions", [])) * 60
        STATE.unlink()
    elif args.force:
        elapsed, budget, ext = 0, int(b.get("budget_s", 0)), 0
    else:
        sys.exit(f"{b['_id']} is not the running batch, pass --force to correct a stale entry")
    if args.status not in STATUSES:
        sys.exit(f"status must be one of {STATUSES}")
    set_field(b["_path"], "state", args.status)
    log = ROOT / "logs" / f"{b['_id']}.log"
    with log.open("a") as fh:
        fh.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')} {args.status} {hm(elapsed)} "
                 f"budget {hm(budget + ext)} :: {args.note}\n")
    with LEDGER.open("a") as fh:
        fh.write(f"| {time.strftime('%Y-%m-%d %H:%M')} | {b['_id']} | {args.status} | "
                 f"{hm(elapsed)} / {hm(budget + ext)} | {args.artifact or 'none'} | {args.note} |\n")
    print(f"{b['_id']} {args.status} after {hm(elapsed)} of {hm(budget + ext)}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(prog="batch.py", description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status").set_defaults(fn=cmd_status)
    sub.add_parser("next").set_defaults(fn=cmd_next)
    p = sub.add_parser("start")
    p.add_argument("id")
    p.set_defaults(fn=cmd_start)
    p = sub.add_parser("check")
    p.add_argument("--json", action="store_true")
    p.set_defaults(fn=cmd_check)
    p = sub.add_parser("extend")
    p.add_argument("minutes", type=int)
    p.add_argument("why")
    p.set_defaults(fn=cmd_extend)
    p = sub.add_parser("close")
    p.add_argument("id")
    p.add_argument("status")
    p.add_argument("--note", default="")
    p.add_argument("--artifact", default="")
    p.add_argument("--force", action="store_true")
    p.set_defaults(fn=cmd_close)
    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())

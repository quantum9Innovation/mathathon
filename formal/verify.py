#!/usr/bin/env python3
"""Build the exported proof closure with bounded parallelism, then audit axioms."""
from __future__ import annotations

import argparse
import concurrent.futures
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def without_comments(source: str) -> str:
    """Remove Lean's nested block comments and line comments."""
    result: list[str] = []
    depth = 0
    position = 0
    while position < len(source):
        pair = source[position : position + 2]
        if pair == "/-":
            depth += 1
            position += 2
        elif depth and pair == "-/":
            depth -= 1
            position += 2
        elif depth:
            if source[position] == "\n":
                result.append("\n")
            position += 1
        elif pair == "--":
            end = source.find("\n", position)
            position = len(source) if end < 0 else end
        else:
            result.append(source[position])
            position += 1
    return "".join(result)


def module_imports(path: Path) -> list[str]:
    source = without_comments(path.read_text())
    imports: list[str] = []
    for line in source.splitlines():
        match = re.match(r"\s*(?:(?:public|private|meta)\s+)*import\s+(.+)", line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--all-local", action="store_true", help="also check unexported local modules")
    parser.add_argument("--no-audit", action="store_true")
    parser.add_argument("--resume-log", type=Path,
                        help="revalidate successful modules from an interrupted verification log")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")

    environment = dict(os.environ)
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    installed = Path.home() / ".elan/toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin"
    environment["PATH"] = str(installed) + os.pathsep + environment.get("PATH", "")
    lake = shutil.which("lake", path=environment["PATH"])
    if lake is None:
        raise SystemExit("Lake is unavailable; install the pinned Lean toolchain first")

    sources = {"HierarchicalAbsoluteSpectral": ROOT / "HierarchicalAbsoluteSpectral.lean"}
    for path in (ROOT / "HierarchicalAbsoluteSpectral").rglob("*.lean"):
        sources[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    for directory in (ROOT / "vendor/matmul", ROOT / "vendor/srht"):
        for path in directory.rglob("*.lean"):
            sources[".".join(path.relative_to(directory).with_suffix("").parts)] = path

    graph: dict[str, tuple[str, ...]] = {}
    active: set[str] = set()

    def visit(name: str) -> None:
        if name in active:
            raise ValueError(f"cyclic local imports at {name}")
        if name in graph:
            return
        active.add(name)
        dependencies = tuple(dep for dep in module_imports(sources[name]) if dep in sources)
        for dependency in dependencies:
            visit(dependency)
        active.remove(name)
        graph[name] = dependencies

    visit("HierarchicalAbsoluteSpectral")
    if args.all_local:
        for name in sorted(sources):
            if name.startswith("HierarchicalAbsoluteSpectral."):
                visit(name)

    for name in graph:
        source = without_comments(sources[name].read_text())
        forbidden = re.search(r"\b(?:sorry|admit|native_decide|sorryAx|skipKernelTC)\b|"
                              r"^\s*(?:unsafe\s+|axiom\s)", source, re.M)
        if forbidden:
            raise SystemExit(f"unpermitted proof escape in {sources[name]}: {forbidden.group(0)!r}")

    logs = ROOT / ".lake/build/verification"
    logs.mkdir(parents=True, exist_ok=True)

    def build(name: str) -> tuple[int, Path]:
        log = logs / f"{name}.log"
        with log.open("w") as output:
            completed = subprocess.run([lake, "-q", "build", name], cwd=ROOT, env=environment,
                                       stdout=output, stderr=subprocess.STDOUT)
        return completed.returncode, log

    pending = set(graph)
    done: set[str] = set()
    failed: set[str] = set()
    running: dict[concurrent.futures.Future, str] = {}
    print(f"Checking {len(graph)} proof modules with {args.jobs} compiler slots", flush=True)
    if args.resume_log:
        candidates = set(re.findall(r"^OK \d+/\d+ ([\w.]+)$",
                                    args.resume_log.read_text(), re.M)) & set(graph)
        # A previous success is only reused after Lake rehashes its entire
        # dependency closure and confirms every artifact is current.
        if candidates:
            cache_log = logs / "ResumeValidation.log"
            with cache_log.open("w") as output:
                checked_cache = subprocess.run(
                    [lake, "--rehash", "--no-build", "-q", "build", *sorted(candidates)],
                    cwd=ROOT, env=environment, stdout=output, stderr=subprocess.STDOUT)
            if checked_cache.returncode == 0:
                done.update(candidates)
                pending.difference_update(candidates)
                print(f"Revalidated {len(done)} current modules from {args.resume_log}", flush=True)
            else:
                print(f"Previous cache is stale; rebuilding in dependency order ({cache_log})", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            blocked = {name for name in pending if any(dep in failed for dep in graph[name])}
            pending.difference_update(blocked)
            failed.update(blocked)
            for name in sorted(pending):
                if len(running) >= args.jobs:
                    break
                if all(dep in done for dep in graph[name]):
                    running[pool.submit(build, name)] = name
                    pending.remove(name)
            if not running:
                break
            finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                code, log = future.result()
                if code:
                    failed.add(name)
                    print(f"FAILED {name}: {log}\n{log.read_text()[-12000:]}", flush=True)
                else:
                    done.add(name)
                    print(f"OK {len(done)}/{len(graph)} {name}", flush=True)
    if failed or pending:
        print(f"Verified {len(done)}; failed or blocked {len(failed | pending)}", flush=True)
        return 1

    # This final collective check catches a source/dependency edit that
    # happened while a long verification run was in progress.
    freshness = logs / "FinalFreshness.log"
    with freshness.open("w") as output:
        checked_freshness = subprocess.run(
            [lake, "--rehash", "--no-build", "-q", "build", *sorted(graph)],
            cwd=ROOT, env=environment, stdout=output, stderr=subprocess.STDOUT)
    if checked_freshness.returncode:
        print(f"Final source freshness check failed: {freshness}\n"
              f"{freshness.read_text()[-12000:]}", flush=True)
        return 1

    if not args.no_audit:
        audit = logs / "MainClosedAudit.log"
        with audit.open("w") as output:
            checked = subprocess.run([lake, "env", "lean", "MainClosedAudit.lean"], cwd=ROOT, env=environment,
                                     stdout=output, stderr=subprocess.STDOUT)
        audit_text = audit.read_text()
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        axiom_lists = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit_text, re.S)
        unexpected = {item.strip() for group in axiom_lists for item in group.split(",")} - allowed - {""}
        if checked.returncode or not axiom_lists or unexpected or "sorryAx" in audit_text:
            print(f"Axiom audit failed: {audit}\n{audit_text[-12000:]}", flush=True)
            return 1
        print(f"Axiom audit passed for {len(axiom_lists)} endpoints: {audit}", flush=True)
    print(f"Verified all {len(graph)} proof modules", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())

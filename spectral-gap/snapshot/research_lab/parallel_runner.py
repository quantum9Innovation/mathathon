"""Bounded parallel research controller."""

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
import uuid

import research_runner as engine
from checkpoint_transport import checkpoint_mcp_overrides, validate_schema, REPLY_SCHEMA, MAX_EVIDENCE_BYTES

ROOT = Path(__file__).resolve().parent
TERMINAL = {"completed", "limited", "failed", "time_limit", "unstarted_at_deadline"}
_EVIDENCE_SIGNATURES = {}


def read_json(path):
    return json.loads(Path(path).read_text())


def mark_deadline_tasks(state):
    for job in state["jobs"]:
        if job["status"] not in TERMINAL:
            job.update(status="time_limit" if job["calls"] else "unstarted_at_deadline",
                       error="Global deadline reached")


def validate_task_schedule(task):
    fraction = task.get("finish_by_fraction", 1)
    if type(fraction) not in (int, float) or not math.isfinite(fraction) or not 0 < fraction <= 1:
        raise ValueError("Task phase fraction must be positive and at most one")
    if type(task.get("finalization_only", False)) is not bool:
        raise ValueError("Task finalization flag must be boolean")
    if type(task.get("incremental_finalization", False)) is not bool:
        raise ValueError("Task incremental finalization flag must be boolean")
    if task.get("incremental_finalization", False) and (task.get("role") != "reporting" or
                                                       not task.get("finalization_only", False)):
        raise ValueError("Incremental finalization requires an explicit reporting finalization task")
    if task.get("dependency_context", "transitive") not in ("transitive", "direct"):
        raise ValueError("Task dependency context must be transitive or direct")
    deferred = task.get("deferred_inputs", [])
    if not isinstance(deferred, list) or any(not isinstance(name, str) for name in deferred):
        raise ValueError("Deferred inputs must be a list of unique source paths")
    if len(set(deferred)) != len(deferred):
        raise ValueError("Deferred inputs must be unique")
    for name in deferred:
        path = Path(name)
        if (path.is_absolute() or path.as_posix() != name or ".." in path.parts or
                len(path.parts) < 2 or path.parts[0] != "sources" or
                name == task["instruction"] or name not in task["inputs"]):
            raise ValueError("Deferred inputs must be safe source paths from the task inputs")


def checked_deferred_source(root, relative, expected_hash=None):
    root = Path(root).absolute()
    path = root
    for part in Path(relative).parts:
        path = path / part
        if path.is_symlink():
            raise ValueError("Deferred source paths cannot contain symbolic links")
    try:
        if not path.resolve(strict=True).is_relative_to(root.resolve()) or not path.is_file():
            raise ValueError("Deferred source must be a file inside its allowed input directory")
        if path.stat().st_size > MAX_EVIDENCE_BYTES:
            raise ValueError("Deferred source exceeds the complete evidence read limit")
        data = path.read_bytes()
    except OSError as error:
        raise ValueError("Deferred source is missing or unreadable") from error
    if len(data) > MAX_EVIDENCE_BYTES:
        raise ValueError("Deferred source exceeds the complete evidence read limit")
    if expected_hash is not None and hashlib.sha256(data).hexdigest() != expected_hash:
        raise ValueError("Frozen deferred source changed")
    return path, len(data)


def frozen_deferred_source(run_dir, job, name):
    validate_task_schedule(job)
    if name not in job.get("deferred_inputs", []) or name not in job["input_hashes"]:
        raise ValueError("Deferred source is outside the frozen task input allowlist")
    relative = Path("jobs") / job["id"] / "input" / name
    return checked_deferred_source(run_dir, relative, job["input_hashes"][name])


def prepare_run(plan_path, run_dir, minutes=60, profile_name="bounded", allow_large=False, network=None,
                reasoning_effort=None, service_tier=None):
    from model_policy import apply_run_overrides, load_profile, route_task
    profile = apply_run_overrides(load_profile(profile_name, allow_disabled=allow_large), reasoning_effort, service_tier)
    if type(minutes) is not int or not 1 <= minutes <= 180:
        raise ValueError("Minutes must be an integer from 1 to 180")
    if network is not None and network not in {"public_sources", "no_browsing", "offline"}:
        raise ValueError("Unknown network mode")
    plan_path, run_dir = Path(plan_path).resolve(), Path(run_dir).resolve()
    plan = read_json(plan_path)
    if minutes * 60 > min(profile["total_seconds"], plan.get("global_runtime_seconds", profile["total_seconds"])):
        raise ValueError("Requested duration exceeds the profile or task-plan ceiling")
    tasks = plan["tasks"]
    if not 0 < len(tasks) <= profile["max_total_tasks"]:
        raise ValueError("Task count exceeds the profile limit")
    identifiers = [task["id"] for task in tasks]
    if len(set(identifiers)) != len(tasks) or any(not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", name) for name in identifiers):
        raise ValueError("Task identifiers must be unique safe directory names")
    visited = set()
    while len(visited) < len(tasks):
        ready = [task for task in tasks if task["id"] not in visited and set(task["depends_on"]) <= visited]
        if not ready:
            raise ValueError("Task dependencies are cyclic or unknown")
        visited.update(task["id"] for task in ready)
    if run_dir.exists():
        raise ValueError("Run already exists, use resume without resetting the deadline")
    prepared = []
    for task in tasks:
        validate_task_schedule(task)
        sources = {}
        for name in set([task["instruction"]] + task["inputs"]):
            if not isinstance(name, str) or Path(name).is_absolute() or ".." in Path(name).parts or name == "worker_contract.md":
                raise ValueError("Task input name must be a safe relative path")
            source = (plan_path.parent / name).resolve()
            if not source.is_relative_to(plan_path.parent) or not source.is_file():
                raise ValueError("Task input must be a file inside its packet")
            if name in task.get("deferred_inputs", []):
                checked_deferred_source(plan_path.parent, name)
            sources[name] = source
        prepared.append((task, sources, route_task(task, profile)))
    config = read_json(ROOT / "pilot/config.json")
    config.update({key: profile[key] for key in ("model", "reasoning_effort", "billing", "network")})
    if "service_tier" in profile:
        config["service_tier"] = profile["service_tier"]
    config.update(experiment_id=run_dir.name, total_seconds=minutes * 60)
    if network is not None:
        config["network"] = network
    jobs = []
    for task, sources, route in prepared:
        directory = run_dir / "jobs" / task["id"] / "input"
        directory.mkdir(parents=True)
        for name, source in sources.items():
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read_bytes())
            target.chmod(0o444)
        contract = directory / "worker_contract.md"
        contract.write_bytes((ROOT / "pilot/prompts/contract.md").read_bytes())
        contract.chmod(0o444)
        hashes = {str(p.relative_to(directory)): engine.digest(p) for p in directory.rglob("*") if p.is_file()}
        jobs.append(dict(task, route=route, status="pending", calls=0, consumed_seconds=0,
                         max_calls=min(task.get("max_calls", profile["max_task_calls"]), profile["max_task_calls"]),
                         input_hashes=hashes))
    shutil.copy2(ROOT / "pilot/reply.schema.json", run_dir / "reply.schema.json")
    engine.atomic_json(run_dir / "plan.json", plan)
    state = {"created_at": time.time(), "started_at": None, "deadline": None, "status": "prepared",
             "profile_name": profile_name, "large_profile_authorized": allow_large,
             "profile": profile, "config": config, "jobs": jobs, "calls": 0,
             "report_bundle_version": 1,
             "schema_hash": engine.digest(run_dir / "reply.schema.json")}
    state["policy_hash"] = policy_hash(state)
    engine.atomic_json(run_dir / "state.json", state)
    return run_dir


def allocate_seconds(state, job, now=None):
    now = time.time() if now is None else now
    available = engine.remaining(state, now)
    profile = state["profile"]
    fraction = job.get("finish_by_fraction", 1)
    if state["started_at"] is not None:
        available = min(available, state["started_at"] + state["config"]["total_seconds"] * fraction - now)
    if not job["depends_on"] and "finish_by_fraction" not in job:
        available -= min(profile["review_reserve_seconds"], state["config"]["total_seconds"] / 3)
    unfinished = [item for item in state["jobs"] if item["status"] not in TERMINAL and
                  ("finish_by_fraction" not in job or item.get("finish_by_fraction", 1) == fraction)]

    def depth(identifier):
        children = [item for item in unfinished if identifier in item["depends_on"]]
        return 1 + max((depth(item["id"]) for item in children), default=0)

    waves = max(1, math.ceil(len(unfinished) / profile["max_parallel_workers"]), depth(job["id"]))
    fair_share = max(0, available) / waves
    return max(0, min(profile["call_seconds"], fair_share,
                      profile["max_task_seconds"] - job["consumed_seconds"]))


def policy_hash(state):
    immutable = {"config": {key: value for key, value in state["config"].items() if key != "runtime_image_id"},
                 "profile": state["profile"], "large_profile_authorized": state["large_profile_authorized"],
                 "jobs": [{key: job[key] for key in ("id", "role", "route", "max_calls", "depends_on", "input_hashes")} for job in state["jobs"]]}
    for frozen, job in zip(immutable["jobs"], state["jobs"]):
        for key in ("finish_by_fraction", "finalization_only", "incremental_finalization", "deferred_inputs", "dependency_context"):
            if key in job:
                frozen[key] = job[key]
    if "report_bundle_version" in state:
        immutable["report_bundle_version"] = state["report_bundle_version"]
    return hashlib.sha256(json.dumps(immutable, sort_keys=True).encode()).hexdigest()


def audit_run(run_dir, state):
    from model_policy import validate_profile, route_task
    validate_profile(state["profile"])
    if policy_hash(state) != state["policy_hash"]:
        raise ValueError("Frozen execution policy changed")
    if state["config"]["total_seconds"] > state["profile"]["total_seconds"]:
        raise ValueError("Run exceeds its profile duration ceiling")
    if not state["profile"]["enabled"] and not state["large_profile_authorized"]:
        raise ValueError("Disabled larger profile has not been activated")
    if engine.digest(run_dir / "reply.schema.json") != state["schema_hash"]:
        raise ValueError("Reply contract changed")
    for job in state["jobs"]:
        validate_task_schedule(job)
        if job["route"] != route_task(job, state["profile"]):
            raise ValueError("Worker route changed")
        directory = run_dir / "jobs" / job["id"] / "input"
        actual = {str(p.relative_to(directory)) for p in directory.rglob("*") if p.is_file()}
        if actual != set(job["input_hashes"]):
            raise ValueError("Unexpected worker input")
        for name in job.get("deferred_inputs", []):
            frozen_deferred_source(run_dir, job, name)
        for name, expected in job["input_hashes"].items():
            path = directory / name
            if path.is_symlink() or engine.digest(path) != expected:
                raise ValueError("Frozen worker input changed")


def harvest_checkpoints(run_dir, state):
    changed = False
    for job in state["jobs"]:
        receipts = sorted((run_dir / "jobs" / job["id"] / "calls").glob("*/checkpoints/checkpoint-*.json"))
        if not receipts:
            continue
        path = receipts[-1]
        relative = str(path.relative_to(run_dir))
        if relative == job.get("latest_checkpoint"):
            continue
        reply = read_json(path)
        validate_schema(reply, REPLY_SCHEMA)
        engine.validate_reply(reply)
        job["latest_checkpoint"] = relative
        job["checkpoint_count"] = len(receipts)
        changed = True
    return changed


def atomic_text(path, value):
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w") as stream:
        stream.write(value)
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def saved_evidence_records(run_dir, state):
    records = []
    for job in state["jobs"]:
        directory = run_dir / "jobs" / job["id"]
        paths = list((directory / "calls").glob("*/checkpoints/checkpoint-*.json"))
        for pattern in ("*/controller_reply.json", "*/validated.json"):
            paths.extend((directory / "calls").glob(pattern))
        if (directory / "submission.json").exists():
            paths.append(directory / "submission.json")
        for path in sorted(set(paths)):
            if path.is_symlink() or not path.resolve().is_relative_to(directory.resolve()):
                raise ValueError("Report evidence escapes its task directory")
            records.append((job["id"], path))
    return records


def write_evidence_index(run_dir, state):
    if not any(job.get("incremental_finalization", False) for job in state["jobs"]):
        return
    grouped = {job["id"]: [] for job in state["jobs"]}
    for identifier, path in saved_evidence_records(run_dir, state):
        reply = read_json(path)
        grouped[identifier].append({"path": str(path.relative_to(run_dir)), "sha256": engine.digest(path),
                                    "action": reply["action"], "summary": reply["summary"]})
    notice = "Saved records are claims and arguments, not mathematical certification."
    tasks = [{"id": job["id"], "execution_status": job["status"], "calls": job["calls"],
              "records": sorted(grouped[job["id"]], key=lambda record: record["path"])}
             for job in sorted(state["jobs"], key=lambda job: job["id"])]
    engine.atomic_json(run_dir / "EVIDENCE_INDEX.json", {"version": 1, "notice": notice, "tasks": tasks})
    lines = ["# Saved evidence index", "", notice, "",
             "This deterministic index includes every retained mathematical receipt. "
             "An explicit finish records task completion, not proof acceptance. "
             "[Complete saved arguments](EVIDENCE.md) remain available even if reporting emits nothing.", ""]
    for task in tasks:
        lines += [f"## {task['id']}", "", f"Execution status: {task['execution_status']}. Calls: {task['calls']}.", ""]
        for record in task["records"]:
            lines += [f"- [{record['path']}]({record['path']}), action {record['action']}, SHA256 {record['sha256']}."]
        if not task["records"]:
            lines += ["No mathematical receipt was saved."]
        lines.append("")
    atomic_text(run_dir / "EVIDENCE_INDEX.md", "\n".join(lines))


def write_evidence_bundle(run_dir, state):
    records = saved_evidence_records(run_dir, state)
    signature = tuple((str(path), path.stat().st_size, path.stat().st_mtime_ns) for _, path in records)
    if _EVIDENCE_SIGNATURES.get(str(run_dir)) == signature and (run_dir / "EVIDENCE.md").exists():
        return
    lines = ["# Saved research evidence", "",
             "All retained mathematical receipts are included below. Later plans and budget notes do not supersede earlier derivations. "
             "These are emitted claims and arguments, not automatic proof certification. "
             "Raw prompts, events, computations and transport records remain in their call directories.", ""]
    for identifier, path in records:
        reply = read_json(path)
        relative = str(path.relative_to(run_dir))
        lines += [f"## {identifier}: {relative}", "", f"[Raw record]({relative})", "",
                  reply["summary"], "", "Target: " + reply["target"], "", reply["argument"], "",
                  "Claims:", "", "```json", json.dumps(reply["claims"], indent=2), "```", "",
                  "Sources:", "", "```json", json.dumps(reply["sources"], indent=2), "```", "",
                  "Strongest objection: " + reply["strongest_objection"], "",
                  "Next action: " + reply["next_action"], ""]
        if reply.get("code"):
            lines += ["Recorded computation request:", "", "```python", reply["code"], "```", ""]
    atomic_text(run_dir / "EVIDENCE.md", "\n".join(lines))
    _EVIDENCE_SIGNATURES[str(run_dir)] = signature


def write_report(run_dir, state):
    write_evidence_index(run_dir, state)
    lines = ["# Parallel verification report", "", f"Execution status: {state['status']}", "",
             "Execution completeness and mathematical validity are separate. Read checked steps and objections.", "",
             f"Profile: {state['profile_name']}. Worker ceiling: {state['profile']['max_parallel_workers']}.",
             f"Calls reserved: {state['calls']}. Runtime cap: {state['config']['total_seconds']} seconds.", "",
             "[Complete saved mathematical evidence](EVIDENCE.md)", "",
             "This report is assembled from saved records even if the final worker is interrupted. "
             "A completed execution report does not mean the mathematical target is proved.", ""]
    if any(job.get("incremental_finalization", False) for job in state["jobs"]):
        lines += ["[Saved evidence index](EVIDENCE_INDEX.md). The index provides no mathematical certification.", ""]
    for job in state["jobs"]:
        lines += [f"## {job['id']}", "", f"Status: {job['status']}. Calls: {job['calls']}.",
                  f"Route: {job['route']['model']}, {job['route']['reasoning_effort']} reasoning.",
                  f"Durable tool checkpoints: {job.get('checkpoint_count', 0)}.", ""]
        path = job.get("final_reply") or job.get("latest_response") or job.get("latest_checkpoint")
        if path:
            reply = read_json(run_dir / path)
            lines += [reply["summary"], "", "Strongest objection: " + reply["strongest_objection"], "",
                      "Next action: " + reply["next_action"], "", f"[Saved evidence]({path})", ""]
        if job.get("error"):
            lines += ["Execution issue: " + job["error"], ""]
    write_evidence_bundle(run_dir, state)
    atomic_text(run_dir / "REPORT.md", "\n".join(lines))
    atomic_text(run_dir / "FINAL_REPORT.md", "\n".join(lines).replace("# Parallel verification report", "# Research run report", 1))


def apply_outcome(run_dir, job, outcome):
    job["consumed_seconds"] += outcome["transport"].get("seconds", 0)
    job["reserved_seconds"] = 0
    reply = outcome.get("reply")
    if reply is None and job.get("latest_checkpoint"):
        reply = read_json(run_dir / job["latest_checkpoint"])
    if reply is not None:
        validate_schema(reply, REPLY_SCHEMA)
        engine.validate_reply(reply)
        if reply["action"] == "finish":
            path = run_dir / "jobs" / job["id"] / "submission.json"
            engine.atomic_json(path, reply)
            job.update(status="completed", final_reply=str(path.relative_to(run_dir)))
            return
        if outcome.get("reply") is not None:
            path = run_dir / "jobs" / job["id"] / "calls" / job.get("active_call", uuid.uuid4().hex) / "controller_reply.json"
            engine.atomic_json(path, reply)
            job["latest_response"] = str(path.relative_to(run_dir))
    if outcome.get("error"):
        job["error"] = outcome["error"]
    job["status"] = "pending"


def run_jobs(run_dir, client=None, invoke=None, check_runtime=True):
    run_dir = Path(run_dir).resolve()
    invoke = execute_call if invoke is None else invoke
    client = str(client or ROOT / "runtime/subscription-client")
    with (run_dir / "controller.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        state = read_json(run_dir / "state.json")
        audit_run(run_dir, state)
        if state["status"] == "time_limit" and "finished_at" in state:
            if state.get("report_bundle_version") == 1:
                write_report(run_dir, state)
            return
        if state["status"] in {"completed_with_submissions", "partial_submissions"} and all(job["status"] in TERMINAL for job in state["jobs"]):
            if state.get("report_bundle_version") == 1:
                write_report(run_dir, state)
            return
        if (run_dir / "STOP").exists():
            raise ValueError("Explicit stop is present, use resume")
        if engine.remaining(state) <= 0:
            harvest_checkpoints(run_dir, state)
            mark_deadline_tasks(state)
            state["status"] = "time_limit"
            state["finished_at"] = time.time()
            engine.atomic_json(run_dir / "state.json", state)
            write_report(run_dir, state)
            return
        if check_runtime:
            engine.preflight(ROOT, state["config"], client)
        if state["started_at"] is None:
            state["started_at"] = time.time()
            state["deadline"] = state["started_at"] + state["config"]["total_seconds"]
        monotonic_deadline = time.monotonic() + engine.remaining(state)
        state["status"] = "running"
        engine.atomic_json(run_dir / "state.json", state)
        harvest_checkpoints(run_dir, state)
        outstanding = [job for job in state["jobs"] if job["status"] == "running"]
        lease_deadline = max((job.get("active_deadline", 0) for job in outstanding), default=0)
        while time.time() < min(lease_deadline, state["deadline"]):
            if (run_dir / "STOP").exists():
                state["status"] = "stopped"
                engine.atomic_json(run_dir / "state.json", state)
                write_report(run_dir, state)
                return
            state["status"] = "recovering_worker_leases"
            harvest_checkpoints(run_dir, state)
            engine.atomic_json(run_dir / "state.json", state)
            time.sleep(min(0.25, max(0, lease_deadline - time.time())))
        state["status"] = "running"
        for job in state["jobs"]:
            if job["status"] == "running":
                reservation = job.get("reserved_seconds")
                if reservation is None:
                    invocation = run_dir / "jobs" / job["id"] / "calls" / job.get("active_call", "") / "invocation.json"
                    reservation = read_json(invocation)["allowance_seconds"] if invocation.exists() else state["profile"]["call_seconds"]
                job["consumed_seconds"] += reservation
                job["reserved_seconds"] = 0
                job["status"] = "pending"
        running = {}
        stopping = None
        with ThreadPoolExecutor(max_workers=state["profile"]["max_parallel_workers"]) as pool:
            try:
                while True:
                    if (run_dir / "STOP").exists():
                        stopping = "stopped"
                    if min(engine.remaining(state), monotonic_deadline - time.monotonic()) <= 0:
                        stopping = "time_limit"
                    if harvest_checkpoints(run_dir, state):
                        engine.atomic_json(run_dir / "state.json", state)
                        write_report(run_dir, state)
                    if stopping:
                        for _, stop_file in running.values():
                            stop_file.touch()
                    else:
                        for job in sorted(state["jobs"], key=lambda item: (-item.get("priority", 0), item["calls"])):
                            if job["status"] != "pending":
                                continue
                            if job["calls"] >= job["max_calls"] or state["calls"] >= state["profile"]["max_total_calls"]:
                                job.update(status="limited", error="Call allowance exhausted")
                                continue
                            dependencies = [item for item in state["jobs"] if item["id"] in job["depends_on"]]
                            if any(item["status"] not in TERMINAL for item in dependencies):
                                continue
                            seconds = min(allocate_seconds(state, job), monotonic_deadline - time.monotonic())
                            if seconds <= 1:
                                job.update(status="limited", error="Time protected for downstream review or task allowance exhausted")
                                continue
                            if len(running) >= state["profile"]["max_parallel_workers"]:
                                break
                            job["calls"] += 1
                            state["calls"] += 1
                            call_id = f"{job['calls']:03d}-{uuid.uuid4().hex[:8]}"
                            directory = run_dir / "jobs" / job["id"] / "calls" / call_id
                            directory.mkdir(parents=True)
                            stop_file = directory / "STOP"
                            job.update(status="running", active_call=call_id, active_deadline=time.time() + seconds + 2,
                                       reserved_seconds=seconds)
                            engine.atomic_json(run_dir / "state.json", state)
                            if job.get("incremental_finalization", False):
                                write_evidence_index(run_dir, state)
                            snapshot = json.loads(json.dumps(state))
                            snapshot["client"] = client
                            running[pool.submit(invoke, run_dir, snapshot, dict(job), call_id, seconds, stop_file)] = (job, stop_file)
                    engine.atomic_json(run_dir / "state.json", state)
                    write_report(run_dir, state)
                    if not running:
                        if stopping or all(job["status"] in TERMINAL for job in state["jobs"]):
                            break
                        continue
                    done, _ = wait(running, timeout=0.25, return_when=FIRST_COMPLETED)
                    for future in done:
                        job, _ = running.pop(future)
                        try:
                            outcome = future.result()
                            harvest_checkpoints(run_dir, state)
                            apply_outcome(run_dir, job, outcome)
                            if outcome.get("service_error"):
                                stopping = "service_stopped"
                        except Exception as error:
                            job["consumed_seconds"] += job.get("reserved_seconds", 0)
                            job["reserved_seconds"] = 0
                            job.update(status="failed", error=str(error))
                        job["last_call_finished_at"] = time.time()
                if stopping:
                    state["status"] = stopping
                else:
                    state["status"] = ("completed_with_submissions" if all(job["status"] == "completed" for job in state["jobs"])
                                       else "partial_submissions")
            except BaseException:
                for _, stop_file in running.values():
                    stop_file.touch()
                state["status"] = "interrupted"
                raise
            finally:
                harvest_checkpoints(run_dir, state)
                if state["status"] == "time_limit":
                    mark_deadline_tasks(state)
                state["finished_at"] = time.time()
                engine.atomic_json(run_dir / "state.json", state)
                write_report(run_dir, state)


def call_prompt(run_dir, state, job, seconds):
    inputs = run_dir / "jobs" / job["id"] / "input"
    deferred_sources = {name: frozen_deferred_source(run_dir, job, name) for name in job.get("deferred_inputs", [])}
    incremental = job.get("incremental_finalization", False)
    finalize = (job.get("finalization_only", False) or seconds <= 180 or
                (job["calls"] >= job["max_calls"] and
                 (job["calls"] > 1 or bool(job.get("latest_checkpoint") or job.get("latest_response")))))
    pieces = [f"Task identifier: {job['id']}. Role: {job['role']}.",
              f"This is call {max(1, job['calls'])} of at most {job['max_calls']} for this task.",
              f"This call has at most {seconds:.0f} seconds. All work shares a fixed experiment deadline.",
              ("INCREMENTAL FINALIZATION ONLY. Metadata discovery needed to locate checkpoint tools is permitted first. "
               "Your first substantive action must use save_checkpoint with action=checkpoint for a concise useful result "
               "from the supplied evidence, with an actual checked implication, exact record references and honest gaps. "
               "An initialization note or a promise to assemble later is insufficient. "
               "Then save incremental assembly of reporting sections with action=checkpoint, preserving earlier checked work. "
               "Use action=finish explicitly only when the best available reconciliation is saved, with unresolved premises named. "
               "A complete result may finish immediately. Do not restart the investigation or perform new research or computation. "
               "After the initial save, retrieve only specific essential proof receipts needed to check a reported implication. "
               "The controller publishes EVIDENCE_INDEX.json and EVIDENCE_INDEX.md before reporting. "
               "This evidence index and completed execution provide no mathematical certification. "
               if incremental else
               "FINALIZATION ONLY. Your first external action must publish the best available complete result "
               "using save_checkpoint with action=finish, with honest unresolved claims and exact saved-step references. "
               "Do not restart the investigation or replace prior checked work with an initialization note. "
               "Do not begin a broad source search, computation or evidence reread. "
               "If one essential receipt is missing, identify that exact gap instead of claiming it checked. "
               "Finishing the task does not mean the mathematical target is proved. "
               if finalize else
               "Your first external action must call save_checkpoint with your exact target, plan, and current gaps. ") +
              "Save a new checkpoint after each checked implication and before a long calculation. "
              f"Aim for a receipt every {state['profile']['checkpoint_seconds']} seconds. "
              "The checkpoint tool writes through to durable storage during this call. Its remaining_budget tool reports time left. "
              "When fewer than 90 seconds remain, save the best current argument and finish with honest gaps. "
              "A stall watchdog can interrupt the session. Un-emitted reasoning cannot be recovered. "
              "Always use the exact structured response schema for both checkpoints and final output."]
    if job["calls"] >= job["max_calls"]:
        pieces.append("This is the last permitted call. Deliver the strongest concise final result before its deadline. "
                      "Use exact saved-step references for already checked work and focus on unresolved dependencies. "
                      "State unresolved gaps explicitly rather than restarting the entire investigation.")
    for name in [job["instruction"], *sorted(set(job["input_hashes"]) - {job["instruction"]})]:
        if name in job.get("deferred_inputs", []):
            path, size = deferred_sources[name]
            pieces.append(f"Deferred source {name}. Evidence id: {path.relative_to(run_dir)}. "
                          f"bytes: {size}. sha256: {job['input_hashes'][name]}. "
                          "Read this source with read_evidence after the initial checkpoint and before consequential use. "
                          "During finalization only, identify unread essential evidence as a gap without starting new research.")
        else:
            pieces.append(f"Supplied input {name}:\n" + (inputs / name).read_text())
    direct = job.get("dependency_context", "transitive") == "direct"
    ancestors = set()

    def include(identifier):
        parent = next(item for item in state["jobs"] if item["id"] == identifier)
        for dependency in parent["depends_on"]:
            include(dependency)
        ancestors.add(identifier)

    for dependency in job["depends_on"]:
        if direct:
            ancestors.add(dependency)
        else:
            include(dependency)
    if direct:
        pieces.append("Only immediate dependency records are supplied below. All original ancestor proof receipts "
                      "and permitted deferred sources remain available through list_evidence and read_evidence. " +
                      ("Complete available branch reviews appear below before your first finish checkpoint. "
                       "Reconcile these records without new research and name any missing essential evidence as a gap."
                       if finalize and not incremental else
                       "Read original ancestor proofs after the initial checkpoint whenever needed before consequential use. "
                       "A dependency summary does not certify an unseen argument."))
    for parent in state["jobs"]:
        if parent["id"] in ancestors:
            label = ""
            if direct:
                final = parent.get("final_reply")
                complete = False
                if final and (run_dir / final).is_file():
                    reply = read_json(run_dir / final)
                    validate_schema(reply, REPLY_SCHEMA)
                    engine.validate_reply(reply)
                    complete = reply["action"] == "finish"
                keys = ("final_reply",) if complete else ("latest_response", "latest_checkpoint")
                label = ", record status complete" if complete else ", record status incomplete"
            else:
                keys = ("latest_response", "latest_checkpoint", "final_reply")
            paths = list(dict.fromkeys(parent.get(key) for key in keys if parent.get(key)))
            if direct and not complete and paths:
                paths = [max(paths, key=lambda path: ((run_dir / path).stat().st_mtime_ns,
                                                      path == parent.get("latest_checkpoint")))]
            pieces.append(f"Earlier task {parent['id']}, execution status {parent['status']}{label}:\n" +
                          ("\n\n".join((run_dir / path).read_text() for path in paths) if paths else "No mathematical checkpoint was produced"))
    if job.get("latest_checkpoint"):
        pieces.append("Your prior saved work, not automatically verified:\n" + (run_dir / job["latest_checkpoint"]).read_text())
    if job.get("latest_response"):
        pieces.append("Your most recent validated returned response:\n" + (run_dir / job["latest_response"]).read_text())
    if job.get("error"):
        pieces.append("Prior execution issue: " + job["error"])
    for path in sorted((run_dir / "jobs" / job["id"] / "calls").glob("*/compute.*")):
        if path.suffix in {".json", ".log"}:
            pieces.append(f"Recorded computation {path.name}:\n" + path.read_text(errors="replace"))
    return "\n\n".join(pieces)


def evidence_manifest(run_dir, state, job):
    allowed = {job["id"]}

    def include(identifier):
        parent = next(item for item in state["jobs"] if item["id"] == identifier)
        for dependency in parent["depends_on"]:
            include(dependency)
        allowed.add(identifier)

    for dependency in job["depends_on"]:
        include(dependency)
    manifest = {}
    for identifier in allowed:
        parent = next(item for item in state["jobs"] if item["id"] == identifier)
        directory = run_dir / "jobs" / identifier
        paths = list((directory / "calls").glob("*/checkpoints/checkpoint-*.json"))
        for pattern in ("*/controller_reply.json", "*/validated.json", "*/compute.json", "*/compute.log"):
            paths.extend((directory / "calls").glob(pattern))
        if (directory / "submission.json").exists():
            paths.append(directory / "submission.json")
        for path in paths:
            if path.is_symlink() or not path.resolve().is_relative_to(directory.absolute()):
                raise ValueError("Evidence entry escapes its allowed task directory")
            manifest[str(path.relative_to(run_dir))] = str(path.resolve())
        for name in parent.get("deferred_inputs", []):
            path, _ = frozen_deferred_source(run_dir, parent, name)
            manifest[str(path.relative_to(run_dir))] = {"path": str(path), "sha256": parent["input_hashes"][name]}
    return manifest


def execute_call(run_dir, state, job, call_id, seconds, stop_file):
    started = time.monotonic()
    directory = run_dir / "jobs" / job["id"] / "calls" / call_id
    directory.mkdir(parents=True, exist_ok=True)
    checkpoints = directory / "checkpoints"
    checkpoints.mkdir(exist_ok=True)
    output = directory / "reply.json"
    prompt = call_prompt(run_dir, state, job, seconds)
    prompt += ("\n\nUse list_evidence and read_evidence for earlier individual checkpoint derivations or computation receipts. "
               "Only your own earlier evidence and the permitted dependency evidence are listed. "
               "A summary or a reference to an unseen step does not substitute for checking that step. "
               "Read results explicitly marked truncated are incomplete evidence.")
    (directory / "prompt.md").write_text(prompt)
    config = dict(state["config"], **job["route"])
    command = engine.worker_command(state["client"], config, run_dir / "jobs" / job["id"] / "input",
                                    run_dir / "reply.schema.json", output)
    manifest_path = directory / "evidence_manifest.json"
    engine.atomic_json(manifest_path, evidence_manifest(run_dir, state, job))
    command = command[:-1] + ["-c", "project_doc_max_bytes=0"] + checkpoint_mcp_overrides(checkpoints, time.time() + seconds, manifest_path) + command[-1:]
    if shutil.which("timeout") is None:
        raise ValueError("Independent process timeout executable is required")
    command = ["timeout", "--signal=TERM", "--kill-after=1", str(seconds), *command]
    engine.atomic_json(directory / "invocation.json", {"route": job["route"], "allowance_seconds": seconds,
                                                      "started_at": time.time(), "checkpoint_directory": "checkpoints"})
    finished = threading.Event()
    watchdog = {}

    def monitor():
        while not finished.wait(0.25):
            paths = list(checkpoints.glob("checkpoint-*.json"))
            newest = max((path.stat().st_mtime for path in paths), default=time.time() - (time.monotonic() - started))
            if (run_dir / "STOP").exists():
                watchdog["reason"] = "operator_stop"
            elif sum(path.stat().st_size for path in paths) > 4 * 1024 * 1024:
                watchdog["reason"] = "checkpoint_storage_limit"
            elif time.time() - newest > state["profile"]["checkpoint_seconds"] + state["profile"]["checkpoint_grace_seconds"]:
                watchdog["reason"] = "checkpoint_stall"
            if watchdog:
                stop_file.touch()
                break

    supervisor = threading.Thread(target=monitor, daemon=True)
    supervisor.start()
    try:
        transport = engine.bounded_run(command, prompt, directory / "events.jsonl", seconds,
                                       config["event_log_bytes"], stop_file=stop_file)
    finally:
        finished.set()
        supervisor.join(timeout=1)
    transport.update(watchdog)
    engine.atomic_json(directory / "transport.json", transport)
    outcome = {"transport": transport, "reply": None}
    if output.exists():
        try:
            if output.stat().st_size > config["event_log_bytes"]:
                raise ValueError("Final response exceeds storage limit")
            reply = read_json(output)
            validate_schema(reply, REPLY_SCHEMA)
            outcome["reply"] = engine.validate_reply(reply)
            engine.atomic_json(directory / "validated.json", reply)
            if reply["action"] == "compute":
                script = directory / "computation.py"
                script.write_text(reply["code"])
                allowance = min(config["computation_seconds"], engine.remaining(state), seconds - (time.monotonic() - started))
                if allowance >= 1 and not stop_file.exists():
                    compute_config = dict(config, computation_seconds=int(allowance))
                    result = engine.bounded_run(engine.container_command(compute_config, script), "", directory / "compute.log",
                                                 allowance, config["computation_output_bytes"], stop_file=stop_file)
                    engine.atomic_json(directory / "compute.json", result)
        except (ValueError, OSError) as error:
            outcome["error"] = "Invalid final response: " + str(error)
    elif transport["reason"] == "completed" and transport["returncode"] not in {0, 124, 137}:
        outcome.update(service_error=True, error="Subscription transport stopped, inspect saved events")
    transport["seconds"] = time.monotonic() - started
    engine.atomic_json(directory / "transport.json", transport)
    return outcome


def main():
    parser = argparse.ArgumentParser(description="Bounded parallel mathematical verification")
    parser.add_argument("command", choices=("prepare", "start", "run", "resume", "stop", "status", "audit"))
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--minutes", type=int, default=60)
    parser.add_argument("--profile", default="bounded", choices=("bounded", "many"))
    parser.add_argument("--activate-large-profile", action="store_true")
    parser.add_argument("--reasoning-effort", choices=("high", "xhigh"))
    parser.add_argument("--service-tier", choices=("fast",))
    parser.add_argument("--network", choices=("public_sources", "no_browsing", "offline"))
    parser.add_argument("--client", type=Path, default=ROOT / "runtime/subscription-client")
    args = parser.parse_args()
    if args.network is not None and args.command != "prepare":
        parser.error("Network mode is frozen during prepare")
    if (args.reasoning_effort is not None or args.service_tier is not None) and args.command != "prepare":
        parser.error("Run effort and speed are frozen during prepare")
    directory = args.run_dir.resolve()
    if args.command == "prepare":
        if args.plan is None:
            parser.error("prepare requires --plan")
        print(prepare_run(args.plan, directory, args.minutes, args.profile, args.activate_large_profile, args.network,
                          args.reasoning_effort, args.service_tier))
        return
    if args.command == "stop":
        (directory / "STOP").touch()
        print("Stop requested, durable checkpoints will be retained")
        return
    state = read_json(directory / "state.json")
    if (directory / "open_math" / "plan.json").exists() and args.command in {"start", "run", "resume"}:
        raise ValueError("Open Math native run: use open_math_native.py, not the subscription executor")
    if args.command == "audit":
        audit_run(directory, state)
        print("Frozen inputs verified")
    elif args.command == "status":
        print(json.dumps({"status": state["status"], "remaining_seconds": engine.remaining(state),
                          "started_at": state["started_at"], "deadline": state["deadline"],
                          "jobs": [{key: job.get(key) for key in ("id", "status", "calls", "checkpoint_count", "route")} for job in state["jobs"]]}, indent=2))
    elif args.command == "start":
        audit_run(directory, state)
        engine.preflight(ROOT, state["config"], args.client)
        if (directory / "STOP").exists() or engine.remaining(state) <= 0:
            raise ValueError("Run is stopped or expired")
        logfile = directory / f"controller-{uuid.uuid4().hex[:8]}.log"
        with logfile.open("xb") as output:
            process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "run", "--run-dir", str(directory),
                                        "--client", str(args.client)], stdin=subprocess.DEVNULL, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        engine.atomic_json(directory / "launch.json", {"pid": process.pid, "log": logfile.name, "time": time.time()})
        print(f"Started bounded parallel controller, pid {process.pid}")
    else:
        if args.command == "resume":
            (directory / "STOP").unlink(missing_ok=True)
        run_jobs(directory, client=args.client)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(f"Cannot proceed: {error}", file=sys.stderr)
        sys.exit(2)

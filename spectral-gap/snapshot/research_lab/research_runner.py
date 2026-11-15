"""Bounded research experiment controller."""

import hashlib
import argparse
import fcntl
import json
import os
from pathlib import Path
import random
import re
import shutil
import selectors
import signal
import subprocess
import sys
import tempfile
import uuid
import time

ROOT = Path(__file__).resolve().parent


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)
    descriptor = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(root=ROOT, minutes=None):
    root = Path(root)
    config = json.loads((root / "pilot/config.json").read_text())
    defaults = json.loads((ROOT / "defaults.json").read_text())
    config.update({key: defaults[key] for key in ("model", "reasoning_effort", "billing")})
    validate_config(config)
    if minutes is not None:
        if type(minutes) is not int or not 1 <= minutes <= 180:
            raise ValueError("Preparation minutes must be an integer from 1 to 180")
        scale = minutes * 60 / config["total_seconds"]
        config["arm_seconds"] = max(3, int(config["arm_seconds"] * scale))
        config["workflow_solver_seconds"] = max(1, int(config["workflow_solver_seconds"] * scale))
        config["workflow_reconstruction_seconds"] = max(1, int(config["workflow_reconstruction_seconds"] * scale))
        config["workflow_critique_seconds"] = (config["arm_seconds"] - config["workflow_solver_seconds"] -
                                               config["workflow_reconstruction_seconds"])
        config["checkpoint_reserve_seconds"] = max(1, int(config["checkpoint_reserve_seconds"] * scale))
        config["call_seconds"] = max(config["call_seconds"], config["arm_seconds"])
        config["total_seconds"] = minutes * 60
        config["preparation_minutes"] = minutes
        validate_config(config)
    directory = root / "runs" / config["experiment_id"]
    if directory.exists():
        raise ValueError("Experiment already exists, use resume or choose a new experiment id")
    order = [(case, condition) for case in ("a", "b", "c")
             for condition in ("baseline", "workflow")]
    random.Random(config["seed"]).shuffle(order)
    arms = []
    for index, (case, condition) in enumerate(order, 1):
        identifier = f"arm_{index:02d}"
        inputs = directory / identifier / "input"
        inputs.mkdir(parents=True)
        mapping = {
            "task.md": root / f"pilot/cases/case_{case}.md",
            "instruction.md": root / f"pilot/prompts/{condition}.md",
            "contract.md": root / "pilot/prompts/contract.md",
        }
        hashes = {}
        for name, source in mapping.items():
            target = inputs / name
            target.write_bytes(source.read_bytes())
            target.chmod(0o444)
            hashes[name] = digest(target)
        phases = [{"name": "solve", "seconds": config["arm_seconds"],
                   "max_calls": config["baseline_calls"], "status": "pending"}]
        if condition == "workflow":
            phases = [
                {"name": "solve", "seconds": config["workflow_solver_seconds"],
                 "max_calls": config["workflow_solver_calls"], "status": "pending"},
                {"name": "reconstruct", "seconds": config["workflow_reconstruction_seconds"],
                 "max_calls": config["review_calls"], "status": "pending"},
                {"name": "critique", "seconds": config["workflow_critique_seconds"],
                 "max_calls": config["review_calls"], "status": "pending"},
            ]
        arms.append({"id": identifier, "case": case, "condition": condition,
                     "input_hashes": hashes, "phases": phases})
    frozen = {str(p.relative_to(root)): digest(p) for name in ("pilot", "sources")
              for p in sorted((root / name).rglob("*")) if p.is_file()}
    state = {"created_at": time.time(), "started_at": None, "deadline": None,
             "config": config, "pilot_hashes": frozen, "arms": arms, "status": "prepared"}
    atomic_json(directory / "state.json", state)
    return directory


def validate_config(config):
    identifier = config["experiment_id"]
    if not isinstance(identifier, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", identifier):
        raise ValueError("Experiment id must be a single directory name")
    if not 0 < config["total_seconds"] <= 10800:
        raise ValueError("Experiment runtime must be positive and at most three hours")
    if config["billing"] != "subscription_only":
        raise ValueError("Only subscription use is authorized")
    if config["network"] not in {"public_sources", "no_browsing", "offline"}:
        raise ValueError("Unknown network mode")
    if sum(config[k] for k in ("workflow_solver_seconds", "workflow_reconstruction_seconds",
                               "workflow_critique_seconds")) != config["arm_seconds"]:
        raise ValueError("Workflow phases must fit the same total allowance as baseline")
    if config["workflow_solver_calls"] + 2 * config["review_calls"] != config["baseline_calls"]:
        raise ValueError("Both conditions must have equal total call allowances")
    for key, value in config.items():
        if isinstance(value, (int, float)) and key != "seed" and value <= 0:
            raise ValueError(f"Positive limit required: {key}")


def remaining(state, now=None):
    now = time.time() if now is None else now
    if state["deadline"] is None:
        return state["config"]["total_seconds"]
    return max(0, state["deadline"] - now)


def validate_reply(reply):
    text_fields = ("summary", "target", "argument", "strongest_objection", "next_action", "code")
    if not isinstance(reply, dict) or reply.get("action") not in {"checkpoint", "compute", "finish"}:
        raise ValueError("Invalid reply action")
    if any(not isinstance(reply.get(key), str) for key in text_fields):
        raise ValueError("Missing reply text fields")
    if not isinstance(reply.get("claims"), list) or not isinstance(reply.get("sources"), list):
        raise ValueError("Claims and sources must be lists")
    seen = set()
    for claim in reply["claims"]:
        if not isinstance(claim, dict) or claim.get("status") not in {
                "sourced", "derived", "conjectural", "blocked"}:
            raise ValueError("Only provisional claim classifications are allowed")
        if any(not isinstance(claim.get(k), str) for k in
               ("id", "statement", "evidence", "objection")):
            raise ValueError("Incomplete claim")
        if not claim["id"] or claim["id"] in seen or not isinstance(claim.get("dependencies"), list):
            raise ValueError("Claim ids must be unique and dependencies must be listed")
        seen.add(claim["id"])
    for source in reply["sources"]:
        if not isinstance(source, dict) or any(not isinstance(source.get(k), str) for k in
                ("title", "url", "pinpoint", "supports")) or not isinstance(source.get("checked"), bool):
            raise ValueError("Incomplete source receipt")
    if reply["action"] == "compute" and not reply["code"].strip():
        raise ValueError("Compute request needs code")
    return reply


def worker_command(client, config, directory, schema, output):
    if config["network"] == "offline":
        raise ValueError("Strict offline blocks remote subscription inference as well as browsing")
    if config["network"] not in {"public_sources", "no_browsing"}:
        raise ValueError("Unknown network mode")
    if config.get("billing") != "subscription_only":
        raise ValueError("Only the existing subscription is authorized")
    command = [str(client), "exec", "--ignore-user-config", "--ephemeral",
               "--skip-git-repo-check", "--json",
               "--output-schema", str(schema), "--output-last-message", str(output),
               "--cd", str(directory), "-c", 'approval_policy="never"',
               "-c", 'web_search="live"' if config["network"] == "public_sources"
               else 'web_search="disabled"', "-c", 'mcp_servers={}',
               "-c", 'default_permissions="research-packet"',
               "-c", 'permissions={research-packet={filesystem={":root"="deny",":minimal"="read",":tmpdir"="deny",":slash_tmp"="deny",' +
               json.dumps(str(Path(directory).resolve())) + '="read"},network={enabled=false}}}',
               "-c", 'apps._default.enabled=false',
               "-c", f"model_reasoning_effort={json.dumps(config.get('reasoning_effort', 'high'))}"]
    if "service_tier" in config:
        if config["service_tier"] != "fast":
            raise ValueError("Unsupported worker service tier")
        command += ["-c", 'service_tier="fast"', "-c", "features.fast_mode=true"]
    disabled = ("shell_tool", "unified_exec",
                "apps", "plugins", "hooks", "plugin_hooks", "multi_agent",
                "multi_agent_v2", "browser_use", "computer_use", "view_image",
                "artifact", "workspace_dependencies", "skill_search", "memories",
                "goals", "image_generation", "tool_suggest", "sleep_tool")
    for feature in disabled:
        command += ["-c", f"features.{feature}=false"]
    command += ["-c", "features.skip_host_skill_discovery=true"]
    command += ["-c", "features.code_mode_host=true",
                "-c", 'features.code_mode={enabled=true,excluded_tool_namespaces=["functions","collaboration","image_gen"]}']
    if config.get("model"):
        command += ["--model", config["model"]]
    return command + ["-"]


def container_command(config, script):
    return ["podman", "run", "--rm", "--pull=never", "--network=none", "--read-only",
            "--cap-drop=all", "--security-opt=no-new-privileges", "--userns=keep-id",
            f"--memory={config['computation_memory']}",
            f"--pids-limit={config['computation_pids']}",
            f"--timeout={config['computation_seconds']}",
            f"--ulimit=cpu={config['computation_seconds']}:{config['computation_seconds']}",
            "--tmpfs=/tmp:rw,noexec,nosuid,size=16m", "--env", "PYTHONDONTWRITEBYTECODE=1",
            "--volume", f"{Path(script).resolve()}:/task.py:ro",
            config.get("runtime_image_id", config["container_image"]), "python3", "/task.py"]


def bounded_run(command, prompt, logfile, seconds, max_bytes, stop_file=None):
    started = time.monotonic()
    reason = "completed"
    count = 0
    logfile.parent.mkdir(parents=True, exist_ok=True)
    allowed = {"HOME", "PATH", "LANG", "LC_ALL", "USER", "LOGNAME", "TERM", "XDG_RUNTIME_DIR"}
    environment = {key: value for key, value in os.environ.items() if key in allowed}
    with tempfile.TemporaryFile() as input_stream, logfile.open("xb") as log:
        input_stream.write(prompt.encode())
        input_stream.seek(0)
        process = subprocess.Popen(command, stdin=input_stream, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, env=environment, start_new_session=True)
        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ)
        try:
            while selector.get_map() or process.poll() is None:
                if time.monotonic() - started >= seconds:
                    reason = "timeout"
                    break
                if stop_file is not None and Path(stop_file).exists():
                    reason = "stopped"
                    break
                for key, _ in selector.select(timeout=0.1):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    room = max(0, max_bytes - count)
                    log.write(chunk[:room])
                    log.flush()
                    count += min(len(chunk), room)
                    if len(chunk) > room:
                        reason = "output_limit"
                        break
                if reason != "completed":
                    break
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=min(1, max(0, seconds - (time.monotonic() - started))))
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
            os.set_blocking(process.stdout.fileno(), False)
            while count < max_bytes:
                try:
                    chunk = os.read(process.stdout.fileno(), min(65536, max_bytes - count))
                except BlockingIOError:
                    break
                if not chunk:
                    break
                log.write(chunk)
                count += len(chunk)
            log.flush()
            os.fsync(log.fileno())
        except BaseException:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
        finally:
            selector.close()
            process.stdout.close()
    return {"reason": reason, "returncode": process.returncode,
            "seconds": time.monotonic() - started, "bytes": count}


def computation_evidence(checkpoint):
    pieces = []
    for suffix in (".compute.log", ".compute.result.json"):
        path = checkpoint.with_name(checkpoint.name.replace(".checkpoint.json", suffix))
        if path.exists():
            pieces.append(f"Recorded computation {path.name}:\n" + path.read_text(errors="replace"))
    return pieces


def phase_prompt(root, directory, arm, phase):
    folder = directory / arm["id"]
    inputs = folder / "input"
    pieces = [(inputs / "task.md").read_text(), (inputs / "contract.md").read_text()]
    if phase["name"] == "solve":
        pieces.append((inputs / "instruction.md").read_text())
    else:
        pieces.append((root / f"pilot/prompts/{phase['name']}.md").read_text())
    if phase["name"] == "critique":
        for role in ("solve", "reconstruct"):
            path = folder / f"{role}.final.json"
            if not path.exists():
                path = folder / f"{role}.latest.json"
            pieces.append(f"{role} provisional result:\n" +
                          (path.read_text() + ("\nIncomplete checkpoint" if ".latest." in path.name else "")
                           if path.exists() else "No valid result was produced"))
            for checkpoint in sorted((folder / role).glob("*.checkpoint.json")):
                pieces.extend(computation_evidence(checkpoint))
    history = sorted((folder / phase["name"]).glob("*.checkpoint.json"))
    for checkpoint in history:
        pieces.append("Prior saved checkpoint:\n" + checkpoint.read_text())
        pieces.extend(computation_evidence(checkpoint))
    return "\n\n".join(pieces)


def run_phase(root, directory, state, arm, phase, client, invoke=bounded_run):
    terminal = {"completed", "call_limit", "time_limit", "failed", "invalid_reply", "output_limit"}
    phase.pop("transport_failure", None)
    if phase["status"] in terminal:
        return
    config = state["config"]
    folder = directory / arm["id"] / phase["name"]
    folder.mkdir(parents=True, exist_ok=True)
    phase.setdefault("started_at", time.time())
    phase.setdefault("deadline", phase["started_at"] + phase["seconds"])
    phase.setdefault("calls", 0)
    phase["status"] = "running"
    atomic_json(directory / "state.json", state)

    while phase["calls"] < phase["max_calls"]:
        if (directory / "STOP").exists():
            phase["status"] = "interrupted"
            break
        available = min(remaining(state), phase["deadline"] - time.time())
        if available <= 1:
            phase["status"] = "time_limit"
            break
        call_id = f"{phase['calls'] + 1:02d}-{uuid.uuid4().hex[:8]}"
        prefix = folder / call_id
        output = prefix.with_suffix(".reply.json")
        prompt = phase_prompt(root, directory, arm, phase)
        reserve = config["checkpoint_reserve_seconds"]
        if remaining(state) <= reserve or available <= 60 or phase["calls"] + 1 == phase["max_calls"]:
            prompt += "\nFinalize now with your strongest saved evidence, gaps, and next decision."
        command = worker_command(client, config, directory / arm["id"] / "input",
                                 root / "pilot/reply.schema.json", output)
        prefix.with_suffix(".prompt.md").write_text(prompt)
        phase["calls"] += 1
        phase["active_call"] = call_id
        atomic_json(directory / "state.json", state)
        result = invoke(command, prompt, prefix.with_suffix(".events.jsonl"),
                        min(available, config["call_seconds"]), config["event_log_bytes"],
                        stop_file=directory / "STOP")
        atomic_json(prefix.with_suffix(".transport.json"), result)
        if result["reason"] != "completed" or result["returncode"] != 0:
            phase["status"] = "output_limit" if result["reason"] == "output_limit" else "interrupted"
            if remaining(state) <= 0 or phase["deadline"] <= time.time():
                phase["status"] = "time_limit"
            if phase["status"] == "time_limit" and result["reason"] == "timeout":
                phase["budget_stop"] = result
            else:
                phase["transport_failure"] = result
            break
        try:
            if output.stat().st_size > config["event_log_bytes"]:
                raise ValueError("Reply exceeds output budget")
            reply = validate_reply(json.loads(output.read_text()))
        except (ValueError, OSError) as error:
            phase["status"] = "invalid_reply"
            phase["error"] = str(error)
            break
        atomic_json(prefix.with_suffix(".checkpoint.json"), reply)
        atomic_json(directory / arm["id"] / f"{phase['name']}.latest.json", reply)
        if reply["action"] == "compute":
            script = prefix.with_suffix(".py")
            script.write_text(reply["code"])
            seconds = min(config["computation_seconds"], remaining(state), phase["deadline"] - time.time())
            if seconds > 0 and not (directory / "STOP").exists():
                compute_config = dict(config, computation_seconds=max(1, int(seconds)))
                computation = invoke(container_command(compute_config, script), "",
                                     prefix.with_suffix(".compute.log"), seconds,
                                     config["computation_output_bytes"], stop_file=directory / "STOP")
                atomic_json(prefix.with_suffix(".compute.result.json"), computation)
        if reply["action"] == "finish":
            atomic_json(directory / arm["id"] / f"{phase['name']}.final.json", reply)
            phase["status"] = "completed"
            break
        atomic_json(directory / "state.json", state)
    else:
        phase["status"] = "call_limit"
    phase["finished_at"] = time.time()
    atomic_json(directory / "state.json", state)


def experiment_path(root):
    config = json.loads((root / "pilot/config.json").read_text())
    validate_config(config)
    return root / "runs" / config["experiment_id"]


def audit(root, directory, state):
    validate_config(state["config"])
    for name, expected in state["pilot_hashes"].items():
        if digest(root / name) != expected:
            raise ValueError(f"Protocol changed after preparation: {name}")
    for arm in state["arms"]:
        inputs = directory / arm["id"] / "input"
        if set(p.name for p in inputs.iterdir()) != set(arm["input_hashes"]):
            raise ValueError("Unexpected file in a solver input packet")
        for name, expected in arm["input_hashes"].items():
            if (inputs / name).is_symlink() or digest(inputs / name) != expected:
                raise ValueError("Solver input packet changed")
    return {"inputs": "verified", "claims_accepted_automatically": 0}


def preflight(root, config, client):
    validate_config(config)
    if config["network"] == "offline":
        raise ValueError("Strict offline selected, remote subscription work is disabled")
    if not Path(client).is_file() or not os.access(client, os.X_OK):
        raise ValueError("Subscription client is missing")
    report_dir = root / "runtime" / ("check-" + uuid.uuid4().hex[:8])
    report_dir.mkdir(parents=True)
    login_log = report_dir / "authentication.log"
    result = bounded_run([str(client), "login", "status"], "", login_log, 20, 8192)
    login = login_log.read_text()
    if result["returncode"] != 0 or "Logged in using " not in login or "api" in login.lower():
        raise ValueError("An existing subscription login is required, no key-based fallback is allowed")
    feature_log = report_dir / "features.log"
    result = bounded_run([str(client), "features", "list"], "", feature_log, 20, 65536)
    features = feature_log.read_text()
    if result["returncode"] != 0 or any(name not in features for name in (
            "shell_tool", "unified_exec", "skip_host_skill_discovery", "apps", "hooks", "plugins")):
        raise ValueError("Installed client cannot establish the required tool boundaries")
    image_log = report_dir / "image.log"
    result = bounded_run(["podman", "image", "inspect", config["container_image"],
                          "--format", "{{.Id}}"], "", image_log, 20, 8192)
    image_id = image_log.read_text().strip()
    if result["returncode"] != 0 or not re.fullmatch(r"(?:sha256:)?[0-9a-f]{64}", image_id):
        raise ValueError("Local computation image unavailable, automatic downloads are disabled")
    image_id = "sha256:" + image_id.removeprefix("sha256:")
    config["runtime_image_id"] = image_id
    report = {"checked_at": time.time(), "authentication": "subscription",
              "network": config["network"], "image_id": image_id,
              "host_local_tools": "disabled by worker command", "computed_code_network": "none"}
    atomic_json(report_dir / "report.json", report)
    return report


def write_brief(directory, state):
    lines = ["# Research pilot morning brief", "", f"Experiment status: {state['status']}", "",
             "All mathematical results remain provisional until human review.", "",
             "## What changed", ""]
    assessments = []
    for arm in state["arms"]:
        lines += [f"### {arm['id']}: case {arm['case']}, {arm['condition']}", ""]
        for phase in arm["phases"]:
            latest = directory / arm["id"] / f"{phase['name']}.latest.json"
            lines += [f"- {phase['name']}: {phase['status']}, calls {phase.get('calls', 0)}"]
            if latest.exists():
                reply = json.loads(latest.read_text())
                lines += [f"- Finding: {reply['summary']}",
                          f"- Strongest objection: {reply['strongest_objection']}",
                          f"- Next decision: {reply['next_action']}",
                          f"- [Saved argument]({arm['id']}/{phase['name']}.latest.json)"]
        lines += [""]
        assessments.append({"arm": arm["id"], "case": arm["case"],
                            "correctness": None, "fidelity": None, "novelty": None,
                            "human_checking_minutes": None, "decisive_evidence": None,
                            "serious_objections": None, "contamination": None})
    lines += ["## Claims needing review", "",
              "Inspect source applicability, changed hypotheses, unproved dependencies, and every serious objection.",
              "A completed worker phase is a completed submission, not an accepted theorem.", "",
              "## Measurement limits", "",
              "Raw event logs preserve usage metadata when the service returns it. Missing usage and costs remain unknown.",
              "The experiment uses the subscription. No per-result monetary cost is inferred from token counts.",
              "Human checking time and correctness, fidelity, and novelty scores require assessment.", ""]
    temporary = directory / "MORNING_BRIEF.md.tmp"
    temporary.write_text("\n".join(lines))
    temporary.replace(directory / "MORNING_BRIEF.md")
    if not (directory / "assessment.json").exists():
        atomic_json(directory / "assessment.json", assessments)


def run_experiment(root, directory, client, network=None):
    with (directory / "controller.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        state = json.loads((directory / "state.json").read_text())
        audit(root, directory, state)
        if network:
            state["config"]["network"] = network
            state.setdefault("network_changes", []).append({"time": time.time(), "mode": network})
            atomic_json(directory / "state.json", state)
        if remaining(state) <= 0:
            state["status"] = "time_limit"
            atomic_json(directory / "state.json", state)
            write_brief(directory, state)
            return
        if (directory / "STOP").exists():
            raise ValueError("STOP is present, explicitly resume to clear it")
        preflight(root, state["config"], client)
        if state["started_at"] is None:
            state["started_at"] = time.time()
            state["deadline"] = state["started_at"] + state["config"]["total_seconds"]
        state["status"] = "running"
        atomic_json(directory / "state.json", state)
        try:
            for arm in state["arms"]:
                for phase in arm["phases"]:
                    if remaining(state) <= 0 or (directory / "STOP").exists():
                        state["status"] = "time_limit" if remaining(state) <= 0 else "stopped"
                        return
                    run_phase(root, directory, state, arm, phase, client)
                    write_brief(directory, state)
                    if phase["status"] in {"invalid_reply", "output_limit", "failed"}:
                        state["status"] = "submission_stopped"
                        return
                    if phase.get("transport_failure"):
                        state["status"] = "transport_stopped"
                        return
            state["status"] = "queue_exhausted"
        except BaseException:
            state["status"] = "interrupted"
            raise
        finally:
            atomic_json(directory / "state.json", state)
            write_brief(directory, state)


def main():
    parser = argparse.ArgumentParser(description="Bounded mathematical research pilot")
    parser.add_argument("command", choices=("prepare", "doctor", "start", "run", "resume", "stop", "status", "audit", "brief"))
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--client", type=Path)
    parser.add_argument("--network", choices=("public_sources", "no_browsing", "offline"))
    parser.add_argument("--minutes", type=int, help="Total runtime cap for prepare, without changing defaults")
    args = parser.parse_args()
    if args.minutes is not None and args.command != "prepare":
        parser.error("--minutes is set during prepare, existing run deadlines are immutable")
    root = args.root.resolve()
    client = args.client or root / "runtime/subscription-client"
    if args.command == "prepare":
        print(prepare(root, minutes=args.minutes))
        return
    if args.command == "doctor":
        config = json.loads((root / "pilot/config.json").read_text())
        if args.network:
            config["network"] = args.network
        print(json.dumps(preflight(root, config, client), indent=2))
        return
    directory = experiment_path(root)
    if args.command == "start":
        state = json.loads((directory / "state.json").read_text())
        audit(root, directory, state)
        config = dict(state["config"])
        if args.network:
            config["network"] = args.network
        preflight(root, config, client)
        if (directory / "STOP").exists() or remaining(state) <= 0:
            raise ValueError("Experiment stopped or expired, inspect status before resuming")
        command = [sys.executable, str(Path(__file__).resolve()), "run", "--root", str(root),
                   "--client", str(client)]
        if args.network:
            command += ["--network", args.network]
        log = directory / ("controller-" + uuid.uuid4().hex[:8] + ".log")
        with log.open("xb") as output:
            process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        atomic_json(directory / "launch.json", {"pid": process.pid, "log": log.name, "time": time.time()})
        print(f"Started bounded controller, pid {process.pid}, log {log}")
        return
    if args.command == "stop":
        (directory / "STOP").write_text("Operator requested stop\n")
        print("Stop requested, checkpoints and logs will be retained")
        return
    if args.command in {"run", "resume"}:
        if args.command == "resume":
            (directory / "STOP").unlink(missing_ok=True)
        run_experiment(root, directory, client, args.network)
        return
    state = json.loads((directory / "state.json").read_text())
    if args.command == "audit":
        print(json.dumps(audit(root, directory, state), indent=2))
    elif args.command == "brief":
        write_brief(directory, state)
        print(directory / "MORNING_BRIEF.md")
    else:
        print(json.dumps({"status": state["status"], "remaining_seconds": remaining(state),
                          "network": state["config"]["network"], "arms": state["arms"]}, indent=2))
if __name__ == "__main__":
    try:
        main()
    except (ValueError, BlockingIOError, FileNotFoundError) as error:
        print(f"Cannot proceed: {error}", file=sys.stderr)
        sys.exit(2)

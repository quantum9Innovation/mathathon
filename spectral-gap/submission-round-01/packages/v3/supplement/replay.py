"""Replay the three preserved finite checkers in a fresh bounded temporary copy."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
MEMORY_BYTES = 2 * 1024**3
TIMEOUT_SECONDS = 300
CHECKS = [
    ("mixed-by-saddle-checks-v1.py", "mixed-by-saddle-check-results-v1.json"),
    ("one-conflict-v1-checks.py", "one-conflict-v1-check-results.json"),
    ("two-conflict-v1-checks.py", "two-conflict-v1-check-results.json"),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_copies(provenance):
    for entry in provenance["files"]:
        path = ROOT / entry["included_path"]
        if not path.is_file() or path.is_symlink():
            raise RuntimeError("Missing or nonregular copied file: " + entry["included_path"])
        if digest(path) != entry["sha256"]:
            raise RuntimeError("Copied source hash mismatch: " + entry["included_path"])


def restrict_child():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_BYTES, MEMORY_BYTES))
    resource.setrlimit(resource.RLIMIT_CPU, (TIMEOUT_SECONDS, TIMEOUT_SECONDS))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_NOFILE, (256, 256))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    receipt_path = args.receipt.resolve()
    provenance_path = ROOT / "SOURCE_PROVENANCE.json"
    provenance = json.loads(provenance_path.read_text())
    immutable = {(ROOT / entry["included_path"]).resolve() for entry in provenance["files"]}
    immutable.update({Path(__file__).resolve(), provenance_path.resolve()})
    if receipt_path in immutable:
        raise SystemExit("The receipt must not replace a preserved source file")
    verify_copies(provenance)
    receipt = {
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "checker_dependencies": "Python standard library only",
        "replay_script_sha256": digest(Path(__file__)),
        "source_provenance_sha256": digest(provenance_path),
        "copied_source_files_verified": len(provenance["files"]),
        "limits_per_checker": {
            "wall_seconds": TIMEOUT_SECONDS,
            "cpu_seconds": TIMEOUT_SECONDS,
            "address_space_bytes": MEMORY_BYTES,
        },
        "execution": "Sequential subprocesses in a fresh temporary directory",
        "output_comparison": "Every JSON field and exact report bytes, without exclusions",
        "checks": [],
        "scope": "Replay of finite corroboration only, not an unrestricted proof or external peer review",
    }
    try:
        with tempfile.TemporaryDirectory(prefix="problem21-mixed-replay-") as temporary:
            work = Path(temporary) / "supplement"
            shutil.copytree(ROOT / "extension-round-02", work / "extension-round-02")
            reviews = work / "extension-round-02/reviews"
            for script_name, report_name in CHECKS:
                expected_path = ROOT / "extension-round-02/reviews" / report_name
                report_path = reviews / report_name
                expected = json.loads(expected_path.read_text())
                report_path.unlink()
                before = time.monotonic()
                completed = subprocess.run(
                    [sys.executable, "-I", str(reviews / script_name)],
                    cwd=work,
                    env={"PATH": os.defpath, "PYTHONHASHSEED": "0", "PYTHONDONTWRITEBYTECODE": "1"},
                    capture_output=True,
                    timeout=TIMEOUT_SECONDS,
                    preexec_fn=restrict_child,
                    start_new_session=True,
                )
                record = {
                    "script": "extension-round-02/reviews/" + script_name,
                    "script_sha256": digest(reviews / script_name),
                    "elapsed_seconds": round(time.monotonic() - before, 3),
                    "exit_code": completed.returncode,
                    "stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
                    "stderr": completed.stderr.decode(errors="replace"),
                    "expected_report_sha256": digest(expected_path),
                }
                receipt["checks"].append(record)
                if completed.returncode != 0:
                    raise RuntimeError(script_name + " failed")
                actual = json.loads(report_path.read_text())
                record["all_json_fields_equal"] = actual == expected
                record["report_bytes_equal"] = report_path.read_bytes() == expected_path.read_bytes()
                record["actual_report_sha256"] = digest(report_path)
                record["counts"] = actual.get("counts", actual.get("checks"))
                if not record["all_json_fields_equal"] or not record["report_bytes_equal"]:
                    raise RuntimeError(script_name + " report differs from the preserved result")
                print(script_name + ": passed, all report fields and bytes match", flush=True)
        verify_copies(provenance)
        receipt["preserved_source_files_unchanged"] = True
        receipt["status"] = "passed"
    except Exception as error:
        receipt["status"] = "failed"
        receipt["failure"] = type(error).__name__ + ": " + str(error)
        raise
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        print("Receipt: " + str(receipt_path), flush=True)


if __name__ == "__main__":
    main()

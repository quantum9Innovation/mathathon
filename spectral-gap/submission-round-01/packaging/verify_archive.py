"""Verify an actual ZIP through safe extraction and its portable verifier."""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    archive_path = args.archive.resolve()
    output = args.receipt.resolve()
    if output == archive_path or output.exists():
        raise SystemExit("Receipt must be a new file distinct from the archive")
    receipt = {
        "status": "running",
        "archive": archive_path.name,
        "archive_sha256": digest(archive_path),
        "archive_bytes": archive_path.stat().st_size,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "submission_performed": False,
        "scope": "Archive integrity, clean PDF reproduction and finite-check replay. Preparation status is recorded in the included manifest.",
    }
    try:
        with tempfile.TemporaryDirectory(prefix="problem21-zip-verification-") as temporary:
            work = Path(temporary)
            extracted = work / "extracted"
            extracted.mkdir()
            with zipfile.ZipFile(archive_path) as archive:
                entries = archive.infolist()
                names = [entry.filename for entry in entries]
                if len(names) != len(set(names)):
                    raise RuntimeError("Duplicate ZIP member names")
                for entry in entries:
                    path = PurePosixPath(entry.filename)
                    mode = entry.external_attr >> 16
                    if path.is_absolute() or ".." in path.parts or "\\" in entry.filename:
                        raise RuntimeError("Unsafe archive path")
                    if path.as_posix() != entry.filename or not stat.S_ISREG(mode):
                        raise RuntimeError("Archive members must be normalized regular files")
                if archive.testzip() is not None:
                    raise RuntimeError("ZIP CRC check failed")
                archive.extractall(extracted)
            receipt["zip_members"] = len(entries)
            receipt["safe_paths_and_crc"] = True
            receipt["manifest_sha256"] = digest(extracted / "MANIFEST.json")
            verifier_receipt = work / "verification.json"
            completed = subprocess.run(
                [sys.executable, "-I", str(extracted / "verify.py"), "--receipt", str(verifier_receipt)],
                cwd=extracted, capture_output=True, text=True, timeout=900,
            )
            receipt["verifier_exit_code"] = completed.returncode
            receipt["verifier_stdout"] = completed.stdout
            receipt["verifier_stderr"] = completed.stderr
            if verifier_receipt.exists():
                receipt["verification"] = json.loads(verifier_receipt.read_text())
            if completed.returncode != 0:
                raise RuntimeError("Extracted portable verifier failed")
            if receipt["verification"]["verification_status"] != "passed":
                raise RuntimeError("Portable verification did not pass")
            receipt["final_archive_sha256"] = digest(archive_path)
            if receipt["final_archive_sha256"] != receipt["archive_sha256"]:
                raise RuntimeError("Archive changed during verification")
            receipt["status"] = "passed"
    except Exception as error:
        receipt["status"] = "failed"
        receipt["failure"] = type(error).__name__ + ": " + str(error)
        raise
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps({key: receipt[key] for key in ["status", "archive", "archive_sha256", "archive_bytes"]}, indent=2))
        print("Receipt: " + str(output))


if __name__ == "__main__":
    main()

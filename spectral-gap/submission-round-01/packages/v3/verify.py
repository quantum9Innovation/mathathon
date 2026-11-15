"""Verify the portable package from a copy of this script at the package root."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
BLOCK_PATTERN = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary|proof|example)\}.*?\\end\{\1\}",
    re.S,
)
LOG_FINDINGS = re.compile(
    r"Warning|Overfull|Underfull|undefined|^!", re.MULTILINE
)
EXPECTED_PAGES = {"report": 44, "slides": 16}


class VerificationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def read_json(path):
    def unique_keys(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "Duplicate JSON key in " + str(path) + ": " + key)
            result[key] = value
        return result
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_keys)


def safe_relative(value):
    require(isinstance(value, str) and value, "Manifest path must be a nonempty string")
    require("\\" not in value and "\x00" not in value, "Unsafe manifest path: " + repr(value))
    path = PurePosixPath(value)
    require(not path.is_absolute(), "Absolute manifest path: " + value)
    require(all(part not in {"", ".", ".."} for part in value.split("/")),
            "Noncanonical manifest path: " + value)
    require(str(path) == value, "Noncanonical manifest path: " + value)
    return value


def regular_files(directory):
    found = set()
    for parent, directories, files in os.walk(directory, followlinks=False):
        parent = Path(parent)
        for name in directories:
            mode = (parent / name).lstat().st_mode
            require(stat.S_ISDIR(mode), "Nonregular directory in package: " + str(parent / name))
        for name in files:
            path = parent / name
            mode = path.lstat().st_mode
            require(stat.S_ISREG(mode), "Nonregular file in package: " + str(path))
            found.add(path.relative_to(directory).as_posix())
    return found


def verify_manifest():
    actual = regular_files(ROOT)
    require("MANIFEST.json" in actual, "MANIFEST.json is missing")
    manifest = read_json(ROOT / "MANIFEST.json")
    require(isinstance(manifest, dict), "Manifest must be an object")
    require(type(manifest.get("schema_version")) is int and manifest["schema_version"] == 1,
            "Unsupported manifest schema")
    require(isinstance(manifest.get("status"), str) and manifest["status"],
            "Manifest metadata status must be a nonempty string")
    require(isinstance(manifest.get("files"), list), "Manifest files must be a list")
    listed = set()
    total_bytes = 0
    for entry in manifest["files"]:
        require(isinstance(entry, dict), "Manifest file entry must be an object")
        relative = safe_relative(entry.get("path"))
        require(relative != "MANIFEST.json", "Manifest must exclude itself")
        require(relative not in listed, "Duplicate manifest file: " + relative)
        listed.add(relative)
        expected_hash = entry.get("sha256")
        require(isinstance(expected_hash, str) and re.fullmatch(r"[0-9a-f]{64}", expected_hash),
                "Invalid SHA-256 for " + relative)
        require(type(entry.get("bytes")) is int and entry["bytes"] >= 0,
                "Invalid byte count for " + relative)
        require(relative in actual, "Listed file is missing: " + relative)
        path = ROOT / relative
        require(path.stat().st_size == entry["bytes"], "Size mismatch: " + relative)
        require(sha256(path) == expected_hash, "Hash mismatch: " + relative)
        total_bytes += entry["bytes"]
    require(listed == actual - {"MANIFEST.json"},
            "Unlisted package files: " + ", ".join(sorted(actual - listed - {"MANIFEST.json"})))
    required = {
        "report.tex", "report.pdf", "slides.pdf", "presentation/slides.tex",
        "metadata/math-blocks.json", "supplement/replay.py", "verify.py",
    }
    require(required <= listed, "Missing required files: " + ", ".join(sorted(required - listed)))
    require((ROOT / "reviews").is_dir(), "The reviews directory is missing")
    return manifest, {
        "status": "passed",
        "manifest_sha256": sha256(ROOT / "MANIFEST.json"),
        "files_verified": len(listed),
        "bytes_verified": total_bytes,
        "exact_file_inventory": True,
        "all_paths_regular_and_relative": True,
    }


def verify_math_blocks():
    expected = read_json(ROOT / "metadata/math-blocks.json")
    require(isinstance(expected, list) and len(expected) == 37,
            "Expected exactly 37 recorded mathematical block hashes")
    require(all(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value)
                for value in expected), "Invalid mathematical block hash")
    require(expected == sorted(expected), "Recorded mathematical block hashes must be sorted")
    source = (ROOT / "report.tex").read_text(encoding="utf-8")
    hashes = sorted(hashlib.sha256(match.group(0).encode("utf-8")).hexdigest()
                    for match in BLOCK_PATTERN.finditer(source))
    require(len(hashes) == 37, "Report does not contain exactly 37 mathematical blocks")
    require(hashes == expected, "Mathematical block hashes differ from metadata")
    return {
        "status": "passed", "matched_blocks": len(hashes),
        "environments": ["theorem", "proposition", "lemma", "corollary", "proof", "example"],
        "comparison": "Sorted SHA-256 values of complete matched source blocks",
        "scope": "Source identity only, not a proof check",
    }


def run(command, cwd, timeout=300):
    environment = dict(os.environ)
    environment.update({"LC_ALL": "C", "openin_any": "p", "openout_any": "p"})
    completed = subprocess.run(
        command, cwd=cwd, env=environment, capture_output=True, timeout=timeout,
        start_new_session=True,
    )
    if completed.returncode != 0:
        detail = (completed.stderr + b"\n" + completed.stdout).decode(errors="replace")[-4000:]
        raise VerificationError(Path(command[0]).name + " failed: " + detail)
    return completed


def page_count(pdf, tools, cwd):
    result = run([tools["pdfinfo"], str(pdf)], cwd)
    text = result.stdout.decode(errors="replace")
    match = re.search(r"^Pages:\s+(\d+)\s*$", text, re.MULTILINE)
    require(match is not None, "Could not determine page count for " + pdf.name)
    return int(match.group(1))


def compare_document(name, source, delivered_pdf, temporary, tools):
    build = temporary / (name + "-build")
    build.mkdir()
    local_source = build / (name + ".tex")
    shutil.copyfile(source, local_source)
    for unused_pass in range(3):
        run([tools["pdflatex"], "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", local_source.name], build)
    log = (build / (name + ".log")).read_text(errors="replace")
    findings = [line for line in log.splitlines() if LOG_FINDINGS.search(line)]
    require(not findings, name + " final-pass log findings: " + " | ".join(findings[:12]))
    rebuilt_pdf = build / (name + ".pdf")
    rebuilt_pages = page_count(rebuilt_pdf, tools, build)
    require(rebuilt_pages == EXPECTED_PAGES[name], name + " rebuilt page count differs")
    delivered_text = run([tools["pdftotext"], "-layout", str(delivered_pdf), "-"], build).stdout
    rebuilt_text = run([tools["pdftotext"], "-layout", str(rebuilt_pdf), "-"], build).stdout
    require(delivered_text == rebuilt_text, name + " extracted text differs after rebuilding")
    raster_hashes = {}
    for label, pdf in [("delivered", delivered_pdf), ("rebuilt", rebuilt_pdf)]:
        folder = temporary / (name + "-" + label + "-pages")
        folder.mkdir()
        run([tools["pdftoppm"], "-r", "96", str(pdf), str(folder / "page")], folder)
        pages = sorted(folder.glob("page-*.ppm"), key=lambda path: int(path.stem.split("-")[-1]))
        require(len(pages) == EXPECTED_PAGES[name], name + " rendered page count differs")
        raster_hashes[label] = [sha256(page) for page in pages]
    require(raster_hashes["delivered"] == raster_hashes["rebuilt"],
            name + " page pixels differ after rebuilding")
    return {
        "status": "passed", "page_count": rebuilt_pages,
        "source_only_rebuild": True, "pdflatex_passes": 3, "shell_escape": False,
        "final_pass_log_findings": [], "extracted_text_identical": True,
        "extracted_text_sha256": hashlib.sha256(rebuilt_text).hexdigest(),
        "render_dpi": 96, "all_page_ppm_bytes_identical": True,
        "page_ppm_sha256": raster_hashes["rebuilt"],
        "delivered_pdf_sha256": sha256(delivered_pdf),
        "rebuilt_pdf_sha256": sha256(rebuilt_pdf),
        "pdf_bytes_identical_informational": delivered_pdf.read_bytes() == rebuilt_pdf.read_bytes(),
    }


def replay_supplement(temporary):
    receipt_path = temporary / "supplement-replay-receipt.json"
    run([sys.executable, "-I", str(ROOT / "supplement/replay.py"),
         "--receipt", str(receipt_path)], temporary, timeout=925)
    receipt = read_json(receipt_path)
    require(receipt.get("status") == "passed", "Supplement replay did not pass")
    require(len(receipt.get("checks", [])) == 3, "Supplement replay did not run all three checkers")
    require(all(check.get("exit_code") == 0 and check.get("all_json_fields_equal") is True
                and check.get("report_bytes_equal") is True for check in receipt["checks"]),
            "Supplement replay did not exactly reproduce all saved results")
    require(receipt.get("preserved_source_files_unchanged") is True,
            "Supplement preserved-source comparison did not pass")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--quick", action="store_true", help="Skip PDF rebuilds and rendering")
    args = parser.parse_args()
    require(args.receipt.is_absolute(), "The receipt path must be absolute")
    receipt_path = args.receipt.resolve()
    require(not receipt_path.is_relative_to(ROOT), "The receipt path must be outside the package")
    require(not receipt_path.exists() or receipt_path.is_file(), "The receipt path is not a file")
    started = time.monotonic()
    receipt = {
        "verification_status": "running", "mode": "quick" if args.quick else "full",
        "started_utc": utc_now(), "python_version": platform.python_version(),
        "scope": "Artifact integrity, preserved mathematical source identity, finite-check replay and selected rebuild checks. This does not certify mathematical correctness, historical novelty or submission readiness.",
        "skipped_checks": ["PDF rebuilds", "PDF text comparisons", "page raster comparisons"] if args.quick else [],
    }
    try:
        manifest, receipt["manifest"] = verify_manifest()
        receipt["package_metadata_status"] = manifest["status"]
        print("Manifest: all file identities match", flush=True)
        receipt["mathematical_blocks"] = verify_math_blocks()
        needed = ["pdfinfo"] if args.quick else ["pdfinfo", "pdflatex", "pdftotext", "pdftoppm"]
        tools = {name: shutil.which(name) for name in needed}
        require(all(tools.values()), "Missing required programs: " + ", ".join(name for name in needed if not tools[name]))
        with tempfile.TemporaryDirectory(prefix="problem21-package-verify-") as temporary_name:
            temporary = Path(temporary_name)
            receipt["delivered_page_counts"] = {}
            for name, expected in EXPECTED_PAGES.items():
                count = page_count(ROOT / (name + ".pdf"), tools, temporary)
                require(count == expected, name + " must contain " + str(expected) + " pages")
                receipt["delivered_page_counts"][name] = count
            receipt["supplement_replay"] = replay_supplement(temporary)
            print("Finite checks: all three saved reports reproduced", flush=True)
            if not args.quick:
                receipt["rebuilds"] = {}
                for name, source in [("report", ROOT / "report.tex"),
                                     ("slides", ROOT / "presentation/slides.tex")]:
                    receipt["rebuilds"][name] = compare_document(
                        name, source, ROOT / (name + ".pdf"), temporary, tools,
                    )
                    print(name.capitalize() + ": source rebuild, text and every page match", flush=True)
        final_manifest, final_verification = verify_manifest()
        require(final_manifest == manifest and final_verification == receipt["manifest"],
                "Package changed during verification")
        receipt["package_unchanged_after_verification"] = True
        receipt["verification_status"] = "passed"
    except Exception as error:
        receipt["verification_status"] = "failed"
        receipt["failure"] = type(error).__name__ + ": " + str(error)
    finally:
        receipt["finished_utc"] = utc_now()
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("Artifact verification: " + receipt["verification_status"], flush=True)
    print("Receipt: " + str(receipt_path), flush=True)
    if receipt["verification_status"] != "passed":
        print(receipt["failure"], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except VerificationError as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)

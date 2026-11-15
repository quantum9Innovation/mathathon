"""Verify frozen evidence, deliverable identity, links and final build logs."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    checked = []

    def entries(base, values):
        for value in values:
            target = base / value["path"]
            assert target.is_file(), target
            assert digest(target) == value["sha256"], target
            checked.append(str(target.relative_to(PROJECT)))

    entries(ROOT / "inputs", json.loads((ROOT / "inputs/MANIFEST.json").read_text()))
    core = json.loads((ROOT / "proof/MANIFEST-v1.json").read_text())
    entries(ROOT, core["frozen_files"])
    ext = json.loads((ROOT / "extensions/MANIFEST-v1.json").read_text())
    entries(ROOT / "extensions", ext["files"])
    priority = json.loads((ROOT / "priority/MANIFEST-v1.json").read_text())
    entries(ROOT / "priority", priority["outputs"])
    entries(ROOT, priority["dependencies"])
    frozen = sorted(ROOT.glob("frozen-manuscript-v*"),
                    key=lambda p: int(p.name.rsplit("v", 1)[1]))
    for base in frozen:
        entries(base, json.loads((base / "MANIFEST.json").read_text()))

    presubmission = ROOT / "presubmission-01"
    entries(presubmission, json.loads((presubmission / "MANIFEST.json").read_text()))

    extension = PROJECT / "extension-round-02"
    entries(extension, json.loads((extension / "MANIFEST-v1.json").read_text()))

    final = frozen[-1]
    final_entries = json.loads((final / "MANIFEST.json").read_text())
    for entry in final_entries:
        if entry["path"].startswith(("manuscript/", "guide/", "figures/", "output/pdf/")):
            assert digest(ROOT / entry["path"]) == entry["sha256"], entry["path"]

    for source in ["main", "reading-guide"]:
        log = (ROOT / "build" / (source + ".log")).read_text()
        assert "LaTeX Warning:" not in log, source
        assert "Overfull" not in log, source

    page_counts = {}
    for name in ["centered-permutation-products", "reading-guide"]:
        pdf = ROOT / "output/pdf" / (name + ".pdf")
        info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
        count = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
        frozen_info = subprocess.check_output(
            ["pdfinfo", str(final / "output/pdf" / (name + ".pdf"))], text=True)
        expected = int(re.search(r"^Pages:\s+(\d+)", frozen_info, re.M).group(1))
        assert count == expected, (name, count)
        page_counts[name] = count

    documents = [ROOT / name for name in ["README.md", "HANDOFF.md", "VERIFICATION.md", "TEAM_BOARD.md"]]
    documents += [ROOT.parent / name for name in ["README.md", "CLAIM_LEDGER.md", "CONTRIBUTION.md", "EXPLANATION.md"]]
    documents += [presubmission / name for name in [
        "BORDENAVE_JOURNAL_CHECK.md", "PRIORITY_AUDIT_V2.md", "SEARCH_LOG.md",
        "SUBMISSION_READINESS.md", "INDEPENDENT_SOURCE_REVIEW.md"]]
    documents += [extension / name for name in [
        "README.md", "TEAM_BOARD.md", "SUBMISSION_READINESS.md", "PRIORITY_SYNTHESIS.md",
        "PACKAGED_PROJECT_README.md"]]
    link_count = 0
    for document in documents:
        content = document.read_text()
        link_base = PROJECT if document.name == "PACKAGED_PROJECT_README.md" else document.parent
        assert not any(c in content for c in [chr(8211), chr(8212), chr(59)]), document
        for target in re.findall(r"\]\(([^)]+)\)", content):
            if target.startswith(("https://", "http://", "#")):
                continue
            path = target.split("#", 1)[0]
            if path:
                assert (link_base / path).exists(), (document, target)
                link_count += 1

    report = {"status": "passed", "frozen_hash_comparisons": len(checked),
              "final_source_and_pdf_identity": f"matches {final.name}",
              "page_counts": page_counts, "local_link_checks": link_count,
              "build_warnings": 0,
              "scope": "Integrity, compilation and link checks. Mathematical evidence is recorded separately."}
    (ROOT / "checks/package-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

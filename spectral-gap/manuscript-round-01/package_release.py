"""Assemble the portable manuscript package with explicit included files."""

import hashlib
import json
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent
OUTPUT = ROOT / "output/centered-permutation-final-package.zip"
EXTENSION = PROJECT / "extension-round-02"


def main():
    selected = {}

    def include(path, target=None):
        assert path.is_file(), path
        name = target or str(Path("spectral-gap") / path.relative_to(PROJECT))
        selected[name] = path

    for name in ["README.md", "HANDOFF.md", "RUN_CONTRACT.md", "TEAM_BOARD.md",
                 "VERIFICATION.md", "build_artifacts.py", "package_release.py"]:
        include(ROOT / name)
    frozen = sorted(ROOT.glob("frozen-manuscript-v*"),
                    key=lambda p: int(p.name.rsplit("v", 1)[1]))
    final_revision = int(frozen[-1].name.rsplit("v", 1)[1])
    folders = ["manuscript", "guide", "figures", "inputs", "proof", "extensions",
               "priority", "reviews"] + [p.name for p in frozen]
    for folder in folders:
        for path in sorted((ROOT / folder).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts:
                if folder in {"reviews", "priority"} and path.suffix not in {".md", ".json", ".py", ".bib"}:
                    continue
                include(path)
    for path in sorted((ROOT / "presubmission-01").iterdir()):
        if path.is_file() and path.suffix in {".md", ".json", ".bib"}:
            include(path)
    reviewer = ROOT / "presubmission-01/reviewer"
    if reviewer.exists():
        for path in sorted(reviewer.rglob("*")):
            if path.is_file() and path.suffix in {".py", ".json", ".md", ".bib"}:
                include(path)
    for name in ["main.log", "reading-guide.log"]:
        include(ROOT / "build" / name)
    for name in ["verify_package.py", "verify_release.py", "package-verification.json"]:
        include(ROOT / "checks" / name)
    for path in sorted((ROOT / "output/pdf").glob("*.pdf")):
        include(path)
    for name in ["CLAIM_LEDGER.md", "CONTRIBUTION.md", "EXPLANATION.md"]:
        include(PROJECT / name)
    include(EXTENSION / "PACKAGED_PROJECT_README.md", "spectral-gap/README.md")
    for path in sorted(EXTENSION.rglob("*")):
        if path.is_file() and path.suffix in {".md", ".json", ".py", ".tex", ".bib"}:
            if any(part in {"__pycache__", "sources", "build", "scratch", "renders"}
                   or part.endswith(("-build", "-pages"))
                   for part in path.relative_to(EXTENSION).parts):
                continue
            include(path)
    for folder in ["audit-2026-11-14", "cross-review-2026-11-14", "integration-audit-2026-11-14"]:
        for path in sorted((PROJECT / folder).rglob("*")):
            if path.is_file() and path.suffix in {".md", ".json", ".py"}:
                include(path)

    entries = []
    with ZipFile(OUTPUT, "w", compression=ZIP_DEFLATED) as archive:
        for name, path in sorted(selected.items()):
            data = path.read_bytes()
            archive.writestr(name, data)
            entries.append({"path": name, "bytes": len(data),
                            "sha256": hashlib.sha256(data).hexdigest()})
        manifest = {"release": f"manuscript revision {final_revision}", "files": entries,
                    "portable_index": "spectral-gap/README.md is the packaged project index",
                    "excluded": ["Historical imported snapshot", "Third-party source downloads",
                                 "Scratch page renders", "Other projects"]}
        archive.writestr("PACKAGE_MANIFEST.json", json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"archive": str(OUTPUT), "files": len(entries),
                      "bytes": OUTPUT.stat().st_size,
                      "sha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()

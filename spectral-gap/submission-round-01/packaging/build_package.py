"""Create a new immutable local package candidate from reviewed artifacts."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT.parent / "manuscript-round-01/frozen-manuscript-v10"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def copy(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--slides-review", required=True)
    parser.add_argument("--identity-review")
    args = parser.parse_args()
    if not re.fullmatch(r"v[1-9][0-9]*", args.revision):
        raise SystemExit("Revision must be v followed by a positive integer")
    package = ROOT / "packages" / args.revision
    if package.exists():
        raise SystemExit("Refusing to replace an existing package candidate")
    slide_review = ROOT / "reviews" / args.slides_review
    if not slide_review.is_file():
        raise SystemExit("Final exact-target slide review is required")
    if not (ROOT / "packaging/verify.py").is_file():
        raise SystemExit("Portable verifier is required")
    metadata = json.loads((ROOT / "metadata/team.json").read_text())
    identified = bool(metadata["team_name"] and metadata["authors"])
    if identified and not args.identity_review:
        raise SystemExit("Identity supplied, an exact-target identity review is required")
    if args.identity_review and not (ROOT / "reviews" / args.identity_review).is_file():
        raise SystemExit("The identity review is missing")
    package.mkdir(parents=True)
    files = {
        "frozen-v1/report.tex": "report.tex",
        "frozen-v1/report.pdf": "report.pdf",
        "slides/problem21-slides.pdf": "slides.pdf",
        "slides/problem21-slides.tex": "presentation/slides.tex",
        "slides/speaker-notes.md": "presentation/speaker-notes.md",
        "packaging/README-template.md": "README.md",
        "packaging/verify.py": "verify.py",
        "checks/ASSEMBLY.json": "metadata/ASSEMBLY.json",
        "reviews/report-v1-review.md": "reviews/report-v1-review.md",
        "reviews/report-v1/source-checks.json": "reviews/report-v1/source-checks.json",
        "reviews/report-v1/figure-checks.json": "reviews/report-v1/figure-checks.json",
        "reviews/" + args.slides_review: "reviews/" + args.slides_review,
    }
    if identified:
        for source in ["frozen-v1/report.tex", "frozen-v1/report.pdf", "slides/problem21-slides.pdf",
                       "slides/problem21-slides.tex", "slides/speaker-notes.md"]:
            del files[source]
        files.update({
            "frozen-v2/report.tex": "report.tex",
            "frozen-v2/report.pdf": "report.pdf",
            "frozen-v2/slides.tex": "presentation/slides.tex",
            "frozen-v2/slides.pdf": "slides.pdf",
            "frozen-v2/speaker-notes.md": "presentation/speaker-notes.md",
            "reviews/" + args.identity_review: "reviews/" + args.identity_review,
            "reviews/identity-v3/checks.json": "reviews/identity-v3/checks.json",
        })
    for source, destination in files.items():
        copy(ROOT / source, package / destination)
    shutil.copytree(ROOT / "supplement", package / "supplement")
    slide_evidence = slide_review.stem.removesuffix("-review")
    for name in ["source-checks.json", "render-delta.json"]:
        path = ROOT / "reviews" / slide_evidence / name
        copy(path, package / "reviews" / path.relative_to(ROOT / "reviews"))
    for name in ["moment-regimes-data.json", "rate-and-hierarchy-data.json", "global-error-data.json"]:
        copy(BASE / "figures" / name, package / "data" / name)
    baseline = json.loads((ROOT / "metadata/SOURCE_BASELINE.json").read_text())
    baseline["frozen_root"] = "manuscript-round-01/frozen-manuscript-v10"
    (package / "metadata/SOURCE_BASELINE.json").write_text(json.dumps(baseline, indent=2) + "\n")
    assembly = json.loads((ROOT / "checks/ASSEMBLY.json").read_text())
    pattern = r"\\begin\{(theorem|proposition|lemma|corollary|proof|example)\}.*?\\end\{\1\}"
    original = "\n".join((BASE / entry["path"]).read_text() for entry in assembly["section_sources"])
    block_hashes = sorted(sha256(m.group(0).encode()).hexdigest() for m in re.finditer(pattern, original, re.S))
    if len(block_hashes) != 37:
        raise RuntimeError("Expected exactly 37 reviewed mathematical blocks")
    (package / "metadata/math-blocks.json").write_text(json.dumps(block_hashes, indent=2) + "\n")
    manifest = {
        "schema_version": 1,
        "status": "verified-prepared-not-submitted" if identified else "verified-draft-identity-pending",
        "problem": 21,
        "track": "Combinatorics",
        "revision": args.revision,
        "pending": [] if identified else ["Exact team name, author names and affiliations for the title blocks"],
        "files": [
            {"path": str(p.relative_to(package)), "sha256": digest(p), "bytes": p.stat().st_size}
            for p in sorted(package.rglob("*")) if p.is_file()
        ],
    }
    (package / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
    prefix = "problem-21-submission-" if identified else "problem-21-submission-draft-"
    destination = ROOT / "output" / (prefix + args.revision + ".zip")
    if destination.exists():
        raise RuntimeError("Refusing to replace an existing archive")
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(package.rglob("*")):
            if not path.is_file():
                continue
            info = zipfile.ZipInfo(str(path.relative_to(package)), (2026, 11, 15, 18, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    record = {
        "archive": destination.name,
        "archive_sha256": digest(destination),
        "archive_bytes": destination.stat().st_size,
        "manifest_sha256": digest(package / "MANIFEST.json"),
        "manifest_files": len(manifest["files"]),
        "status": "built, fresh-extraction verification required",
    }
    (ROOT / "checks" / ("PACKAGE-" + args.revision + "-BUILD.json")).write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()

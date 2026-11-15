"""Extract, replay and rebuild the portable release without the workspace."""

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=300)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    archive = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / "output/centered-permutation-final-package.zip"
    report = {"archive": archive.name, "archive_sha256": digest(archive),
              "scope": "Portable integrity, finite-check replay and content-identical rebuild. No proof or priority certificate."}
    with tempfile.TemporaryDirectory(prefix="spectral-release-") as temporary:
        staging = Path(temporary)
        with ZipFile(archive) as bundle:
            assert bundle.testzip() is None
            manifest = json.loads(bundle.read("PACKAGE_MANIFEST.json"))
            expected_names = {entry["path"] for entry in manifest["files"]} | {"PACKAGE_MANIFEST.json"}
            assert set(bundle.namelist()) == expected_names
            assert len(bundle.namelist()) == len(expected_names)
            excluded_source_files = {"bordenave-layout.txt", "biregular-layout.txt",
                                     "bdh-page-15.png", "cn-page-09.png", "cn-page-10.png"}
            assert not any(Path(name).name in excluded_source_files for name in bundle.namelist())
            assert not any("sources" in Path(name).parts for name in bundle.namelist())
            assert not any(part.endswith(("-build", "-pages"))
                           for name in bundle.namelist() for part in Path(name).parts)
            for name in bundle.namelist():
                target = staging / name
                assert target.resolve().is_relative_to(staging.resolve()), name
            bundle.extractall(staging)
        for entry in manifest["files"]:
            target = staging / entry["path"]
            assert target.stat().st_size == entry["bytes"], target
            assert digest(target) == entry["sha256"], target
        report["archive_files_verified"] = len(manifest["files"])
        work = staging / "spectral-gap/manuscript-round-01"
        report["portable_package_check"] = json.loads(run([sys.executable, "checks/verify_package.py"], work))

        checks = []
        for script, output in [
            ("proof/check_core.py", "proof/core-checks-v1.json"),
            ("extensions/check_extension.py", "extensions/extension-checks-v1.json"),
            ("reviews/extension-review-checks.py", "reviews/extension-review-checks.json"),
            ("reviews/manuscript-referee-checks.py", "reviews/manuscript-referee-checks.json"),
            ("../extension-round-02/mixed/check_envelope.py", "../extension-round-02/mixed/envelope-checks-v1.json"),
            ("../extension-round-02/rate/check_rate.py", "../extension-round-02/rate/rate-checks-v1.json"),
            ("../extension-round-02/rate/check_first_correction.py", "../extension-round-02/rate/first-correction-checks-v1.json"),
            ("../extension-round-02/rate/global/check_global.py", "../extension-round-02/rate/global/checks-v1.json"),
            ("../extension-round-02/saddle/saddle-check.py", "../extension-round-02/saddle/saddle-check-results.json"),
            ("../extension-round-02/reviews/mixed-by-saddle-checks-v1.py", "../extension-round-02/reviews/mixed-by-saddle-check-results-v1.json"),
            ("../extension-round-02/reviews/global-by-saddle-checks-v1.py", "../extension-round-02/reviews/global-by-saddle-check-results-v1.json"),
            ("../extension-round-02/reviews/assembled-v6-checks-portable.py", "../extension-round-02/reviews/assembled-v6-check-results.json"),
            ("../extension-round-02/priority-special-functions/verify_specialization.py", "../extension-round-02/priority-special-functions/FINITE_CHECKS-v1.json"),
            ("../extension-round-02/mixed-one-conflict/check_one_conflict.py", "../extension-round-02/mixed-one-conflict/checks-v1.json"),
            ("../extension-round-02/mixed-one-conflict/check_general.py", "../extension-round-02/mixed-one-conflict/general-checks-v1.json"),
            ("../extension-round-02/reviews/one-conflict-v1-checks.py", "../extension-round-02/reviews/one-conflict-v1-check-results.json"),
            ("../extension-round-02/global-sharp-rate/check_global_sharp.py", "../extension-round-02/global-sharp-rate/checks-v1.json"),
            ("../extension-round-02/reviews/global-sharp-v1-check.py", "../extension-round-02/reviews/global-sharp-v1-checks.json"),
            ("../extension-round-02/reviews/assembled-v8-checks.py", "../extension-round-02/reviews/assembled-v8-check-results.json"),
            ("../extension-round-02/mixed-two-conflict/check_two_conflict.py", "../extension-round-02/mixed-two-conflict/checks-v1.json"),
            ("../extension-round-02/root/check_two_conflict_independent.py", "../extension-round-02/root/two-conflict-independent-checks.json"),
            ("../extension-round-02/final-priority-addendum/check_derangement.py", "../extension-round-02/final-priority-addendum/DERANGEMENT_CHECKS-v1.json"),
            ("../extension-round-02/reviews/two-conflict-v1-checks.py", "../extension-round-02/reviews/two-conflict-v1-check-results.json"),
        ]:
            reference = json.loads((work / output).read_text())
            run([sys.executable, script], work)
            replay = json.loads((work / output).read_text())
            assert replay == reference, script
            checks.append({"script": script, "result": "matches saved finite-check report"})
        report["finite_check_replays"] = checks

        run([sys.executable, "build_artifacts.py"], work)
        final = max(work.glob("frozen-manuscript-v*"),
                    key=lambda p: int(p.name.rsplit("v", 1)[1]))
        render_results = {}
        for name in ["centered-permutation-products", "reading-guide"]:
            reference = final / "output/pdf" / (name + ".pdf")
            rebuilt = work / "output/pdf" / (name + ".pdf")
            reference_text = run(["pdftotext", "-layout", str(reference), "-"], work)
            rebuilt_text = run(["pdftotext", "-layout", str(rebuilt), "-"], work)
            assert rebuilt_text == reference_text, name
            rendered = []
            for label, pdf in [("reference", reference), ("rebuilt", rebuilt)]:
                folder = staging / name / label
                folder.mkdir(parents=True)
                run(["pdftoppm", "-r", "96", "-png", str(pdf), str(folder / "page")], work)
                rendered.append({p.name: digest(p) for p in folder.glob("page-*.png")})
            assert rendered[0] == rendered[1], name
            render_results[name] = {"text": "identical", "pages": len(rendered[0]),
                                    "all_page_pixels_at_96_dpi": "identical"}
        for name in ["moment-regimes-data.json", "moment-regimes.png", "cell-patterns.png",
                     "rate-and-hierarchy-data.json", "rate-and-hierarchy.png",
                     "global-error-data.json", "global-error.png"]:
            assert digest(work / "figures" / name) == digest(final / "figures" / name), name
        report["rebuilt_documents"] = render_results
        report["rebuilt_plot_data_and_images"] = "identical"
        report["build_warnings"] = 0
        report["status"] = "passed"
    output = ROOT / "checks/release-verification.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

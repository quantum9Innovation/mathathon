"""Verify the manuscript packet, proof bindings, builds, and exact checks."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

PACKET = Path(__file__).resolve().parent
WORKSPACE = PACKET.parents[1]
POPP = Path("/nix/store/q0ld5mmjh89nar306jb0izrcf8phy5v9-poppler-utils-26.10.0/bin")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest(path, base, fallback=None):
    checked = 0
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        expected, relative = line.split("  ", 1)
        target = base/relative
        snapshot = fallback/relative if fallback else None
        if target.exists():
            assert digest(target) == expected, f"Hash mismatch: {relative}"
        elif not snapshot:
            raise AssertionError(f"Missing file: {relative}")
        if snapshot:
            assert digest(snapshot) == expected, f"Snapshot mismatch: {relative}"
        checked += 1
    return checked


def reachable_tex(path, seen=None):
    seen = set() if seen is None else seen
    path = path.resolve()
    assert path not in seen, f"Repeated or cyclic TeX input: {path}"
    seen.add(path)
    raw = path.read_bytes()
    assert not any(x < 32 and x not in (9, 10) for x in raw), path
    source = raw.decode()
    parts = [source]
    for included in re.findall(r"\\input\{([^}]+)\}", source):
        child = PACKET/(included+".tex")
        assert child.exists(), f"Missing input: {included}"
        parts.extend(reachable_tex(child, seen))
    return parts


def main():
    internal = manifest(PACKET/"SHA256SUMS.txt", PACKET)
    sources = manifest(PACKET/"SOURCE-HASHES.txt", WORKSPACE,
                       PACKET/"provenance"/"proof-inputs")
    frozen = manifest(PACKET/"FROZEN-PACKET-HASHES.txt", WORKSPACE,
                      PACKET/"provenance"/"frozen-packet")
    parts = reachable_tex(PACKET/"main.tex")
    source = "\n".join(parts)
    labels = re.findall(r"\\label\{([^}]+)\}", source)
    references = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", source)
    assert len(labels) == len(set(labels)), "Duplicate labels"
    assert set(references) <= set(labels), sorted(set(references)-set(labels))
    bibliography = set(re.findall(r"\\bibitem\{([^}]+)\}", source))
    citations = set()
    for group in re.findall(r"\\cite(?:\[[^]]*\])*\{([^}]+)\}", source):
        citations.update(group.split(","))
    assert citations <= bibliography, sorted(citations-bibliography)
    metadata = json.loads((PACKET/"packet-metadata.json").read_text())
    pages = {}
    pdfinfo = shutil.which("pdfinfo") or str(POPP/"pdfinfo")
    for name, expected in metadata["pages"].items():
        if name == "plain-language/results-explained":
            log_path = PACKET/"plain-language"/"build"/"overview.log"
        else:
            log_path = PACKET/"build"/(name+".log")
        log = log_path.read_text()
        assert not re.search(r"Warning:|Overfull|undefined|Rerun to get", log), name
        info = subprocess.check_output([pdfinfo, str(PACKET/(name+".pdf"))], text=True)
        count = int(re.search(r"^Pages:\s+(\d+)", info, re.M)[1])
        assert count == expected, (name, count, expected)
        pages[name] = count
    assert pages["reading-guide"] <= 2
    plain = (PACKET/"plain-language"/"overview.tex").read_text()
    assert "\\end{document}" in plain
    for check in ["check_fibers.py", "check_boundaries.py", "check_linear_algebra.py"]:
        subprocess.run([sys.executable, "-B", str(PACKET/"verification"/check)],
                       check=True, stdout=subprocess.DEVNULL)
    counts = metadata["checks"]
    assert len(json.loads((PACKET/"verification"/"fiber-checks.json").read_text())
               ["cases"]) == counts["fiber_configuration_cases"]
    assert len(json.loads((PACKET/"verification"/"boundary-checks.json").read_text())
               ["cycle_cases"]) == counts["cycle_cases"]
    assert len(json.loads((PACKET/"verification"/"boundary-checks.json").read_text())
               ["ambiguity_constant_cases"]) == counts["ambiguity_constant_cases"]
    assert len(json.loads((PACKET/"verification"/"linear-algebra-checks.json").read_text())
               ["cases"]) == counts["linear_algebra_cases"]
    # The checks may regenerate reports: verify the final outputs too.
    manifest(PACKET/"SHA256SUMS.txt", PACKET)
    report = {"status": "PASS", "packet_hashes": internal,
              "source_bindings_and_snapshots": sources,
              "frozen_packet_files": frozen, "active_tex_files": len(parts),
              "labels": len(labels), "references": len(references),
              "bibliography_entries": len(bibliography), "pages": pages,
              "exact_checks": counts}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()


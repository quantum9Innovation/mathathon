from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import argparse

from PIL import Image, ImageDraw


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SNAPSHOTS = ROOT / "manuscript-round-01"
parser = argparse.ArgumentParser()
parser.add_argument("--output-root", type=Path, required=True)
args = parser.parse_args()
OUTPUT = args.output_root.resolve()
OUTPUT.mkdir(parents=True, exist_ok=True)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, cwd=None):
    return subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=True).stdout


def blocks(path):
    expression = r"\\begin\{(theorem|lemma|corollary|proposition|proof|example)\}.*?\\end\{\1\}"
    result = []
    for source in sorted((path / "manuscript").rglob("*.tex")):
        result.extend(m.group(0) for m in re.finditer(expression, source.read_text(), re.S))
    return Counter(result)


@lru_cache(None)
def polynomial(n, h, s):
    if h == 0:
        return 1
    return sum(
        comb(h - 1, j - 1) * ((j - 1) * n + s) * factorial(j - 1)
        * polynomial(n, h - j, s)
        for j in range(1, h + 1)
    )


def direct_scaled(n, cells):
    total = sum(
        prod((n * int(sigma[row] == col) - 1) ** power for row, col, power in cells)
        for sigma in permutations(range(n))
    )
    return Fraction(total, factorial(n))


def verify_algebra():
    pairs = [(row, 2 * row + offset, 1) for row in range(4) for offset in range(2)]
    pair_value = direct_scaled(8, pairs)
    clique_value = direct_scaled(8, [(0, col, 1) for col in range(8)])
    row_expansion = sum(Fraction(comb(4, j) * (-2) ** j * 8**j * factorial(8 - j), factorial(8)) for j in range(5))
    assert pair_value == row_expansion == Fraction(1121, 105)
    assert clique_value == -7
    comparisons = 0
    for n in range(1, 31):
        for h in range(n + 1):
            for s in range(n - h + 1):
                shape = n - s - h + 1
                derangement = sum(
                    comb(h, j) * (-n) ** j * factorial(shape + h - j - 1) // factorial(shape - 1)
                    for j in range(h + 1)
                )
                assert polynomial(n, h, s) == (-1) ** h * derangement
                comparisons += 1
    remark_values = []
    for n in range(4, 9):
        actual = direct_scaled(n, [(0, 0, 2), (0, 1, 2), (0, 2, 1), (0, 3, 1)])
        assert actual == 2 * n - 5
        remark_values.append({"n": n, "scaled_by_n6": str(actual)})
    return {
        "b8_disjoint_pairs_scaled_expectation": str(pair_value),
        "b8_clique_scaled_expectation": str(clique_value),
        "b8_row_expansion": str(row_expansion),
        "derangement_identity_exact_integer_comparisons": comparisons,
        "cn_remark_original_product_checks": remark_values,
    }


def build_and_render(version):
    snapshot = SNAPSHOTS / ("frozen-manuscript-v" + str(version))
    prefix = "assembled-v" + str(version)
    manifest = json.loads((snapshot / "MANIFEST.json").read_text())
    manifest_checks = []
    for entry in manifest:
        actual = sha(snapshot / entry["path"])
        assert actual == entry["sha256"]
        manifest_checks.append({**entry, "matches": True})
    build = OUTPUT / (prefix + "-build")
    shutil.copytree(snapshot, build, dirs_exist_ok=True)
    rendering = OUTPUT / (prefix + "-pages")
    rendering.mkdir(exist_ok=True)
    documents = []
    for kind, source, pdf_name in [
        ("main", "manuscript/main.tex", "centered-permutation-products.pdf"),
        ("guide", "guide/reading-guide.tex", "reading-guide.pdf"),
    ]:
        local = build / source
        for iteration in range(3):
            output = run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", local.name], cwd=local.parent)
            (OUTPUT / (prefix + "-" + kind + "-pass" + str(iteration + 1) + ".txt")).write_text(output)
        frozen_pdf = snapshot / "output/pdf" / pdf_name
        rebuilt_pdf = local.with_suffix(".pdf")
        frozen_text = run(["pdftotext", "-layout", str(frozen_pdf), "-"])
        rebuilt_text = run(["pdftotext", "-layout", str(rebuilt_pdf), "-"])
        assert frozen_text == rebuilt_text, (version, kind)
        (OUTPUT / (prefix + "-" + kind + "-text.txt")).write_text(frozen_text)
        final_log = local.with_suffix(".log").read_text()
        warning_lines = [line for line in final_log.splitlines() if any(term in line for term in ["Warning", "Overfull", "Underfull", "undefined", "multiply defined"])]
        assert not warning_lines, (version, kind, warning_lines)
        info = run(["pdfinfo", str(frozen_pdf)])
        page_count = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
        page_dir = rendering / kind
        page_dir.mkdir(exist_ok=True)
        run(["pdftoppm", "-png", "-r", "90", str(frozen_pdf), str(page_dir / "page")])
        pages = sorted(page_dir.glob("page-*.png"))
        assert len(pages) == page_count
        contacts = []
        for offset in range(0, len(pages), 9):
            group = pages[offset:offset + 9]
            sheet = Image.new("RGB", (1200, 1695), "#d0d0d0")
            draw = ImageDraw.Draw(sheet)
            for index, page in enumerate(group):
                with Image.open(page) as im:
                    im.thumbnail((386, 534))
                    x = (index % 3) * 400 + (400 - im.width) // 2
                    y = (index // 3) * 565 + 24
                    sheet.paste(im, (x, y))
                    draw.text(((index % 3) * 400 + 10, (index // 3) * 565 + 5), kind + " page " + str(offset + index + 1), fill="black")
            contact = rendering / (kind + "-contact-" + str(offset // 9 + 1) + ".png")
            sheet.save(contact)
            contacts.append(str(contact.relative_to(OUTPUT)))
        documents.append({
            "kind": kind,
            "frozen_pdf_sha256": sha(frozen_pdf),
            "page_count": page_count,
            "three_pass_rebuild_text_identical": True,
            "warnings": warning_lines,
            "contacts": contacts,
        })
    all_tex = "\n".join(path.read_text() for path in (snapshot / "manuscript").rglob("*.tex"))
    labels = re.findall(r"\\label\{([^}]+)\}", all_tex)
    refs = re.findall(r"\\(?:eqref|ref|pageref)\{([^}]+)\}", all_tex)
    assert len(labels) == len(set(labels))
    assert set(refs) <= set(labels)
    candidate = (ROOT / "extension-round-02/mixed-two-conflict/integration-candidate-v1.tex").read_text()
    mixed = (snapshot / "manuscript/sections/mixed.tex").read_text()
    assert candidate in mixed
    return {
        "version": version,
        "manifest_sha256": sha(snapshot / "MANIFEST.json"),
        "manifest_checks": manifest_checks,
        "documents": documents,
        "labels": len(labels),
        "unresolved_references": [],
        "duplicate_labels": [],
        "candidate_included_byte_for_byte": True,
    }


algebra = verify_algebra()
source_blocks = {v: blocks(SNAPSHOTS / ("frozen-manuscript-v" + str(v))) for v in [8, 9, 10]}
assert not (source_blocks[8] - source_blocks[9])
assert source_blocks[9] == source_blocks[10]
checks = [build_and_render(version) for version in [9, 10]]
changed_rasters = {}
for kind in ["main", "guide"]:
    old = OUTPUT / "assembled-v9-pages" / kind
    new = OUTPUT / "assembled-v10-pages" / kind
    changed_rasters[kind] = [int(path.stem.split("-")[-1]) for path in old.glob("page-*.png") if path.read_bytes() != (new / path.name).read_bytes()]
result = {
    "status": "all automated checks passed",
    "algebra": algebra,
    "formal_blocks": {str(v): sum(source_blocks[v].values()) for v in source_blocks},
    "old_v8_blocks_preserved_in_v9": True,
    "v9_v10_blocks_identical": True,
    "v9_v10_changed_page_rasters": changed_rasters,
    "revisions": checks,
}
(OUTPUT / "assembled-v9-v10-check-results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: value for key, value in result.items() if key != "revisions"}, indent=2))

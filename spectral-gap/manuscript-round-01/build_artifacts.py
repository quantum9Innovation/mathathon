"""Rebuild the manuscript and companion guide from their maintained sources."""

import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
OUTPUT = ROOT / "output" / "pdf"


def main():
    BUILD.mkdir(exist_ok=True)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, str(ROOT / "figures" / "build_figures.py")], check=True)
    for folder, source, destination in [
        ("manuscript", "main", "centered-permutation-products"),
        ("guide", "reading-guide", "reading-guide"),
    ]:
        for number in range(1, 4):
            result = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 f"-output-directory={BUILD}", source + ".tex"],
                cwd=ROOT / folder, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            (BUILD / f"{source}-pass-{number}.txt").write_text(result.stdout)
            if result.returncode:
                raise RuntimeError(f"Build failed, inspect {source}-pass-{number}.txt")
        log = (BUILD / (source + ".log")).read_text()
        bad = [line for line in log.splitlines()
               if "LaTeX Warning:" in line or "Overfull" in line]
        if bad:
            raise RuntimeError("Unresolved layout or reference warnings: " + " | ".join(bad))
        final_path = OUTPUT / (destination + ".pdf")
        shutil.copyfile(BUILD / (source + ".pdf"), final_path)
        print(final_path)


if __name__ == "__main__":
    main()

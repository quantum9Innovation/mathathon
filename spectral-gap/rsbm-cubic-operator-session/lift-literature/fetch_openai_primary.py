"""Fetch the two specifically requested primary manuscripts and path metadata."""

import json
from pathlib import Path
from urllib.request import Request, urlopen


DESTINATION = Path(__file__).parent
SOURCES = {
    "openai-rrg-september23": (
        "GOE-bulk-universality-for-fixed-degree-random-regular-graphs-September-23-2026",
        "paper.pdf",
    ),
    "openai-anderson-october5": (
        "Fixed-energy-universality-for-weak-Anderson-disorder-on-random-regular-graphs-October-5-2026",
        "fixed-energy-universality-weak-anderson-disorder-random-regular-graphs.pdf",
    ),
}


def fetch(url):
    request = Request(url, headers={"User-Agent": "research-primary-audit"})
    with urlopen(request, timeout=60) as response:
        return response.read()


if __name__ == "__main__":
    metadata = {}
    for label, (directory, filename) in SOURCES.items():
        url = f"https://raw.githubusercontent.com/openai/math/main/preprints/{directory}/{filename}"
        contents = fetch(url)
        assert contents.startswith(b"%PDF"), url
        (DESTINATION / f"{label}.pdf").write_bytes(contents)
        listing = json.loads(
            fetch(f"https://api.github.com/repos/openai/math/contents/preprints/{directory}")
        )
        metadata[label] = {"url": url, "directory_files": listing}
        print(label, len(contents), [entry["name"] for entry in listing])
    (DESTINATION / "openai-primary-metadata.json").write_text(
        json.dumps(metadata, indent=2) + "\n"
    )

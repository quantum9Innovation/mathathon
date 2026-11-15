#!/usr/bin/env python3
"""Archive one already downloaded paper source without executing it."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile

MAX_DOWNLOAD = 512 * 1024 * 1024
MAX_EXPANDED = 512 * 1024 * 1024
MAX_MEMBERS = 10000


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_members(archive):
    members = archive.getmembers()
    if len(members) > MAX_MEMBERS or sum(m.size for m in members) > MAX_EXPANDED:
        raise ValueError("Expanded archive exceeds the source size or member limit")
    for member in members:
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("Archive contains an unsafe path")
        if not member.isfile() and not member.isdir():
            raise ValueError("Archive contains a link or special file")
    return members


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("downloaded", type=Path)
    parser.add_argument("library_directory", type=Path)
    parser.add_argument("--source-url", default="")
    args = parser.parse_args()
    incoming = args.downloaded.resolve(strict=True)
    if incoming.stat().st_size > MAX_DOWNLOAD:
        raise ValueError("Download exceeds the source size limit")
    destination = args.library_directory.resolve()
    if destination.exists():
        raise ValueError("Library entry already exists. Inspect before replacing it")
    payload = incoming.read_bytes()
    receipt = {"source_file": incoming.name, "source_url": args.source_url,
               "download_sha256": digest(payload), "kind": None}
    destination.mkdir(parents=True)
    try:
        if payload.startswith(b"%PDF-"):
            (destination / "source.pdf").write_bytes(payload)
            receipt["kind"] = "pdf"
        elif tarfile.is_tarfile(incoming):
            with tempfile.TemporaryDirectory(dir=incoming.parent) as temporary:
                unpack = Path(temporary) / "unpacked"
                unpack.mkdir()
                with tarfile.open(incoming, "r:*") as archive:
                    safe_members(archive)
                    archive.extractall(unpack, filter="data")
                shutil.copytree(unpack, destination / "source")
            shutil.copyfile(incoming, destination / "source.archive")
            receipt["kind"] = "archive"
        elif payload.startswith(b"\x1f\x8b"):
            with gzip.open(incoming, "rb") as stream:
                expanded = stream.read(MAX_EXPANDED + 1)
            if len(expanded) > MAX_EXPANDED:
                raise ValueError("Expanded TeX source exceeds the size limit")
            (destination / "source").mkdir()
            (destination / "source/main.tex").write_bytes(expanded)
            receipt["kind"] = "single_gzip_tex"
        else:
            raise ValueError("Input is not a PDF, tar archive, or single gzipped TeX file")
        files = []
        for path in sorted(destination.rglob("*")):
            if path.is_file():
                files.append({"path": path.relative_to(destination).as_posix(),
                              "size": path.stat().st_size,
                              "sha256": digest(path.read_bytes())})
        receipt["files"] = files
        (destination / "source-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    except Exception:
        shutil.rmtree(destination)
        raise
    print(json.dumps({"library_directory": str(destination), "kind": receipt["kind"],
                      "download_sha256": receipt["download_sha256"]}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, tarfile.TarError) as error:
        raise SystemExit(f"Cannot archive source: {error}") from error

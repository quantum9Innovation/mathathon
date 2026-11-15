import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

MODULE_PATH = Path(__file__).resolve().parents[1] / "scripts/archive_source.py"
SPEC = importlib.util.spec_from_file_location("archive_source", MODULE_PATH)
archive_source = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = archive_source
SPEC.loader.exec_module(archive_source)


class ArchiveSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.saved_argv = sys.argv

    def tearDown(self):
        sys.argv = self.saved_argv
        self.temp.cleanup()

    def test_preserves_pdf_and_identity(self):
        downloaded = self.root / "paper.pdf"
        payload = b"%PDF-1.7\nexample source bytes\n"
        downloaded.write_bytes(payload)
        target = self.root / "library/paper"
        sys.argv = [
            "archive_source.py", str(downloaded), str(target), "--source-url", "https://example.invalid/paper"]
        archive_source.main()
        self.assertEqual((target / "source.pdf").read_bytes(), payload)
        receipt = json.loads((target / "source-receipt.json").read_text())
        self.assertEqual(receipt["download_sha256"], hashlib.sha256(payload).hexdigest())
        self.assertEqual(receipt["kind"], "pdf")

    def test_extracts_only_regular_safe_archive_contents(self):
        downloaded = self.root / "paper.src"
        with tarfile.open(downloaded, "w:gz") as source:
            member = tarfile.TarInfo("paper/main.tex")
            body = b"\\documentclass{article}\n\\begin{document}Text\\end{document}\n"
            member.size = len(body)
            source.addfile(member, io.BytesIO(body))
        target = self.root / "library/safe"
        sys.argv = ["archive_source.py", str(downloaded), str(target)]
        archive_source.main()
        self.assertIn("documentclass", (target / "source/paper/main.tex").read_text())
        self.assertTrue((target / "source.archive").is_file())

    def test_accepts_a_single_gzipped_tex_file(self):
        downloaded = self.root / "paper.src"
        with gzip.open(downloaded, "wb") as stream:
            stream.write(b"\\documentclass{article}\n")
        target = self.root / "library/single"
        sys.argv = ["archive_source.py", str(downloaded), str(target)]
        archive_source.main()
        self.assertIn("documentclass", (target / "source/main.tex").read_text())

    def test_rejects_traversal_and_removes_incomplete_library_entry(self):
        downloaded = self.root / "bad.src"
        with tarfile.open(downloaded, "w:gz") as source:
            member = tarfile.TarInfo("../escape")
            member.size = 1
            source.addfile(member, io.BytesIO(b"x"))
        target = self.root / "library/bad"
        sys.argv = ["archive_source.py", str(downloaded), str(target)]
        with self.assertRaisesRegex(ValueError, "unsafe path"):
            archive_source.main()
        self.assertFalse(target.exists())

    def test_rejects_links(self):
        downloaded = self.root / "linked.src"
        with tarfile.open(downloaded, "w:gz") as source:
            member = tarfile.TarInfo("source/link")
            member.type = tarfile.SYMTYPE
            member.linkname = "/etc/passwd"
            source.addfile(member)
        target = self.root / "library/linked"
        sys.argv = ["archive_source.py", str(downloaded), str(target)]
        with self.assertRaisesRegex(ValueError, "link or special"):
            archive_source.main()
        self.assertFalse(target.exists())


if __name__ == "__main__":
    unittest.main()

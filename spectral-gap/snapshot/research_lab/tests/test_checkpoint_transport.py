import json
import io
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from unittest import mock

from research_lab import checkpoint_transport as transport


def reply():
    return {"action": "checkpoint", "summary": "saved before completion", "target": "T",
            "argument": "partial", "claims": [], "sources": [],
            "strongest_objection": "unfinished", "next_action": "continue", "code": ""}


class CheckpointTests(unittest.TestCase):
    def test_structured_evidence_checks_frozen_hash_and_preserves_legacy_entries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.txt"
            source.write_bytes(b"FROZEN_SOURCE")
            manifest = root / "manifest.json"
            entry = {"path": str(source), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            manifest.write_text(json.dumps({"source": entry, "legacy": str(source)}))
            catalog = transport.EvidenceCatalog(manifest)
            self.assertEqual(catalog.read("source")["text"], "FROZEN_SOURCE")
            self.assertEqual(catalog.read("legacy")["text"], "FROZEN_SOURCE")
            entry["sha256"] = "0" * 64
            manifest.write_text(json.dumps({"source": entry}))
            with self.assertRaisesRegex(ValueError, "hash"):
                transport.EvidenceCatalog(manifest)

    def test_structured_evidence_rechecks_hash_when_size_inode_and_mtime_match(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.txt"
            source.write_bytes(b"ORIGINAL")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"source": {"path": str(source),
                                                     "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}}))
            catalog = transport.EvidenceCatalog(manifest)
            original = source.stat()
            source.write_bytes(b"MUTATION")
            os.utime(source, ns=(original.st_atime_ns, original.st_mtime_ns))
            self.assertEqual(source.stat().st_ino, original.st_ino)
            self.assertEqual(source.stat().st_size, original.st_size)
            self.assertEqual(source.stat().st_mtime_ns, original.st_mtime_ns)
            with self.assertRaisesRegex(ValueError, "hash"):
                catalog.read("source")

    def test_structured_evidence_rejects_symlink_parent_and_malformed_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actual = root / "actual"
            actual.mkdir()
            source = actual / "source.txt"
            source.write_bytes(b"FROZEN")
            (root / "linked").symlink_to(actual, target_is_directory=True)
            manifest = root / "manifest.json"
            entry = {"path": str(root / "linked/source.txt"), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
            manifest.write_text(json.dumps({"source": entry}))
            with self.assertRaisesRegex(ValueError, "symbolic"):
                transport.EvidenceCatalog(manifest)
            for bad in ({"path": str(source)}, {"path": str(source), "sha256": []},
                        {"path": str(source), "sha256": "wrong"},
                        {"path": str(source), "sha256": "0" * 64, "extra": True}):
                with self.subTest(entry=bad), self.assertRaises(ValueError):
                    manifest.write_text(json.dumps({"source": bad}))
                    transport.EvidenceCatalog(manifest)

    def test_loaded_manifest_does_not_reload_new_ids_or_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_text("allowed")
            private = root / "private.txt"
            private.write_text("PRIVATE_VALUE")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior": str(prior)}))
            catalog = transport.EvidenceCatalog(manifest)
            manifest.write_text(json.dumps({"prior": str(private), "private": str(private)}))
            self.assertEqual(catalog.read("prior")["text"], "allowed")
            with self.assertRaises(ValueError):
                catalog.read("private")

    def test_evidence_tools_are_unavailable_without_a_manifest(self):
        requests = [{"jsonrpc": "2.0", "id": index, "method": "tools/call",
                     "params": {"name": name, "arguments": arguments}}
                    for index, (name, arguments) in enumerate(
                        [("list_evidence", {}), ("read_evidence", {"id": "prior"})], 1)]
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            transport.serve(directory, io.StringIO("\n".join(map(json.dumps, requests))), output)
            results = [json.loads(line)["result"] for line in output.getvalue().splitlines()]
        self.assertTrue(all(result["isError"] for result in results))

    def test_evidence_listing_is_paged_with_bounded_integer_arguments(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_text("saved")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({f"step-{index:03d}": str(prior) for index in range(201)}))
            catalog = transport.EvidenceCatalog(manifest)
            first = catalog.list()
            self.assertEqual(len(first["evidence"]), 100)
            self.assertEqual(first["next_offset"], 100)
            last = catalog.list(offset=200, limit=200)
            self.assertEqual([item["id"] for item in last["evidence"]], ["step-200"])
            self.assertIsNone(last["next_offset"])
            for options in ({"offset": -1}, {"offset": True}, {"limit": 0}, {"limit": 201}, {"limit": 1.5}):
                with self.subTest(options=options), self.assertRaises(ValueError):
                    catalog.list(**options)

    def test_evidence_rejects_unknown_ids_paths_and_malformed_arguments_without_crashing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_text("allowed")
            private = root / "private.txt"
            private.write_text("PRIVATE_VALUE")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior": str(prior)}))
            cases = [("read_evidence", {"id": "../private.txt"}),
                     ("read_evidence", {"id": str(private)}),
                     ("read_evidence", {"id": "prior", "path": str(private)}),
                     ("read_evidence", {"id": []}), ("read_evidence", None),
                     ("list_evidence", []), ("list_evidence", {"path": str(private)})]
            requests = [{"jsonrpc": "2.0", "id": index, "method": "tools/call",
                         "params": {"name": name, "arguments": arguments}}
                        for index, (name, arguments) in enumerate(cases, 1)]
            requests.append({"jsonrpc": "2.0", "id": 99, "method": "ping"})
            output = io.StringIO()
            transport.serve(root / "receipts", io.StringIO("\n".join(map(json.dumps, requests))),
                            output, evidence_manifest=manifest)
            results = [json.loads(line)["result"] for line in output.getvalue().splitlines()]
            self.assertTrue(all(result["isError"] for result in results[:-1]))
            self.assertEqual(results[-1], {})
            self.assertNotIn("PRIVATE_VALUE", output.getvalue())

    def test_manifest_configuration_enables_only_four_fixed_tools_and_cli_reads(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_text("retained derivation")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior": str(prior)}))
            flags = transport.checkpoint_mcp_overrides(root / "receipts", evidence_manifest=manifest)
            settings = tomllib.loads(flags[1])["mcp_servers"]["checkpoint"]
            expected = ["save_checkpoint", "remaining_budget", "list_evidence", "read_evidence"]
            self.assertEqual(settings["enabled_tools"], expected)
            self.assertEqual(settings["tools"], {name: {"approval_mode": "approve"} for name in expected})
            request = {"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                       "params": {"name": "read_evidence", "arguments": {"id": "prior"}}}
            result = subprocess.run([settings["command"], *settings["args"]],
                                    input=json.dumps(request) + "\n", capture_output=True, text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
            output = json.loads(result.stdout)["result"]
            self.assertEqual(json.loads(output["content"][0]["text"])["text"], "retained derivation")

    def test_evidence_cannot_follow_replaced_files_or_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_text("allowed")
            outside = root / "private.txt"
            outside.write_text("PRIVATE_VALUE")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior": str(prior)}))
            catalog = transport.EvidenceCatalog(manifest)
            prior.unlink()
            prior.symlink_to(outside)
            with self.assertRaises((ValueError, OSError)):
                catalog.read("prior")

    def test_evidence_reads_are_bounded_and_report_truncation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.txt"
            prior.write_bytes(b"x" * (256 * 1024 + 10))
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior": str(prior)}))
            result = transport.EvidenceCatalog(manifest).read("prior")
            self.assertEqual(len(result["text"].encode()), 256 * 1024)
            self.assertEqual(result["bytes"], 256 * 1024)
            self.assertTrue(result["truncated"])

    def test_evidence_tools_list_and_read_only_the_manifest_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prior = root / "prior.json"
            prior.write_text(json.dumps(reply()))
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"prior-step": str(prior)}))
            requests = [{"jsonrpc": "2.0", "id": 1, "method": "tools/list"},
                        {"jsonrpc": "2.0", "id": 2, "method": "tools/call",
                         "params": {"name": "list_evidence", "arguments": {}}},
                        {"jsonrpc": "2.0", "id": 3, "method": "tools/call",
                         "params": {"name": "read_evidence", "arguments": {"id": "prior-step"}}}]
            output = io.StringIO()
            transport.serve(root / "receipts", io.StringIO("\n".join(map(json.dumps, requests))),
                            output, evidence_manifest=manifest)
            results = [json.loads(line)["result"] for line in output.getvalue().splitlines()]
            self.assertEqual({item["name"] for item in results[0]["tools"]},
                             {"save_checkpoint", "remaining_budget", "list_evidence", "read_evidence"})
            self.assertEqual(json.loads(results[1]["content"][0]["text"]),
                             {"evidence": [{"id": "prior-step", "bytes": prior.stat().st_size}], "next_offset": None})
            saved = json.loads(results[2]["content"][0]["text"])
            self.assertEqual(json.loads(saved["text"]), reply())
            self.assertFalse(saved["truncated"])

    def test_checkpoint_count_limit_preserves_existing_receipts(self):
        with tempfile.TemporaryDirectory() as directory:
            store = transport.CheckpointStore(directory)
            store.save(reply())
            original = (Path(directory) / "checkpoint-000001.json").read_bytes()
            with mock.patch.object(transport, "MAX_CHECKPOINTS", 1, create=True):
                with self.assertRaises(ValueError):
                    store.save(reply())
            self.assertEqual((Path(directory) / "checkpoint-000001.json").read_bytes(), original)

    def test_checkpoint_storage_rejects_oversized_receipts(self):
        with tempfile.TemporaryDirectory() as directory:
            oversized = reply()
            oversized["argument"] = "x" * (256 * 1024)
            with self.assertRaises(ValueError):
                transport.CheckpointStore(directory).save(oversized)
            self.assertEqual(list(Path(directory).glob("checkpoint-*.json")), [])

    def test_non_object_tool_parameters_cannot_crash_server(self):
        requests = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": []},
                    {"jsonrpc": "2.0", "id": 2, "method": "ping"}]
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            transport.serve(directory, io.StringIO("\n".join(map(json.dumps, requests))), output)
            responses = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertTrue(responses[0]["result"]["isError"])
        self.assertEqual(responses[1]["result"], {})

    def test_malformed_messages_do_not_disable_following_valid_requests(self):
        good = {"jsonrpc": "2.0", "id": 2, "method": "ping"}
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            transport.serve(directory, io.StringIO("{bad\n[]\n" + json.dumps(good)), output)
            responses = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(responses[0]["error"]["code"], -32700)
        self.assertEqual(responses[1]["error"]["code"], -32600)
        self.assertEqual(responses[2]["result"], {})

    def test_command_overrides_allow_only_fixed_server_and_checkpoint_tools(self):
        with tempfile.TemporaryDirectory() as directory:
            options = transport.checkpoint_mcp_overrides(directory, deadline=123.5)
            self.assertEqual(options[0], "-c")
            settings = tomllib.loads(options[1])["mcp_servers"]["checkpoint"]
            self.assertEqual(settings["enabled_tools"], ["save_checkpoint", "remaining_budget"])
            self.assertEqual(settings["env_vars"], [])
            self.assertEqual(settings["tools"], {"save_checkpoint": {"approval_mode": "approve"},
                                                 "remaining_budget": {"approval_mode": "approve"}})
            self.assertEqual(settings["args"][-4:], ["--directory", directory, "--deadline", "123.5"])
            self.assertEqual(settings["command"], sys.executable)

    def test_budget_never_reports_negative_remaining_time(self):
        request = {"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                   "params": {"name": "remaining_budget", "arguments": {}}}
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            transport.serve(directory, io.StringIO(json.dumps(request)), output, deadline=time.time() - 1)
            result = json.loads(output.getvalue())["result"]
        self.assertEqual(json.loads(result["content"][0]["text"])["remaining_seconds"], 0)

    def test_protocol_negotiates_and_lists_only_checkpoint_and_budget_tools(self):
        requests = [{"jsonrpc": "2.0", "id": 1, "method": "initialize",
                     "params": {"protocolVersion": "2024-11-05"}},
                    {"jsonrpc": "2.0", "method": "notifications/initialized"},
                    {"jsonrpc": "2.0", "id": 2, "method": "tools/list"}]
        with tempfile.TemporaryDirectory() as directory:
            output = io.StringIO()
            transport.serve(directory, io.StringIO("\n".join(map(json.dumps, requests))), output)
            responses = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(responses[0]["result"]["protocolVersion"], "2024-11-05")
        self.assertEqual({item["name"] for item in responses[1]["result"]["tools"]},
                         {"save_checkpoint", "remaining_budget"})

    def test_stdio_tool_saves_before_server_process_ends(self):
        with tempfile.TemporaryDirectory() as directory:
            process = subprocess.Popen(
                [sys.executable, str(Path(transport.__file__)), "--directory", directory],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            try:
                request = {"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                           "params": {"name": "save_checkpoint", "arguments": {"checkpoint": reply()}}}
                process.stdin.write(json.dumps(request) + "\n")
                process.stdin.flush()
                response = json.loads(process.stdout.readline() or "{}")
                self.assertIn("result", response)
                self.assertEqual(json.loads((Path(directory) / "checkpoint-000001.json").read_text()), reply())
                self.assertIsNone(process.poll())
            finally:
                process.kill()
                process.wait(timeout=3)
                process.stdin.close()
                process.stdout.close()
            self.assertEqual(json.loads((Path(directory) / "checkpoint-000001.json").read_text()), reply())

    def test_invalid_checkpoint_cannot_create_a_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            invalid = reply()
            invalid["write_path"] = "../escape"
            with self.assertRaises(ValueError):
                transport.CheckpointStore(directory).save(invalid)
            self.assertEqual(list(Path(directory).glob("checkpoint-*.json")), [])

    def test_receipts_are_numbered_and_survive_server_restart(self):
        with tempfile.TemporaryDirectory() as directory:
            first = transport.CheckpointStore(directory).save(reply())
            original = (Path(directory) / first["receipt"]).read_bytes()
            second = transport.CheckpointStore(directory).save(reply())
            self.assertEqual(first["receipt"], "checkpoint-000001.json")
            self.assertEqual(second["receipt"], "checkpoint-000002.json")
            self.assertEqual((Path(directory) / first["receipt"]).read_bytes(), original)
            self.assertEqual(json.loads(original), reply())

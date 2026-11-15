import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest

from research_lab import checkpoint_transport as transport

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("parallel_runner", ROOT / "parallel_runner.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class ParallelTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.packet = self.root / "packet"
        self.packet.mkdir()
        (self.packet / "task.md").write_text("Original problem without the candidate")
        (self.packet / "candidate.md").write_text("CANDIDATE_SECRET")
        self.plan = self.packet / "dag.json"
        self.plan.write_text(json.dumps({"tasks": [
            {"id": "blind", "role": "reconstruction", "instruction": "task.md", "inputs": [],
             "depends_on": [], "max_calls": 2, "priority": 100},
            {"id": "audit", "role": "algebra_audit", "instruction": "task.md", "inputs": ["candidate.md"],
             "depends_on": [], "max_calls": 2, "priority": 100},
            {"id": "final", "role": "synthesis", "instruction": "task.md", "inputs": [],
             "depends_on": ["blind", "audit"], "max_calls": 2, "priority": 90}]}))
        self.run = self.root / "run"

    def tearDown(self):
        self.temp.cleanup()

    def _deferred_packet(self):
        source = self.packet / "sources/reference.txt"
        source.parent.mkdir(exist_ok=True)
        source.write_text("FROZEN_SOURCE_EVIDENCE")
        plan = json.loads(self.plan.read_text())
        plan["tasks"][0].update(inputs=["sources/reference.txt"], deferred_inputs=["sources/reference.txt"])
        self.plan.write_text(json.dumps(plan))
        return source

    def _save_reply(self, job, relative, argument, action="checkpoint"):
        path = self.run / "jobs" / job["id"] / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        reply = {"action": action, "summary": argument, "target": "T", "argument": argument,
                 "claims": [], "sources": [], "strongest_objection": "none checked",
                 "next_action": "done" if action == "finish" else "review", "code": ""}
        path.write_text(json.dumps(reply))
        return str(path.relative_to(self.run))

    def test_prepare_freezes_default_routes_and_blind_input_isolation(self):
        runner.prepare_run(self.plan, self.run, minutes=60)
        state = json.loads((self.run / "state.json").read_text())
        self.assertEqual(state["config"]["total_seconds"], 3600)
        self.assertEqual(state["config"]["reasoning_effort"], "high")
        self.assertEqual(state["jobs"][0]["route"]["model"], "gpt-6.1-sol")
        blind = "".join(p.read_text() for p in (self.run / "jobs/blind/input").rglob("*") if p.is_file())
        self.assertNotIn("CANDIDATE_SECRET", blind)

    def test_prepare_freezes_fast_xhigh_override_and_detects_tampering(self):
        runner.prepare_run(self.plan, self.run, minutes=20, reasoning_effort="xhigh", service_tier="fast")
        state = json.loads((self.run / "state.json").read_text())
        runner.audit_run(self.run, state)
        self.assertEqual(state["config"]["total_seconds"], 1200)
        self.assertEqual(state["profile"]["review_reserve_seconds"], 900)
        for job in state["jobs"]:
            config = dict(state["config"], **job["route"])
            command = runner.engine.worker_command("/worker", config, self.run, "s", "o")
            self.assertIn('model_reasoning_effort="xhigh"', command)
            self.assertIn('service_tier="fast"', command)
            self.assertIn("features.fast_mode=true", command)
        state["jobs"][0]["route"]["service_tier"] = "standard"
        with self.assertRaises(ValueError):
            runner.audit_run(self.run, state)

    def test_two_hour_many_preparation_preserves_routes_and_passes_frozen_policy_audit(self):
        plan = json.loads(self.plan.read_text())
        plan["tasks"].insert(-1, dict(plan["tasks"][1], id="averaging", role="averaging_audit"))
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run, minutes=120, profile_name="many", allow_large=True)
        state = json.loads((self.run / "state.json").read_text())
        self.assertEqual(state["config"]["total_seconds"], 7200)
        self.assertEqual({key: state["config"][key] for key in
                          ("model", "reasoning_effort", "billing", "network")},
                         {"model": "gpt-6.1-sol", "reasoning_effort": "high",
                          "billing": "subscription_only", "network": "public_sources"})
        self.assertEqual(state["profile"]["max_parallel_workers"], 16)
        self.assertEqual(state["profile"]["total_seconds"], 10800)
        self.assertFalse(state["profile"]["enabled"])
        self.assertTrue(state["large_profile_authorized"])
        self.assertEqual({job["role"]: job["route"] for job in state["jobs"]},
                         {role: {"model": "gpt-6.1-sol", "reasoning_effort": effort}
                          for role, effort in (("reconstruction", "high"), ("algebra_audit", "xhigh"),
                                               ("averaging_audit", "max"), ("synthesis", "max"))})
        runner.audit_run(self.run, state)

    def test_deferred_source_stays_frozen_and_fully_readable_without_prompt_body(self):
        source = self.packet / "sources/reference.txt"
        source.parent.mkdir()
        contents = ("DEFERRED_SOURCE_PROOF_é\n" * 2000).encode()
        source.write_bytes(contents)
        plan = json.loads(self.plan.read_text())
        plan["tasks"][0].update(inputs=["sources/reference.txt"], deferred_inputs=["sources/reference.txt"])
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        job = state["jobs"][0]
        frozen = self.run / "jobs/blind/input/sources/reference.txt"
        source.write_text("LATER_PACKET_CHANGE")
        prompt = runner.call_prompt(self.run, state, job, 600)
        identifier = "jobs/blind/input/sources/reference.txt"
        self.assertNotIn("DEFERRED_SOURCE_PROOF", prompt)
        self.assertIn(identifier, prompt)
        self.assertIn(str(len(contents)), prompt)
        self.assertIn(job["input_hashes"]["sources/reference.txt"], prompt)
        self.assertIn("read_evidence", prompt)
        self.assertIn("after the initial checkpoint", prompt)
        self.assertEqual(frozen.read_bytes(), contents)
        self.assertEqual(frozen.stat().st_mode & 0o222, 0)
        manifest = runner.evidence_manifest(self.run, state, job)
        manifest_path = self.root / "manifest.json"
        manifest_path.write_text(json.dumps(manifest))
        result = transport.EvidenceCatalog(manifest_path).read(identifier)
        self.assertEqual(result["text"].encode(), contents)
        self.assertFalse(result["truncated"])
        self.assertNotIn("jobs/blind/input/task.md", manifest)
        self.assertIn("CANDIDATE_SECRET", runner.call_prompt(self.run, state, state["jobs"][1], 600))

    def test_direct_context_supplies_complete_branch_review_and_retains_original_ancestor_evidence(self):
        self._deferred_packet()
        plan = runner.read_json(self.plan)
        plan["tasks"].insert(-1, dict(plan["tasks"][0], id="review", role="algebra_audit",
                                      depends_on=["blind"], inputs=[], deferred_inputs=[]))
        plan["tasks"][-1].update(depends_on=["review"], dependency_context="direct", finalization_only=True)
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        blind, _, review, final = state["jobs"]
        blind["latest_checkpoint"] = self._save_reply(blind, "calls/001-test/checkpoints/checkpoint-000001.json",
                                                       "ORIGINAL_ANCESTOR_PROOF")
        review["latest_response"] = self._save_reply(review, "calls/001-test/controller_reply.json", "OLDER_LONG_PARTIAL")
        review["final_reply"] = self._save_reply(review, "submission.json", "COMPLETE_BRANCH_REVIEW", action="finish")
        review["status"] = "completed"
        prompt = runner.call_prompt(self.run, state, final, 600)
        self.assertNotIn("ORIGINAL_ANCESTOR_PROOF", prompt)
        self.assertNotIn("OLDER_LONG_PARTIAL", prompt)
        self.assertEqual(prompt.count('"argument": "COMPLETE_BRANCH_REVIEW"'), 1)
        self.assertIn("record status complete", prompt)
        self.assertIn("original ancestor", prompt)
        self.assertIn("FINALIZATION ONLY", prompt)
        self.assertIn("first external action must publish", prompt)
        manifest_path = self.root / "manifest.json"
        manifest_path.write_text(json.dumps(runner.evidence_manifest(self.run, state, final)))
        catalog = transport.EvidenceCatalog(manifest_path)
        self.assertIn("ORIGINAL_ANCESTOR_PROOF", catalog.read(blind["latest_checkpoint"])["text"])
        self.assertEqual(catalog.read("jobs/blind/input/sources/reference.txt")["text"], "FROZEN_SOURCE_EVIDENCE")

    def test_direct_context_marks_newest_dependency_record_incomplete_without_final_submission(self):
        plan = runner.read_json(self.plan)
        plan["tasks"][-1]["dependency_context"] = "direct"
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        job = state["jobs"][0]
        job["latest_checkpoint"] = self._save_reply(job, "calls/001-test/checkpoints/checkpoint-000001.json", "LATEST_STEP")
        job["latest_response"] = self._save_reply(job, "calls/001-test/controller_reply.json", "RETURNED_PARTIAL")
        import os
        os.utime(self.run / job["latest_checkpoint"], ns=(100, 100))
        os.utime(self.run / job["latest_response"], ns=(200, 200))
        prompt = runner.call_prompt(self.run, state, state["jobs"][-1], 600)
        self.assertNotIn("LATEST_STEP", prompt)
        self.assertIn("RETURNED_PARTIAL", prompt)
        self.assertIn("record status incomplete", prompt)
        os.utime(self.run / job["latest_checkpoint"], ns=(300, 300))
        prompt = runner.call_prompt(self.run, state, state["jobs"][-1], 600)
        self.assertIn("LATEST_STEP", prompt)
        self.assertNotIn("RETURNED_PARTIAL", prompt)
        self.assertIn(job["latest_checkpoint"], runner.evidence_manifest(self.run, state, state["jobs"][-1]))
        self.assertIn(job["latest_response"], runner.evidence_manifest(self.run, state, state["jobs"][-1]))

    def test_default_transitive_context_keeps_all_ancestor_records(self):
        plan = runner.read_json(self.plan)
        plan["tasks"][1]["depends_on"] = ["blind"]
        plan["tasks"][-1]["depends_on"] = ["audit"]
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        blind, audit, final = state["jobs"]
        blind["latest_checkpoint"] = self._save_reply(blind, "calls/001-test/checkpoints/checkpoint-000001.json", "GRANDPARENT_STEP")
        audit["latest_response"] = self._save_reply(audit, "calls/001-test/controller_reply.json", "PARENT_PARTIAL")
        audit["final_reply"] = self._save_reply(audit, "submission.json", "PARENT_FINAL", action="finish")
        prompt = runner.call_prompt(self.run, state, final, 600)
        for marker in ("GRANDPARENT_STEP", "PARENT_PARTIAL", "PARENT_FINAL"):
            self.assertIn(marker, prompt)
        self.assertNotIn("record status", prompt)
        final["dependency_context"] = "transitive"
        self.assertEqual(runner.call_prompt(self.run, state, final, 600), prompt)

    def test_deferred_sources_respect_root_isolation_and_transitive_review_access(self):
        self._deferred_packet()
        other = self.packet / "sources/other.txt"
        other.write_text("UNRELATED_ROOT_SOURCE")
        plan = runner.read_json(self.plan)
        plan["tasks"][1].update(inputs=["candidate.md", "sources/other.txt"], deferred_inputs=["sources/other.txt"])
        plan["tasks"].insert(-1, dict(plan["tasks"][0], id="review", role="algebra_audit",
                                      depends_on=["blind"], inputs=[], deferred_inputs=[], dependency_context="direct"))
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        blind, _, review, final = state["jobs"]
        own = "jobs/blind/input/sources/reference.txt"
        unrelated = "jobs/audit/input/sources/other.txt"
        for job in (blind, review):
            manifest = runner.evidence_manifest(self.run, state, job)
            self.assertIn(own, manifest)
            self.assertNotIn(unrelated, manifest)
            self.assertNotIn("jobs/audit/input/candidate.md", manifest)
            path = self.root / f"{job['id']}-manifest.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "Unknown evidence id"):
                transport.EvidenceCatalog(path).read(unrelated)
        manifest = runner.evidence_manifest(self.run, state, final)
        self.assertIn(own, manifest)
        self.assertIn(unrelated, manifest)

    def test_invalid_deferred_inputs_are_rejected_before_any_preparation(self):
        self._deferred_packet()
        plan = runner.read_json(self.plan)
        invalid = (None, "sources/reference.txt", [True], ["sources/reference.txt"] * 2,
                   ["sources/missing.txt"], ["../reference.txt"], ["/sources/reference.txt"],
                   ["sources/../reference.txt"], ["sources//reference.txt"], ["sources/./reference.txt"],
                   ["task.md"], ["worker_contract.md"], ["protocol.md"])
        for deferred in invalid:
            with self.subTest(deferred=deferred):
                plan["tasks"][0]["deferred_inputs"] = deferred
                self.plan.write_text(json.dumps(plan))
                with self.assertRaises(ValueError):
                    runner.prepare_run(self.plan, self.run)
                self.assertFalse(self.run.exists())
        plan["tasks"][0].update(instruction="sources/reference.txt", deferred_inputs=["sources/reference.txt"])
        self.plan.write_text(json.dumps(plan))
        with self.assertRaises(ValueError):
            runner.prepare_run(self.plan, self.run)
        self.assertFalse(self.run.exists())

    def test_invalid_dependency_context_is_rejected_before_preparation(self):
        plan = runner.read_json(self.plan)
        for value in (None, [], True, "all", "DIRECT"):
            with self.subTest(context=value):
                plan["tasks"][0]["dependency_context"] = value
                self.plan.write_text(json.dumps(plan))
                with self.assertRaises(ValueError):
                    runner.prepare_run(self.plan, self.run)
                self.assertFalse(self.run.exists())

    def test_deferred_sources_cannot_exceed_the_complete_read_limit(self):
        source = self._deferred_packet()
        source.write_bytes(b"x" * (transport.MAX_EVIDENCE_BYTES + 1))
        with self.assertRaisesRegex(ValueError, "complete evidence read limit"):
            runner.prepare_run(self.plan, self.run)
        self.assertFalse(self.run.exists())

    def test_deferred_source_symlinks_are_rejected_before_preparation(self):
        source = self._deferred_packet()
        target = self.packet / "actual.txt"
        target.write_text("FROZEN_SOURCE_EVIDENCE")
        source.unlink()
        source.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "symbolic"):
            runner.prepare_run(self.plan, self.run)
        self.assertFalse(self.run.exists())
        source.unlink()
        source.parent.rmdir()
        target_dir = self.packet / "actual"
        target_dir.mkdir()
        (target_dir / "reference.txt").write_text("FROZEN_SOURCE_EVIDENCE")
        source.parent.symlink_to(target_dir, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symbolic"):
            runner.prepare_run(self.plan, self.run)
        self.assertFalse(self.run.exists())

    def test_frozen_deferred_sources_reject_change_missing_file_and_symlink_parents(self):
        self._deferred_packet()
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        job = state["jobs"][0]
        source = self.run / "jobs/blind/input/sources/reference.txt"
        contents = source.read_bytes()
        target = self.root / "same.txt"
        target.write_bytes(contents)
        for mutation in ("changed", "missing", "symlink", "parent_symlink", "input_symlink"):
            with self.subTest(mutation=mutation):
                if mutation == "changed":
                    source.chmod(0o644)
                    source.write_bytes(b"CHANGED_SOURCE")
                elif mutation == "missing":
                    source.unlink()
                elif mutation == "symlink":
                    source.unlink()
                    source.symlink_to(target)
                else:
                    source.unlink()
                    directory = source.parent if mutation == "parent_symlink" else source.parent.parent
                    if mutation == "input_symlink":
                        import shutil
                        shutil.rmtree(directory)
                    else:
                        directory.rmdir()
                    actual = self.root / mutation
                    actual.mkdir()
                    if mutation == "input_symlink":
                        (actual / "sources").mkdir()
                        (actual / "sources/reference.txt").write_bytes(contents)
                    else:
                        (actual / "reference.txt").write_bytes(contents)
                    directory.symlink_to(actual, target_is_directory=True)
                for operation in (lambda: runner.call_prompt(self.run, state, job, 600),
                                  lambda: runner.evidence_manifest(self.run, state, job),
                                  lambda: runner.audit_run(self.run, state)):
                    with self.assertRaises(ValueError):
                        operation()
                if mutation == "input_symlink":
                    directory.unlink()
                    directory.mkdir()
                    for name, text in (("task.md", "Original problem without the candidate"),
                                       ("worker_contract.md", (ROOT / "pilot/prompts/contract.md").read_text())):
                        (directory / name).write_text(text)
                    source.parent.mkdir()
                elif mutation == "parent_symlink":
                    directory.unlink()
                    directory.mkdir()
                elif source.exists() or source.is_symlink():
                    source.unlink()
                source.write_bytes(contents)

    def test_context_options_are_frozen_in_policy_audit(self):
        self._deferred_packet()
        plan = runner.read_json(self.plan)
        plan["tasks"][0]["dependency_context"] = "direct"
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = runner.read_json(self.run / "state.json")
        runner.audit_run(self.run, state)
        for key, value in (("deferred_inputs", []), ("dependency_context", "transitive")):
            changed = json.loads(json.dumps(state))
            changed["jobs"][0][key] = value
            with self.subTest(field=key), self.assertRaisesRegex(ValueError, "Frozen execution policy changed"):
                runner.audit_run(self.run, changed)

    def test_completed_work_releases_time_for_final_verification(self):
        runner.prepare_run(self.plan, self.run, minutes=60)
        state = json.loads((self.run / "state.json").read_text())
        state.update(started_at=100, deadline=3700)
        state["profile"]["call_seconds"] = 3000
        first = runner.allocate_seconds(state, state["jobs"][0], now=100)
        for job in state["jobs"][:-1]:
            job["status"] = "completed"
        final = runner.allocate_seconds(state, state["jobs"][-1], now=100)
        self.assertGreater(final, first)

    def test_parallel_workers_are_bounded_and_dependencies_follow_roots(self):
        plan = json.loads(self.plan.read_text())
        for name in ("third", "fourth"):
            plan["tasks"].insert(-1, dict(plan["tasks"][0], id=name))
            plan["tasks"][-1]["depends_on"].append(name)
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        active = 0
        peak = 0
        completed = set()
        mutex = threading.Lock()

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            nonlocal active, peak
            with mutex:
                if job["id"] == "final":
                    self.assertEqual(completed, {"blind", "audit", "third", "fourth"})
                active += 1
                peak = max(peak, active)
            time.sleep(0.08)
            with mutex:
                active -= 1
                completed.add(job["id"])
            reply = {"action": "finish", "summary": "synthetic checked result", "target": "T", "argument": "A",
                     "claims": [], "sources": [], "strongest_objection": "none checked", "next_action": "done", "code": ""}
            return {"transport": {"reason": "completed", "returncode": 0, "seconds": 0.08}, "reply": reply}

        runner.run_jobs(self.run, client="/fake", invoke=fake, check_runtime=False)
        state = json.loads((self.run / "state.json").read_text())
        self.assertEqual(peak, 3)
        self.assertLessEqual(peak, 3)
        self.assertEqual(state["status"], "completed_with_submissions")

    def test_finished_tool_checkpoint_survives_timeout_and_finishes_submission(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        job = state["jobs"][0]
        folder = self.run / "jobs/blind/calls/001-saved/checkpoints"
        folder.mkdir(parents=True)
        reply = {"action": "finish", "summary": "saved before interruption", "target": "T", "argument": "A",
                 "claims": [], "sources": [], "strongest_objection": "none found", "next_action": "check", "code": ""}
        (folder / "checkpoint-000001.json").write_text(json.dumps(reply))
        runner.harvest_checkpoints(self.run, state)
        runner.apply_outcome(self.run, job, {"transport": {"reason": "timeout", "seconds": 30}, "reply": None})
        self.assertEqual(job["status"], "completed")
        self.assertEqual(json.loads((self.run / job["final_reply"]).read_text())["summary"], "saved before interruption")

    def test_execution_uses_checkpoint_tools_and_explicit_high_route(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state["client"] = "/fake"
        job = state["jobs"][0]
        calls = []

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            calls.append((command, prompt))
            Path(logfile).write_text("")
            reply = {"action": "finish", "summary": "done", "target": "T", "argument": "A", "claims": [],
                     "sources": [], "strongest_objection": "none", "next_action": "done", "code": ""}
            Path(command[command.index("--output-last-message") + 1]).write_text(json.dumps(reply))
            return {"reason": "completed", "returncode": 0, "seconds": 0.1}

        from unittest import mock
        with mock.patch.object(runner.engine, "bounded_run", side_effect=fake):
            outcome = runner.execute_call(self.run, state, job, "001-test", 600, self.run / "stop")
        self.assertEqual(outcome["reply"]["action"], "finish")
        self.assertIn('model_reasoning_effort="high"', calls[0][0])
        self.assertTrue(any("mcp_servers.checkpoint=" in x for x in calls[0][0]))
        self.assertIn("save_checkpoint", calls[0][1])

    def test_returned_partial_work_is_included_in_continuation(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        job = state["jobs"][0]
        reply = {"action": "checkpoint", "summary": "newer partial argument", "target": "T", "argument": "NEW_PROOF_STEP",
                 "claims": [], "sources": [], "strongest_objection": "gap", "next_action": "next step", "code": ""}
        runner.apply_outcome(self.run, job, {"transport": {"reason": "completed", "seconds": 1}, "reply": reply})
        self.assertIn("NEW_PROOF_STEP", runner.call_prompt(self.run, state, job, 600))

    def test_resume_preserves_global_deadline_and_prior_receipt(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        deadline = time.time() + 1200
        state.update(started_at=time.time(), deadline=deadline)
        job = state["jobs"][0]
        job.update(status="running", calls=1, active_deadline=time.time() + 0.2)
        folder = self.run / "jobs/blind/calls/001-prior/checkpoints"
        folder.mkdir(parents=True)
        reply = {"action": "checkpoint", "summary": "prior work", "target": "T", "argument": "SAVED_STEP", "claims": [],
                 "sources": [], "strongest_objection": "gap", "next_action": "continue", "code": ""}
        receipt = folder / "checkpoint-000001.json"
        receipt.write_text(json.dumps(reply))
        runner.engine.atomic_json(self.run / "state.json", state)
        dispatch_start = time.monotonic()

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            self.assertGreaterEqual(time.monotonic() - dispatch_start, 0.15)
            persisted = json.loads((run_dir / "state.json").read_text())
            self.assertEqual(persisted["deadline"], deadline)
            self.assertGreaterEqual(persisted["calls"], 1)
            if job["id"] == "blind":
                self.assertEqual(job["calls"], 2)
                self.assertIn("SAVED_STEP", runner.call_prompt(run_dir, state, job, seconds))
            return {"transport": {"reason": "completed", "returncode": 0}, "reply": dict(reply, action="finish")}

        runner.run_jobs(self.run, client="/fake", invoke=fake, check_runtime=False)
        recovered = json.loads((self.run / "state.json").read_text())
        self.assertEqual(recovered["deadline"], deadline)
        self.assertTrue(receipt.exists())
        self.assertEqual(recovered["status"], "completed_with_submissions")

    def test_expired_run_launches_no_new_call(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state.update(started_at=1, deadline=2)
        runner.engine.atomic_json(self.run / "state.json", state)

        def forbidden(*args):
            self.fail("Expired run launched a worker")

        runner.run_jobs(self.run, invoke=forbidden, check_runtime=False)
        self.assertEqual(json.loads((self.run / "state.json").read_text())["status"], "time_limit")

    def test_checkpoint_watchdog_interrupts_stalled_call(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state.update(client="/fake")
        state["profile"].update(checkpoint_seconds=0.01, checkpoint_grace_seconds=0.01)
        stop = self.run / "watchdog-stop"

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            Path(logfile).write_text("")
            limit = time.monotonic() + 2
            while not stop_file.exists() and time.monotonic() < limit:
                time.sleep(0.02)
            return {"reason": "stopped", "returncode": -15, "seconds": 0.3}

        from unittest import mock
        with mock.patch.object(runner.engine, "bounded_run", side_effect=fake):
            outcome = runner.execute_call(self.run, state, state["jobs"][0], "001-stall", 600, stop)
        self.assertEqual(outcome["transport"]["reason"], "checkpoint_stall")

    def test_preparation_cannot_exceed_profile_duration_ceiling(self):
        with self.assertRaises(ValueError):
            runner.prepare_run(self.plan, self.run, minutes=121)

    def test_two_hour_many_preparation_requires_explicit_activation(self):
        with self.assertRaisesRegex(ValueError, "explicit activation"):
            runner.prepare_run(self.plan, self.run, minutes=120, profile_name="many")
        self.assertFalse(self.run.exists())

    def test_many_preparation_rejects_more_than_three_hours(self):
        with self.assertRaisesRegex(ValueError, "180"):
            runner.prepare_run(self.plan, self.run, minutes=181, profile_name="many", allow_large=True)
        self.assertFalse(self.run.exists())

    def test_three_hour_many_preparation_requires_activation_and_keeps_frozen_limits(self):
        with self.assertRaisesRegex(ValueError, "explicit activation"):
            runner.prepare_run(self.plan, self.run, minutes=180, profile_name="many")
        self.assertFalse(self.run.exists())
        runner.prepare_run(self.plan, self.run, minutes=180, profile_name="many", allow_large=True)
        state = runner.read_json(self.run / "state.json")
        self.assertEqual(state["config"]["total_seconds"], 10800)
        self.assertEqual(state["profile"]["max_task_seconds"], 3600)
        self.assertFalse(state["profile"]["enabled"])
        runner.audit_run(self.run, state)
        state["large_profile_authorized"] = False
        with self.assertRaisesRegex(ValueError, "Frozen execution policy changed"):
            runner.audit_run(self.run, state)

    def test_historical_two_hour_many_frozen_profile_still_passes_audit(self):
        runner.prepare_run(self.plan, self.run, minutes=120, profile_name="many", allow_large=True)
        state = runner.read_json(self.run / "state.json")
        state["profile"].update(total_seconds=7200, max_task_seconds=2400)
        state["policy_hash"] = runner.policy_hash(state)
        runner.audit_run(self.run, state)

    def test_three_hour_plan_and_frozen_profile_limits_cannot_be_bypassed(self):
        plan = runner.read_json(self.plan)
        plan["global_runtime_seconds"] = 7200
        self.plan.write_text(json.dumps(plan))
        with self.assertRaisesRegex(ValueError, "ceiling"):
            runner.prepare_run(self.plan, self.run, minutes=180, profile_name="many", allow_large=True)
        self.assertFalse(self.run.exists())
        runner.prepare_run(self.plan, self.run, minutes=120, profile_name="many", allow_large=True)
        state = runner.read_json(self.run / "state.json")
        state["profile"]["max_task_seconds"] = 2400
        with self.assertRaisesRegex(ValueError, "Frozen execution policy changed"):
            runner.audit_run(self.run, state)

    def test_historical_hour_many_frozen_profile_still_passes_audit(self):
        runner.prepare_run(self.plan, self.run, minutes=60, profile_name="many", allow_large=True)
        state = json.loads((self.run / "state.json").read_text())
        state["profile"]["total_seconds"] = 3600
        state["policy_hash"] = runner.policy_hash(state)
        runner.audit_run(self.run, state)

    def test_two_hour_many_frozen_policy_rejects_duration_change(self):
        runner.prepare_run(self.plan, self.run, minutes=120, profile_name="many", allow_large=True)
        state = json.loads((self.run / "state.json").read_text())
        state["config"]["total_seconds"] = 3600
        with self.assertRaisesRegex(ValueError, "Frozen execution policy changed"):
            runner.audit_run(self.run, state)

    def test_input_traversal_names_are_rejected_before_copy(self):
        plan = json.loads(self.plan.read_text())
        plan["tasks"][0]["inputs"] = ["../packet/task.md"]
        self.plan.write_text(json.dumps(plan))
        with self.assertRaises(ValueError):
            runner.prepare_run(self.plan, self.run)

    def test_changed_policy_is_rejected_before_resume(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state["jobs"][0]["route"]["reasoning_effort"] = "max"
        with self.assertRaises(ValueError):
            runner.audit_run(self.run, state)

    def test_downstream_receives_newer_receipts_and_older_returned_response(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        job = state["jobs"][0]
        (self.run / "old.json").write_text('"OLDER_RESPONSE"')
        (self.run / "new.json").write_text('"NEW_DURABLE_STEP"')
        job.update(latest_response="old.json", latest_checkpoint="new.json", status="limited")
        prompt = runner.call_prompt(self.run, state, state["jobs"][-1], 600)
        self.assertIn("OLDER_RESPONSE", prompt)
        self.assertIn("NEW_DURABLE_STEP", prompt)

    def test_abandoned_call_time_is_charged_before_resuming_task(self):
        plan = json.loads(self.plan.read_text())
        plan["tasks"][0]["max_calls"] = 6
        self.plan.write_text(json.dumps(plan))
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state.update(started_at=time.time(), deadline=time.time()+3600)
        state["jobs"][0].update(status="running", calls=4, consumed_seconds=1800,
                                reserved_seconds=600, active_deadline=time.time()-1)
        runner.engine.atomic_json(self.run / "state.json", state)

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            self.assertNotEqual(job["id"], "blind")
            reply = {"action": "finish", "summary": "done", "target": "T", "argument": "A", "claims": [],
                     "sources": [], "strongest_objection": "none", "next_action": "done", "code": ""}
            return {"transport": {"reason": "completed", "seconds": 1}, "reply": reply}

        runner.run_jobs(self.run, invoke=fake, check_runtime=False)
        recovered = json.loads((self.run / "state.json").read_text())
        self.assertEqual(recovered["jobs"][0]["consumed_seconds"], 2400)
        self.assertEqual(recovered["jobs"][0]["calls"], 4)

    def test_offline_preparation_refuses_subscription_launch(self):
        runner.prepare_run(self.plan, self.run, network="offline")
        from unittest import mock
        with mock.patch.object(runner.engine, "bounded_run", side_effect=AssertionError("Offline launched a process")):
            with self.assertRaisesRegex(ValueError, "offline"):
                runner.run_jobs(self.run, client="/fake")

    def test_evidence_manifest_preserves_incremental_steps_and_blindness(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        files = []
        for task, number in (("blind", 1), ("blind", 2), ("audit", 1)):
            path = self.run / "jobs" / task / "calls/001-test/checkpoints" / f"checkpoint-{number:06d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('{}')
            files.append(str(path.resolve()))
        blind = runner.evidence_manifest(self.run, state, state["jobs"][0])
        self.assertIn(files[0], blind.values())
        self.assertIn(files[1], blind.values())
        self.assertNotIn(files[2], blind.values())
        final = runner.evidence_manifest(self.run, state, state["jobs"][-1])
        self.assertIn(files[2], final.values())

    def test_evidence_manifest_rejects_symlink_into_other_task(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        secret = self.run / "jobs/audit/private.json"
        secret.write_text('"OTHER_WORKER_EVIDENCE"')
        path = self.run / "jobs/blind/calls/001-test/checkpoints/checkpoint-000001.json"
        path.parent.mkdir(parents=True)
        path.symlink_to(secret)
        with self.assertRaises(ValueError):
            runner.evidence_manifest(self.run, state, state["jobs"][0])

    def test_completed_run_resume_preserves_recorded_finish_and_verdict(self):
        runner.prepare_run(self.plan, self.run)
        state = json.loads((self.run / "state.json").read_text())
        state.update(status="completed_with_submissions", started_at=1, deadline=2, finished_at=1.5)
        for job in state["jobs"]:
            job["status"] = "completed"
        runner.engine.atomic_json(self.run / "state.json", state)
        original = (self.run / "state.json").read_bytes()
        runner.run_jobs(self.run, client="/fake", check_runtime=False)
        self.assertEqual((self.run / "state.json").read_bytes(), original)


if __name__ == "__main__":
    unittest.main()

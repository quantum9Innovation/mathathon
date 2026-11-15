import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("finalization_runner", ROOT / "parallel_runner.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class FinalizationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.packet = self.root / "packet"
        self.packet.mkdir()
        (self.packet / "task.md").write_text("Bounded test task")
        self.plan = self.packet / "dag.json"
        self.plan.write_text(json.dumps({"tasks": [
            {"id": "attempted", "role": "reconstruction", "instruction": "task.md", "inputs": [],
             "depends_on": [], "max_calls": 2},
            {"id": "unstarted", "role": "algebra_audit", "instruction": "task.md", "inputs": [],
             "depends_on": [], "max_calls": 2}]}))
        self.run = self.root / "run"
        runner.prepare_run(self.plan, self.run)
        self.state = runner.read_json(self.run / "state.json")

    def tearDown(self):
        self.temp.cleanup()

    def test_expiry_distinguishes_attempted_and_unstarted_tasks(self):
        self.state.update(started_at=1, deadline=2)
        self.state["jobs"][0]["calls"] = 1
        runner.engine.atomic_json(self.run / "state.json", self.state)
        runner.run_jobs(self.run, check_runtime=False)
        state = runner.read_json(self.run / "state.json")
        self.assertEqual(state["jobs"][0]["status"], "time_limit")
        self.assertEqual(state["jobs"][1]["status"], "unstarted_at_deadline")
        self.assertEqual(state["status"], "time_limit")
        self.assertIn("finished_at", state)

    def test_short_continuation_is_finalization_only(self):
        job = self.state["jobs"][0]
        job["calls"] = 1
        prompt = runner.call_prompt(self.run, self.state, job, 104)
        self.assertIn("FINALIZATION ONLY", prompt)
        self.assertIn("action=finish", prompt)
        self.assertIn("Do not restart", prompt)

    def test_call_allowance_cannot_cross_its_phase_cutoff(self):
        self.state.update(started_at=100, deadline=7300)
        self.state["config"]["total_seconds"] = 7200
        job = self.state["jobs"][0]
        job["finish_by_fraction"] = 1 / 3
        allowance = runner.allocate_seconds(self.state, job, now=2490)
        self.assertGreater(allowance, 0)
        self.assertLessEqual(allowance, 10)

    def test_invalid_phase_fraction_is_rejected_before_preparation(self):
        plan = runner.read_json(self.plan)
        plan["tasks"][0]["finish_by_fraction"] = 1.1
        self.plan.write_text(json.dumps(plan))
        with self.assertRaises(ValueError):
            runner.prepare_run(self.plan, self.root / "invalid")

    def test_phase_cutoff_cannot_change_after_freezing(self):
        plan = runner.read_json(self.plan)
        plan["tasks"][0]["finish_by_fraction"] = 0.5
        self.plan.write_text(json.dumps(plan))
        path = self.root / "phased"
        runner.prepare_run(self.plan, path)
        state = runner.read_json(path / "state.json")
        state["jobs"][0]["finish_by_fraction"] = 1
        with self.assertRaises(ValueError):
            runner.audit_run(path, state)

    def test_two_hour_preparation_keeps_the_bounded_worker_limit(self):
        path = self.root / "two-hour"
        runner.prepare_run(self.plan, path, minutes=120)
        state = runner.read_json(path / "state.json")
        self.assertEqual(state["config"]["total_seconds"], 7200)
        self.assertEqual(state["profile"]["max_parallel_workers"], 3)
        self.assertFalse(state["large_profile_authorized"])

    def test_deadline_report_keeps_proofs_hidden_by_a_later_plan_note(self):
        folder = self.run / "jobs/attempted/calls/001-test/checkpoints"
        folder.mkdir(parents=True)
        reply = {"action": "checkpoint", "summary": "checked step", "target": "T",
                 "argument": "EARLIER_RECONSTRUCTIBLE_PROOF", "claims": [], "sources": [],
                 "strongest_objection": "gap remains", "next_action": "review", "code": ""}
        (folder / "checkpoint-000001.json").write_text(json.dumps(reply))
        reply.update(summary="new initialization", argument="PLAN_NOTE_ONLY")
        (folder / "checkpoint-000002.json").write_text(json.dumps(reply))
        self.state.update(started_at=1, deadline=2)
        self.state["jobs"][0]["calls"] = 1
        runner.engine.atomic_json(self.run / "state.json", self.state)
        runner.run_jobs(self.run, check_runtime=False)
        self.assertIn("EARLIER_RECONSTRUCTIBLE_PROOF", (self.run / "EVIDENCE.md").read_text())
        self.assertIn("PLAN_NOTE_ONLY", (self.run / "EVIDENCE.md").read_text())
        self.assertIn("EVIDENCE.md", (self.run / "FINAL_REPORT.md").read_text())

    def test_expired_closed_run_preserves_its_historical_state(self):
        self.state.update(status="time_limit", started_at=1, deadline=2, finished_at=2.1)
        self.state.pop("report_bundle_version", None)
        self.state["policy_hash"] = runner.policy_hash(self.state)
        self.state["jobs"][0]["calls"] = 2
        runner.engine.atomic_json(self.run / "state.json", self.state)
        (self.run / "REPORT.md").write_text("HISTORICAL_REPORT_SENTINEL")
        original = (self.run / "state.json").read_bytes()
        runner.run_jobs(self.run, check_runtime=False)
        self.assertEqual((self.run / "state.json").read_bytes(), original)
        self.assertEqual((self.run / "REPORT.md").read_text(), "HISTORICAL_REPORT_SENTINEL")

    def test_closed_run_recovers_reports_without_reopening_research(self):
        self.state.update(status="time_limit", started_at=1, deadline=2, finished_at=2.1,
                          report_bundle_version=1)
        self.state["policy_hash"] = runner.policy_hash(self.state)
        runner.engine.atomic_json(self.run / "state.json", self.state)
        original = (self.run / "state.json").read_bytes()
        runner.run_jobs(self.run, check_runtime=False,
                        invoke=lambda *args: self.fail("Closed run launched a worker"))
        self.assertTrue((self.run / "FINAL_REPORT.md").exists())
        self.assertTrue((self.run / "EVIDENCE.md").exists())
        self.assertEqual((self.run / "state.json").read_bytes(), original)

    def test_last_continuation_finalizes_even_when_prior_calls_saved_nothing(self):
        job = self.state["jobs"][0]
        job.update(calls=2, max_calls=2)
        self.assertIn("FINALIZATION ONLY", runner.call_prompt(self.run, self.state, job, 600))

    def test_sole_research_call_keeps_its_research_allowance(self):
        job = self.state["jobs"][0]
        job.update(calls=1, max_calls=1)
        self.assertNotIn("FINALIZATION ONLY", runner.call_prompt(self.run, self.state, job, 600))

    def test_completed_run_recovers_missing_report_without_changing_finish(self):
        self.state.update(status="completed_with_submissions", started_at=1, deadline=2,
                          finished_at=1.5)
        for job in self.state["jobs"]:
            job["status"] = "completed"
        runner.engine.atomic_json(self.run / "state.json", self.state)
        original = (self.run / "state.json").read_bytes()
        runner.run_jobs(self.run, check_runtime=False)
        self.assertTrue((self.run / "FINAL_REPORT.md").exists())
        self.assertEqual((self.run / "state.json").read_bytes(), original)

    def test_last_continuation_and_explicit_final_task_finish_first(self):
        job = self.state["jobs"][0]
        prior = self.run / "prior.json"
        prior.write_text('"SAVED_CHECKED_ARGUMENT"')
        job.update(calls=2, latest_checkpoint="prior.json")
        self.assertIn("FINALIZATION ONLY", runner.call_prompt(self.run, self.state, job, 600))
        job.update(calls=1, finalization_only=True)
        self.assertIn("FINALIZATION ONLY", runner.call_prompt(self.run, self.state, job, 600))

    def test_live_deadline_marks_an_interrupted_attempt(self):
        import threading
        from unittest import mock
        active = threading.Event()
        for job in self.state["jobs"]:
            job["finish_by_fraction"] = 1
        self.state["policy_hash"] = runner.policy_hash(self.state)
        runner.engine.atomic_json(self.run / "state.json", self.state)

        def remaining(state, now=None):
            return 0 if active.is_set() else 3600

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            active.set()
            self.assertTrue(active.wait(1))
            import time
            end = time.monotonic() + 2
            while not stop_file.exists() and time.monotonic() < end:
                time.sleep(0.01)
            self.assertTrue(stop_file.exists())
            return {"transport": {"reason": "timeout", "seconds": 0.05}, "reply": None}

        with mock.patch.object(runner.engine, "remaining", side_effect=remaining):
            runner.run_jobs(self.run, invoke=fake, check_runtime=False)
        state = runner.read_json(self.run / "state.json")
        self.assertEqual(state["status"], "time_limit")
        self.assertEqual(state["jobs"][0]["status"], "time_limit")


class IncrementalFinalizationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.packet = self.root / "packet"
        self.packet.mkdir()
        (self.packet / "task.md").write_text("Save a concise checked result with exact evidence references.")
        self.plan = self.packet / "dag.json"
        self.plan.write_text(json.dumps({"tasks": [
            {"id": "branch", "role": "reconstruction", "instruction": "task.md", "inputs": [],
             "depends_on": [], "max_calls": 1},
            {"id": "report", "role": "reporting", "instruction": "task.md", "inputs": [],
             "depends_on": ["branch"], "max_calls": 2, "finalization_only": True,
             "incremental_finalization": True, "dependency_context": "direct"}]}))
        self.run = self.root / "run"

    def tearDown(self):
        self.temp.cleanup()

    def prepare(self):
        runner.prepare_run(self.plan, self.run)
        return runner.read_json(self.run / "state.json")

    def reply(self, argument="CHECKED_BRANCH_ARGUMENT", action="finish"):
        return {"action": action, "summary": argument, "target": "T", "argument": argument,
                "claims": [], "sources": [], "strongest_objection": "A gap remains",
                "next_action": "Review the gap", "code": ""}

    def test_reporting_opt_in_allows_saved_incremental_assembly_before_explicit_finish(self):
        state = self.prepare()
        job = state["jobs"][-1]
        job["calls"] = 1
        prompt = runner.call_prompt(self.run, state, job, 600)
        self.assertIn("INCREMENTAL FINALIZATION", prompt)
        self.assertIn("action=checkpoint", prompt)
        self.assertIn("concise useful result", prompt)
        self.assertIn("action=finish", prompt)
        self.assertNotIn("first external action must publish the best available complete result", prompt)

    def test_incremental_policy_is_frozen_for_new_reporting_tasks(self):
        state = self.prepare()
        state["jobs"][-1]["incremental_finalization"] = False
        with self.assertRaisesRegex(ValueError, "Frozen execution policy changed"):
            runner.audit_run(self.run, state)

    def test_incremental_opt_in_rejects_non_reporting_or_non_finalization_tasks(self):
        original = runner.read_json(self.plan)
        for change in ({"incremental_finalization": "true"}, {"role": "synthesis"},
                       {"finalization_only": False}):
            with self.subTest(change=change):
                plan = json.loads(json.dumps(original))
                plan["tasks"][-1].update(change)
                self.plan.write_text(json.dumps(plan))
                with self.assertRaisesRegex(ValueError, "[Ii]ncremental"):
                    runner.prepare_run(self.plan, self.run)
                self.assertFalse(self.run.exists())

    def test_index_precedes_zero_output_reporting_and_survives_exhaustion(self):
        self.prepare()
        attempted = []

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            if job["id"] == "branch":
                return {"transport": {"seconds": 0.01}, "reply": self.reply()}
            attempted.append((run_dir / "EVIDENCE_INDEX.json").exists())
            if not attempted[-1]:
                return {"transport": {"seconds": 0.01, "reason": "checkpoint_stall"}, "reply": None}
            index = runner.read_json(run_dir / "EVIDENCE_INDEX.json")
            self.assertIn("not mathematical certification", index["notice"])
            branch = next(task for task in index["tasks"] if task["id"] == "branch")
            record = next(record for record in branch["records"] if record["path"].endswith("submission.json"))
            self.assertEqual(record["sha256"], runner.engine.digest(run_dir / record["path"]))
            self.assertEqual(record["action"], "finish")
            self.assertIn("jobs/branch/submission.json", (run_dir / "EVIDENCE_INDEX.md").read_text())
            return {"transport": {"seconds": 0.01, "reason": "checkpoint_stall"}, "reply": None}

        runner.run_jobs(self.run, invoke=fake, check_runtime=False)
        state = runner.read_json(self.run / "state.json")
        self.assertTrue(all(attempted), "Controller evidence index was absent before reporting")
        self.assertEqual(len(attempted), 2)
        self.assertEqual(state["status"], "partial_submissions")
        self.assertEqual(state["jobs"][-1]["status"], "limited")
        self.assertNotIn("final_reply", state["jobs"][-1])
        self.assertIn("CHECKED_BRANCH_ARGUMENT", (self.run / "EVIDENCE.md").read_text())
        self.assertIn("Call allowance exhausted", (self.run / "FINAL_REPORT.md").read_text())
        self.assertIn("[Saved evidence index](EVIDENCE_INDEX.md)", (self.run / "FINAL_REPORT.md").read_text())
        original = (self.run / "EVIDENCE_INDEX.json").read_bytes()
        runner.write_report(self.run, state)
        self.assertEqual((self.run / "EVIDENCE_INDEX.json").read_bytes(), original)

    def test_interrupted_initial_receipt_resumes_incrementally_under_the_same_clock(self):
        import time
        state = self.prepare()
        started = time.time()
        deadline = started + 1800
        state.update(started_at=started, deadline=deadline)
        runner.engine.atomic_json(self.run / "state.json", state)

        def first(run_dir, state, job, call_id, seconds, stop_file):
            if job["id"] == "branch":
                return {"transport": {"seconds": 0.01}, "reply": self.reply()}
            folder = run_dir / "jobs/report/calls" / call_id / "checkpoints"
            folder.mkdir()
            runner.engine.atomic_json(folder / "checkpoint-000001.json",
                                      self.reply("INITIAL_USEFUL_REPORT_SECTION", action="checkpoint"))
            (run_dir / "STOP").touch()
            return {"transport": {"seconds": 0.01, "reason": "stopped"}, "reply": None}

        runner.run_jobs(self.run, invoke=first, check_runtime=False)
        interrupted = runner.read_json(self.run / "state.json")
        self.assertEqual(interrupted["status"], "stopped")
        self.assertEqual(interrupted["jobs"][-1]["calls"], 1)
        self.assertNotIn("final_reply", interrupted["jobs"][-1])
        receipt = interrupted["jobs"][-1]["latest_checkpoint"]
        original_receipt = (self.run / receipt).read_bytes()
        self.assertIn(receipt, (self.run / "EVIDENCE_INDEX.md").read_text())
        (self.run / "STOP").unlink()

        def finish(run_dir, state, job, call_id, seconds, stop_file):
            self.assertEqual(job["id"], "report")
            self.assertEqual(job["calls"], 2)
            self.assertEqual(state["started_at"], started)
            self.assertEqual(state["deadline"], deadline)
            self.assertIn("INITIAL_USEFUL_REPORT_SECTION", runner.call_prompt(run_dir, state, job, seconds))
            return {"transport": {"seconds": 0.01}, "reply": self.reply("FINISHED_RECONCILIATION")}

        runner.run_jobs(self.run, invoke=finish, check_runtime=False)
        resumed = runner.read_json(self.run / "state.json")
        self.assertEqual(resumed["status"], "completed_with_submissions")
        self.assertEqual(resumed["deadline"], deadline)
        self.assertEqual(resumed["calls"], 3)
        self.assertEqual((self.run / receipt).read_bytes(), original_receipt)
        self.assertIn("INITIAL_USEFUL_REPORT_SECTION", (self.run / "EVIDENCE.md").read_text())
        self.assertIn("FINISHED_RECONCILIATION", (self.run / "EVIDENCE.md").read_text())

    def test_partial_receipts_do_not_become_finish_when_report_calls_are_exhausted(self):
        self.prepare()

        def fake(run_dir, state, job, call_id, seconds, stop_file):
            action = "finish" if job["id"] == "branch" else "checkpoint"
            return {"transport": {"seconds": 0.01}, "reply": self.reply("SAVED_PARTIAL_SECTION", action=action)}

        runner.run_jobs(self.run, invoke=fake, check_runtime=False)
        state = runner.read_json(self.run / "state.json")
        report = state["jobs"][-1]
        self.assertEqual(report["calls"], 2)
        self.assertEqual(report["status"], "limited")
        self.assertNotIn("final_reply", report)
        self.assertFalse((self.run / "jobs/report/submission.json").exists())
        index = runner.read_json(self.run / "EVIDENCE_INDEX.json")
        records = next(task for task in index["tasks"] if task["id"] == "report")["records"]
        self.assertEqual([record["action"] for record in records], ["checkpoint", "checkpoint"])
        self.assertIn("SAVED_PARTIAL_SECTION", (self.run / "FINAL_REPORT.md").read_text())

    def test_expiry_retains_branch_evidence_and_original_deadline_without_reporting_output(self):
        state = self.prepare()
        branch = state["jobs"][0]
        path = self.run / "jobs/branch/submission.json"
        runner.engine.atomic_json(path, self.reply())
        branch.update(status="completed", calls=1, final_reply=str(path.relative_to(self.run)))
        state.update(started_at=1, deadline=2, calls=2)
        state["jobs"][-1].update(status="running", calls=1, reserved_seconds=600, active_deadline=3)
        runner.engine.atomic_json(self.run / "state.json", state)
        runner.run_jobs(self.run, check_runtime=False,
                        invoke=lambda *args: self.fail("Expired run launched reporting"))
        expired = runner.read_json(self.run / "state.json")
        self.assertEqual(expired["deadline"], 2)
        self.assertEqual(expired["jobs"][-1]["status"], "time_limit")
        self.assertEqual(expired["calls"], 2)
        self.assertIn("CHECKED_BRANCH_ARGUMENT", (self.run / "EVIDENCE.md").read_text())
        self.assertIn("jobs/branch/submission.json", (self.run / "EVIDENCE_INDEX.md").read_text())

    def test_closed_index_recovery_preserves_exact_state_and_never_restarts_work(self):
        self.prepare()
        base = runner.read_json(self.run / "state.json")
        path = self.run / "jobs/branch/submission.json"
        runner.engine.atomic_json(path, self.reply())
        base["jobs"][0].update(calls=1, final_reply=str(path.relative_to(self.run)), status="completed")
        for status in ("time_limit", "completed_with_submissions", "partial_submissions"):
            with self.subTest(status=status):
                state = json.loads(json.dumps(base))
                state.update(status=status, started_at=1, deadline=2, finished_at=1.9, calls=3)
                state["jobs"][-1].update(status="completed" if status == "completed_with_submissions" else "limited", calls=2)
                runner.engine.atomic_json(self.run / "state.json", state)
                for name in ("EVIDENCE_INDEX.json", "EVIDENCE_INDEX.md", "EVIDENCE.md", "REPORT.md", "FINAL_REPORT.md"):
                    (self.run / name).unlink(missing_ok=True)
                original = (self.run / "state.json").read_bytes()
                runner.run_jobs(self.run, check_runtime=False,
                                invoke=lambda *args: self.fail("Closed run launched reporting"))
                self.assertEqual((self.run / "state.json").read_bytes(), original)
                self.assertIn("not mathematical certification", (self.run / "EVIDENCE_INDEX.md").read_text())
                self.assertIn("jobs/branch/submission.json", (self.run / "EVIDENCE_INDEX.md").read_text())
                self.assertIn("CHECKED_BRANCH_ARGUMENT", (self.run / "EVIDENCE.md").read_text())


if __name__ == "__main__":
    unittest.main()

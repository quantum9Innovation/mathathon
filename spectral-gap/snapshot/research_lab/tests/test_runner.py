import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import sys
import unittest
from unittest import mock

MODULE_PATH = Path(__file__).resolve().parents[1] / "research_runner.py"
spec = importlib.util.spec_from_file_location("research_runner", MODULE_PATH)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class PilotTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        shutil.copytree(MODULE_PATH.parent / "tests/fixtures/pilot", self.root / "pilot")

    def tearDown(self):
        self.temp.cleanup()

    def test_prepare_exports_six_arms_without_answers(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(len(state["arms"]), 6)
        for arm in state["arms"]:
            names = {p.name for p in (directory / arm["id"] / "input").iterdir()}
            self.assertEqual(names, {"task.md", "instruction.md", "contract.md"})
            task = (directory / arm["id"] / "input" / "task.md").read_text()
            self.assertNotIn("reference checks", task.lower())

    def test_new_legacy_preparations_use_high_project_default(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(state["config"]["reasoning_effort"], "high")
        self.assertEqual(state["config"]["model"], "gpt-6.1-sol")

    def test_deadline_cannot_be_reset_by_resume(self):
        state = {"deadline": 1100, "config": {"total_seconds": 10800}}
        self.assertEqual(runner.remaining(state, now=1050), 50)
        self.assertEqual(runner.remaining(state, now=1200), 0)

    def test_one_hour_preparation_scales_allowances_without_changing_defaults(self):
        original = (self.root / "pilot/config.json").read_bytes()
        directory = runner.prepare(self.root, minutes=60)
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(state["config"]["total_seconds"], 3600)
        self.assertEqual(state["config"]["arm_seconds"], 500)
        self.assertTrue(all(sum(p["seconds"] for p in a["phases"]) == 500 for a in state["arms"]))
        self.assertEqual((self.root / "pilot/config.json").read_bytes(), original)

    def test_longer_preparation_keeps_planned_timeouts_at_phase_boundary(self):
        directory = runner.prepare(self.root, minutes=120)
        state = json.loads((directory / "state.json").read_text())
        longest = max(p["seconds"] for arm in state["arms"] for p in arm["phases"])
        self.assertGreaterEqual(state["config"]["call_seconds"], longest)

    def test_prepare_rejects_path_traversal(self):
        path = self.root / "pilot/config.json"
        config = json.loads(path.read_text())
        config["experiment_id"] = "../outside"
        path.write_text(json.dumps(config))
        with self.assertRaises(ValueError):
            runner.prepare(self.root)

    def test_audit_detects_changed_source_snapshot(self):
        sources = self.root / "sources"
        sources.mkdir()
        snapshot = sources / "snapshot.md"
        snapshot.write_text("original evidence")
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        snapshot.write_text("changed evidence")
        with self.assertRaises(ValueError):
            runner.audit(self.root, directory, state)

    def test_reply_cannot_accept_its_own_claims(self):
        reply = {"action": "finish", "summary": "partial", "target": "T", "argument": "A",
                 "claims": [{"id": "L1", "statement": "S", "status": "accepted",
                             "dependencies": [], "evidence": "E", "objection": "none"}],
                 "sources": [], "strongest_objection": "gap", "next_action": "check", "code": ""}
        with self.assertRaises(ValueError):
            runner.validate_reply(reply)

    def test_strict_offline_refuses_remote_subscription(self):
        with self.assertRaises(ValueError):
            runner.worker_command("/worker", {"network": "offline"}, self.root, "s", "o")

    def test_browsing_transport_keeps_local_tools_disabled(self):
        config = json.loads((self.root / "pilot/config.json").read_text())
        command = runner.worker_command("/worker", config, self.root, "s", "o")
        self.assertIn("features.code_mode_host=true", command)
        self.assertIn("features.shell_tool=false", command)
        self.assertIn('default_permissions="research-packet"', command)
        self.assertNotIn("--sandbox", command)

    def test_computation_mounts_only_its_script_without_network(self):
        config = json.loads((self.root / "pilot/config.json").read_text())
        command = runner.container_command(config, self.root / "experiment.py")
        self.assertIn("--network=none", command)
        self.assertIn("--pull=never", command)
        self.assertIn("--read-only", command)
        mounts = [command[i + 1] for i, arg in enumerate(command) if arg == "--volume"]
        self.assertEqual(len(mounts), 1)
        self.assertTrue(mounts[0].endswith(":/task.py:ro"))
        self.assertNotIn("socket", " ".join(command))

    def test_timeout_preserves_partial_output(self):
        log = self.root / "partial.log"
        command = [sys.executable, "-u", "-c", "import time\nprint('saved evidence')\ntime.sleep(5)"]
        result = runner.bounded_run(command, "", log, 0.2, 4096)
        self.assertEqual(result["reason"], "timeout")
        self.assertIn("saved evidence", log.read_text())

    def test_reconstruction_does_not_receive_candidate(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        arm = next(a for a in state["arms"] if a["condition"] == "workflow")
        (directory / arm["id"] / "solve.final.json").write_text('"CANDIDATE_SECRET"')
        prompt = runner.phase_prompt(self.root, directory, arm, {"name": "reconstruct"})
        self.assertNotIn("CANDIDATE_SECRET", prompt)

    def test_checkpoints_survive_and_finished_phase_is_not_repeated(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        arm = state["arms"][0]
        phase = arm["phases"][0]
        calls = []

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            calls.append(prompt)
            Path(logfile).write_text("synthetic transport log")
            reply = {"action": "checkpoint" if len(calls) == 1 else "finish",
                     "summary": "persistent finding", "target": "T", "argument": "partial",
                     "claims": [], "sources": [], "strongest_objection": "still provisional",
                     "next_action": "review", "code": ""}
            output = Path(command[command.index("--output-last-message") + 1])
            output.write_text(json.dumps(reply))
            return {"reason": "completed", "returncode": 0, "seconds": 0, "bytes": 0}

        runner.run_phase(self.root, directory, state, arm, phase, "/client", invoke=fake)
        self.assertEqual(phase["status"], "completed")
        self.assertIn("persistent finding", calls[1])
        runner.run_phase(self.root, directory, state, arm, phase, "/client", invoke=fake)
        self.assertEqual(len(calls), 2)
        self.assertTrue((directory / arm["id"] / "solve.final.json").exists())

    def test_critique_receives_incomplete_checkpoint(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        arm = next(a for a in state["arms"] if a["condition"] == "workflow")
        (directory / arm["id"] / "solve.latest.json").write_text('"PARTIAL_FINDING"')
        prompt = runner.phase_prompt(self.root, directory, arm, {"name": "critique"})
        self.assertIn("PARTIAL_FINDING", prompt)

    def test_critique_receives_computation_output_and_status(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        arm = next(a for a in state["arms"] if a["condition"] == "workflow")
        folder = directory / arm["id"] / "solve"
        folder.mkdir()
        (folder / "01-test.checkpoint.json").write_text('{}')
        (folder / "01-test.compute.log").write_text('ACTUAL_NUMERICAL_OUTPUT')
        (folder / "01-test.compute.result.json").write_text('{"reason":"timeout"}')
        prompt = runner.phase_prompt(self.root, directory, arm, {"name": "critique"})
        self.assertIn("ACTUAL_NUMERICAL_OUTPUT", prompt)
        self.assertIn('"reason":"timeout"', prompt)

    def test_successful_resume_clears_active_transport_failure(self):
        directory = runner.prepare(self.root)
        state = json.loads((directory / "state.json").read_text())
        arm = state["arms"][0]
        phase = arm["phases"][0]
        phase["status"] = "interrupted"
        phase["transport_failure"] = {"reason": "stopped"}

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            reply = {"action": "finish", "summary": "resumed", "target": "T", "argument": "partial",
                     "claims": [], "sources": [], "strongest_objection": "unverified",
                     "next_action": "review", "code": ""}
            output = Path(command[command.index("--output-last-message") + 1])
            output.write_text(json.dumps(reply))
            return {"reason": "completed", "returncode": 0}

        runner.run_phase(self.root, directory, state, arm, phase, "/client", invoke=fake)
        self.assertNotIn("transport_failure", phase)
        self.assertEqual(phase["status"], "completed")

    def test_preflight_accepts_raw_local_image_digest(self):
        config = json.loads((self.root / "pilot/config.json").read_text())

        def fake(command, prompt, log, *args):
            if "login" in command:
                content = "Logged in using subscription"
            elif "features" in command:
                content = "shell_tool unified_exec skip_host_skill_discovery apps hooks plugins"
            else:
                content = "a" * 64
            Path(log).write_text(content)
            return {"returncode": 0}

        with mock.patch.object(runner, "bounded_run", side_effect=fake):
            report = runner.preflight(self.root, config, sys.executable)
        self.assertEqual(report["image_id"], "sha256:" + "a" * 64)

    def test_controller_recovers_timeout_without_resetting_deadline(self):
        directory = runner.prepare(self.root)
        original = json.loads((directory / "state.json").read_text())
        deadline = runner.time.time() + 120
        original["started_at"] = runner.time.time()
        original["deadline"] = deadline
        runner.atomic_json(directory / "state.json", original)
        invoked = []

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            invoked.append(Path(logfile))
            Path(logfile).write_text("saved transport evidence")
            if len(invoked) == 1:
                return {"reason": "timeout", "returncode": -15}
            reply = {"action": "finish", "summary": "synthetic result", "target": "T", "argument": "A",
                     "claims": [], "sources": [], "strongest_objection": "unverified",
                     "next_action": "review", "code": ""}
            Path(command[command.index("--output-last-message") + 1]).write_text(json.dumps(reply))
            return {"reason": "completed", "returncode": 0}

        original_phase_runner = runner.run_phase

        def phase_runner(*args):
            return original_phase_runner(*args, invoke=fake)

        with mock.patch.object(runner, "preflight"), mock.patch.object(runner, "run_phase", side_effect=phase_runner):
            runner.run_experiment(self.root, directory, "/client")
            runner.run_experiment(self.root, directory, "/client")
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(state["deadline"], deadline)
        self.assertEqual(state["arms"][0]["phases"][0]["calls"], 2)
        self.assertEqual(state["status"], "queue_exhausted")
        self.assertTrue(invoked[0].exists())

    def test_malformed_submission_stops_before_next_phase(self):
        directory = runner.prepare(self.root)
        invoked = []

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            invoked.append(command)
            Path(command[command.index("--output-last-message") + 1]).write_text("invalid json")
            return {"reason": "completed", "returncode": 0}

        original_phase_runner = runner.run_phase

        def phase_runner(*args):
            return original_phase_runner(*args, invoke=fake)

        with mock.patch.object(runner, "preflight"), mock.patch.object(runner, "run_phase", side_effect=phase_runner):
            runner.run_experiment(self.root, directory, "/client")
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(state["status"], "submission_stopped")
        self.assertEqual(len(invoked), 1)

    def test_planned_phase_deadline_advances_to_later_tasks(self):
        directory = runner.prepare(self.root)
        invoked = []
        active = {}

        def fake(command, prompt, logfile, seconds, max_bytes, stop_file=None):
            invoked.append(command)
            Path(logfile).write_text("partial evidence retained")
            if len(invoked) == 1:
                active["phase"]["deadline"] = runner.time.time() - 1
                return {"reason": "timeout", "returncode": -9}
            reply = {"action": "finish", "summary": "synthetic result", "target": "T", "argument": "A",
                     "claims": [], "sources": [], "strongest_objection": "unverified",
                     "next_action": "review", "code": ""}
            Path(command[command.index("--output-last-message") + 1]).write_text(json.dumps(reply))
            return {"reason": "completed", "returncode": 0}

        original_phase_runner = runner.run_phase

        def phase_runner(root, directory, state, arm, phase, client):
            active["phase"] = phase
            return original_phase_runner(root, directory, state, arm, phase, client, invoke=fake)

        with mock.patch.object(runner, "preflight"), mock.patch.object(runner, "run_phase", side_effect=phase_runner):
            runner.run_experiment(self.root, directory, "/client")
        state = json.loads((directory / "state.json").read_text())
        self.assertEqual(state["status"], "queue_exhausted")
        self.assertEqual(state["arms"][0]["phases"][0]["status"], "time_limit")
        self.assertGreater(len(invoked), 1)

    def test_stop_marker_interrupts_call_and_preserves_output(self):
        log = self.root / "stopped.log"
        stop = self.root / "STOP"
        script = "from pathlib import Path\nimport time\nprint('checkpoint evidence', flush=True)\nPath(" + repr(str(stop)) + ").write_text('stop')\ntime.sleep(5)"
        result = runner.bounded_run([sys.executable, "-u", "-c", script], "", log, 2, 4096, stop_file=stop)
        self.assertEqual(result["reason"], "stopped")
        self.assertIn("checkpoint evidence", log.read_text())

    def test_output_cap_terminates_without_exceeding_log_limit(self):
        log = self.root / "capped.log"
        result = runner.bounded_run([sys.executable, "-u", "-c", "print('x' * 10000)"], "", log, 2, 100)
        self.assertEqual(result["reason"], "output_limit")
        self.assertEqual(log.stat().st_size, 100)

    def test_stop_is_polled_after_child_closes_output(self):
        stop = self.root / "STOP"
        script = "import os, time\nfrom pathlib import Path\nos.close(1)\nos.close(2)\ntime.sleep(0.1)\nPath(" + repr(str(stop)) + ").write_text('stop')\ntime.sleep(5)"
        result = runner.bounded_run([sys.executable, "-c", script], "", self.root / "closed.log", 1, 4096, stop_file=stop)
        self.assertEqual(result["reason"], "stopped")


if __name__ == "__main__":
    unittest.main()

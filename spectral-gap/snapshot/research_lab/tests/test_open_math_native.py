import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest import mock

from research_lab import open_math_native as native
from research_lab.parallel_runner import prepare_run


class NativeControllerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.project = Path(self.temp.name).resolve()
        self.old_project = native.PROJECT
        native.PROJECT = self.project
        (self.project / "AGENTS.md").write_text("NATIVE_TEST_RULES\n")
        self.run_dir = self.project / "runs" / "native"
        self.template = native.ROOT / "templates/research-packet"

    def tearDown(self):
        native.PROJECT = self.old_project
        self.temp.cleanup()

    def prepare_template(self):
        prepare_run(self.template / "dag.json", self.run_dir, minutes=30, network="no_browsing")
        controller = native.NativeController(self.run_dir)
        controller.initialize("deepseek/deepseek-v4.1-flash", members=2, member_steps=50)
        return controller

    def packet(self, tasks):
        packet = self.project / "packet"
        (packet / "sources").mkdir(parents=True)
        (packet / "problem.md").write_text("FROZEN_PROBLEM\n")
        for task in tasks:
            (packet / f"{task['id']}.md").write_text(f"ASSIGNMENT_{task['id']}\n")
            task.update(instruction=f"{task['id']}.md", inputs=["problem.md"], max_calls=2)
        (packet / "dag.json").write_text(json.dumps({"global_runtime_seconds": 7200, "tasks": tasks}))
        return packet / "dag.json"

    def initialize_custom(self, tasks):
        prepare_run(self.packet(tasks), self.run_dir, minutes=30, network="no_browsing")
        controller = native.NativeController(self.run_dir)
        controller.initialize("meta/muse-spark-open", members=1)
        return controller

    def finish_job(self, controller, identifier, marker):
        request_path = controller.begin(identifier)
        request = json.loads(request_path.read_text())
        controller.attach(identifier, f"swarm-{identifier}")
        receipt = self.receipt(marker)
        return request["task"], controller.accept(identifier, "m1", receipt, f"Reviewed {marker}")

    def receipt(self, marker):
        path = self.project / f"incoming-{marker}.json"
        path.write_text(json.dumps({
            "action": "finish", "summary": f"SUMMARY_{marker}", "target": "the prepared target",
            "argument": f"COMPLETE_ARGUMENT_{marker}", "claims": [{
                "id": marker, "statement": marker, "status": "derived", "dependencies": [],
                "evidence": "explicit derivation", "objection": "requires human review"}],
            "sources": [], "strongest_objection": f"OBJECTION_{marker}",
            "next_action": "independent review", "code": ""}))
        return path

    def test_begin_freezes_exact_launch_request_and_acceptance_unlocks_dependencies(self):
        controller = self.prepare_template()
        self.assertEqual(controller.ready(), ["baseline", "direct", "adversary"])
        with self.assertRaisesRegex(ValueError, "direct dependencies"):
            controller.begin("candidate")
        task, accepted = self.finish_job(controller, "baseline", "BASE")
        self.assertIn("NATIVE_TEST_RULES", task)
        self.assertIn("# Baseline reconstruction", task)
        self.assertIn("Browsing and other public network retrieval are disabled", task)
        self.assertIn("reply.schema.json", task)
        self.assertIn(controller.read()[0]["schema_hash"], task)
        self.assertNotIn("COMPLETE_ARGUMENT_DIRECT", task)
        payload = json.loads((self.run_dir / "open_math/jobs/baseline/attempt-01/launch_request.json").read_text())
        self.assertEqual(payload["model"], "deepseek/deepseek-v4.1-flash")
        self.assertEqual(payload["members"], 2)
        self.assertEqual(payload["minutes"], 30)
        self.assertEqual(payload["task"], task)
        self.assertTrue(accepted.is_file())
        self.assertEqual(accepted.stat().st_mode & 0o444, 0o444)
        with self.assertRaisesRegex(ValueError, "direct dependencies"):
            controller.begin("candidate")
        self.finish_job(controller, "direct", "DIRECT")
        self.finish_job(controller, "adversary", "ADVERSARY")
        self.assertIn("candidate", controller.ready())
        candidate_task = json.loads(controller.begin("candidate").read_text())["task"]
        for marker in ("BASE", "DIRECT", "ADVERSARY"):
            self.assertIn(f"COMPLETE_ARGUMENT_{marker}", candidate_task)

    def test_accept_checks_receipt_and_audit_detects_guidance_or_evidence_changes(self):
        controller = self.prepare_template()
        controller.begin("baseline")
        bad = self.project / "bad.json"
        bad.write_text('{"not": "a receipt"}')
        with self.assertRaises(Exception):
            controller.accept("baseline", "m1", bad, "review")
        with self.assertRaisesRegex(ValueError, "awaiting"):
            controller.attach("direct", "another")
        controller.attach("baseline", "s-good")
        accepted = controller.accept("baseline", "m1", self.receipt("BASE"), "reviewed")
        controller.read()
        accepted.chmod(0o644)
        accepted.write_text("{}")
        with self.assertRaisesRegex(ValueError, "evidence changed"):
            controller.read()
        accepted.unlink()
        (self.project / "AGENTS.md").write_text("changed")
        with self.assertRaisesRegex(ValueError, "AGENTS.md changed"):
            controller.read()

    def test_direct_and_transitive_visibility_and_root_blindness(self):
        tasks = [
            {"id": "a", "role": "reconstruction", "depends_on": []},
            {"id": "b", "role": "reconstruction", "depends_on": []},
            {"id": "c", "role": "synthesis", "depends_on": ["a"], "dependency_context": "direct"},
            {"id": "d", "role": "synthesis", "depends_on": ["c", "b"], "dependency_context": "transitive"},
        ]
        controller = self.initialize_custom(tasks)
        b_task = json.loads(controller.begin("b").read_text())["task"]
        controller.attach("b", "s-b")
        b_receipt = self.receipt("B_MARKER")
        controller.accept("b", "m1", b_receipt, "checked B")
        a_task = json.loads(controller.begin("a").read_text())["task"]
        self.assertNotIn("COMPLETE_ARGUMENT_B_MARKER", a_task)
        controller.attach("a", "s-a")
        controller.accept("a", "m1", self.receipt("A_MARKER"), "checked A")
        c_task = json.loads(controller.begin("c").read_text())["task"]
        self.assertIn("COMPLETE_ARGUMENT_A_MARKER", c_task)
        self.assertNotIn("COMPLETE_ARGUMENT_B_MARKER", c_task)
        controller.attach("c", "s-c")
        controller.accept("c", "m1", self.receipt("C_MARKER"), "checked C")
        d_task = json.loads(controller.begin("d").read_text())["task"]
        for marker in ("A_MARKER", "B_MARKER", "C_MARKER"):
            self.assertIn(f"COMPLETE_ARGUMENT_{marker}", d_task)

    def test_deferred_source_is_referenced_not_inlined(self):
        tasks = [{"id": "only", "role": "reconstruction", "depends_on": []}]
        packet = self.packet(tasks)
        body = "SECRET_COMPLETE_SOURCE_BODY\n"
        (packet.parent / "sources/source.txt").write_text(body)
        tasks[0]["inputs"].append("sources/source.txt")
        tasks[0]["deferred_inputs"] = ["sources/source.txt"]
        packet.write_text(json.dumps({"global_runtime_seconds": 7200, "tasks": tasks}))
        prepare_run(packet, self.run_dir, minutes=30, network="no_browsing")
        controller = native.NativeController(self.run_dir)
        controller.initialize("meta/muse-spark-open")
        task = json.loads(controller.begin("only").read_text())["task"]
        self.assertNotIn(body, task)
        self.assertIn("Complete deferred input: sources/source.txt", task)
        self.assertIn("sources/source.txt", task)

    def test_subscription_executor_refuses_an_initialized_native_run(self):
        controller = self.prepare_template()
        with mock.patch.object(native.graph.sys, "argv", ["parallel_runner.py", "resume", "--run-dir", str(self.run_dir)]):
            with self.assertRaisesRegex(ValueError, "subscription executor"):
                native.graph.main()
        self.assertEqual(controller.read()[0]["status"], "prepared")

    def test_deadline_and_call_ceilings_are_not_reset(self):
        controller = self.prepare_template()
        controller.begin("baseline")
        controller.close("baseline", "failed", "test closure before launch")
        source, _, state = controller.read()
        source_job = next(job for job in source["jobs"] if job["id"] == "baseline")
        state["jobs"]["baseline"]["attempts"] = source_job["max_calls"]
        controller.save(state)
        with self.assertRaisesRegex(ValueError, "call ceiling"):
            controller.begin("baseline")
        _, _, state = controller.read()
        state["deadline"] = time.time() - 1
        controller.save(state)
        with self.assertRaisesRegex(ValueError, "usable minute"):
            controller.begin("direct")
        self.assertEqual(controller.begin.__name__, "begin")
        report = controller.report()
        self.assertIn("not certified mathematical results", report.read_text())
        status = controller.status()
        self.assertEqual(status["total_remaining_seconds"], 0)
        self.assertEqual(status["ready"], ["direct", "adversary"])

    def test_oversized_task_consumes_neither_attempt_nor_launch_clock(self):
        tasks = [{"id": "only", "role": "reconstruction", "depends_on": []}]
        packet = self.packet(tasks)
        (packet.parent / "problem.md").write_text("x" * (native.MAX_NATIVE_TASK_BYTES + 1))
        prepare_run(packet, self.run_dir, minutes=30, network="no_browsing")
        controller = native.NativeController(self.run_dir)
        controller.initialize("meta/muse-spark-open")
        with self.assertRaisesRegex(ValueError, "byte launch limit"):
            controller.begin("only")
        _, _, state = controller.read()
        self.assertEqual(state["attempts"], 0)
        self.assertEqual(state["jobs"]["only"]["attempts"], 0)
        self.assertIsNone(state["started_at"])
        self.assertIsNone(state["deadline"])
        self.assertFalse((self.run_dir / "open_math/jobs/only/attempt-01").exists())


if __name__ == "__main__":
    unittest.main()

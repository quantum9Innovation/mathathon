import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

from research_lab import model_policy as policy


class ModelPolicyTests(unittest.TestCase):
    def test_explicit_run_settings_preserve_defaults_and_apply_to_every_role(self):
        original = policy.load_profile()
        profile = policy.apply_run_overrides(original, "xhigh", "fast")
        self.assertEqual(policy.load_profile(), original)
        self.assertNotIn("run_overrides", original)
        self.assertEqual(profile["max_parallel_workers"], 3)
        for role in [*policy.ROLES, "reporting"]:
            self.assertEqual(policy.route_task(role, profile),
                             {"model": "gpt-6.1-sol", "reasoning_effort": "xhigh", "service_tier": "fast"})
        profile["routes"]["reconstruction"]["reasoning_effort"] = "high"
        with self.assertRaises(ValueError):
            policy.validate_profile(profile)

    def test_run_settings_reject_unregistered_efforts_and_tiers(self):
        for effort, tier in [("max", "fast"), ("low", None), (None, "ultrafast")]:
            with self.subTest(effort=effort, tier=tier), self.assertRaises(ValueError):
                policy.apply_run_overrides(policy.load_profile(), effort, tier)

    def test_budget_limits_fit_their_enclosing_allowances(self):
        for change in ({"total_seconds": 600}, {"max_task_seconds": 100},
                       {"call_seconds": 100}, {"max_total_tasks": 1}, {"max_total_calls": 1}):
            with self.subTest(change=change):
                profile = policy.load_profile()
                profile.update(change)
                with self.assertRaises(ValueError):
                    policy.validate_profile(profile)

    def test_task_routing_revalidates_profile_and_rejects_malformed_tasks(self):
        profile = policy.load_profile()
        profile["routes"]["algebra_audit"]["model"] = "other"
        with self.assertRaises(ValueError):
            policy.route_task({"role": "algebra_audit"}, profile)
        for task in (None, [], True, {"role": []}):
            with self.subTest(task=task), self.assertRaises(ValueError):
                policy.route_task(task, policy.load_profile())

    def test_profile_ceilings_and_routes_are_validated_before_use(self):
        mutations = [{"max_parallel_workers": 4}, {"max_total_tasks": 13},
                     {"max_total_calls": 49}, {"total_seconds": 7201}, {"call_seconds": 601},
                     {"checkpoint_seconds": 0}, {"checkpoint_grace_seconds": -1},
                     {"review_reserve_seconds": True}, {"max_task_seconds": 2401},
                     {"max_task_calls": 7}, {"billing": "api"}, {"model": "other"},
                     {"reasoning_effort": "max"}, {"allowed_reasoning": ["high", "max"]},
                     {"default_route": {"model": "other", "reasoning_effort": "high"}},
                     {"routes": {"reconstruction": {"model": "gpt-6.1-sol", "reasoning_effort": "low"}}}]
        for change in mutations:
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                shutil.copy(policy.ROOT / "defaults.json", root / "defaults.json")
                (root / "profiles").mkdir()
                profile = policy.load_profile()
                profile.update(change)
                (root / "profiles/bounded.json").write_text(json.dumps(profile))
                with mock.patch.object(policy, "ROOT", root), self.assertRaises(ValueError):
                    policy.load_profile()

    def test_defaults_reject_configuration_that_changes_subscription_model_or_effort(self):
        for change in ({"model": "other"}, {"reasoning_effort": "max"}, {"billing": "api"},
                       {"network": "public_sources"}):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                defaults = policy.new_run_defaults()
                defaults.update(change)
                (Path(directory) / "defaults.json").write_text(json.dumps(defaults))
                with mock.patch.object(policy, "ROOT", Path(directory)), self.assertRaises(ValueError):
                    policy.new_run_defaults()

    def test_profile_rejects_path_names_before_file_access(self):
        for name in ("../defaults", "/tmp/profile", "unregistered"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                policy.load_profile(name)

    def test_task_routing_uses_profile_role_and_default_without_external_model_overrides(self):
        profile = policy.load_profile()
        self.assertEqual(policy.route_task({"role": "algebra_audit"}, profile), profile["default_route"])
        self.assertEqual(policy.route_task({"role": "repair"}, profile), profile["default_route"])
        self.assertEqual(policy.route_task("reconstruction", profile), profile["default_route"])
        with self.assertRaises(ValueError):
            policy.route_task({"role": "algebra_audit", "model": "other"}, profile)
        with self.assertRaises(ValueError):
            policy.route_task({"role": "algebra_audit", "reasoning_effort": "max"}, profile)

    def test_many_profile_requires_explicit_access_and_routes_effort_only(self):
        with self.assertRaises(ValueError):
            policy.load_profile("many")
        profile = policy.load_profile("many", allow_disabled=True)
        self.assertFalse(profile["enabled"])
        self.assertEqual(profile["max_parallel_workers"], 16)
        self.assertEqual(profile["max_total_tasks"], 64)
        self.assertEqual(profile["max_total_calls"], 256)
        self.assertEqual(profile["total_seconds"], 10800)
        self.assertEqual(profile["max_task_seconds"], 3600)
        self.assertEqual(profile["allowed_reasoning"], ["high", "xhigh", "max"])
        self.assertEqual({key: value["reasoning_effort"] for key, value in profile["routes"].items()},
                         {"reconstruction": "high", "algebra_audit": "xhigh",
                          "averaging_audit": "max", "synthesis": "max"})
        self.assertTrue(all(route["model"] == "gpt-6.1-sol" for route in profile["routes"].values()))

    def test_many_profile_rejects_excess_duration_workers_and_task_overrides(self):
        for change in ({"total_seconds": 10801}, {"max_task_seconds": 3601}, {"max_parallel_workers": 17}):
            with self.subTest(change=change):
                profile = policy.load_profile("many", allow_disabled=True)
                profile.update(change)
                with self.assertRaises(ValueError):
                    policy.validate_profile(profile)
        profile = policy.load_profile("many", allow_disabled=True)
        for change in ({"model": "other"}, {"reasoning_effort": "high"}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                policy.route_task(dict(role="algebra_audit", **change), profile)

    def test_reporting_uses_existing_high_default_without_changing_role_table(self):
        profile = policy.load_profile("many", allow_disabled=True)
        self.assertEqual(policy.route_task({"role": "reporting"}, profile), profile["default_route"])
        self.assertNotIn("reporting", profile["routes"])

    def test_historical_two_hour_many_profile_remains_valid(self):
        profile = policy.load_profile("many", allow_disabled=True)
        profile.update(total_seconds=7200, max_task_seconds=2400)
        self.assertEqual(policy.validate_profile(profile), profile)

    def test_bounded_profile_sets_active_equal_high_routes_and_limits(self):
        profile = policy.load_profile()
        expected = {"max_parallel_workers": 3, "max_total_tasks": 12, "max_total_calls": 48,
                    "total_seconds": 7200, "call_seconds": 600, "checkpoint_seconds": 120,
                    "checkpoint_grace_seconds": 180, "review_reserve_seconds": 900,
                    "max_task_seconds": 2400, "max_task_calls": 6}
        for key, value in expected.items():
            self.assertEqual(profile[key], value)
        self.assertTrue(profile["enabled"])
        self.assertEqual(profile["allowed_reasoning"], ["high"])
        self.assertEqual(profile["default_route"], {"model": "gpt-6.1-sol", "reasoning_effort": "high"})
        self.assertEqual(set(profile["routes"]), {"reconstruction", "algebra_audit", "averaging_audit", "synthesis"})
        for route in profile["routes"].values():
            self.assertEqual(route, profile["default_route"])

    def test_new_defaults_are_high_and_do_not_mutate_between_calls(self):
        defaults = policy.new_run_defaults()
        self.assertEqual(defaults, {"model": "gpt-6.1-sol", "reasoning_effort": "high",
                                    "billing": "subscription_only"})
        defaults["reasoning_effort"] = "low"
        self.assertEqual(policy.new_run_defaults()["reasoning_effort"], "high")

"""Project defaults and validated worker routing."""

import json
import math
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parent
ROLES = {"reconstruction", "algebra_audit", "averaging_audit", "synthesis"}
LIMITS = {"total_seconds": 7200, "call_seconds": 600, "checkpoint_seconds": 120,
          "checkpoint_grace_seconds": 180, "review_reserve_seconds": 900,
          "max_task_seconds": 2400, "max_task_calls": 6}


def validate_run_overrides(overrides):
    if not isinstance(overrides, dict) or set(overrides) - {"reasoning_effort", "service_tier"}:
        raise ValueError("Unknown run setting")
    if "reasoning_effort" in overrides and overrides["reasoning_effort"] not in {"high", "xhigh"}:
        raise ValueError("Run effort must be high or xhigh")
    if "service_tier" in overrides and overrides["service_tier"] != "fast":
        raise ValueError("Only the explicitly selected Fast tier is supported")
    return overrides


def apply_run_overrides(profile, reasoning_effort=None, service_tier=None):
    validate_profile(profile)
    result = deepcopy(profile)
    overrides = {key: value for key, value in
                 (("reasoning_effort", reasoning_effort), ("service_tier", service_tier)) if value is not None}
    validate_run_overrides(overrides)
    if overrides:
        result["run_overrides"] = overrides
        result.update(overrides)
        for route in [result["default_route"], *result["routes"].values()]:
            route.update(overrides)
    return validate_profile(result)


def validate_profile(profile):
    if not isinstance(profile, dict) or profile.get("name") not in {"bounded", "many"}:
        raise ValueError("Unknown worker profile")
    name = profile["name"]
    overrides = validate_run_overrides(profile.get("run_overrides", {}))
    effort = overrides.get("reasoning_effort", "high")
    if profile.get("model") != "gpt-6.1-sol" or profile.get("reasoning_effort") != effort:
        raise ValueError("Default route differs from the configured subscription effort")
    if profile.get("service_tier") != overrides.get("service_tier"):
        raise ValueError("Service tier must match the frozen run setting")
    if profile.get("billing") != "subscription_only":
        raise ValueError("Only the existing subscription is authorized")
    if type(profile.get("enabled")) is not bool:
        raise ValueError("Profile enabled flag must be boolean")
    if profile.get("network") not in {"public_sources", "no_browsing"}:
        raise ValueError("Unknown network mode")
    limits = dict(LIMITS)
    if name == "many":
        limits.update(total_seconds=10800, max_task_seconds=3600)
    limits.update(dict(zip(("max_parallel_workers", "max_total_tasks", "max_total_calls"),
                           (3, 12, 48) if name == "bounded" else (16, 64, 256))))
    for key, ceiling in limits.items():
        value = profile.get(key)
        if type(value) not in (int, float) or not math.isfinite(value) or not 0 < value <= ceiling:
            raise ValueError(f"Profile limit must be positive and at most {ceiling}: {key}")
        if not key.endswith("seconds") and type(value) is not int:
            raise ValueError(f"Profile count must be an integer: {key}")
    if not profile["call_seconds"] <= profile["max_task_seconds"] <= profile["total_seconds"]:
        raise ValueError("Call and task allowances must fit the global time budget")
    if max(profile["checkpoint_seconds"], profile["checkpoint_grace_seconds"]) > profile["call_seconds"]:
        raise ValueError("Checkpoint allowances must fit each call")
    if profile["review_reserve_seconds"] >= profile["total_seconds"]:
        raise ValueError("Review reserve must leave time for independent work")
    if profile["max_parallel_workers"] > profile["max_total_tasks"]:
        raise ValueError("Worker limit cannot exceed the task limit")
    if profile["max_task_calls"] > profile["max_total_calls"]:
        raise ValueError("Task calls must fit the global call limit")
    allowed = ["high"] if name == "bounded" else ["high", "xhigh", "max"]
    if profile.get("allowed_reasoning") != allowed:
        raise ValueError("Profile reasoning levels differ from the allowed policy")
    routes = profile.get("routes")
    if not isinstance(routes, dict) or set(routes) != ROLES:
        raise ValueError("Profile must define every independent review route")
    for route in [profile.get("default_route")] + list(routes.values()):
        keys = {"model", "reasoning_effort"} | ({"service_tier"} if "service_tier" in overrides else set())
        if not isinstance(route, dict) or set(route) != keys:
            raise ValueError("Every route must define its model and reasoning effort")
        route_efforts = [overrides["reasoning_effort"]] if "reasoning_effort" in overrides else allowed
        if route["model"] != "gpt-6.1-sol" or route["reasoning_effort"] not in route_efforts:
            raise ValueError("Route is outside the configured subscription policy")
        if route.get("service_tier") != overrides.get("service_tier"):
            raise ValueError("Route service tier differs from the frozen run setting")
    if profile["default_route"]["reasoning_effort"] != effort:
        raise ValueError("The default route must match the configured effort")
    return profile


def new_run_defaults():
    defaults = json.loads((ROOT / "defaults.json").read_text())
    if defaults != {"model": "gpt-6.1-sol", "reasoning_effort": "high", "billing": "subscription_only"}:
        raise ValueError("New runs require the configured subscription model at high effort")
    return defaults


def load_profile(name="bounded", allow_disabled=False):
    if name not in {"bounded", "many"}:
        raise ValueError("Unknown worker profile")
    profile = new_run_defaults()
    profile.update(json.loads((ROOT / "profiles" / f"{name}.json").read_text()))
    if profile.get("name") != name:
        raise ValueError("Profile name must match its registered file")
    validate_profile(profile)
    if not profile["enabled"] and not allow_disabled:
        raise ValueError("Profile is disabled and requires explicit activation")
    return profile


def route_task(task, profile):
    validate_profile(profile)
    if not isinstance(task, (str, dict)):
        raise ValueError("Task must be a role name or an object")
    role = task if isinstance(task, str) else task.get("role")
    if role is not None and not isinstance(role, str):
        raise ValueError("Task role must be text")
    route = dict(profile["routes"].get(role, profile["default_route"]))
    if isinstance(task, dict):
        for key in ("model", "reasoning_effort", "service_tier"):
            if key in task and task[key] != route.get(key):
                raise ValueError("Task cannot override the configured route")
    return route

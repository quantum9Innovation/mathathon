# Open Math native adapter validation

## What was added

- `AGENTS.md`: project execution and evidence contract, embedded in native task
  prompts and frozen by SHA256 during initialization.
- `research_lab/open_math_native.py`: agent-driven DAG controller, separate
  from the original subscription model/billing/execution route.
- `research_lab/OPEN_MATH_NATIVE.md`: exact preparation, launch, judging,
  receipt import, deadline, restore and reporting protocol.
- `.skill/research-lab-native/SKILL.md`: auto-discoverable native workflow.
- `research_lab/tests/test_open_math_native.py`: focused offline tests.
- One protective guard in `parallel_runner.py`: initialized native runs refuse
  the original subscription executor's `start`, `run` and `resume` commands.

The original subscription preflight, client requirement, model route, frozen
profiles and Podman computation constraints were not disabled or replaced.
Its earlier `research-lab-validation.md` limitations still apply to that route.

## Verified locally

The complete offline test suite passed **125 tests in 2.023 seconds**, including
all 119 original tests and 6 new native tests. Full output is retained in
[open-math-native-tests.log](open-math-native-tests.log).

The new tests cover:

- native initialization and exact frozen launch requests.
- dependency readiness only after imported accepted receipts.
- independent-root blindness and direct/transitive evidence visibility.
- complete deferred sources referenced with their hash instead of inlined.
- invalid-receipt rejection and accepted-receipt integrity checks.
- AGENTS.md tamper detection.
- refusal of the old subscription route for native runs.
- call ceilings and persistent deadlines.
- status and non-certifying report generation.

A separately cleaned-up CLI smoke run exercised `prepare`, native `init`,
`audit`, `ready`, `begin`, `status`, native attempt `close`, and `report`.
The original `resume` returned the intended route-confusion error (exit 2).
The local generated request selected `deepseek/deepseek-v4.1-flash` with one
member and ten member steps. No actual swarm construction or inference call
was made during this test. Its temporary run directory was deleted.

## Not yet verified live

No real research packet has been executed. No actual native swarm was started,
no model inference or billing was incurred, and no member submission was judged
against a real problem. Therefore the following remain unverified in a real
run rather than simulated by tests:

- actual matching between a launch request and Open Math's returned swarm.
- remote model route and worker availability.
- an actual swarm callback, verdict, interruption and resume cycle.
- mathematical quality and acceptance of live research evidence.
- full multi-hour autonomous operation under real research load.

The adapter cannot inspect remote swarms by itself. The chat agent must perform
those operations and accurately report the limited attestation boundary.

## Current scope

Native time and call ceilings fit inside the originally prepared packet's
ceilings. The adapter does not silently turn a three-hour packet into a
24-hour campaign, even though an individual Open Math swarm can be started for
up to 1440 minutes with an appropriate tool request. Longer research requires a
separate explicitly designed and approved profile/prepared run.

For ordinary time-boxed non-DAG work, the pre-existing `.orchestrator/` batch
queue remains available, but is not merged into DAG proof-evidence semantics.

See [../research_lab/OPEN_MATH_NATIVE.md](../research_lab/OPEN_MATH_NATIVE.md)
and [../AGENTS.md](../AGENTS.md) for operation.

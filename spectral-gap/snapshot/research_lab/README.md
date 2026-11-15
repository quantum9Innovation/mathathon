# Reusable research harness

This directory contains the execution infrastructure for bounded and larger research runs. This is a clean starter distribution of the current execution code, retaining its fixes and preparation-only effort and Fast overrides. It is not an exact historical snapshot. The base configuration has a neutral experiment identifier and high reasoning. Research packets and run evidence are stored separately from the reusable engine.

## Install in another project

Copy this entire research_lab/ directory into the destination project. Keep that directory name because the tests import it as a package. Run the commands below from its parent, the destination project root. The destination project's rules are not loaded automatically into worker prompts. Include them explicitly in the packet's instructions or declared inputs, with source provenance and the intended evidence visibility.

Requirements: Python 3.12 or later on Linux, a compatible installed subscription client with an existing subscription login, and working rootless Podman. There are no third-party Python dependencies. The engine uses POSIX process controls and fcntl, so native Windows is unsupported. Other hosts have not been validated.

Set up the destination client link using the absolute path to its installed executable:

```bash
ln -s /absolute/path/to/subscription-executable research_lab/runtime/subscription-client
```

The placeholder must be replaced with a real executable path. No executable, login data, credentials or container image is bundled. On a new machine, provision the image named in pilot/config.json separately, currently docker.io/library/python:3.12-bookworm. The doctor command inspects the existing image and refuses to download it automatically. It checks login state and required client features without making a research call, then writes local check logs under runtime/.

Run the offline test suite first:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s research_lab/tests -v
```

Copy a neutral packet and edit its problem and assignments:

```bash
cp -R research_lab/templates/research-packet research_lab/packets/my-project
```

Then use that packet's dag.json with the preparation command below instead of the template path. Preparation and audit do not start workers. Check prerequisites with doctor before an authorized launch. To copy this starter again after using it, omit runs/, runtime/ contents, project packets, caches and machine-specific links.

## Why SHA256 appears

SHA256 values fingerprint files, frozen instructions, evidence and the local container image. They detect changes and preserve the identity of a prepared experiment. The integrity code remains part of this clean starter. New preparation will produce new hashes even before workers start. Directories named runtime/check-* are prerequisite-check receipts, not research results. Completed experiments and their checkpoint records belong under runs/.

## Profiles

| Setting | Default profile, bounded | Larger profile, many |
| --- | --- | --- |
| Concurrent worker ceiling | 3 | 16 |
| Total runtime ceiling | 120 minutes | 180 minutes |
| Task ceiling | 12 | 64 |
| Total call ceiling | 48 | 256 |
| Per-task cumulative time | 40 minutes | 60 minutes |
| Per-task call ceiling | 6 | 6 |
| Ordinary call ceiling | 10 minutes | 10 minutes |
| Reasoning | high | high, xhigh and max by task role |
| Saved activation state | enabled | disabled |

Both profiles use gpt-6.1-sol and existing-subscription billing. Routes and limits are frozen during preparation. The larger profile requires explicit per-run activation. Worker ceilings are subject to subscription availability. Workers cannot spawn uncontrolled child processes or select a different model or billing path.

An explicit user request can select --reasoning-effort xhigh and --service-tier fast during preparation. These apply to every role, including reporting, without changing the authoritative default files or activating the larger profile. Omitting them retains the existing routes. They cannot be changed by start or resume. Fast forwarding uses service_tier=fast and features.fast_mode=true. It requests the tier without certifying actual response latency.

## Start here

Run commands from the project root containing research_lab/. Copy templates/research-packet/ to a new packet directory, replace problem.md and give each root a concrete distinct assignment. Both supplied graphs are neutral templates. They do not select a research problem or authorize a launch. The bounded template has three roots and nine tasks. The larger template has eight roots and 21 tasks. More workers require more independent ready tasks in a deliberately prepared graph.

Prepare a default-profile run with a chosen cap:

```bash
python3 research_lab/parallel_runner.py prepare --plan research_lab/templates/research-packet/dag.json --run-dir research_lab/runs/example-default --minutes 60 --profile bounded --network public_sources
```

Prepare an explicitly authorized larger run:

```bash
python3 research_lab/parallel_runner.py prepare --plan research_lab/templates/research-packet/dag.large.json --run-dir research_lab/runs/example-large --minutes 180 --profile many --activate-large-profile --network public_sources
```

These commands only prepare frozen runs. Substitute the edited packet path and a unique run directory. Set --minutes before preparation to vary the cap within the plan and profile ceilings. The template phase fractions scale with the chosen duration. Inspect all ready work and source visibility before starting.

Check local prerequisites without a research call:

```bash
python3 research_lab/research_runner.py doctor
```

Use the graph controller for execution:

```bash
python3 research_lab/parallel_runner.py audit --run-dir research_lab/runs/example-default
python3 research_lab/parallel_runner.py start --run-dir research_lab/runs/example-default
python3 research_lab/parallel_runner.py status --run-dir research_lab/runs/example-default
python3 research_lab/parallel_runner.py stop --run-dir research_lab/runs/example-default
python3 research_lab/parallel_runner.py resume --run-dir research_lab/runs/example-default
```

Start detaches the controller. Resume runs in the foreground, so use a persistent terminal when needed. The machine must remain running and awake. There is no automatic reboot recovery. Resume preserves the original absolute deadline and call reservations. Choose a new directory for a separate experiment. Do not edit frozen state to extend a run.

## Network and computation

public_sources enables hosted public-source browsing. no_browsing disables browsing while retaining remote subscription inference. offline refuses remote inference and launch entirely. Select --network during prepare. Changing a frozen mode requires a separate preparation. The local configuration can be inspected and tests can run without remote inference.

Requested computation uses the existing rootless local container image, with no network, package installation, host credentials or archive access. Resources and output are bounded. The client remains a trusted host dependency. Create runtime/subscription-client on the destination machine as described below. No account data or credentials are copied here. Preflight verifies subscription authentication, required tool restrictions and the existing image without downloading packages or buying capacity.

## Evidence and checkpoints

Workers receive frozen inputs and an allowlisted evidence catalog. save_checkpoint durably records structured partial arguments. list_evidence and read_evidence retrieve complete permitted earlier records, with paginated listings and bounded reads. A root without candidate inputs or ancestors does not receive another task's proof. Source and dependency visibility must be designed explicitly in the graph.

Sources can use deferred_inputs with safe sources/ paths and dependency_context=direct. Each deferred file must fit the complete 256 KiB evidence read limit. Full hashes are checked, source bodies stay unchanged and complete permitted ancestor proofs remain retrievable. Split an oversized source into declared complete parts with provenance rather than pretending a truncated file is complete.

The checkpoint watchdog bounds unreported activity. Per-record, per-call and event-log limits remain enforced. Saved finishes can survive a later local timeout. Only emitted work can be retained. Private unwritten reasoning and bytes lost in a sudden machine failure are outside that guarantee.

Reporting tasks can use role=reporting, finalization_only=true and incremental_finalization=true. They save a concise useful first result, incrementally assemble their report and explicitly finish. REPORT.md, FINAL_REPORT.md, EVIDENCE.md and the opt-in EVIDENCE_INDEX files preserve available records even if final editing fails. A completed graph or reviewer agreement does not establish a mathematical theorem. Correctness, scope, source applicability and novelty require separate checking.

## Files and validation

The four top-level execution modules provide scheduling, persistence, model policy, checkpoint transport, isolated computation and host preflight. profiles/ and defaults.json preserve the working policies. The pilot/ directory contains mandatory base settings, schema and the generic common contract. It does not contain a historical research campaign. research_runner.py supplies the shared engine and doctor command. Use parallel_runner.py for new runs. Its older sequential calibration entry point is retained in the unchanged engine, but its research packets are not installed.

tests/ contains the operational suite. tests/fixtures/pilot/ provides synthetic neutral inputs for legacy engine tests, with no real research material. templates/ contains editable generic workflow examples. runtime/, runs/ and packets/ begin empty. Historical import records and project-specific research material are excluded.

```bash
python3 -m unittest discover -s research_lab/tests -v
```

No live research inference is part of installation or the offline test suite. New research must follow the destination project's rules and an explicitly authorized task graph.

# Running `research_lab` in this Open Math OS project

## Verified local installation

The supplied archive extracted intact at the project root, alongside `README.md`.
The archive SHA256 is
`313aee4f89f697918b2a5eaab1e14f9501f6ef1cd18bf5f43dbf5dd3eb50da7a`.
`research_lab/README.md` is byte-identical to the attached README.

The archive stock `research_lab/README.md` remains unchanged, and the original
subscription module behavior remains intact except for a new guard that refuses
subscription `start/run/resume` on a native run. The subsequently added
`open_math_native.py` is a separate agent-driven adapter, with its own model
route and evidence state. See `OPEN_MATH_NATIVE.md`. Native execution does not
inherit or claim the Podman execution boundary.

- Python: 3.12.14.
- Offline suite: 119 tests in 1.969 s, all passed.
- `parallel_runner.py prepare`: verified with the neutral bounded template.
- `parallel_runner.py audit`: `Frozen inputs verified`.
- The prepared `runs/example-default` has 9 pending jobs and 3600 seconds left.
  It has not started: `started_at` and `deadline` are null.
- `research_runner.py doctor`: exit 2, `Subscription client is missing`.
- No worker was launched and no research inference or billing call was made.

The test output is retained at `../results/research-lab-offline-tests.log`.
See `../results/research-lab-validation.md` for the complete local validation
summary and blockers, if present in the destination project.

## Launch under Open Math OS

Use this section only for the original **subscription** route. For a native run,
use `open_math_native.py` and `OPEN_MATH_NATIVE.md`, not `resume`.

**Do not use `parallel_runner.py start` in this VM.** Its implementation spawns a
new detached session (`start_new_session=True`). Open Math OS instead manages a
long controller as a visible background job and cleans up descendants of ordinary
foreground commands.

Use `resume`, not `start`, for both a new prepared run and a previously stopped
one. `resume` removes an existing `STOP` marker, audits the frozen state, runs
in the foreground, preserves the original deadline, and leaves the deadline
unstarted on a genuinely new run until execution begins:

```bash
python3 research_lab/parallel_runner.py resume --run-dir research_lab/runs/my-run
```

Ask the Open Math OS agent to execute that exact command using
`shell_exec(background: true)`. Its background job is then visible and stoppable
with `shell_jobs`, and wakes the agent when it ends. If running directly in a
shell rather than through the agent, use a foreground persistent terminal.

Use the normal commands for inspection and graceful stop:

```bash
python3 research_lab/parallel_runner.py status --run-dir research_lab/runs/my-run
python3 research_lab/parallel_runner.py audit --run-dir research_lab/runs/my-run
python3 research_lab/parallel_runner.py stop --run-dir research_lab/runs/my-run
```

Do not run two controllers on one run directory. The engine's lock and fences
remain authoritative. An Open Math OS background job or reminder does not extend
the research deadline. A VM restart interrupts the controller: use `resume`
afterward, preserving the absolute deadline exactly as the harness intends.

The VM currently has 4 CPUs and 15 GiB RAM. The default bounded profile permits
up to 3 concurrent workers, but actual subscription worker availability still
applies. The larger profile is not activated here.

## Required external prerequisites

These were **not** established during local installation:

1. A compatible installed subscription client, already logged in with its
   subscription, linked as `research_lab/runtime/subscription-client`. No client
   is bundled or on PATH, so login state could not be checked.
2. A working rootless Podman with the local
   `docker.io/library/python:3.12-bookworm` image. `podman`, `newuidmap`,
   `newgidmap`, `slirp4netns` and `fuse-overlayfs` are not installed. Because
   Podman is absent, an existing stored image could not be inspected.
3. The VM denies unprivileged user-namespace creation (`unshare -Ur true`:
   `Operation not permitted`). A functioning rootless runtime therefore needs
   host/system configuration, not merely a binary copied into this project.

Run `python3 research_lab/research_runner.py doctor` after those prerequisites
are provided. It must pass before `resume`. If only the client is provided,
doctor may also expose the container-runtime failure. Passing the bundled tests
alone does not prove live execution.

Do not replace the Podman computation command with unsandboxed host Python: that
would remove the harness's network, mount, resource and capability boundaries.

## Preparing an actual packet

Copy `templates/research-packet` into `packets/<project>`, edit `problem.md`,
give each initial task a concrete distinct assignment, and prepare a unique run
directory. Example-only preparation did not supply a research problem or any
launch authorization. Include destination-project rules explicitly in packet
inputs. Worker prompts do not load them automatically.

Respect each worker's root isolation and declare sources/dependency visibility
in the DAG. Evidence and finished arguments remain claims requiring separate
mathematical correctness review, regardless of completed task status.

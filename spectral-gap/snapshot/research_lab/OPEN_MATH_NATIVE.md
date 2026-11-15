# Open Math native DAG execution

This is a separate executor for a run prepared by `parallel_runner.py`.
It preserves the original packet, graph, frozen input hashes and DAG report
inputs, but it does not preserve its remote model or billing identity. Native
execution is explicitly labeled `open_math_agent_ultramath` and uses a native
model selected during initialization.

The adapter never calls a model. The Open Math chat agent launches the exact
request, judges results and imports accepted receipts. Native swarm and agent
operations cannot be delegated to this Python module as ordinary subprocess
tools.

The original subscription executor refuses `start`, `run` and `resume` on an
initialized native run. The original executor, its preflight checks and Docker
or Podman computation boundary are not weakened.

## Prepare a research packet

First copy and edit a real packet. Do not use the neutral template as a research
problem or infer permission to launch it.

```bash
cp -R research_lab/templates/research-packet research_lab/packets/my-project
```

Edit `problem.md`, every initial assignment, source declarations, constraints,
and the DAG. Include project rules explicitly where needed, although native
task prompts also embed the complete root `AGENTS.md`.

Prepare a unique directory. This example uses 60 minutes and no web browsing:

```bash
python3 research_lab/parallel_runner.py prepare \
  --plan research_lab/packets/my-project/dag.json \
  --run-dir research_lab/runs/my-native-run \
  --minutes 60 --profile bounded --network no_browsing
python3 research_lab/parallel_runner.py audit --run-dir research_lab/runs/my-native-run
```

The bounded template has 9 tasks and allows up to 3 parallel tasks. The prepared
profile remains the time and attempt authority for the native version. Native
initialization cannot increase its total runtime. Per-job cumulative time,
per-job attempts, total attempts and parallel-task ceilings are enforced when
`begin` or `accept` advances local state.

## Initialize native execution

Model choice is explicit. This is intentionally separate from `gpt-6.1-sol`:

```bash
python3 research_lab/open_math_native.py init \
  --run-dir research_lab/runs/my-native-run \
  --model deepseek/deepseek-v4.1-flash \
  --members 1 --member-steps 100 --reasoning-effort max --minutes 60
python3 research_lab/open_math_native.py audit --run-dir research_lab/runs/my-native-run
```

The models registered by this adapter are the currently available
`deepseek/deepseek-v4.1-flash` and `meta/muse-spark-open`. Revalidate tool
availability before a future run. `--members` is per swarm attempt, not a total
project worker limit. Three simultaneous three-member tasks mean nine members
competing for four CPUs.

Strict offline packets are refused. `public_sources` permits relevant public
retrieval in the native prompt. `no_browsing` forbids it. The source packet's
actual network setting remains frozen.

## Launch one ready task

```bash
python3 research_lab/open_math_native.py ready --run-dir research_lab/runs/my-native-run
python3 research_lab/open_math_native.py begin --job baseline \
  --run-dir research_lab/runs/my-native-run
```

`begin` allocates a fresh attempt, consumes one global and per-job attempt,
creates `open_math/jobs/baseline/attempt-01/TASK.md`, and produces the exact
`launch_request.json` for `ultramath_start`. The actual Open Math tool limit for
that task string is currently 16,384 bytes, lower than the 256 KiB evidence-read
limit. The compiler rejects an oversized task before allocating an attempt or its
launch clock. The receipt schema stays frozen and is referenced by path and hash.
The original auditor verifies the schema bytes. Complete `AGENTS.md` and all
permitted evidence remain intact. Split inputs or tasks rather than dropping
unexamined text. Request failure after
`begin` requires a correct closeout, and the attempt ceiling is never reset to
make a retry possible.


The agent reads that JSON and supplies every field unchanged:
`task`, `model`, `members`, `minutes`, `member_steps` and
`reasoning_effort`. On success, use the returned swarm ID:

```bash
python3 research_lab/open_math_native.py attach --job baseline --swarm s... \
  --run-dir research_lab/runs/my-native-run
```

The adapter records, but cannot independently prove, the agent's attestation
that the returned swarm used the exact request. Do not claim otherwise.

`status` reports active deadlines and structural readiness. Readiness is only
dependency state: `begin` still has to check clocks, attempts and concurrency.
The native adapter does not magically stop remote swarm work when time expires.
At the active or global deadline the agent must stop it with `ultramath_stop`.

## Judge and import evidence

Members are asked to save complete findings early and submit a project-relative
JSON receipt satisfying the packet's existing reply schema. A receipt is at most
256 KiB and must have `action: finish`. Additional mathematical proof content
needed by reviewers must be preserved in the receipt or explicitly retained
project artifacts. Do not cite disappearing private member scratch as evidence.

On a submission wake-up:

1. Read the report and all named artifacts in the correct member workspace.
2. Run Lean, tests or targeted calculations that can discriminate the claim.
3. Check argument completeness, exact target, assumptions, source applicability,
   root/dependency blindness and strongest objections.
4. Reject an unchecked or gapped submission with `ultramath_verdict`, naming the
   right swarm. A second rejection kills that direction according to native
   swarm semantics. Acceptance there and local receipt import are separate
   steps: neither alone certifies the result.

Only after a real review, import the accepted complete receipt:

```bash
python3 research_lab/open_math_native.py accept --job baseline --member m1 \
  --receipt research_lab/runs/my-native-run/approved-baseline.json \
  --note "Checked exact statement, Lean file and remaining nonformal review limits" \
  --run-dir research_lab/runs/my-native-run
```

The path must be a regular project file, without symlinks. It is copied
read-only under the task's `accepted/` directory. Its original project path,
hash, member, swarm, attempt and review note are recorded. Acceptance changes
native dependency state, not mathematical truth. Once accepted, the same task
cannot silently import a different answer. Use an independent review task or a
new preparation.

For an unsuccessful active attempt, first stop/detach it through the native
swarm tool as appropriate, then record its terminal outcome:

```bash
python3 research_lab/open_math_native.py close --job baseline \
  --outcome time_limit --note "Stopped at frozen attempt deadline" \
  --run-dir research_lab/runs/my-native-run
```

A failed attempt may begin again only while its original per-job attempts, call
ceiling, cumulative time and global budget still permit it. Starting another
swarm after exhaustion is not a workaround.

## Long-running continuation and restart

Use visible background jobs with explicit limits for local computation. Native
swarms run independently and wake the agent on reports or completion. Use
`conversation_remind` for deadline enforcement. Do not start a detached native
controller or leave a pending report unjudged.

After a VM restart, `ultramath_resume` can restore an interrupted swarm. Native
approval does not authorize resetting its time: its `minutes` must fit both the
active attempt and global native deadline. The native tool requires at least
five minutes when naming a new resume duration. If five does not fit, close
instead. Do not create a new swarm to evade an expired attempt.

This version does not turn a three-hour `many` packet into an unattended
24-hour research campaign. The tool's own 1440-minute ceiling is not additional
permission. A later explicit long-run profile should define its budgets and
stop/continuation policy rather than editing frozen native state.

## Finish or close out

```bash
python3 research_lab/open_math_native.py status --run-dir research_lab/runs/my-native-run
python3 research_lab/open_math_native.py report --run-dir research_lab/runs/my-native-run
```

The latter writes `open_math/OPEN_MATH_REPORT.md` and
`open_math/OPEN_MATH_INDEX.json`. It includes accepted arguments, hashes,
objections and review notes, as well as tasks without accepted evidence.
It explicitly does not claim mathematical certification.

The original packet `state.json` remains in its prepared source state because
it belongs to the subscription controller. Native progress lives in
`open_math/native-state.json`. Do not edit or merge these progress formats.

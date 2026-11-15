---
name: research-lab-native
description: "Execute or resume research_lab research with Open Math native swarms: frozen DAG packets, accepted-evidence dependencies, time budgets, and independent judging. Use for a native research run, swarm-backed DAG continuation, or importing research receipts."
metadata:
  display_name: "Open Math Native Research Lab"
  category: "Workflow"
  long_description: |-
    Drive prepared research_lab DAG packets through a separate Open Math native
    execution route. Begin one bounded swarm per ready DAG task, preserve root
    blindness and declared dependency visibility, judge reports, import accepted
    finish receipts, and generate an evidence report without claiming a theorem.
---

# Execute a native research DAG

Read `AGENTS.md` completely before planning or resuming a run. It is the frozen
operating contract. Then read `research_lab/OPEN_MATH_NATIVE.md` and the exact
run directory's launch/evidence state.

This route is agent-driven. `open_math_native.py` does not expose a model API
and cannot launch or judge a swarm. Use it for packet state, then perform the
named model and swarm operations yourself. Never call the subscription
`parallel_runner.py start`, `run`, or `resume` on a native run.

## Required loop

1. Audit before acting. Do not use a neutral template as a research problem.
2. Select a structurally ready task, check the global and task clocks, then
   `begin` it once. Read its generated `launch_request.json`.
3. Pass the request's exact task, model, members, minutes, member_steps and
   reasoning_effort to `ultramath_start`. Default to conservative concurrency.
   members share four CPUs. Immediately `attach` the returned swarm ID.
4. Set reminders only as needed to enforce the active and global deadlines.
   When a report wakes you, judge it. Run mechanical checks where possible and
   inspect remaining mathematical gaps yourself. `ultramath_verdict` is required
   for acceptance or rejection. Never leave a report silently unjudged.
5. After genuine acceptance, record the exact schema-valid `finish` receipt via
   `open_math_native.py accept ... --note "what you actually checked"`. A
   receipt enables only the next tasks whose declared dependency contexts allow
   it. Preserve independent root blindness.
6. For an unsuccessful or expired attempt, stop the corresponding swarm and
   `close` it with an accurate note before considering any still-authorized
   retry. Never extend frozen state to permit another attempt.
7. Generate `report` after completion or termination. Report used budget,
   native model, accepted evidence, active jobs, correctness limits, and the
   next new preparation needed.

## Explicit do-nots

- Do not launch a new run merely because the current run completed.
- Do not bypass root or dependency evidence boundaries through other files,
  swarm boards or an unrestricted filesystem.
- Do not copy a truncated source or partial receipt as though complete.
- Do not use Open Math native execution to claim subscription/Podman execution.
- Do not resume a restored swarm past its native active or global deadline.
- Do not trade away statement fidelity or hide a proof gap to finish a graph.

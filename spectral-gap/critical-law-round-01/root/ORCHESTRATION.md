# Current orchestration and the available research_lab harness

November 15, 2026, America/Los_Angeles. Read-only capability inspection.

The current research rounds use the math-collaboration workflow, session-native task delegation, owned output directories, frozen proof hashes and separate revision-bound reviews. They have not been executed by research_lab. The existence of that archived directory does not mean its controller was used.

## What was inspected

The previous [orchestration identity audit](../../../../spectral-reconciliation-2026-11-14/ORCHESTRATOR_AUDIT.md) separates the original local loop engine, the spectral batch-clock sidecar, the research_lab harness and its later native adapter. This inspection reread that audit and directly inspected the following snapshot files without executing them:

- [Harness README](../../snapshot/research_lab/README.md).
- [Native adapter documentation](../../snapshot/research_lab/OPEN_MATH_NATIVE.md).
- [Installation record](../../snapshot/research_lab/OPEN_MATH_OS.md).
- [Graph preparation and audit implementation](../../snapshot/research_lab/parallel_runner.py).
- [Native readiness, request and receipt implementation](../../snapshot/research_lab/open_math_native.py).
- [Neutral dependency graph](../../snapshot/research_lab/templates/research-packet/dag.json) and [reply schema](../../snapshot/research_lab/pilot/reply.schema.json).

No preparation, audit executable, worker launch, queue restart, recovery operation or snapshot write occurred. The historical installation's test result was read as a past record, not rerun or reported as a current validation.

## Verified capabilities

The harness has real reusable infrastructure. Preparation freezes per-task inputs, their hashes, routes, dependency edges and a reply contract. Its audit checks those values and refuses changed inputs. Its controller supports bounded attempts, elapsed-time ceilings, checkpoint retention and structured reporting.

The native adapter is a separate state machine. Its ready operation checks accepted direct dependencies. Its begin operation enforces dependency, concurrency, attempt and time limits and produces a frozen launch request. It does not launch work itself. Acceptance validates a complete finish receipt, copies its bytes to a read-only record, records a hash and a review note, then advances dependency state. Later reads recheck accepted receipt hashes.

These capabilities can reduce coordination mistakes. They do not establish mathematical correctness, historical novelty or complete formalization. Receipt acceptance is a recorded judgment, not a theorem checker.

## Current compatibility limits

The adapter expects a particular remote launch and worker-identifier protocol. That launch protocol is absent from the currently discovered tool inventory. The current session-native delegation interface has different task and lifecycle records. The adapter's acceptance method requires a running attached job, so importing today's results through invented historical worker identifiers would be inaccurate.

The snapshot's subscription-client link is absent at the inspected path. The old installation record also lists environment prerequisites that were missing on its original host. Those historical diagnostics do not establish the present machine's full readiness. No current live-execution preflight was run.

Accordingly, the existing adapter is not a drop-in controller for this session. A faithful integration would need a separate adapter or an explicitly tested compatible execution route in a fresh working copy. It should preserve the distinction between historical source state and current task state.

## Recommendation

Continue the bounded mathematical round with its current delegated tasks and independent proof reviews. The immediate useful addition is a small machine-readable dependency and receipt record beside the present run contract: each task's input hashes, proof artifact hashes, review artifact hashes, actual task identifier, terminal state and unresolved findings. A read-only validator could then detect stale reviews and incomplete dependency chains.

That is a focused reuse of the harness's evidence design. It must be described as such, not as execution through research_lab. It does not require its old worker scheduler, subscription configuration, archived queues or remote protocol. The present manifests already provide much of this evidence, so the main additional value would be automatic dependency and stale-review validation.

If repeated sessions make scheduling itself a bottleneck, port and test a compatible adapter in a new directory before moving a future round onto it. Avoid pausing the present proof work merely to adopt a larger controller. This note recommends that boundary and does not implement or authorize a new unattended execution route.

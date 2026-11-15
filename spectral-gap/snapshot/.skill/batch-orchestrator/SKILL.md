---
name: batch-orchestrator
description: "Run queued work as time-boxed batches: pick the next batch, hold it to its wall-clock budget, record the outcome. Use when the user asks for batched, bounded, phased or orchestrated execution of a work queue."
metadata:
  display_name: "Batch Orchestrator"
  category: "Workflow"
  long_description: |-
    Dispatch queued work one batch at a time, each with an explicit wall-clock
    budget, a definition of done and a ledger entry. Batches are ordinary
    Markdown files whose frontmatter carries the budget and the status. A small
    runner keeps the clock, refuses a batch that has no budget, and makes every
    extension and overrun visible instead of silent.
---

# Run a batch queue

Read the project-root `AGENTS.md` before creating or advancing a queue. It is
the common contract. This skill supplies runner details but cannot widen its
authorization, evidence or correctness rules.

The queue is a folder of batches. The batch is the unit of commitment. Nothing
starts without a budget, nothing ends without a ledger line.

## Layout

```
.orchestrator/
  queue/010-name.md    one batch per file, frontmatter carries the contract
  queue/_TEMPLATE.md   copy this to open a new batch (underscore files are skipped)
  bin/batch.py         status | next | start | check | extend | close
  state.json           clock of the running batch (absent when idle)
  logs/010.log         append-only per-batch log
  LEDGER.md            one row per closed batch
results/               deliverables, named after the batch
```

## Protocol

1. **Survey.** `python3 .orchestrator/bin/batch.py status`. Read the batch file
   of the one you intend to run, in full, including `done_when`.
2. **Open.** `batch.py start <id>`. This prints the deadline. Record the
   remaining seconds, you need them in step 3. `start` refuses a batch with no
   `budget_s`, and refuses to open a second batch while one is running.
3. **Work inside the box.** For every long command, pass
   `timeout_ms = min(remaining_ms - 90000, cap)`, clamping to at least 10000.
   The 90 s reserve is for writing results and closing out. Do not spend it on
   more work. Re-read the clock with `batch.py check --json` before each long
   step, not once at the start.
4. **Stop at the reserve.** Overrunning is a silent lie about the budget. When
   the reserve is reached, stop working, write what you have to
   `results/<id>.md` with an explicit `## State` section saying what is done,
   what is not, and the exact next action.
5. **Close.** `batch.py close <id> done|blocked|abandoned --note "..." --artifact results/<id>.md`.
   `blocked` means an external decision or missing input. `abandoned` means the
   batch was wrong to open. Close even when the work failed. An open batch
   blocks the queue.
6. **Report** the ledger line to the user, one line per batch, then the next
   batch's id and budget.

## Rules

- **One batch at a time.** Parallel batches compete for the same CPUs and make
  every budget a fiction. Two may run together only if the batch files say
  `parallel_ok: true` and `nproc` covers both, and then each needs its own
  `timeout_ms`. `ultramath_start` is the tool for genuine fan-out, not this.
- **Extension is a logged decision.** Run out of budget with the result nearly
  in hand: `batch.py extend 10 "finishing the last case"` then continue. Never
  extend silently by working past the deadline.
- **A batch that cannot fit is not started.** If remaining time before a hard
  stop (end of turn, a meeting, a lease) is less than `budget_s`, say so and
  propose the split.
- **Interrupted state.** If `state.json` exists but no work is running, the run
  was cut off. Run `close --force` it with the truth about what landed.
- Background jobs keep running after a batch closes: a batch may legitimately
  end by launching a job and recording its id, with the check in a later batch.

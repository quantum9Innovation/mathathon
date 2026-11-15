---
id: 010
title: Smoke-test the batch runner
state: done
budget_s: 120
parallel_ok: false
done_when: "batch.py start/check/extend/close round-trips without error and LEDGER.md gains one row"
---

## Goal

Verify the runner actually keeps a clock: start it, read remaining time, extend
once, close it, and confirm the ledger and log lines land.

## Plan

1. `batch.py start 010`, note the deadline.
2. `batch.py check --json`, confirm remaining_ms is sane.
3. `batch.py extend 1`, confirm the deadline moves.
4. `batch.py close 010 done`.
5. Read LEDGER.md and logs/010.log.

# Batch 050 run record

## Active run

- Queue `050` was started within its fixed 10,800-second budget.
- One Ultramath swarm `smwgwbyn9` was launched with six distinct roles.
- Model: `deepseek/deepseek-v4.1-flash`, maximum reasoning effort, at most 160 model
  calls per member run.
- The swarm deadline is 135 minutes after launch. It uses a four-CPU VM shared by all
  six members.
- A final 45-minute review and report reserve sits inside the three-hour batch budget.
- No second swarm or extended deadline is authorized by this launch.

## Current state

The mathematical work is in progress. `results/050-finite-defect.md` has not been
written yet. The preparation statement that no swarm had been launched describes only
the completed preparation phase, not the status after this run began.

## Review obligations

Use the acceptance tests in `README.md`. Gate A requires an exact surviving target or a
corrected weaker hypothesis by 45 minutes. Gate B requires an actionable proof reduction
by 90 minutes. The last 45 minutes are for independent review, not additional research.

Evidence from the prior categorical report remains available in
`results/spectral-research/reviews/d3-first-review.md`. Primary source PDFs and text
snapshots are stored under `sources/` with SHA256 values in `source-baseline.md`.

## Exit requirements

Judge each submission rather than treating it as accepted research. Save any real
theorem, the strongest obstruction, source limitations and failed approaches honestly.
Write `results/050-finite-defect.md`, then close the queue with the actual outcome.

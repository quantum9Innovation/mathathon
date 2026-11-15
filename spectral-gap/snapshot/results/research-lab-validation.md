# Research harness validation: 2026-11-14

## Outcome

The archive opens, the engine is installed without source changes, and all
offline/local controller checks pass. Live research is **not ready** because the
subscription client, subscription-login verification and rootless Podman/image
prerequisites are absent. The VM also denies unprivileged user namespaces.

No worker was launched. No remote inference, browsing or billing call occurred.

## Commands and results

| Check | Result |
| --- | --- |
| `gzip -t attachments/.../research_lab_portable.tar.gz` | pass, no decompression error |
| tar member safety inspection | 56 regular-file/directory members, no unsafe paths or links |
| archive extraction | pass into project-root `research_lab/` |
| README comparison | byte-identical to the attached README |
| `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s research_lab/tests -v` | pass: 119 tests in 1.969 s |
| neutral bounded `parallel_runner.py prepare` | exit 0, 60-minute example run prepared |
| `parallel_runner.py audit` on that run | exit 0, `Frozen inputs verified` |
| `parallel_runner.py status` on that run | 9 pending jobs, 3600 s remaining, null start/deadline |
| `research_runner.py doctor` | exit 2, `Subscription client is missing` |
| `command -v podman` and required helpers | not found |
| `unshare -Ur true` | refused: `Operation not permitted` |

Full offline test output is in [research-lab-offline-tests.log](research-lab-offline-tests.log).
Operation in this VM, including the foreground `resume` requirement, is documented
in [../research_lab/OPEN_MATH_OS.md](../research_lab/OPEN_MATH_OS.md).

## Exact prepared example

The test preparation used:

```bash
python3 research_lab/parallel_runner.py prepare \
  --plan research_lab/templates/research-packet/dag.json \
  --run-dir research_lab/runs/example-default \
  --minutes 60 --profile bounded --network public_sources
python3 research_lab/parallel_runner.py audit --run-dir research_lab/runs/example-default
python3 research_lab/parallel_runner.py status --run-dir research_lab/runs/example-default
```

This is a neutral **template**, not a ready research packet. It prepared audit
fixtures only. No actual authorization or research target was inferred from it.

## External prerequisites still required

1. Provide the installed compatible subscription client's executable path for
   the required symlink. Its own subscription login must already exist. There
   is nothing to point the symlink at in this VM.
2. Configure working rootless Podman and its user-namespace support through the
   host/system administrator, and provision the Python 3.12 Bookworm image.
3. Re-run `python3 research_lab/research_runner.py doctor`. Only a passing result
   establishes live prerequisite readiness. Authentication and supported client
   features remain **unverified** until then.

The fixed model/billing route remains `gpt-6.1-sol`, subscription-only and high
reasoning. No attempt was made to route it through the Open Math OS agent model
or another service.

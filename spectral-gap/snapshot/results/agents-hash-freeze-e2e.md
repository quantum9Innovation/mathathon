# End-to-end AGENTS hash freeze verification

## Outcome: passed

A real Open Math native swarm was launched and attached to a frozen native DAG
run. Its contract remained frozen before, during and after the run. A temporary
edit to `AGENTS.md` caused all six tested native commands to refuse work. The
exact original contract bytes restored acceptance. The successful diagnostic
receipt was then independently judged and imported.

The diagnostic arithmetic is correct but trivial. This verification establishes
execution-control behavior only. It does not assert a research result, native
mathematical capability, subscription billing or proof certification.

## Frozen identity and launch

| Item | Verified value |
| --- | --- |
| Run | `research_lab/runs/agents-hash-freeze-e2e-v2` |
| Frozen AGENTS SHA256 | `cf1cdb64293654c36b1317ef26eea5bb85cc2ede626951bf637ed344d6aa17b7` |
| Final AGENTS SHA256 | `cf1cdb64293654c36b1317ef26eea5bb85cc2ede626951bf637ed344d6aa17b7` |
| Byte and mode restoration | passed |
| Swarm ID returned by Open Math | `smwgdfar0` |
| Returned direction | `d1`, submitted by the single member |
| Native model route | `deepseek/deepseek-v4.1-flash` |
| Members, minutes, member steps | 1, 5, 10 |
| Reasoning effort | `max` |
| Accepted launch task size | 16379 bytes, below the 16,384-byte tool ceiling |
| Receipt schema SHA256 | `a89db9b783dd3ca17a6fdad22386b0208a2150a284a874e16b81e6640cd8caf6` |

The complete AGENTS bytes from initialization occur in the prompt that produced
the attached native launch request. The prompt also references the frozen schema
by path and SHA256. The native plan's model and member controls were supplied
exactly to `ultramath_start`.

The returned swarm status separately agreed with this model route and direction,
and no other workers were running after the accepted verdict. As documented by
the adapter, its local records are not cryptographic attestation of remote model
actions beyond what the Open Math tool reports. The service returned no monetary
usage total here.

## Live edit refusal

The contract was attached before editing. A single harmless temporary line was
then appended to `AGENTS.md`, changing its hash to
`bb084ca20105cdd4a0021bd37a9f5a2f8709f6f9b43c46916e4ea1655c5c925e`.

| Command tested through its CLI | Exit | Result |
| --- | --- | --- |
| `audit` | 2 | exact mismatch refusal |
| `status` | 2 | exact mismatch refusal |
| `begin` | 2 | exact mismatch refusal |
| `attach` | 2 | exact mismatch refusal |
| `accept` | 2 | exact mismatch refusal |
| `close` | 2 | exact mismatch refusal |

Each command returned exactly:

`Cannot proceed: AGENTS.md changed, create a new prepared native run`

No advancement, import, closure or report mutation was allowed to bypass the
mismatch. This works because every one of those command paths checks the plan's
guidance hash through the native controller's audited read routine.

Afterward the saved original bytes and original file mode were restored. The
restored SHA256 was independently compared with the plan again, and native
`audit` returned `Frozen source packet and native execution plan verified`.

The control did not depend on pretending the file had not changed. Its changed
hash is recorded here, as are the restored exact bytes and fresh audit result.

## Judging and receipt import

The member submitted `.ultramath/smwgdfar0/m1/finish-receipt.json`. Before
acceptance, the controller independently checked:

- actual schema and reply validation with the controller's validators,
- exact frozen schema bytes and SHA256,
- `action: finish`, required fields and scope-limiting text,
- the arithmetic argument $7(10 + 3) = 70 + 21 = 91$.

The verdict accepted the diagnostic and finished the swarm. The tool reports
one accepted solution and a solved terminal state, with no running members.
The native import subsequently stored an identical read-only copy:

`research_lab/runs/agents-hash-freeze-e2e-v2/open_math/jobs/hash-freeze-probe/accepted/m1-f6a1fb06d56590e5.json`

Receipt SHA256: `f6a1fb06d56590e5ccbae29f8a1af0ad6988b49d628d2daaa785c86189c7f66e`.

The native job is `accepted`, has no active attempt, and consumed one attempt.
The separate subscription-controller source state remains `prepared`, as
required by the two-route separation. The original `reply.schema.json` remains
the schema authority and was not changed.

## Tool-limit discovery and regression

The first attempted launch produced no swarm because its task was 18,942 bytes,
above the 16,384-byte limit returned by `ultramath_start`. That attempt was
closed as failed without resetting its one-attempt ceiling: [initial status](agents-freeze-initial-oversize-status.json).

The prompt compiler now enforces 16,384 bytes, references the frozen schema by
path and hash, and removes duplicated scaffolding without dropping AGENTS or
evidence. Further oversized preflights on the replacement run consumed neither
an attempt nor its launch clock. The successful replacement contains the
complete updated contract and fits in 16,379 bytes.

The complete regression suite passed **126 tests in 2.008 seconds**, including
the oversized-prompt no-consumption regression: [test log](agents-freeze-regression.log).

## Evidence paths

- Frozen plan: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/plan.json`
- Exact launch request: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/jobs/hash-freeze-probe/attempt-01/launch_request.json`
- Attached swarm attestation: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/jobs/hash-freeze-probe/attempt-01/swarm.json`
- Edit refusal details: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/verification/edit-refusal.json`
- Backup before temporary edit: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/verification/AGENTS.md.before`
- Accepted receipt: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/jobs/hash-freeze-probe/accepted/m1-f6a1fb06d56590e5.json`
- Native report: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/OPEN_MATH_REPORT.md`
- Native state: `research_lab/runs/agents-hash-freeze-e2e-v2/open_math/native-state.json`

`AGENTS.md` remains uncommitted and is not ignored. No further remote diagnostic
run, research task or new budget was authorized or started.

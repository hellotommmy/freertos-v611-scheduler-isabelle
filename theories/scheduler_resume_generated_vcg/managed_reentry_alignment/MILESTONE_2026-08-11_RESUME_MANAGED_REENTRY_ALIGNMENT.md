# Resume managed re-entry alignment — 2026-08-11

Baseline: `c2cc7c1f2966436896dac1d85998ab15bd93abe6` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child re-establishes the pure and proof-only portions of the
managed pending-drain phase after one abstract `resume_one_pending_abs` step.
The exact post objects are the literal
`resume_pending_drained_context C t rest` and
`resume_pending_drained_snapshot C t P`.

The child proves that the managed pending task list is exactly `rest`, carries
the tasks-live subset across the unchanged live set, and reconstructs the
managed phase alignment at the post abstract state.  It deliberately imposes
no equality on `rpc_generic_owner`: the drained context retains the old ghost
function, and pure entry constrains it only for remaining pending tasks.

A reverse one-due adapter copies the stable resume snapshot fields and resets
the two transient one-due registers to `None`.  Its inverse has the sharp
premise `\<not> rps_local_yield P`; the drained pure relation supplies that
premise for the exact post roundtrip.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_pending_snapshot_of_one_due_inverse` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_managed_tasksD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_pureD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_tasks_liveD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_one_due_projectionD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_snapshot_roundtripD` | 2 | 0 |

The embedded ML ledger is exactly `1/2/2/2/2/2/2`, with zero hidden
hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Alignment` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Captured_Key`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-alignment-01-drained-context` | 1 | 196.776 s | pending selector/map composition remained |
| `20260811Tresume-managed-reentry-alignment-02-pending-selector` | 1 | 188.193 s | selector passed; `map (node_owner \<circ> Event)` remained |
| `20260811Tresume-managed-reentry-alignment-03-owner-map-induction` | 1 | 186.668 s | task tail passed; local alias `context` parsed as an outer command |
| `20260811Tresume-managed-reentry-alignment-04-fact-aliases` | 0 | 187.355 s | green; leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `7AC434B2481E4A3930863DDF1090DC68913FCA091405695560FC3E51458B95E7` |
| `command.txt` | `8CD72914CE085823F17EA0399BD65AD33D5F6A73A0ED4D4AC33201ED75F45B4F` |
| `status.txt` | `6E08A95159774B89887CB39C588AE0452E5AE6E2E77E851F7F2C3DB0C6E9B6E8` |
| `stdout.log` | `A666BC51BD9E98E4EEFE92FBE0793C4A877788335E7DC50745D24FC7F7127940` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The post drained context/snapshot now satisfy the pure, live, alignment, and
one-due projection clauses required by the future managed phase.  The next
abstract rungs transport the managed domain and wake projection, followed by
the strong Generic and Event role projections.  Concrete public-shadow
reconstruction remains separate.

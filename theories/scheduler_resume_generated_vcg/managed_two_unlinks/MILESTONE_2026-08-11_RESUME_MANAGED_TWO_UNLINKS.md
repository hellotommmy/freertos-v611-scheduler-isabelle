# Resume managed two-unlink source composition — 2026-08-11

Baseline: `3e28542276fbf3b34bb93c6339d5dcc4e477f823` on
`agent/universal-scheduler-refinement`.

## Checked scope

This thin exclusive child composes the already-green generated Event-list and
Generic-list removals for the pending head.  The first call starts in `c`; its
exact Event-removed post-state is the exact input of the second call; the bind
ends in
`scheduler_mem_state (resume_pending_generic_remove_heap D t c) c` with
`Result ()`.

The child adds no relational postcondition, legacy Resume gate, global owner
equation, or ready-insertion claim.  Its proof is only `runs_to_bind` plus the
two exact managed source theorems and their intermediate-state substitution.

## Theorem-object audit

`CursorGeneralStrongResumePendingManagedPhaseRel_generated_two_unlinks_exact`
has exactly two premises—the managed phase and
`rpc_tasks C = t # rest`—and zero hidden hypotheses.  The embedded ML check
audits the exact `2/0` ledger in the checked theory.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Two_Unlinks` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_Relational`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-two-unlinks-01-exact-bind` | 0 | 239.463 s | green; parent 10 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `9F453770A1EBEA997ACD940A7D7DEDDCEDCB6E1F7169F96C41469345CB895C45` |
| `command.txt` | `E33DB5969A727BA717D1AB38F56E9AF1A3B46DA148A5AF4855BF40ACC524C7FE` |
| `status.txt` | `9080653A792716403881883A7F14FC2E30F58A60E1166646E6CA1CBB1BFB501B` |
| `stdout.log` | `BAFBB6ACEC6310C39BBCB1DAF4F36B09E5352854E62A64A168A6016C65F4711F` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The two generated unlink calls are now source-composed.  Ready insertion and
its freshness use, ready/top/scalar/yield effects, managed snapshot re-entry,
body composition, and loop induction remain later rungs.

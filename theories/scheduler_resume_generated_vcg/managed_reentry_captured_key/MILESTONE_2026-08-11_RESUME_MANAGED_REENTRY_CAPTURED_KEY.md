# Resume managed re-entry captured key — 2026-08-11

Baseline: `f3e3a3fa2b9ec7daaada41e5abf0ffc7702a4fe0` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child recovers the abstract Generic item value captured before
the pending task is unlinked.  The managed gate theorem is task-scoped: the
canonical pending owner and strong Generic role projection identify the
physical delayed-A, delayed-B, or suspended source, while the one-due snapshot
projection supplies the exact `K_G t` payload.

The managed phase wrapper additionally rewrites the payload through
`rpc_K_G C`.  It introduces no global owner-function equality, no old resume
gate, and no `managed = sa_live` collapse.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedGateRel_captured_keyD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_captured_keyD` | 2 | 0 |

The embedded ML ledger checks both theorem objects at exactly `2/0`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Captured_Key` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Core`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-key-01-task-scoped` | 0 | 196.990 s | green; parent 10 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `4C47BC2C4AFD098769FA16139FE0BB33F9DFEA2F3419FA0B22B7FF6F69B69193` |
| `command.txt` | `B7E17065BC77525DE920A5B9FB9654F3EC79F89872085A7B7811A611A1B5CBCC` |
| `status.txt` | `EE0E238190EF5EF87A2E0E3192AC9594FE3155C2CAA9A8D837B41DFB1B4723B2` |
| `stdout.log` | `058E16B53738AD4685B17C7910E8013C35BFBA9368AB0EAD02EF863E68A1F8B7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The post Generic ready insertion can now be matched to
`resume_one_pending_abs t a` with the exact captured key.  The next abstract
re-entry rungs transport the managed domain, wake and role projections, and
construct the reverse one-due snapshot adapter around the literal drained
resume snapshot.

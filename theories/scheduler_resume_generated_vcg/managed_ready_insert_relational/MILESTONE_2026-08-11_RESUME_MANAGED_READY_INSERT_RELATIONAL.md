# Resume managed ready-insert relational cutpoint — 2026-08-11

Baseline: `97fcb85cd64a6668b26dc69e6f59f1d1fede5dae` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child classifies the exact state after the source-faithful
ready insertion.  From the managed phase and
`rpc_tasks C = t # rest`, it proves:

- complete Generic coverage for `resume_pending_drained_generic_fam` and the
  drained abstract snapshot;
- Event coverage framed across the Generic insert-end;
- preserved managed task observation;
- reconstructed post-insert Generic/Event cross-storage separation;
- the exact `RP_ReadyInserted` phase invariant; and
- equality of the concrete raised top-ready priority with the drained
  snapshot's abstract top.

The checker-green pre-insert global-unlinked fact is consumed to establish
freshness.  It is intentionally not preserved: after insertion the Generic
item is linked at its ready root.  The proof uses the managed gate only to
recover the protected public shadow's entry top; it does not use the legacy
Resume gate, collapse `managed` to live tasks, or reconstruct a full transient
scheduler snapshot.

The top result is deliberately narrow.  A full
`scheduler_managed_scalar_rel` would be false when the head raises the top
above `sa_top_ready a`, and the abstract local-yield flag is not identified
with the concrete missed-yield global.

## Theorem-object audit

The capstone and all six projections have exactly two premises and zero hidden
hypotheses:

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_cross_storageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insertedD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_topD` | 2 |

The embedded ML ledger is `2/2/2/2/2/2/2`, with `0` hidden hypotheses
throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Insert_Relational` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Fragment`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-ready-insert-relational-01-six-relations` | 0 | 175.163 s | green; parent 9 s, leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `F56304323E127919ADA6521B18CC9E9687294D39B6EF7F7C599399544BA3818F` |
| `command.txt` | `1D0AE5EC3A41C826078F973735AC997D6935C9E9D7066E9E71E96F3AABA50199` |
| `status.txt` | `82106BB644CB949E00EED7D037D7289E72F9BCA0BA3105EAD212E69578A50539` |
| `stdout.log` | `EEA1DFF7F6A0AC960C36D914D06AD1B85331F53370995E6C25833545E0B00A90` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The ready-inserted heap now has a managed relational certificate.  The next
source rung may execute the current-task guard and yield comparison using the
preserved managed observation, followed separately by the drained next-head
read.  Managed re-entry against `resume_one_pending_abs t a`, body composition,
and loop induction remain later rungs.

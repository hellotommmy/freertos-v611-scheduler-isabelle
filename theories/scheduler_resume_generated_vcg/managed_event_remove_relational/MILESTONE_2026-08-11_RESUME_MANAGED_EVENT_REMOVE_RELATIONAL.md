# Resume managed Event-remove relational cutpoint — 2026-08-11

Baseline: `c47f68fcf3a75f678695bdb4b93a1e9e1e6225a6` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child classifies the exact transient state after the generated
pending-head Event removal.  From the managed phase and
`rpc_tasks C = t # rest`, it establishes five facts on the exact removed heap:

- complete Event coverage for the updated raw and abstract Event families;
- unchanged complete Generic coverage;
- preserved managed task observation;
- reconstructed Generic/Event cross-storage separation; and
- the generated `RP_EventUnlinked` phase invariant.

The proof applies the generic Event remove, Generic frame, observation frame,
and cross-storage theorems only after recovering the represented pending head
from the managed phase.  It does not use `resume_pending_gate_entry_rel`,
identify `managed` with `sa_live a`, or claim a full scheduler snapshot at the
transient Event-unlinked state.

## Theorem-object audit

All six audited theorem objects have zero hidden hypotheses and exactly two
premises: the managed phase and nonempty task-list equation.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_event_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_generic_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_observationD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_cross_storageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_event_unlinkedD` | 2 |

The exact ledger is `2/2/2/2/2/2`, with `0` hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove_Relational` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  Its sole parent import already contains the generic frame and
task-observation support.  The repository wrapper remained bounded at 300
seconds and used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-event-remove-relational-01-five-relations` | 0 | 164.614 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `5AB415237B569B73BAA7A194887A49ADDE9B638052D1688B667CE1F6A0DAEC3C` |
| `command.txt` | `E0946A251E9328E114B528C9B7D680E90D17CA2612A82E82F42640A69C5BF392` |
| `status.txt` | `49F213477B5E7548AFF81DFBC02F769FF0515661B4B555E12FF8ABB6538F547F` |
| `stdout.log` | `65CD70B8B693B3A5465D44F7F5154EDFE8DB92BCEB6A52492307237C6A2F02B1` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next child should use the task-scoped canonical owner result and the green
post-Event Generic coverage to execute only the generated Generic
`vListRemove'`, with an explicit delayed-A/delayed-B/suspended owner-pointer
case split.  Generic/Event two-step source composition, ready insertion,
scalar/yield effects, and managed re-entry remain later rungs.

# Resume managed Generic remove after Event — 2026-08-11

Baseline: `35618f6029f4e47f18be8671fd4a1b59f68268c4` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child executes only the generated Generic `vListRemove'` from
the exact Event-removed state.  Its load-bearing bridge is task scoped:

`rpc_generic_owner C t = resume_pending_managed_owner a t`

for the current nonempty pending head.  No global owner-function equality is
introduced.  The bridge follows from the pure phase's head-owner membership,
the canonical task-owner uniqueness theorem, and the common strong-snapshot
Generic family.

The exact source theorem then uses the green post-Event
`GenericRootFamilyCoverage` to recover the raw owner root and member.  The
task-scoped owner equality normalises `resume_pending_owner_list_ptr` to the
delayed-A, delayed-B, or suspended source pointer.  The proof calls only
`resume_pending_generic_remove_generated_interface`; it does not call the
legacy managed-body Generic-after-Event theorem or assume the legacy gate.

## Theorem-object audit

Both audited theorem objects have zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_head_owner_eq` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_generic_remove_after_event` | 2 |

The exact ledger is `2/2`, with `0` hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_After_Event` has
sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove_Relational`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

The first run stopped at the first error: automation did not compose the phase
task-list alignment with `rpc_tasks C = t # rest`.  The bounded patch named
the canonical task-list equality explicitly; no theorem statement or owner
design changed.  The second run was green.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-generic-remove-after-event-01-task-owner-eq` | 1 | 166.307 s | first error at head task membership |
| `20260811Tresume-managed-generic-remove-after-event-02-explicit-task-membership` | 0 | 154.398 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `42F8D7CFD8F2B27FFE78D4F0BA396E4804A334A1A8C7CCE0BDDD45F3E6389E8D` |
| run01 `command.txt` | `6870B9071F421F3A3D71FB9129217CD77F36058608950EB19C08800923EBECD9` |
| run01 `status.txt` | `3F89DAC2DA790FC1BA834478744F0C0CEAAA154F32B1BE78DC514C1B87AC151C` |
| run01 `stdout.log` | `D0DE6F1BCD77A1AFFA94F50F15FA5404F71AD2AC70616916046571E24D3B78D7` |
| run01 `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |
| run02 `command.txt` | `6870B9071F421F3A3D71FB9129217CD77F36058608950EB19C08800923EBECD9` |
| run02 `status.txt` | `6901B86DE4DE04596CAA9C202258B78AFB269E3A8A8C224F86AFD5DF8133DF22` |
| run02 `stdout.log` | `FC0F022ADC959287C2CAA94B27209D1F8D38D20E00C393779C88049121F61094` |
| run02 `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next relational rung should classify the exact Generic-unlinked cutpoint:
updated Generic coverage, Event coverage framed across the Generic remove,
managed observation, reconstructed cross-storage, and
`RP_GenericUnlinked`.  Only after that classification should the two generated
unlinks be composed.  Ready insertion, scalar/yield effects, and managed
re-entry remain later rungs.

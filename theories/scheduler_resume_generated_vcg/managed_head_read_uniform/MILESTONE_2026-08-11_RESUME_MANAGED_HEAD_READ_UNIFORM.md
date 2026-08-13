# Resume managed uniform head read — 2026-08-11

Baseline: `6a8b75a68d1bd505b6c5c5118bb2096f72ea0994` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child completes the managed generated pending-head read.

The empty theorem derives a zero concrete pending count from the managed Event
family, transfers it across the ABI list lens and protected heap overlay, and
executes the exact generated false branch returning `NULL`.  The uniform
theorem then cases on `rpc_tasks C` and combines the checked empty and nonempty
siblings.  Its postcondition returns the source pointer whose TCB coercion is
exactly `resume_pending_next_head_tcb D (rpc_tasks C)`.

No body mutation, snapshot re-entry, or legacy gate is used.

## Theorem-object audit

Both audited theorems have zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_empty` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_uniform` | 1 |

The exact ledger is `2/1`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Uniform` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Nonempty`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-head-read-uniform-01-empty-cases` | 0 | 158.211 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `E7B00E9A20948E460329B89470B1F1BBA93E553A61AE9998A0CD00E8DB0EC6D0` |
| `command.txt` | `0DE10424B2E6AB6CBC85F24C176B3BC72C17D554537FC46F2F99947311C40831` |
| `status.txt` | `ECBA274AA4CD2DC764A98EC16EB63B36E4E605261434D202D34812AEDD43C571` |
| `stdout.log` | `0DF4B0DD9EBA4AAFBE6B63C5480E62741F2D3BF4D00A7D9A79AFABF9E5DEA185` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive operational child proves only the generated Event-list
removal for a nonempty managed phase.  It should obtain the raw pending member
from managed Event coverage and use the existing general `vListRemove` exact
state theorem.  Generic removal, ready insertion, scalar/yield steps, and
snapshot re-entry remain later children.

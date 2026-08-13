# Resume managed phase-adapter context — 2026-08-11

Baseline: `0005d3034f956400b3bdf009536635e029344008` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves that the canonical managed pending context is
well formed from one cursor-general managed Resume-gate premise.

The proof keeps the two carrier roles separate:

- `rpc_live` is the full `managed` representation domain;
- `rpc_tasks` is the public-live pending-ring order; and
- the public task subset is lifted into `managed` through the strong managed
  domain relation.

Priority bounds for every managed task are obtained from the strong managed
`TaskObservationRel`, not from the public core invariant.  The remaining
context obligations establish finite Generic/Event carriers, distinct pending
tasks, generated ready-root membership, top/current priority bounds, canonical
owner-root membership, and owner/ready-root separation.

Owner facts remain scoped to pending tasks.  This theorem does not impose a
global owner-function equality and therefore preserves the intended
singleton-to-empty re-entry shape.

## Theorem-object audit

The audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedGateRel_canonical_context_wf` | 1 |

The exact ledger is `1`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Context` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Base`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=60`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

First-error history:

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-phase-adapter-context-01-cold` | 1 | 150.273 s | owner-root membership |
| `20260811Tresume-managed-phase-adapter-context-02-owner-root-cases` | 1 | 136.388 s | over-refined nested owner proof |
| `20260811Tresume-managed-phase-adapter-context-03-owner-root-facts` | 1 | 135.804 s | over-refined quantified inequality proof |
| `20260811Tresume-managed-phase-adapter-context-04-owner-ready-direct` | 1 | 136.444 s | priority instance not fixed for ready-root separation |
| `20260811Tresume-managed-phase-adapter-context-05-owner-ready-helper` | 1 | 137.135 s | outer conjunction pre-split by recursive intro |
| `20260811Tresume-managed-phase-adapter-context-06-owner-conjunction` | 0 | 137.567 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `49A3B5EC10634CF160F7A110567BAAE01CD8EB0A6E2CD866B2B62BC1560F6CC6` |
| `command.txt` | `96FBFC81A9690D678E6F6EC0B47930990C4788CFF131E9B6661909989ECD0680` |
| `status.txt` | `91478F38FF0B5F4537F9EABCCF3A9B3FD8F1BCE6BF038255B93A1CAF857AA058` |
| `stdout.log` | `6DCA836B3BD0B33C4B93BBA144EFFC74F0C0146312C12215A9D665CF1F95B7FF` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child proves the canonical Resume family shape by
transferring the already-checked full-coverage one-due family theorem.  A
later task-scoped owner/source/key assembler may then establish the canonical
`resume_pending_entry_rel`, followed by canonical and existential managed
phase witnesses.  Generated body execution, re-entry preservation,
control-frame composition, and arbitrary-list drain remain later rungs.

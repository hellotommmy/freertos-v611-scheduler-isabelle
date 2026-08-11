# Resume managed phase-adapter base — 2026-08-11

Baseline: `63a3ba1c0a2912673c25202312e07e1086fb8656` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child introduces the proof-only objects needed to connect the
managed Resume gate to the pending-drain phase without reusing the legacy
gate.

The checked objects are:

- pending tasks in exact source-ring order,
  `map node_owner (ring (sa_pending a))`;
- a canonical initial owner function over delayed-A, delayed-B, and suspended
  roots;
- a total current-priority view whose legal empty/current-`None` value is zero;
- a canonical context with `rpc_live = managed`, complete Generic/Event root
  universes, generated pending/ready roots, public priority/top values, and
  symbolic `K_G`/`K_E` maps;
- an explicit one-due-to-Resume snapshot conversion preserving complete
  abstract families, payloads, top, and cursors;
- `resume_pending_managed_phase_alignment`, which deliberately does not impose
  full-function owner equality; and
- `CursorGeneralStrongResumePendingManagedPhaseRel`, which conjoins the managed
  gate, pure pending entry, the separate public-live task subset, and the field
  alignment.

The Event-only owner lemmas establish exact pending-ring reconstruction, task
set equality, and distinctness without asserting the false global injectivity
of `node_owner`.  Gate projections then prove the canonical tasks are distinct
and public-live.  The phase relation exports its gate, pure, public-live, and
alignment parts independently.

This is the algebraic adapter base.  It does not yet claim that the canonical
context/snapshot satisfies `resume_pending_entry_rel`; that one-premise
canonical witness is the next proof rung.

## Theorem-object audit

Every audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `event_node_list_owner_map` | 1 |
| `event_node_list_owner_set` | 1 |
| `event_node_list_owner_distinct` | 2 |
| `resume_pending_canonical_managed_context_components` | 0 |
| `resume_pending_snapshot_of_one_due_components` | 0 |
| `resume_pending_canonical_managed_phase_alignment` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_pending_event_ringD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_pending_xlist_wfD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_setD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_distinctD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_liveD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_canonical_alignmentD` | 1 |
| `CursorGeneralStrongResumePendingManagedPhaseRelI` | 4 |
| `CursorGeneralStrongResumePendingManagedPhaseRelD` | 1 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_gateD` | 1 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_pureD` | 1 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD` | 1 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD` | 1 |

The exact ledger is
`1/1/2/0/0/1/1/1/1/1/1/1/1/4/1/1/1/1/1`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Base` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Gate_Base`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and leaf
`timeout=60`.  The Gate_Base parent alone has `timeout=120`: a measured cold
promotion finished in 69 seconds after its former 60-second bound timed out.
The repository wrapper remained bounded at 300 seconds and used
`-o quick_and_dirty=false -j 1`.

First-error history:

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-phase-adapter-base-01-cold` | 142 | 195.151 s | parent Gate_Base promotion timeout; leaf cancelled |
| `20260811Tresume-managed-phase-adapter-base-02-parent-promotion-bound` | 1 | 209.659 s | parent green in 69 s; Event-owner set proof |
| `20260811Tresume-managed-phase-adapter-base-03-first-error-repair` | 1 | 133.473 s | inductive set equality remainder |
| `20260811Tresume-managed-phase-adapter-base-04-set-extensionality` | 1 | 137.183 s | Event-only distinctness |
| `20260811Tresume-managed-phase-adapter-base-05-event-inj-on` | 0 | 201.291 s | green; leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `D0DF997A11A72A108C7856A4D370FC9F2819DCC0EC16354B975B3FC5CBE14A71` |
| `command.txt` | `24F8172A027447B07DBC32A86448E3FB67AEDB4CAC3F080C4B11D488B04A276B` |
| `status.txt` | `A361927D7A2814E6A80C6DE8C8CC4D000C62267E516BBE8AFBDA798CDE64E5A7` |
| `stdout.log` | `8919DF01E5CD8246DD9B63628BA773705D4CF4F2390DAFCFE77E3CDC58758DEA` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child must prove, from one managed-gate premise, canonical
context well-formedness, canonical family shape, pending-task owner/source/key
correctness, `resume_pending_entry_rel` for the canonical objects, and finally
the canonical/existential managed phase witness.  Owner correctness must stay
scoped to pending tasks.  Generated body, raw owner geometry, re-entry,
control-frame composition, and the arbitrary-list drain remain later rungs.

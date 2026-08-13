# Resume managed phase-adapter owner — 2026-08-11

Baseline: `1ccde63432f4c7e2d8075115ec549149c09bf3f7` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the canonical pending owner/source/key triple for
one task.  Its only premises are the cursor-general managed Resume gate and
membership of that task in the canonical pending task list.

The cursor-general core is used through its canonical cursor shadow solely to
recover the delayed-A, delayed-B, or suspended physical source of the pending
task.  The strong Generic role projection then places the task at the
canonical owner root.  The already-green canonical context supplies managed
and owner-root membership, while the already-green family shape supplies
pairwise root disjointness and the managed Generic key ledger.  Thus root
uniqueness and `K_G` agreement are obtained without reopening raw decoder
coverage.

The conclusion is directly over `ods_generic_family S` and remains scoped to
the selected pending task.  No global owner-function equality is introduced.

## Theorem-object audit

The audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD` | 2 |

The exact ledger is `2`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Owner` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Family`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=60`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

First-error history:

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-phase-adapter-owner-01-family-ledger` | 1 | 149.996 s | reserved `context` label caused outer-syntax failure |
| `20260811Tresume-managed-phase-adapter-owner-02-context-label` | 1 | 139.305 s | physical-source branch projection needed logical elimination |
| `20260811Tresume-managed-phase-adapter-owner-03-source-branches` | 0 | 140.243 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `B56390F6758DB45DA3EBB03CC3F397320A114C3256C3D58C6A06E41AAA7D8FDB` |
| `command.txt` | `6425264B194D5068675B772E8276CCAD89B2EF2CECD75A0ED8899EB474B38423` |
| `status.txt` | `AD2326854193CF392A612820B627A085D535142F0A079DF6824FA828B2A9C7F9` |
| `stdout.log` | `BE480FFAF7B2C83ECDE8A999280928E5DDEF39B53E178F10414E1E5B0E71430B` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child assembles the six canonical
`resume_pending_entry_rel` conjuncts from one managed-gate premise: context,
family, pending Event-ring order, task-scoped owner triple, top equality, and
false local yield.  A subsequent thin child can combine that pure entry with
the canonical alignment and public-live task subset into the managed phase
relation.  Generated head read, body execution, re-entry preservation,
control-frame composition, and arbitrary-list drain remain later rungs.

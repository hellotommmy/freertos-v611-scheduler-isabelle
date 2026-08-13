# Resume managed Event remove — 2026-08-11

Baseline: `1758eb9338fe1b3056309b997c299d39d55fd6bd` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the first destructive generated step of the
managed pending body: removal of the nonempty head task's Event item.

From the managed phase and `rpc_tasks C = t # rest`, the proof obtains the
pending abstract Event member, lifts the public-live task into the full managed
domain, and uses complete Event coverage to recover the corresponding raw
member and raw pending-list relation.  The protected heap equality transports
that relation to the actual 1/1 state, where
`scheduler_vListRemove_general_exact_state` executes the real generated source.

The post state is exactly
`scheduler_mem_state (resume_pending_event_remove_heap D t c) c`.  No legacy
gate, Generic removal, ready insertion, scalar update, or re-entry claim is
used.

## Theorem-object audit

The audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_event_remove` | 2 |

The exact ledger is `2`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Uniform`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-event-remove-01-coverage-member` | 0 | 163.178 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `C2C8BD3B13FF717C52B5E2CF6D6F4A7418BA33B0C38C37B116C40A7ABE550CBC` |
| `command.txt` | `B21DC791A0771CA94FE69C230E7C515431ADB66104133D5296E7B8C5F4E25EDB` |
| `status.txt` | `9D036047B182D9BE22C112B07CBE033ADE01F1220BAC6A3CCBB7D0D5E7250551` |
| `stdout.log` | `D32CCA7E7B1418CBF2597247E275B79B48CD565B3EFD931AF77ACF23499BB017` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next operational child must establish the Generic-list relation and
canonical owner member after the Event removal, then execute only the generated
Generic `vListRemove'`.  Ready insertion, scalar/yield steps, body composition,
and managed snapshot re-entry remain later children.

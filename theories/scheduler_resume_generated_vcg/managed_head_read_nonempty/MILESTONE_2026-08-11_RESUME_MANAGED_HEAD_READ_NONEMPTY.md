# Resume managed nonempty head read — 2026-08-11

Baseline: `1b98670dae0b74d278524b2d1d4aadb1039af55e` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive operational child proves the exact generated pending-head read
for a nonempty managed phase.  Its only premises are the managed phase relation
and `rpc_tasks C = t # rest`.

The proof:

- extracts the protected public shadow and heap equality;
- obtains complete Generic/Event coverage and task observation;
- instantiates `represented_event_head_owner_priority` on
  `managed_scheduler_view a managed`;
- recovers the Event-item guard from managed task observation;
- transfers the pending ABI count through `GeneratedPendingEventRoot` and
  `abi_list_count_h_val`; and
- runs the exact generated source factor on the actual protected state.

The result is the correctly coerced `unit ptr` owner and the concrete state is
unchanged.  No legacy gate, generated body, or re-entry claim is used.

## Theorem-object audit

The audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_nonempty` | 2 |

The exact ledger is `2`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Nonempty` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Capstone`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-head-read-nonempty-01-managed-view` | 0 | 158.216 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `AEAC9AA2718901E8155883EAECCD329C9984624F01144DF03018727F243A01AC` |
| `command.txt` | `805B62EFEA19586B50E5001FBFBF44EECB1BF248606B6435ACBE09E9AF640014` |
| `status.txt` | `CEAADDB1979CC14BA928FE761838B83426C59C156AC1FE15A906171F7C90A6D8` |
| `stdout.log` | `A208A8BCB7AE02B0CB23910E7E54B5F54BE946563637E7C2C6D21E9BFECC6986` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next thin operational child may prove the two-premise empty sibling and a
uniform one-premise head-read theorem.  Generated body execution and managed
snapshot re-entry remain separate later children and must not reuse the legacy
Resume gate.

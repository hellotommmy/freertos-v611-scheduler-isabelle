# Resume managed re-entry snapshot — 2026-08-11

Baseline: `2e829c9` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child assembles the full scheduler snapshot after one managed
Resume pending-head body.  It proves:

- the complete public `CursorGeneralStrongSchedulerSnapshotRel` at the `0/0`
  shadow of the actual ready-inserted state; and
- the corresponding protected `1/1` snapshot at the actual state.

The post abstract state is `resume_one_pending_abs t a`.  The Generic and Event
families are the exact drained families, and the one-due snapshot is the exact
reverse adapter of `resume_pending_drained_snapshot C t P`.  The public theorem
combines the checked abstract snapshot, post Generic/Event coverages and raw
cross-storage, and the concrete shadow pins.  The protected theorem consumes
only the exact `1/1` overlay recovery and the public snapshot.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, a
managed/live equality, or a global Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_public_snapshotD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_protected_snapshotD` | 2 | 0 |

The embedded ML ledger checks exactly `2/2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Snapshot` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Concrete_Shadow`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-snapshot-01-full-public-protected` | 0 | 217.532 s | green; parent 10 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `8CC91689F39F2BFAC40362FDA3533D9DE4E3E20D3B964BC7692DCDF41B77391A` |
| `command.txt` | `2AFECBAD2BB0185E43A3FBFED572C15A520D818E5DFBDE39F179B5CBF90FE71C` |
| `status.txt` | `9BCE31CFD85E0AD6CA1EB16992966D688E5034E25D99487DDE809A369A59A7A4` |
| `stdout.log` | `29F63359D3787BBFE3CDA5D5E89F7CDB6008D84A5920D60B4EFD8D0A8690997B` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The complete protected scheduler snapshot is now checked.  The next thin rung
derives post quietness and current safety, assembles the managed gate, and then
combines that gate with the already checked drained pure relation, task-live
inclusion, and phase alignment to reconstruct the managed phase relation for
the remaining pending tail.

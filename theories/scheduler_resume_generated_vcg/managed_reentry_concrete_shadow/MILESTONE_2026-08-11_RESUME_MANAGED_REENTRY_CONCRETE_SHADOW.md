# Resume managed re-entry concrete shadow — 2026-08-11

Baseline: `09e0cdb` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child reconstructs the public `0/0` concrete shadow after one
managed Resume pending-head body.  It proves:

- exact recovery of the actual ready-inserted state as a `1/1` overlay of the
  public shadow;
- the public scheduler boundary relation;
- scheduler role and current-task relations for
  `resume_one_pending_abs t a`;
- the managed scalar relation, including the raised top-ready priority;
- managed task observation on the shadow heap.

The structural shadow theorem is sharper than the phase theorem: it needs only
the managed gate.  Scalar and observation retain the exact phase-plus-head
premises because they consume the checked ready-insert top and post heap.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, a
managed/live equality, or a global Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `scheduler_port_overlay_current_id` | 0 | 0 |
| `CursorGeneralStrongResumePendingManagedGateRel_reentry_concrete_shadowD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_scalar_shadowD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_concrete_shadowD` | 2 | 0 |

The embedded ML ledger checks exactly `0/1/2/2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Concrete_Shadow` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Observation`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-concrete-shadow-01-public-overlay` | 0 | 216.287 s | green; parent 9 s, leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `DACDE39719B57815260A73542165717A67337FCD691786003956821A15C7AE5D` |
| `command.txt` | `CEC22CE14337915B21644EAC59F3CD2E9A5C79CFCC65DFD51D9DF7DF1930AB38` |
| `status.txt` | `C4E4689AD56566059D8B2FD3298B41192B0C95CC704858CFEBC987286B571767` |
| `stdout.log` | `DFF78974CD2C8E32E53D493F262A0912C07CC3722E1E9050FE922FDAB15C8CED` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The public shadow now has every concrete pin required by
`CursorGeneralStrongSchedulerSnapshotRel`.  The next thin assembler combines
these pins with the checked abstract snapshot, post Generic/Event coverages,
managed observation, and raw cross-storage to obtain the full public snapshot,
then witnesses the actual `1/1` protected snapshot.

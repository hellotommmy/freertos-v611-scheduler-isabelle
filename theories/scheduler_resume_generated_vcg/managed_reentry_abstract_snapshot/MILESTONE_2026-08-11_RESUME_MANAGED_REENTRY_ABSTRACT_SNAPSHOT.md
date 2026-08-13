# Resume managed re-entry abstract snapshot — 2026-08-11

Baseline: `c47000b` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive capstone packages the six abstract clauses of the post
`CursorGeneralStrongSchedulerSnapshotRel` cut after one managed Resume
pending-head step:

- cursor-general scheduler core;
- cursor-general managed domain;
- strong Generic-root role projection;
- strong Event-root role projection;
- strong wake-payload projection;
- strong one-due snapshot projection over the reverse Resume adapter.

The public boundary remains exactly the managed phase relation plus
`rpc_tasks C = t # rest`.  The captured-key equality is consumed inside the
checked Generic-role transport; the post one-due projection itself records the
two families, two payload maps, top priority, and `captured=None` /
`checked=None`.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, a
managed/live equality, or a global Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_abstract_snapshotD` | 2 | 0 |

The embedded ML ledger checks the exact `2/0` boundary.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Abstract_Snapshot` has
sole parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Event_Role`,
one theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-abstract-snapshot-01-six-clauses` | 0 | 210.596 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `ACE33B29C306F7E0445BBD66025EE87FB1291F91F0194E9E8AE282BFED9A3415` |
| `command.txt` | `1E8F66FD8AF48A909FDDDD7B79A079536DC0CFF2CF9B6FE72B153C3AFAFE4E63` |
| `status.txt` | `5A9E70B162E557CDE27ED6EC87CD6CB3C5A5525338A4877E1F90EE9DDDE8BFFA` |
| `stdout.log` | `A237FDF8F55E5D6689113A18EADEBA6C3EA64BA1D7F62114EF51FE9B64AA18EC` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The full managed post snapshot still needs the heap-relative Generic/Event
coverages, managed task observation on `resume_one_pending_abs t a`, raw
cross-storage, and the concrete role/scalar/current/boundary pins.  The next
thin child transports the already-green ready-insert observation to the post
abstract state and can package the exact snapshot roundtrip; concrete shadow
reconstruction remains separate.

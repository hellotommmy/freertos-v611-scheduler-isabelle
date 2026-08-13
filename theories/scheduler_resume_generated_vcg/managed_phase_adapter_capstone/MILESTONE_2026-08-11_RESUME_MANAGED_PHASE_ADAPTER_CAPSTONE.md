# Resume managed phase-adapter capstone — 2026-08-11

Baseline: `e1b77ec220925df1da46ffb6ee316378dca75c56` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child completes the proof-only adapter from the cursor-general
managed Resume gate to the managed pending phase.

The canonical theorem combines exactly four already-green facts:

- the managed gate itself;
- canonical `resume_pending_entry_rel`;
- the canonical pending-task subset of public live tasks; and
- canonical field alignment over the full managed families.

An existential corollary witnesses the same canonical context and snapshot.
Neither theorem claims a generated execution step.  The managed carrier,
termination family, external Event roots, and cursor-bearing families remain
symbolic, and no legacy gate or global owner equality is introduced.

## Theorem-object audit

Both audited theorems have zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedGateRel_canonical_phaseD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_phase_exD` | 1 |

The exact ledger is `1/1`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Capstone` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry`,
one theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=60`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-phase-adapter-capstone-01-canonical-phase` | 0 | 154.226 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `76CB9E01F486378416BE95DD2BFBEEB95ED99E64BAE2A2DDFAEBF24BB7CC4A61` |
| `command.txt` | `061CB69D9DAAD86F638BED284BB2096E92828A81BA328CB81CC62B7393879A9E` |
| `status.txt` | `EC7BBEBC0E5BE734118F97F261486E9FA51FE223BEF02F6757D9FB0AE1F4B151` |
| `stdout.log` | `7FCDB8E517B78F51FAA0B9D54AD10CC518B93956EB85462BAB7F31C5CE11192C` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The managed gate-to-phase adapter is complete.  The next exclusive operational
child proves only the nonempty generated head read from the managed phase and
`rpc_tasks C = t # rest`.  It must instantiate represented Event-head facts on
`managed_scheduler_view a managed`; generated body execution and snapshot
re-entry remain separate later children.

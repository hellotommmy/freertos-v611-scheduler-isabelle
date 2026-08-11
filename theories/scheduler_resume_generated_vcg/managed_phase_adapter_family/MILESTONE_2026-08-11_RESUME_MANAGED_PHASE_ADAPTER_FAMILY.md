# Resume managed phase-adapter family — 2026-08-11

Baseline: `d42d20779907b0ed4a252240c96ed6275905c838` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the complete canonical Resume family shape without
duplicating the existing Generic/Event cross-family ledger.

`full_family_coverage_resume_pending_family_shape` takes complete Generic and
Event coverage plus the strong one-due snapshot projection.  It instantiates a
proof-only one-due context, reuses
`full_family_coverage_one_due_family_shape`, and transfers the seven family
shape clauses to the canonical Resume context and snapshot.  The managed-gate
corollary extracts exactly those three facts from the protected strong
scheduler snapshot.

The proof preserves complete families and cursor-bearing xlist abstractions.
It introduces no legacy Resume gate, no global owner equality, and no new
task/source premise.

## Theorem-object audit

Both audited theorems have zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `full_family_coverage_resume_pending_family_shape` | 3 |
| `CursorGeneralStrongResumePendingManagedGateRel_canonical_family_shapeD` | 1 |

The exact ledger is `3/1`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Family` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Context`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=60`.  The repository wrapper remained bounded at 300 seconds and
used `-o quick_and_dirty=false -j 1`.

First-error history:

| run | exit | wrapper | first result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-phase-adapter-family-01-transfer` | 1 | 148.921 s | dummy task carried a fresh explicit type variable |
| `20260811Tresume-managed-phase-adapter-family-02-inferred-task` | 1 | 138.069 s | gate coverage needed an explicit projection rewrite |
| `20260811Tresume-managed-phase-adapter-family-03-projection-rewrite` | 0 | 140.548 s | green; leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `D8021C7A47EB9B285DAC15CC5DB74A64DDE29F341A9DA5AE0EBC403129A0EF64` |
| `command.txt` | `D14886F62B6B7C83910992DCAD36171BF55164BEC0010C5CBECABB73F15CA79C` |
| `status.txt` | `B712133734A64650C6D9F30381D6AFF972C902839297F1ACD8827E645ECC4235` |
| `stdout.log` | `9BFAE3FDC089CB9CB79347FDD11D5B65843346DB3EA040B1C778AE662FC5698E` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child proves the task-scoped canonical owner/source/key
triple from a managed gate and pending-task membership.  That result, together
with the green context and family theorems, can assemble the one-premise
canonical `resume_pending_entry_rel`.  Generated body execution, re-entry
preservation, control-frame composition, and arbitrary-list drain remain later
rungs.

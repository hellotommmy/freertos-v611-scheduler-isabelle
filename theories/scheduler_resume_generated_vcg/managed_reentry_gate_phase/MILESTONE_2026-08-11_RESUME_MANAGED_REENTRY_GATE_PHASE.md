# Resume managed re-entry gate and phase — 2026-08-11

Baseline: `30690b8` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child reconstructs the managed pending-drain relation after one
generated head body.  It proves:

- gate side-condition preservation for arbitrary removed task `t`: suspend
  depth remains zero, and a nonempty post pending ring still implies a current
  task;
- the exact post `CursorGeneralStrongResumePendingManagedGateRel` at the actual
  ready-inserted `1/1` state; and
- the exact post `CursorGeneralStrongResumePendingManagedPhaseRel`, with the
  drained context, drained snapshot, and remaining task tail.

The side-condition lemma is deliberately sharper than the operational
re-entry theorems.  It needs only the input managed gate because removing one
Event node cannot create a nonempty pending ring, while current and suspend
depth are unchanged.  The full gate and phase retain the exact phase-plus-head
premises needed for the protected snapshot and drained relational objects.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, a
managed/live equality, or a global Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedGateRel_reentry_side_conditionsD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_gateD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_phaseD` | 2 | 0 |

The embedded ML ledger checks exactly `1/2/2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Gate_Phase` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Snapshot`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run reached only a mechanical conditional-rewrite failure in the
side-condition proof.  The bounded repair made the post-pending, pre-pending,
pre-current, and current-frame steps explicit; no statement or premise changed.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-gate-phase-01-tail-phase` | 1 | 218.461 s | first red at current-safety implication |
| `20260811Tresume-managed-reentry-gate-phase-02-explicit-current-transfer` | 0 | 206.381 s | green; leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `93E3AC4093C42F79062287B345DFAF1E687341AAC5B25156B16CE5E5412F90BB` |
| `command.txt` | `FB04735A84DE7447AAD4A2E0095653AA0F7287CE8890F59197735BDB28D8D9D2` |
| `status.txt` | `CC9B34A76589AF744B0C5BE3DFD991305860664609E9947D59B0C0319826640A` |
| `stdout.log` | `1F30B69474D2A71A3A5D44D45EA7381EF0E2D62F718960E18F32DA3B4BA279A7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

One generated body now returns to the same managed phase relation over the
remaining tail.  The next rung composes the checked body execution with this
re-entry theorem, preserving the exact result pair and loop-head ghost state.
That operational step is the reusable induction brick for an arbitrary managed
pending drain.

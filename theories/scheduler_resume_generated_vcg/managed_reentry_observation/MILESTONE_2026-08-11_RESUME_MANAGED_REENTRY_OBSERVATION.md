# Resume managed re-entry observation — 2026-08-11

Baseline: `89aad42` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child transports the ready-inserted managed task observation
from the entry abstract state to `resume_one_pending_abs t a` and packages it
with the checked abstract snapshot clauses and exact Resume/one-due snapshot
roundtrip.

The generic observation bridge is an unconditional equivalence.  A managed
view fixes `sa_live` to the same `managed` set on both sides, while
`resume_one_pending_abs` preserves `sa_priority`; these are the only abstract
state fields observed by `TaskObservationRel`.  The simplifier orientation
strictly removes the Resume step.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, a
managed/live equality, or a global Generic-owner equation.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `scheduler_managed_task_observation_rel_resume_one_pending_abs_iff` | 0 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observationD` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observed_snapshotD` | 2 | 0 |

The embedded ML ledger checks exactly `0/2/2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Observation` has sole
parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Abstract_Snapshot`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-observation-01-managed-view-iff` | 0 | 211.571 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `A2798DB5B89636914E62A21DFB0807AAEECCEABC129F1DCC09006C2E91832AF8` |
| `command.txt` | `A20C04879295F8C73E0C31BBDF24C4622EF1684CA5ADAD475A70D5382C8559D6` |
| `status.txt` | `44925EEDA71453FDE5EB2B4FCE07F5098E4C506E995105F6443AA7A0F4468B83` |
| `stdout.log` | `9DEFF8266DF7ABBB9A6DD14622BFBFB12A8ACAC2DF45462D3F5B5B019568A894` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The post abstract state, roles, domain, wake, one-due projection, observation,
and snapshot roundtrip are now checked.  The remaining full-snapshot work is
the concrete public shadow: scheduler role, managed scalar, current, and
boundary relations at port depth/mask `0/0`, together with the already-green
post family coverages and cross-storage facts.

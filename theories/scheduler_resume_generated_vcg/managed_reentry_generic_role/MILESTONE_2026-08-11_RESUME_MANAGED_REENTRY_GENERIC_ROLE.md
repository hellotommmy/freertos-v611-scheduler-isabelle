# Resume managed re-entry Generic role — 2026-08-11

Baseline: `75de94ec64cd6c12eeca946cce5f1cadb9c446d4` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child transports the strong Generic-root role projection across
one managed Resume pending-head step.  Its public theorem keeps the exact
two-premise boundary: the managed phase relation and
`rpc_tasks C = t # rest`.

The proof is task-scoped.  It identifies only the current head's owner and
captured key, distinguishes the four ready roots, delayed A, delayed B,
suspended, and termination, and never asserts a global owner-function
equality.  For a non-owner blocked root it uses the pure-entry uniqueness and
well-formedness facts plus `list_remove_abs_nonmember`, preserving the exact
cursor-bearing abstract list.  Frozen ready/non-ready root injectivity keeps
both the ready insertion and symbolic termination ring separate.

No theorem or premise uses the legacy `resume_pending_gate_entry_rel`, and no
`managed = sa_live a` collapse is introduced.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_pending_drained_generic_role_match` | 5 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_generic_roleD` | 2 | 0 |

The embedded ML ledger checks exactly `5/2`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Generic_Role` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Domain_Wake`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first four runs stopped at the first error only: canonical blocked-root
membership, then the delayed-A, delayed-B, and termination-owner inequality
orientations.  Each bounded patch retained the theorem statements and public
premise ledger.  The fifth run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-generic-role-01-task-scoped` | 1 | 202.823 s | first error: blocked-root membership |
| `20260811Tresume-managed-reentry-generic-role-02-explicit-root-membership` | 1 | 192.742 s | first error: delayed-A inequality direction |
| `20260811Tresume-managed-reentry-generic-role-03-delayed-a-orientation` | 1 | 192.035 s | first error: delayed-B inequality direction |
| `20260811Tresume-managed-reentry-generic-role-04-all-root-orientations` | 1 | 194.797 s | first error: termination/owner inequality direction |
| `20260811Tresume-managed-reentry-generic-role-05-termination-owner-orientation` | 0 | 194.095 s | green; leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `BA1BEBE27D7E8B53598EE489E7C83DD2FCBEEF6DC27B072BCB3A419BC6E5B673` |
| `command.txt` | `2FF79D8119445FB94EBC052F24530A41F44FC669E7ECA202E9CFFB4F60707C23` |
| `status.txt` | `2A475567E29C252FB85EBA844E0418F4ABC9F825150D6BDAF92EE3F908DA4686` |
| `stdout.log` | `6E29D88F4FA0D3C41842B6A5CBD0C72199240E518367E5EAF84B064233074797` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The cursor-general core, managed domain, wake payload, drained alignment,
one-due projection, captured key, and strong Generic role are now checked for
the iterative post-state.  The next exclusive abstract rung transports the
strong Event-role projection over the same drained snapshot, retaining
`managed`, `termination`, and `external` symbolically.

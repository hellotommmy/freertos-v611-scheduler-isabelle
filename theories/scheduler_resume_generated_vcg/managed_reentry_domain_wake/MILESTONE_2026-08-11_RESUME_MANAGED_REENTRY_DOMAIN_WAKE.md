# Resume managed re-entry domain and wake — 2026-08-11

Baseline: `8e77dcb9faad4111f36a498fbe4e70beffd34c4d` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child transports two cursor-insensitive abstract snapshot
clauses across `resume_one_pending_abs`.

- The cursor-general managed domain is preserved because `sa_live`, managed,
  and the symbolic termination ring are unchanged.
- The strong wake-payload projection is preserved because the processed task
  is removed from both delayed rings and its wake field is cleared, while all
  other live tasks are framed.

The generic wake lemma uses cursor-general core well-formedness only to recover
the exact delayed-ring distinctness needed by `generic_task_set_remove`.
Without distinctness, a duplicate processed node could remain after `remove1`
while its wake field had already been cleared.  No pending-head or live-task
premise is otherwise required.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domainD` | 1 | 0 |
| `cursor_general_strong_wake_payload_projection_resume_one_pending_abs` | 2 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_wakeD` | 1 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domain_wakeD` | 1 | 0 |

The embedded ML ledger is exactly `1/2/1/1`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Domain_Wake` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Alignment`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-reentry-domain-wake-01-cursor-insensitive` | 0 | 199.138 s | green; parent 9 s, leaf 4 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `1AD4ABF901FBC610A8898BFD90EB989C3CB684A31523E0BF4C25B72A277776B2` |
| `command.txt` | `1EB239D93CC9A1CE35D56E25C4EF97CF9AF82BF2FF112591D366E6B5ED0DB569` |
| `status.txt` | `BCEC7A3864E37F55DC128EB7A4797918FEDE25454856E136B7B5031BD018662E` |
| `stdout.log` | `1AEAECBA0D5234EC84DDEA022F4671D76401F6EC191DE089B899038854F76170` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

Managed domain, wake, drained alignment, and one-due projection are now ready
for the post strong snapshot.  The next abstract rungs reconstruct the strong
Generic and Event role projections over the exact drained snapshot families;
those require the checked captured key and task-scoped owner bridge.

# Resume managed yield fragment — 2026-08-11

Baseline: `396dc65d5b19a332790c6b534b4e98ab5a721529` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child proves the exact generated current-task guard and yield
comparison at the managed ready-inserted cutpoint.  From the managed phase and
`rpc_tasks C = t # rest`, it executes the named source factor
`resume_pending_generated_yield_join D t y` and returns

`if rpc_current_priority C <= rpc_priority C t then 1 else y`

without changing the concrete ready-inserted state.

The proof obtains the live current task through the managed gate, transfers its
pointer through the protected overlay and ready-insert frame, and compares the
two concrete TCB priority words using the post-insert managed observation.  It
does not use the legacy Resume gate, identify `managed` with public live tasks,
or claim the later relational yield-phase transition.

## Theorem-object audit

`CursorGeneralStrongResumePendingManagedPhaseRel_generated_yield_fragment_exact`
has exactly two premises and zero hidden hypotheses.  The embedded ML ledger is
`2/0`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Fragment` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Insert_Relational`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-yield-fragment-01-current-guard-compare` | 1 | 179.688 s | first error only: equality-blind guard `blast` |
| `20260811Tresume-managed-yield-fragment-02-explicit-current-guard` | 0 | 166.962 s | green; leaf 3 s |

The bounded repair only named `c_guard (sd_tcb_ptr D current)` from the managed
observation and rewrote it through the already-proved current-pointer equality;
the theorem statement and premise ledger did not change.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `37D8B0F993F3327B0D55DC6058F8C3C0F638727917E96656813B1A002F760B0F` |
| run-02 `command.txt` | `61951F5B5F1CA7D8C4B79D5351DA5E54FED5515338AC9A5CA81D5923AACD67D8` |
| run-02 `status.txt` | `E4291929D3531F28543B7E0C9AAF8B00DAF71C2614AA97BA4723610DCF3EA464` |
| run-02 `stdout.log` | `3EAB1E5623091D80B49B51FF2AA37A640C267DD5347542C28289B1A4E20D0C9B` |
| run-02 `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The source comparison is now checker-green.  The next rung should separately
establish the `RP_YieldChecked` relational transition and its loop-carried
result/local-yield encoding, before composing the complete managed body and
proving managed re-entry.

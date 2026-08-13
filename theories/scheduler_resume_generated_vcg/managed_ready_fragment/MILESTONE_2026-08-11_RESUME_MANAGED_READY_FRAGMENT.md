# Resume managed source-faithful ready fragment — 2026-08-11

Baseline: `de50b7b64e1cfbce983e1b7fbe3596097b452369` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child executes the exact generated fragment after both
pending-head removals:

1. the conditional top-ready-priority raise;
2. the generated priority guard, ready-array guard, and destination read; and
3. the generated `vListInsertEnd'` into that selected ready queue.

It starts at
`scheduler_mem_state (resume_pending_generic_remove_heap D t c) c` and ends
with `Result ()` in
`resume_pending_ready_inserted_state D C t generic_raw c`.  The selected
destination and inserted item are linked by the explicit ABI equalities
`rpc_ready_root C q = abi_list_ptr (sr_ready generated_scheduler_roots q)` and
`abi_item_ptr item = resume_pending_generic_raw_ptr D t`.

Freshness is reconstructed from the managed post-remove Generic coverage,
managed task observation, insert geometry, and the checker-green global
unlinkedness fact.  The child does not use the legacy Resume gate, a global
owner equation, managed/live collapse, a roots premise, or a transient full
scheduler snapshot.  It deliberately exports only the concrete source result;
post-insert relational preservation is the next rung.

## Theorem-object audit

`CursorGeneralStrongResumePendingManagedPhaseRel_generated_ready_fragment_exact`
has exactly two premises—the managed phase and
`rpc_tasks C = t # rest`—and zero hidden hypotheses.  Its embedded ML audit
checks the exact `2/0` ledger.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Fragment` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Two_Unlinks`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-ready-fragment-01-source-faithful` | 1 | 172.334 s | first error only: final bind used generated array-index form while local insert fact used the named ready root |
| `20260811Tresume-managed-ready-fragment-02-array-form-bridge` | 0 | 161.207 s | green; leaf 3 s |

The bounded repair added only the named array-form corollary of the already
proved exact insert theorem, matching the generated `gets` result.  No theorem
statement or premise changed.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `DC484FC204CB3AB50A8C2FE38B6EA194378F43D8A097106C0F4A1657576B2666` |
| run 01 `command.txt` | `3EAD0C57A2B690E6E76C56A54DCC6FB9F8CF4715C9F14708B1E0AA779B40F745` |
| run 01 `status.txt` | `1AEBF7B310E3A32764C69CFF80AEB846E19C6F27903FD7FE1AB3CBF8D8CBC896` |
| run 01 `stdout.log` | `C74733529C07EBC0267609FFA524A3385A6D2544238A50AE16E0F49FE4119112` |
| run 01 `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |
| run 02 `command.txt` | `3EAD0C57A2B690E6E76C56A54DCC6FB9F8CF4715C9F14708B1E0AA779B40F745` |
| run 02 `status.txt` | `20F4BFD565F0DAC4382C097D282393D4BDE92F7180DD775D8104AF3647840090` |
| run 02 `stdout.log` | `5A15155068F820CEBCDD291B4AB856E148683CE4F334C0D513190469B07EB372` |
| run 02 `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The generated ready fragment is now concrete-source exact.  The next child may
preserve the managed Generic/Event coverages and observation across insertion,
rebuild post cross-storage, advance to `RP_ReadyInserted`, and relate the
concrete raised top to the drained snapshot.  It must not claim a full managed
scalar relation at this transient state or equate abstract local yield with
the concrete missed-yield global.

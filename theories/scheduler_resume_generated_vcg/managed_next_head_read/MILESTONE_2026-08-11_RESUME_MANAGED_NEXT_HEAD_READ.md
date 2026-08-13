# Resume managed next-head read — 2026-08-11

Baseline: `b0d4d1921394b6fdcd7d8e5b1324fa68925cc51f` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child executes `resume_pending_generated_head_read` at the
managed ready-inserted concrete state after consuming head task `t`.  From the
managed phase and `rpc_tasks C = t # rest`, it returns exactly

`PTR_COERCE (resume_pending_next_head_tcb D rest)`

and leaves the state unchanged.

The proof derives the drained pending ring from the checker-green
`RP_YieldChecked` invariant.  The empty branch uses the post-ready Event count
and ABI count bridge.  The nonempty branch uses post-ready Generic/Event
coverage, the managed-view decoder and observation, and the represented Event
head to recover the next TCB owner.  It does not reuse the entry-state managed
head-read theorem, the legacy Resume gate, or a roots premise.

## Theorem-object audit

`CursorGeneralStrongResumePendingManagedPhaseRel_generated_next_head_read_exact`
has exactly two premises and zero hidden hypotheses.  The embedded ML ledger is
`2/0`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Next_Head_Read` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Relational`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-next-head-read-01-post-ready-uniform` | 0 | 180.795 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `23E67328D7759AC4E2CE238BBD06A7A656487833410AEA1DE2C5F8E51CCE8B78` |
| `command.txt` | `DF7D5CA2209F0BE63DE25A3C0A466800D2463E686D4614AD60E1640467C3844A` |
| `status.txt` | `4A45D09C4C8B87C183A49D590FF0A12F62CA0F32A5F7F000A21D961E9B99A7B3` |
| `stdout.log` | `FE8EAFF0EE9E7F717356902B187C30457C77ED651B8DB7737C09AFF2FC34853C` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

All source factors of one managed pending-body iteration are now individually
checker-green.  The next relational rung should commit the `RP_YieldChecked`
cut to `RP_LoopHead` with processed prefix `[t]` and tail `rest`; only after
that should the complete source body be composed and managed re-entry proved.

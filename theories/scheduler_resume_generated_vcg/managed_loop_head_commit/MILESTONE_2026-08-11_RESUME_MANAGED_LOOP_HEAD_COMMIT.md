# Resume managed loop-head commit — 2026-08-11

Baseline: `a19eabb7a282e70ff294b37b6552f423990f42c6` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child commits one fully classified pending task from
`RP_YieldChecked` to the next `RP_LoopHead`.  From the managed phase and
`rpc_tasks C = t # rest`, the resulting invariant has processed prefix `[t]`,
todo list `rest`, and the exact current snapshot

`resume_pending_yield_check_state C t (resume_pending_drained_snapshot C t P)`.

The generated next-head read is state preserving, so no concrete result,
coverage, gate, or additional premise is required for this abstract commit.

## Theorem-object audit

`CursorGeneralStrongResumePendingManagedPhaseRel_loop_head_after_oneD` has
exactly two premises and zero hidden hypotheses.  The embedded ML ledger is
`2/0`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Head_Commit` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Next_Head_Read`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-loop-head-commit-01-one-rule` | 0 | 185.778 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `4CCF73808CB298F179FD3486D806B8B98E754A1E332F87C0E6BCF81DB2EB78A5` |
| `command.txt` | `A9392E0E861D265D04CCB570F4BF68BDF968068AE9A181863C6D5C572BF8D53A` |
| `status.txt` | `2A7138DC5605B1247B4F93519B4BDCD263E6A821DD9C5956889AE07BE7C8694D` |
| `stdout.log` | `7D0FD0E7F7D3CDAB103971FE5C1DD0621EDF592A7182D14088B1C5352E98E930` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The full one-iteration source and phase ladder is now green through the next
loop head.  The next child should compose the exact generated body result and
the already-proved managed relational postconditions.  Managed re-entry for
`resume_one_pending_abs t a` remains a separate subsequent rung.

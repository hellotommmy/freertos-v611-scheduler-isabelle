# Resume managed head-TCB guard — 2026-08-11

Baseline: `c9ee9eef1a083c101b12e94e7a8d87a193c4884b` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child supplies the source body’s missing first factor.  From
the managed phase and `rpc_tasks C = t # rest`, the entry shadow’s managed task
observation proves `c_guard (sd_tcb_ptr D t)`, and the exact generated guard
returns `Result ()` without changing the state.

The proof uses the managed gate only to recover its protected public shadow and
strong scheduler snapshot.  It does not use the legacy Resume gate or add a
pointer premise.

## Theorem-object audit

Both exported theorem objects have exactly two premises and zero hidden
hypotheses:

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_head_tcb_guardD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_tcb_guard` | 2 |

The embedded ML ledger is `2/2`, with `0` hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_TCB_Guard` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Head_Commit`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-head-tcb-guard-01-entry-shadow` | 0 | 185.681 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `8E48DCD55E76F8CF20F53FA88B9B0BF0B986AEA5D3A9D414438B31589BCE7DAB` |
| `command.txt` | `F9F044C1548EC02EE42FBA399921A7B74D0498CB045CA345417C36D388E6F5E2` |
| `status.txt` | `9E7AEF1E788A7702C02895EFFACD3224AFC76449D5DE57D51E2C5BEE1493799D` |
| `stdout.log` | `D65FABA3AFB2FA4A02636C83A0AE0EA1B7236DD5FAABE893471839A086037A69` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

Every source factor needed by one managed pending-body iteration is now
checker-green, including the entry guard.  The next child may group the literal
body by a zero-premise factorization equality and compose the five checked
source programs into the exact managed body result.

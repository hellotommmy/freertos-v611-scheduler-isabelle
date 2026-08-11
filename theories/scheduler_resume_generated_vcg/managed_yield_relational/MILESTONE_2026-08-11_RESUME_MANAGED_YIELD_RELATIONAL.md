# Resume managed yield relational cutpoint — 2026-08-11

Baseline: `5964cd96b22d178a710b66ac5190a854734f3a89` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child advances the managed loop-phase invariant from
`RP_ReadyInserted` to `RP_YieldChecked` at
`resume_pending_yield_check_state C t (resume_pending_drained_snapshot C t P)`.
It also proves that the new abstract local-yield flag is exactly the current
priority comparison.

For an arbitrary incoming `y :: int`, the checked result law is deliberately
accumulative:

`result != 0` iff `y != 0` or the new local-yield flag.

The stronger direct equivalence between result nonzeroness and the new flag is
false when the comparison is false and `y` is already nonzero.  The source
fragment remains responsible for the exact returned value and unchanged
concrete state; this relational child introduces no concrete yield global,
legacy Resume gate, or transient full scheduler snapshot.

## Theorem-object audit

The capstone and all three projections have exactly two premises and zero
hidden hypotheses:

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_yield_checkedD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_yield_localD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_yield_word_encodingD` | 2 |

The embedded ML ledger is `2/2/2/2`, with `0` hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Relational` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Fragment`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper was bounded at 300 seconds and invoked
Isabelle with `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-yield-relational-01-accumulated-word` | 0 | 178.7 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `DC8E66F17AECDC89E9D32F4A764C85F4A5DDF8DCD2884509A3B7A9AF4E57C466` |
| `command.txt` | `B62E959A9EC619FA2B53C3A73664703EAB33CDFAB62A4ED65F6C8228AAE423DF` |
| `status.txt` | `F01D96F45A87A0D6B93329CAF206A1B6B38FA11F416CFCC692A886B4A964368D` |
| `stdout.log` | `B1CCA51854877783E363E0F84B4CC20A6E0E0582640256CB24DA06D89EBAFE1F` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The source yield assignment and its abstract classification are now separately
checker-green.  The next source rung should read the drained pending-list head
from the same ready-inserted concrete state, returning the decoded tail head or
NULL without mutation.  The later commit-to-loop-head step must occur only
after that read.

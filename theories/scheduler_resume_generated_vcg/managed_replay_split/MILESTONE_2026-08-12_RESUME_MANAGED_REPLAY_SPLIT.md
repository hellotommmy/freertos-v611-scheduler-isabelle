# Resume managed missed-replay split — 2026-08-12

Baseline: `f33d73e` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child connects an empty managed resume phase to the checked
protected missed-tick replay horizon.  It exports two exact three-premise
theorems:

- when the complete arithmetic horizon is safe, the generated missed-tick
  loop returns `Result ()`, remains at a protected `1/1` tick entry with a
  quiet poststate and safe residual horizon, reaches exactly
  `replay_missed_abs (sa_missed_ticks a) a`, and drains the missed debt to
  zero; and
- when that horizon is unsafe, the generated missed-tick loop has no normal
  successful outcome.

The empty task-list premise is load-bearing because it establishes the
tick-entry pending boundary.  Initial quietness is obtained from the managed
gate, not assumed separately.  The safe theorem only rewrites the checked
source-step endpoint with the zero-premise
`resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs` bridge.

The unsafe conclusion is deliberately only `not succeeds`.  It does not claim
that no operational step occurs, that an exception is inevitable, that the
loop diverges, or that any concrete write is rolled back.  No theorem uses the
legacy gate relation, a managed/live equality, a cursor/no-wrap premise, or a
proof bypass.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_safe` | 3 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_unsafe_no_run` | 3 | 0 |

The embedded ML ledger checks exactly `3/3`, with zero hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Replay_Split` has sole heap parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Capstone`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  It declares the checked
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe`
session as a side import; that side closure also supplies the safe-loop theorem.
The repository wrapper used a 600-second lifecycle budget and Isabelle options
`-o quick_and_dirty=false -j 1`.

| run | exit | elapsed | result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-replay-split-01-safe-unsafe` | 0 | 265.157 s | green on first run; parent 10 s, leaf 9 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `E4D41A81174BD88E14C5ED2B7A2804A563CBE5DE9FFDE5611B68B9F07F36FA43` |
| `command.txt` | `A86CFB4971B3FD6EF2F060DF9227A0970A626E71DCF56DEDA14BAD24EFADAB41` |
| `status.txt` | `469B9BC43DADC6AFA613E04D3FE9AD53F9036616488B732B09D0F449542A09D6` |
| `stdout.log` | `AC68E4AB44A7FF5AA6AD4C0EF9DDD0B2B13638F1D6FB5B1CBF820260F5553B7B` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Frozen-layout evidence recorded by the final status:

- ELF: `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- ledger: `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The next staircase replaces the old exact abstract yield-count snapshot with a
modular endpoint relation.  This is necessary at 32-bit wraparound: a concrete
word can advance from all ones to zero while the unbounded abstract count
advances from `2^32 - 1` to `2^32`.  The yield rung must rebuild the normalized
post snapshot directly; normalization does not commute with abstract yield
request at the wrap boundary.

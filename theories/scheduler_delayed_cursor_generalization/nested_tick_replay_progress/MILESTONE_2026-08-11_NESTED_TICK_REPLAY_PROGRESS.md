# Nested tick replay progress — 2026-08-11

Baseline: `b7f47b3c0aed89ef96ad9076762a0670dab751d0` on
`agent/universal-scheduler-refinement`.

## Checked scope

The exclusive child proves unconditional Spec-monad progress for the exact
generated source staircase used by missed-tick replay:

1. generated `vListRemove'` and `vListInsertEnd'`;
2. Event dispatch, delayed-head remainder, and top-ready tail;
3. after-Generic and the exception-aware due-loop body;
4. the generated due `whileLoop` and its named `finally` wrapper;
5. unlocked role source, prefix source, and complete unlocked source;
6. the whole generated `vTaskIncrementTick'`;
7. the exact replay body `resume_missed_generated_body ()`, whose source order
   is the whole tick followed by the concrete missed-debt decrement.

Here `always_progress f` means that `run f s` is never bottom for any state
`s`.  It does not assert successful execution or termination.  Generated
guard failure is progress, and the `whileLoop` top/divergence case is also
progress.  Consequently every theorem above has no scheduler-relation,
pointer-validity, arithmetic-definedness, success, termination, or desired
outcome premise.

This rung deliberately proves no reachability result at a particular state.
It supplies the global support needed to turn a checked `runs_to` theorem into
an explicit reachable outcome through `Ex_reaches`.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `vTaskIncrementTick_always_progress` | 0 | 0 |
| `resume_missed_generated_body_always_progress` | 0 | 0 |

The ML audit is part of the checked theory and fails the session if either
count changes.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress`
has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop`,
no side session, and its own one-theory directory.  It sets `document=false`,
`quick_and_dirty=false`, `parallel_proofs=0`, and session `timeout=60`.  The
repository wrapper bound was 300 seconds and the checker command used
`-o quick_and_dirty=false -j 1`.

The first cold checker was green; no proof repair or premise change was
needed:

| run | exit | timed out | wrapper | parent | leaf |
| --- | ---: | --- | ---: | ---: | ---: |
| `20260811Tnested-tick-replay-progress-01-cold` | 0 | false | 158.343 s | 9 s | 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `4B3DCF1ADC743B27B50DD0677D1C4B9A65D488CB41F0B35A9AA3DF6A46D58992` |
| `command.txt` | `6000F87387464DD4D1912E98ABF74B7B0D6B56CAEC45AE5554169EAE72249E49` |
| `status.txt` | `4109FEF60E037C6104F0936987C9D873D9D951E9B51DFEE3123FE4AEDA666E6E` |
| `stdout.log` | `82A1FB333F7F7715B6B7D62AE70AC30EC9AEE00A1603DC9AEB9BFEB3B3FCBD90` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child is replay body outcomes.  It must establish
`succeeds` invariance under the proof-port overlay, immediate no-success for
an arithmetic-undefined protected quiet state, truth of the generated loop
condition from protected entry plus positive debt, and an explicit reachable
`Result ()` successor for every arithmetic-defined body execution.  The last
fact must combine the existing body `runs_to` theorem with this rung's
`always_progress` theorem via `Ex_reaches` and project the reachable result
with `runs_toD2`.

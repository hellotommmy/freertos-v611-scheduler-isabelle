# Nested tick horizon-safe replay loop — 2026-08-11

Baseline: `7f8eef0622e5a092ba11ceb64bd7ddafce858d66` on
`agent/universal-scheduler-refinement`.

## Checked scope

The exclusive child closes only the generated missed-tick `whileLoop` when
the complete initial missed-debt horizon is arithmetic-safe.  The public
theorem is
`resume_missed_generated_loop_protected_horizon_safe_1_1`.  Its three and
only three premises are:

1. the cursor-general protected entry relation at proof-port depth/mask 1/1;
2. `sa_suspend_depth a = 0`;
3. `resume_missed_replay_horizon_safe (sa_missed_ticks a) a`.

Positivity is only the existing local step premise supplied by the generic
loop rule.  The current concrete arithmetic-defined guard is derived inside
that step from the positive horizon head and the already-checked protected
arithmetic equivalence.  The concrete missed count is likewise projected
inside the proof from the protected relation.  No positivity,
current-defined, no-wrap, count, body-success, or desired-post premise is
exported.

The loop relation preserves the original `D`, `managed`, `termination`,
`external`, cursor/family witnesses, and protected 1/1 overlay.  Managed and
live domains remain distinct.  On successful exit it retains quietness and
the exact remaining horizon, identifies the abstract state with
`resume_missed_source_steps_abs (sa_missed_ticks a) a`, and proves zero
abstract missed debt.

This cutpoint already assumes the existing protected entry relation; together
with quietness, that relation is after the pending-drain boundary.  This child
does not prove pending drain or arbitrary Resume entry.

## Exact abstract naming bridge

The general bridge

```isabelle
resume_missed_source_steps_abs n a = replay_missed_abs n a
```

has exactly the necessary premise `sa_missed_ticks a = n`.  In the `Suc n`
induction step, that premise makes the source decrement write debt `n`,
exactly matching the first `replay_missed_abs` state, and gives debt `n` for
the induction hypothesis on the successor.  Without this premise the two
iterators are not equal in general: the source iterator decrements the
current debt, while `replay_missed_abs` writes its recursion index.

Instantiating `n` with the initial debt yields the premise-free naming bridge
`resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs`.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `resume_missed_source_steps_abs_eq_replay_missed_abs` | 0 | 1 |
| `resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs` | 0 | 0 |
| `resume_missed_generated_loop_protected_horizon_safe_1_1` | 0 | 3 |

The ML audit is part of the checked theory and fails the session if any count
changes.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop`
has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge`,
no side session, and its own one-theory directory.  It sets
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and session
`timeout=60`.  The wrapper bound is 300 seconds and the checker command uses
`-o quick_and_dirty=false -j 1`.

The first cold checker was green; no proof repair or premise change was
needed:

| run | exit | timed out | elapsed | parent | leaf |
| --- | ---: | --- | ---: | ---: | ---: |
| `20260811Tnested-tick-replay-safe-loop-01-cold` | 0 | false | 147.663 s | 9 s | 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `9EB3AABF1BBD89D49380D1C8A00071B11856041B035EFA1E5F31B6709258BB69` |
| `command.txt` | `A9187505328D6362C3841AE00720E81385BFCC945CE46C5FC7A6E89C08257749` |
| `status.txt` | `8542BB5DF9B720F86DA4778FBED6473EEA3D9BD4FA737E59848D05FCC7E1F8C3` |
| `stdout.log` | `B21A54770BB62776BD850B0CE3FCEC027F2AC947618396C352BDADF479C037B3` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

This child proves only the fully safe horizon.  The first remaining semantic
rule is the first-unsafe boundary: after a safe replay prefix with positive
debt, an abstract arithmetic guard failure at the next replay state must be
connected to the generated body's corresponding non-success behaviour.
Pending drain and the enclosing `xTaskResumeAll` composition remain separate
later rungs and are not proved here.

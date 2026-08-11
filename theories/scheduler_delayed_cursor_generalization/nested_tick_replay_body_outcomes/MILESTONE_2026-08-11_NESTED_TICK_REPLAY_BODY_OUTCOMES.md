# Nested tick replay body outcomes — 2026-08-11

Baseline: `d98c1daaf5e12e112b08a7b5c16009ed5bd99f06` on
`agent/universal-scheduler-refinement`.

## Checked scope

The exclusive child closes the generated missed-replay body's success and
reachability split for arbitrary proof-port depth and interrupt mask:

1. whole generated tick success is invariant under `scheduler_port_overlay`;
2. protected entry, quiet suspension depth, and abstract arithmetic
   undefinedness imply that the replay body has no successful run;
3. protected entry plus positive abstract missed debt make the exact generated
   missed-loop condition true;
4. adding quietness and abstract arithmetic undefinedness therefore makes the
   complete generated while loop immediately non-successful; and
5. protected entry, quietness, positive debt, and abstract arithmetic
   definedness yield an explicit reachable `Result ()` body successor carrying
   the protected relation at `resume_missed_source_step_abs a`.

The no-run body theorem deliberately has no positive-debt premise.  The
positive premise belongs to the loop-entry theorem: at zero concrete debt the
condition is false and the while loop returns successfully without executing
the unsafe body.

The explicit successor is not inferred from `runs_to` alone.  The checked body
`runs_to` theorem is combined with the unconditional progress theorem through
`Ex_reaches`; `runs_toD2` then fixes the reachable result to `Result ()` and
recovers the protected successor relation.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `vTaskIncrementTick_scheduler_port_overlay_succeeds_iff` | 0 | 0 |
| `resume_missed_generated_body_protected_abstract_undefined_no_run` | 0 | 3 |
| `resume_missed_generated_cond_protected_positive` | 0 | 2 |
| `resume_missed_generated_loop_protected_immediate_abstract_undefined_no_run` | 0 | 4 |
| `resume_missed_generated_body_protected_abstract_defined_reaches` | 0 | 4 |

The embedded ML audit fails the session unless the exact premise ledger remains
`0/3/2/4/4` and every exported theorem remains free of hidden hypotheses.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes`
has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress`,
no side session, and its own one-theory directory.  It sets `document=false`,
`quick_and_dirty=false`, `parallel_proofs=0`, and session `timeout=60`.  The
repository wrapper bound was 300 seconds and the checker command used
`-o quick_and_dirty=false -j 1`.

The first cold checker was green; no proof repair or premise change was
needed:

| run | exit | timed out | wrapper | parent | leaf |
| --- | ---: | --- | ---: | ---: | ---: |
| `20260811Tnested-tick-replay-body-outcomes-01-cold` | 0 | false | 154.135 s | 9 s | 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `A09C152349D6A8A9DE10FA5EB5F90BE864C3709202519028A214FE93A1903CFB` |
| `command.txt` | `D897D9BA8FC54F024ED8166D86AB505979DCC926452AEA69685EEF9287EF703B` |
| `status.txt` | `EA365713F198E47A8D39113F154687EE79F928B80A798C7FC26629D07F9DA244` |
| `stdout.log` | `77A411514AF7A206996F09DEFB04C986C9284A3438D9928884E51E650457062D` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child is first-unsafe replay classification.  It must use
the explicit defined-body successor to advance every index before the first
bad arithmetic point, then use the immediate-unsafe while theorem at that
point to prove that the original whole generated while loop has no successful
run.  It must not assume a safe horizon, redo the safe-loop proof, or infer a
reachable successor from partial correctness alone.

# Resume pending control frame — 2026-08-11

Baseline: `74d3d10e07fef71ecdb8f87521eb3f67d7c146e7` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child adds the small, domain-free concrete frame required at
the pending-drain cutpoint:

`resume_pending_control_frame before after` says only that the proof-port
critical depth, proof-port interrupts-disabled word, and
`xSchedulerRunning` are unchanged.

The checked ladder then proves:

1. the exact ready-inserted state satisfies that frame with no premise;
2. one exact generated pending body preserves the frame;
3. a list induction preserves it through the complete generated pending loop;
4. `runs_to_conj` combines the frame with the existing abstract drain theorem;
5. concrete entry values depth 1, interrupts-disabled 1, and scheduler-running
   1 are therefore present at the drained loop exit.

The body/loop/drain results consume the legacy `resume_pending_gate_entry_rel`
only as the already-checked execution certificate required by
`resume_pending_generated_body_exact`, loop re-entry, and the existing drain
summary.  The new frame predicate itself is independent of that gate.  These
theorems do not derive a managed gate, do not identify `managed` with
`sa_live`, and must not be used to erase legal termination tasks.  The future
cursor-general managed gate remains a parallel relation and requires its own
representation bridge.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `resume_pending_ready_inserted_control_frame` | 0 | 0 |
| `resume_pending_generated_body_control_frame` | 0 | 3 |
| `resume_pending_generated_loop_control_frame` | 0 | 2 |
| `resume_pending_generated_loop_drain_pending_abs_control_frame` | 0 | 2 |
| `resume_pending_generated_loop_drain_pending_abs_protected_1_1_running_1` | 0 | 5 |

The embedded ML audit fails the session if any hidden hypothesis appears or
if the exact `0/3/2/2/5` premise ledger changes.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Control_Frame` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drain_Abs_Fold`, the smallest
semantic parent containing both the exact pending body/re-entry staircase and
the abstract drain summary.  It has its own one-theory directory and sets
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and session
`timeout=60`.  The repository wrapper bound was 300 seconds and the checker
command used `-o quick_and_dirty=false -j 1`.

The first cold run stopped at the first proof error: a `clarify` method could
not discard irrelevant exact-body postcondition conjuncts after applying the
induction hypothesis.  Removing that method let the three framed equalities
simplify directly; no statement or premise changed.  The second run was green:

| run | exit | timed out | wrapper | leaf |
| --- | ---: | --- | ---: | ---: |
| `20260811Tresume-pending-control-frame-01-cold` | 1 | false | 46.800 s | first error |
| `20260811Tresume-pending-control-frame-02-first-error-repair` | 0 | false | 45.509 s | 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `0BE3201D8B15E1C3FEB29FD8F4CAEBABEC77E92D336189100288965775986DA4` |
| `command.txt` | `FEBAD0BE8906F92842DDDB06988D9E7482C5A9466A8B0B90533EE198F84DE60B` |
| `status.txt` | `A40EC18B581276B8609796FA766BD8F40ED56717561CE4F32FCE85847A1E8509` |
| `stdout.log` | `7E05CE1AE762FCD2DF6D716A1A28E07457B45F1FCFAB84315589879CBC099FD7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next rung must build the parallel cursor-general managed Resume gate before
any outer composition.  The existing generated outer theorem consumes the
legacy gate on both sides and therefore cannot represent a state with retired
tasks.  The managed gate must quantify representation/count over `managed`,
retain termination and protected external Event roots, and prove pending tasks
are in `sa_live` separately.  After its own body/drain and empty-exit proofs are
green, a new managed outer composition can join the control frame and the
completed safe/unsafe replay classification.

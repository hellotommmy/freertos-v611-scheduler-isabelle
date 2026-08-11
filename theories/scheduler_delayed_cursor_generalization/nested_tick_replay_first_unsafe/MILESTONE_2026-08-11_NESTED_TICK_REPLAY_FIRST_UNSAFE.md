# Nested tick replay first unsafe — 2026-08-11

Baseline: `d3e4a62b2326465b2f22b5489cc5dc51156f38c5` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child completes the unsafe half of generated missed-tick replay
classification:

1. negating `resume_missed_replay_horizon_safe n a` produces an index `i<n`
   whose prefix horizon is safe and whose `i`th abstract tick arithmetic is
   undefined;
2. a generic depth/interrupt-mask induction advances each safe-prefix body only
   through an explicit reachable `Result ()` successor;
3. at the first bad state, the generated loop condition is true because the
   index remains below the missed debt, and the immediate-unsafe body outcome
   makes that loop non-successful;
4. the full-horizon theorem is exported for arbitrary proof-port depth and
   interrupt mask, with a direct protected 1/1 corollary for the Resume gate.

The operational induction needs no determinism assumption.  If the original
while loop succeeded, one true-condition unroll and `succeeds_bind` would force
the continuation to succeed for every reachable normal body successor.  The
explicit successor supplied by the body-outcomes rung instead reaches a tail
loop classified non-successful by the induction hypothesis, giving the
contradiction.

The negated full horizon also excludes zero debt automatically because the
zero-length horizon is true.  The classification therefore covers the
adversarial debt-two trace whose first tick is defined and whose second tick
fails the signed-overflow guard before the debt decrement.

Together with the previously checked protected 1/1 horizon-safe `runs_to`
theorem, this closes the requested safe/unsafe replay split.  It does not claim
a poststate for the unsafe run.

## Theorem-object audit

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `resume_missed_replay_horizon_unsafe_first` | 0 | 1 |
| `resume_missed_generated_loop_protected_first_unsafe_index_no_run` | 0 | 5 |
| `resume_missed_generated_loop_protected_horizon_unsafe_no_run` | 0 | 3 |
| `resume_missed_generated_loop_protected_horizon_unsafe_no_run_1_1` | 0 | 3 |

The embedded ML audit fails the session if any hidden hypothesis appears or
if the exact `1/5/3/3` premise ledger changes.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe`
has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes`,
no side session, and its own one-theory directory.  It sets `document=false`,
`quick_and_dirty=false`, `parallel_proofs=0`, and session `timeout=60`.  Each
repository wrapper bound was 300 seconds and each checker command used
`-o quick_and_dirty=false -j 1`.

The initial generic induction and fixed 1/1 conclusion were green.  A
read-only scope audit then observed that the same conclusion could be exported
for arbitrary proof-port values at no proof cost; the strengthened generic
theorem and retained 1/1 corollary were rechecked green:

| run | exit | timed out | wrapper | parent | leaf |
| --- | ---: | --- | ---: | ---: | ---: |
| `20260811Tnested-tick-replay-first-unsafe-01-cold` | 0 | false | 153.635 s | 9 s | 3 s |
| `20260811Tnested-tick-replay-first-unsafe-02-generic-final` | 0 | false | 145.075 s | cached | 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `BA40CA88B36002AE472CC9DF7DE4C8B9727F21CDA9B9CCFCE6F0988A4BDA34F4` |
| `command.txt` | `59484FB65BF8BDCDB5B5FBF29FEAFA00F79C1EE24418D9878BF6D0E5E5FBE17E` |
| `status.txt` | `6C341ADAB2E5FEA89A8A15F68A66C550B1F1E2F3EE07BAB8643602CE779046F5` |
| `stdout.log` | `BA27C1F8675670A35A8F60E9888FEE47063458534DC1CF0E24204CF66BC238E7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

Safe/unsafe replay classification is complete.  The next permitted rung is the
small pending-drain control frame: equate the concrete proof-port critical
depth, interrupt mask, and scheduler-running word, preserve that frame through
the generated pending loop, and export the actual protected 1/1/running-1
continuation.  Only after that frame is checked should the parallel
cursor-general managed Resume gate be built.

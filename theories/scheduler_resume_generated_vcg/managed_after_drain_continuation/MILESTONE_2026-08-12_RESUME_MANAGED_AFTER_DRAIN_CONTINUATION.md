# Resume managed after-drain continuation — 2026-08-12

Baseline: `3b7c1f8` on `agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child factors and checks the stable continuation that follows
the managed pending-task drain.  Its source-faithful replay choice is

`condition (\<lambda>s. 0 < uxMissedTicks_' s) (missed replay loop; return 1) (return y)`.

The zero-premise factor theorem identifies the generated
`resume_after_drain_continuation y` exactly with that choice bound to the
already checked, branch-complete `resume_managed_yield_branch`.

The child exports five managed-only boundaries:

- under the managed phase, an empty pending-task list, and a safe missed-tick
  replay horizon, the replay choice returns exactly
  `if 0 < sa_missed_ticks a then 1 else y` and reaches modular protected
  tick entry at `replay_missed_abs (sa_missed_ticks a) a`;
- the safe bare continuation returns exactly `1` iff the checked replayed
  state requests the literal generated yield branch, otherwise `0`, and
  exports the corresponding `YieldAbs` plus modular protected entry;
- the safe with-exit continuation preserves that exact result and `YieldAbs`
  while one checked critical exit reaches the public modular endpoint;
- an unsafe replay horizon implies only that the bare continuation has no
  successful result; and
- the same no-success fact propagates through the with-exit wrapper.

The named pure quantities are deliberately ordered as follows:

- `replayed = replay_missed_abs (sa_missed_ticks a) a`;
- `local_y = (if 0 < sa_missed_ticks a then 1 else y)`;
- `requested = resume_managed_yield_requested local_y replayed`;
- `caller = resume_managed_yield_caller_abs local_y replayed`; and
- `final_a = resume_managed_yield_final_abs local_y replayed`.

This retains arbitrary input `y`: when the missed debt is zero, `y = 2`
remains `2` at the replay-choice boundary and is not normalized to `1`.
The subsequent yield branch still uses its literal equality guard, never a
nonzero test.  For positive debt the local word is exactly `1`.  Yield
selection is evaluated over the replayed state, not the entry state, and the
runtime result is determined by `requested`, not by the raw local word.

The unsafe theorems claim only `\<not> succeeds`; they do not claim an error,
rollback, divergence, or absence of operational steps.  No no-wrap premise,
legacy gate relation, managed/live equality, cursor premise,
termination-empty premise, or old `xTaskResumeAll_drain_composed` route is
used.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_after_drain_continuation_factor` | 0 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_replay_choice_horizon_safe` | 3 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_bare_continuation` | 3 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_continuation_with_exit` | 3 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_bare_continuation_horizon_unsafe_no_run` | 3 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_continuation_with_exit_horizon_unsafe_no_run` | 3 | 0 |

The embedded ML ledger checks exactly one `0/0` theorem object followed by
five `3/0` theorem objects.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_After_Drain_Continuation` has
sole heap parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Exit`,
one theory, `document=false`, `quick_and_dirty=false`,
`parallel_proofs=0`, and `timeout=120`.  It declares
`EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Outer_Compose` only as a side
session/import for the generated `resume_after_drain_continuation_def` used by
the exact factor theorem.  No theorem from the legacy outer proof route is
consumed.

The repository wrapper used a 600-second lifecycle budget, both repository
ROOT discovery directories, `-o quick_and_dirty=false`, and `-j 1`.

The bounded first-error chronology was:

| run | exit | elapsed | first result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-after-drain-continuation-01-stable-compose` | 1 | 277.241 s | concrete/abstract missed-count guard equality was not yet normalized |
| `20260812Tresume-managed-after-drain-continuation-02-guard-count-calc` | 1 | 262.096 s | `word_gt_0` had been used as a rule rather than a rewrite |
| `20260812Tresume-managed-after-drain-continuation-03-word-positive-simp` | 1 | 262.737 s | the exact `unat` zero bridge was still missing |
| `20260812Tresume-managed-after-drain-continuation-04-unat-zero-bridge` | 1 | 269.447 s | the true branch had already closed before a trailing proof command |
| `20260812Tresume-managed-after-drain-continuation-05-true-branch-close` | 1 | 273.078 s | the local branch goal still retained the outer `let` context |
| `20260812Tresume-managed-after-drain-continuation-06-branch-let-unfold` | 1 | 332.782 s | true-branch post normalization stopped at the condition boundary |
| `20260812Tresume-managed-after-drain-continuation-07-true-choice-exact` | 1 | 262.750 s | true-branch exact fact and target were in different proof modes |
| `20260812Tresume-managed-after-drain-continuation-08-local-y-rewrite` | 1 | 260.534 s | the local-word rewrite closed before the following refinement |
| `20260812Tresume-managed-after-drain-continuation-09-true-branch-rule` | 1 | 260.561 s | a terminal command followed an already closed branch goal |
| `20260812Tresume-managed-after-drain-continuation-10-true-post-normalize` | 1 | 266.259 s | the exact true post was reached but the next tactic saw no goal |
| `20260812Tresume-managed-after-drain-continuation-11-true-post-weaken` | 1 | 256.845 s | weakening closed the goal before a trailing simplification |
| `20260812Tresume-managed-after-drain-continuation-12-true-branch-terminal-simp` | 1 | 258.248 s | terminal normalization left the exact RunsTo fact to be applied |
| `20260812Tresume-managed-after-drain-continuation-13-true-branch-final` | 1 | 258.601 s | sequential true-branch commands again crossed a closed-goal boundary |
| `20260812Tresume-managed-after-drain-continuation-14-true-branch-done` | 1 | 259.378 s | manual weakening left the identity implication `P \<Longrightarrow> P` |
| `20260812Tresume-managed-after-drain-continuation-15-true-post-tautology` | 1 | 260.426 s | the tautological post was not discharged in the same refinement |
| `20260812Tresume-managed-after-drain-continuation-16-meta-post-assumption` | 1 | 261.018 s | proof-state sequencing still crossed the branch closure |
| `20260812Tresume-managed-after-drain-continuation-17-true-branch-closed` | 1 | 264.559 s | a command was invoked after the local true goal had closed |
| `20260812Tresume-managed-after-drain-continuation-18-close-local-show` | 1 | 264.068 s | the local structured `show` remained in the wrong mode |
| `20260812Tresume-managed-after-drain-continuation-19-true-terminal-method` | 1 | 262.526 s | terminal true-branch normalization and fact use were still split |
| `20260812Tresume-managed-after-drain-continuation-20-true-fact-match` | 1 | 260.866 s | the fact match closed before a following terminal command |
| `20260812Tresume-managed-after-drain-continuation-21-true-branch-simpa` | 1 | 258.864 s | an `unfolding` modifier discharged the goal before `by` |
| `20260812Tresume-managed-after-drain-continuation-22-atomic-true-simp` | 1 | 257.548 s | atomic simp still refined the outer branch rather than a local target |
| `20260812Tresume-managed-after-drain-continuation-23-true-two-method-proof` | 1 | 258.061 s | the two-method true proof left an unstable goal boundary |
| `20260812Tresume-managed-after-drain-continuation-24-true-post-clarsimp` | 1 | 259.986 s | broad true-post simplification did not isolate the outer `let` goal |
| `20260812Tresume-managed-after-drain-continuation-25-local-target` | 1 | 261.468 s | the true branch passed; the zero-debt false branch exposed two VCG obligations |
| `20260812Tresume-managed-after-drain-continuation-26-zero-debt-frames` | 1 | 261.898 s | explicit zero facts did not consume the VCG meta-premises |
| `20260812Tresume-managed-after-drain-continuation-27-zero-vcg-branches` | 1 | 263.229 s | `False` simplification did not introduce the branch meta-premise |
| `20260812Tresume-managed-after-drain-continuation-28-zero-equality-vcg` | 1 | 259.118 s | zero equality still did not consume the branch meta-premise |
| `20260812Tresume-managed-after-drain-continuation-29-zero-meta-contradiction` | 1 | 259.750 s | the three exact false-branch VCG subgoals were exposed |
| `20260812Tresume-managed-after-drain-continuation-30-explicit-zero-subgoals` | 1 | 260.948 s | replay choice passed; bare bind simplification split the exact conditional post |
| `20260812Tresume-managed-after-drain-continuation-31-preserve-if-bind` | 1 | 264.244 s | bare continuation passed; with-exit bind needed the same conditional preservation |
| `20260812Tresume-managed-after-drain-continuation-32-preserve-exit-if` | 0 | 264.227 s | green; leaf reported 5 s |

All 32 runs were outer non-timeout runs with `quick_and_dirty=false`; Runs
01–31 exited at their first proof error, and Run 32 is the promoted final
evidence.  Repairs were limited to guard arithmetic, explicit VCG subgoal
handling, and deterministic RunsTo proof-state plumbing.  The exported source
factor and five theorem statements retained their final premise ledgers.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `EC435451F2AF8BB9E5D4363E25EE10152AEA1FE1B84F0A3786F36B247FE28B8E` |
| `command.txt` | `E7F7F00EEF8E941B55896988D6923365486606821F1DAF080563195D847A743F` |
| `status.txt` | `8814913C0DF8B63AD5AC37318B8A86CAB8B708BFA2844BB6A2C8C439806AB442` |
| `stdout.log` | `D65089AE41D4BEBD260FDA9EE2316A83A50F693B616948EDF2CE15C80B20B807` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Final status:

- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=264.227`
- frozen-layout ELF:
  `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- frozen-layout ledger:
  `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

This child ends at the public modular endpoint after the safe replay/yield/exit
continuation, or at a precise no-success classification when the replay
horizon is unsafe.  It does not yet compose the full generated resume entry,
the managed drain loop, and this continuation into the outermost operation.

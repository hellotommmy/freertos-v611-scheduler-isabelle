# Resume managed outer-loop unsafe composition — 2026-08-12

Baseline: `9b00680` on `agent/universal-scheduler-refinement`.

## Checked scope

This child closes the replay-horizon-unsafe counterpart of the real translated
`Scheduler_V611_Delay_Translation.xTaskResumeAll'` outermost path.  The public
theorem starts from the same cursor-general modular endpoint, suspension depth
one, conditional pending/current legality property, and normalized post-drain
horizon used to split the checked safe branch.  Its conclusion is only

`not succeeds Scheduler_V611_Delay_Translation.xTaskResumeAll' c`.

It does not claim an exception result, rollback, divergence, absence of
intermediate writes, an exit-critical endpoint, or any post-state relation.
The first unsafe replay step may occur after earlier pending-list and replay
writes.  Nested suspension depth, zero-depth invalid input, and transport back
to the unbounded public `ResumeRel` remain separate obligations.

The proof does not infer a real cutpoint from partial correctness alone.  In
this Spec monad, `RunsTo` entails `succeeds` and excludes top/`Failure`, but
bottom `Success {}` has no reachable outcomes and satisfies every postcondition
vacuously.  Four zero-premise structural `always_progress` facts exclude bottom
for the generated pending head read, pending body, pending while loop, and
outer entry prefix.  `Ex_reaches` then supplies real outcomes, and `runs_toD2`
pins them respectively to `Result u`, `Result (NULL, yw)`, and `Result ()`.
Those concrete result reaches are propagated through the literal source binds
with `succeeds_bind` until the checked unsafe after-drain continuation gives a
contradiction.

No success, termination, no-wrap, cursor-normalization, cursor-None,
`managed = sa_live`, termination-empty, desired-post, or legacy pending-gate
premise is added.  The five internal and four public premises are explicit
source-branch/reuse ledgers; this milestone does not claim they are logically
premise-minimal.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `resume_pending_generated_head_read_always_progress` | 0 | 0 |
| `resume_pending_generated_body_always_progress` | 0 | 0 |
| `resume_pending_generated_loop_always_progress` | 0 | 0 |
| `resume_outer_generated_entry_prefix_always_progress` | 0 | 0 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_unsafe_no_run` | 5 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_unsafe_no_run` | 4 | 0 |

The embedded ML audit rejects any changed premise count or hidden hypothesis.

## Checker topology and chronology

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Unsafe` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Safe`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper uses both ROOT discovery directories,
`-o quick_and_dirty=false`, and `-j 1`.

Runs 01--05 ended at their first proof error with `quick_and_dirty=false`,
`timed_out=false`, and `exit_code=1`.  Each repair was proof plumbing only; no
statement or premise changed.

| run | elapsed | first remaining issue |
| --- | ---: | --- |
| `01-structural-endpoints` | 674.040 s | internal negated horizon remained under `let` |
| `02-explicit-let-transfer` | 635.758 s | public negated horizon remained under `let` |
| `03-public-let-transfer` | 644.706 s | negation did not rewrite through normalize/entry commute |
| `04-explicit-normalize-transfer` | 641.797 s | prefix phase was extracted in the post-commute rather than literal form |
| `05-staged-phase-commute` | 627.761 s | `OF` needed the internal theorem's `Let_def` unfolded |
| `06-unfolded-suffix-premise` | 637.999 s | green; all six theorem objects and ML ledgers passed |

The promoted run is:

- run: `20260812Tresume-managed-outer-loop-unsafe-06-unfolded-suffix-premise`
- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=637.999`
- leaf theory: 5 s

Evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `45125D1405B69097F647ECE3F80CFC5E07B44B34FA3FF645BA1DB7C611AA10C6` |
| `command.txt` | `7ADF74D8A7E5F0999FBEFE0D6AB407F95848E0CEF2E69F8AB70D34310253B200` |
| `status.txt` | `442630E2A6F8FFEE091E2B592E5CDA81E7C9DCCB3FB3B17986FFB4C5B00F559F` |
| `stdout.log` | `4C1F0C185268808FF0BB6B15C76FA5DD68A78D5345FAE7BBB8C6E9A156BCA749` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

The frozen-layout ELF, frozen-layout ledger, and generated address
configuration remained respectively
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

## Exact next boundary

The next child should prove the nested positive-depth actual-root branch
without importing the outermost current-safety or replay-horizon premises.
After that, depth zero needs an explicit invalid-input/machine-path
classification, and the normalized modular result must be transported back to
the unbounded public `ResumeRel` before claiming branch-complete Resume.

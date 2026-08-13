# Resume managed outer-loop safe composition — 2026-08-12

Baseline: `89a5a8b` on `agent/universal-scheduler-refinement`.

## Checked scope

This child closes the horizon-safe, outermost branch of the actual translated
`xTaskResumeAll'` source.  It consumes the checked zero-premise source factor

`xTaskResumeAll' = bind resume_outer_generated_entry_prefix
  (lambda _. resume_outer_generated_entry_suffix)`

and composes, in literal source order:

- the suspension-zero and positive generated-task-count conditions;
- the pending-list guard and uniform generated head read;
- the generated pending loop with exact initial local word zero;
- the checked safe missed-tick replay choice;
- the literal `local_y = 1 or xMissedYield = 1` yield branch; and
- the final proof-port critical exit.

The internal suffix theorem retains the five load-bearing premises available at
the managed phase cutpoint.  The public theorem has four premises: a public
cursor-general modular endpoint, outermost suspension depth one, the conditional
pending/current safety property, and a safe replay horizon over the normalized
entry followed by the pending drain.

The public conclusion is about the real
`Scheduler_V611_Delay_Translation.xTaskResumeAll'`.  It returns exactly one iff
the replayed state takes the checked literal yield branch, otherwise zero; it
exports the corresponding `YieldAbs` and a public modular endpoint.  The
normalized snapshot is paired with `yield_count_mod_rel`, so the theorem does
not add a no-wrap premise and remains honest at `MAX_WORD` yield-counter wrap.

No legacy pending gate, `managed = sa_live`, cursor normalization, cursor-None,
termination-empty, desired-post, or old `xTaskResumeAll_drain_composed` premise
is used.  Arbitrary legal cursors, nonempty termination roots, and strict
`sa_live` subsets of `managed` remain in scope.

This child is not the complete universal resume theorem.  The replay-horizon
unsafe no-success branch, nested suspension branch, zero-depth invalid-input
classification, unbounded semantic transport back to `ResumeRel`, and the
mixed/sequential/concurrent public contracts remain separate obligations.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_safe` | 5 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_safe` | 4 | 0 |

The embedded ML audit rejects any changed premise count or hidden hypothesis.

## Checker topology and chronology

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Safe` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry_Factor`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper uses both ROOT discovery directories,
`-o quick_and_dirty=false`, and `-j 1`.

Runs 01--03 and 05--23 ended at their first proof error with
`quick_and_dirty=false`, `timed_out=false`, and `exit_code=1`.  Run 04 produced
only `command.txt`; it has no status or theorem result and is not classified as
red or green.  The bounded progression was:

| runs | checked frontier / first remaining issue |
| --- | --- |
| 01--03 | normalized safe statement and continuation composition; outer `let` exposure |
| 05--07 | exit/return payload transfer; broad bind projection exposed unstable branches |
| 08--12 | local transfer proof plumbing and nested conjunction elimination |
| 13 | bare continuation plus explicit checked exit; top-level VCG still split the abstract post |
| 14--17 | explicit source-order composition; isolated selection of the two concrete source conditions |
| 18 | concrete conditions and guard passed; guard join still split abstract `if`s |
| 19 | the complete five-premise suffix passed; public prefix still retained an outer `let` |
| 20 | actual source factor and prefix theorem connected; prefix witness simplification split the post |
| 21 | prefix witnesses passed; suffix theorem still retained its outer `let` |
| 22 | suffix theorem instantiated; public horizon required the normalization commute |
| 23 | horizon commute passed; only the final public post commute remained |
| 24 | green; both theorem objects and their ML premise/hypothesis ledgers passed |

The promoted run is:

- run: `20260812Tresume-managed-outer-loop-safe-24-final-post-commute`
- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=643.424`
- leaf theory: 8 s

Evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `CA92C2B4DBD769C2A157CF9969DAF76491EE7BFB3E9CF057397041335175EEB2` |
| `command.txt` | `58DD8AE20973A9820CCAB6ECF35F2E100220E45CC78E7618B65BF83142A09344` |
| `status.txt` | `FBA3B9D522A52BF681DB41714081A8EA521FD06E0A9BCD5B830FE82B08D70103` |
| `stdout.log` | `4B8D2CFFAD9919091E1B9847DB6FCBE00195F068A4BE9F9308BE279724AFE21A` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

The frozen-layout ELF, frozen-layout ledger, and generated address
configuration remained respectively
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

## Exact next boundary

The next managed child should prove the horizon-unsafe counterpart as
`not succeeds` only.  It must use structural `always_progress`, `Ex_reaches`,
`runs_toD2`, and `succeeds_bind` to obtain real intermediate endpoints; a
RunsTo post alone is insufficient because bottom/empty outcomes make it
vacuous.  After that, the nested positive-depth branch and zero-depth invalid
classification can be added without imposing the outermost current/horizon
premises on the nested source path.

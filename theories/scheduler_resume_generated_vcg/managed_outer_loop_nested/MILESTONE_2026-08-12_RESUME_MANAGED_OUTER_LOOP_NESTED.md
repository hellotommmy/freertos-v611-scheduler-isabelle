# Resume managed nested branch — 2026-08-12

Baseline: `bc9a2e3` on `agent/universal-scheduler-refinement`.

## Checked scope

This child lifts the existing exact generated-source early-return theorem for
`Scheduler_V611_Delay_Translation.xTaskResumeAll'` from its control-field
relation to the complete cursor-general modular public endpoint.  For every
legal nested suspension depth (`1 < sa_suspend_depth a`), the theorem proves
all of the following in one postcondition:

- the real translated function returns `Result 0`;
- the complete concrete globals equal the exact suspension-word decrement;
- `ResumeRel a False (resume_outer_entry_abs a)` holds; and
- the same managed, termination, external-root, heap, family, observation,
  cursor, and modular yield-count representation is restored at the public
  endpoint.

The public theorem has only two premises: the cursor-general modular endpoint
and the strict nested-depth condition.  It deliberately has no pending-ring,
current-task, replay-horizon, task-count, root-guard, no-wrap, cursor-None,
`managed = sa_live`, termination-empty, desired-post, or legacy pending-gate
premise.  The generated branch returns immediately after decrement because
the suspension word remains nonzero, so it does not read pending tasks, the
current task, missed ticks, a TCB, any list root, or the heap.  `MAX_WORD` is a
valid nested depth and is covered by `Suc_unat_minus_one`; it is not excluded.

Depth zero is intentionally not folded into this theorem.  At concrete word
zero, the source decrement wraps to `MAX_WORD` and the machine still returns
`Result 0`, while nat subtraction keeps the abstract depth at zero and
`ResumeRel` is false.  That invalid-call machine path requires a separate
classification theorem rather than a weakening of the nested premise.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `scheduler_managed_scalar_rel_resume_outer_entry_positive` | 2 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry_positive` | 2 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD` | 1 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_boundaryD` | 1 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_resume_outer_entry_positive` | 2 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_nested` | 2 | 0 |

The embedded ML audit rejects any changed premise count or hidden hypothesis.

## Checker topology and chronology

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Nested` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Unsafe`, the checked
`EAL6_FreeRTOS_V611_Scheduler_Resume_Inner_Source` as a side session, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper discovers the top and generated-vcg
ROOTs, uses `-o quick_and_dirty=false`, and runs with `-j 1`.  It does not add
the standalone inner-source directory, avoiding duplicate session discovery.

Run 01 reached the modular endpoint reassembly after every scalar, snapshot,
depth, and boundary transport lemma had passed.  Its sole first error was
proof plumbing: `auto` did not select the seven already available snapshot
witnesses.  Run 02 supplied those witnesses explicitly; no theorem statement
or premise changed.

| run | elapsed | result |
| --- | ---: | --- |
| `01-positive-modular-endpoint` | 742.59 s | red; endpoint existential witnesses not selected |
| `02-explicit-endpoint-witnesses` | 661.91 s | green; all six theorem objects and ML ledgers passed |

The promoted run is:

- run: `20260812Tresume-managed-outer-loop-nested-02-explicit-endpoint-witnesses`
- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=661.91`
- leaf theory: 11 s

Evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `3FEF31EB1F254E9B297DBDB916F92E9B270FABDBE06A76FC7F01F6CDF89C9713` |
| `command.txt` | `36018F7A0B666613C71F5C4A4723DF3170AE12B0A6FEF30387191FCBB7936EED` |
| `status.txt` | `BEFC587177FE30EEA36D4F618C9ABDE15001CEE3FA40E911FEF2814A1859D4FC` |
| `stdout.log` | `2FFD657E71B5FF26CA657141B7A9DC5E0D1376E1623E5ED3F7D47E0DB00D214F` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

The frozen-layout ELF, frozen-layout ledger, and generated address
configuration remained respectively
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

## Exact next boundary

The next child should classify suspension depth zero as an invalid Resume API
input while proving its exact successful machine underflow path and the
impossibility of the truncated abstract modular endpoint.  After that, the
safe outermost result still needs transport from its normalized modular
representative back to the unbounded public `ResumeRel`, followed by the
branch-complete public join and remaining delay/tick/mixed-trace obligations.

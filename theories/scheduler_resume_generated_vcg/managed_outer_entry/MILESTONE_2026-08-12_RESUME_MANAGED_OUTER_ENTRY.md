# Resume managed outer-entry prefix — 2026-08-12

Baseline: `748c443` on `agent/universal-scheduler-refinement`.

## Checked scope

This child checks the translated outermost entry prefix that enters the proof
port critical section and decrements `uxSchedulerSuspended`.  Its public
boundary starts from `CursorGeneralStrongSchedulerModularEndpointRel`, so an
unbounded abstract yield history, including the concrete `MAX_WORD -> 0`
representation boundary, is not excluded.

The public theorem has exactly three premises:

- a public modular endpoint;
- the outermost abstract branch `sa_suspend_depth a = 1`; and
- the load-bearing reachability condition
  `ring (sa_pending a) ~= [] --> sa_current a ~= None`.

The third premise is conditional rather than an unconditional current-task
assumption.  It is necessary because `current_wf` permits `sa_current = None`,
whereas a nonempty pending drain later dereferences `pxCurrentTCB`.

The exact source post is the critical `1/1` gate state with the suspension
word reduced to zero.  The theorem also exports:

- a positive generated task count, derived from the nonempty live witness,
  `sa_live subseteq managed`, finiteness, and the managed scalar relation;
- the generated pending-list root guard, derived from Event root coverage;
- the original unbounded entry yield count through `yield_count_mod_rel`; and
- an existential managed Resume phase over
  `normalize_yield_count_abs (resume_outer_entry_abs a)`.

The phase therefore observes the exact low-word public shadow while the
modular ledger retains the semantic unbounded count.  No no-wrap premise,
legacy Resume gate, `managed = sa_live`, cursor normalization, termination
emptiness, or desired-post premise is used.

This is deliberately a prefix cutpoint, not yet a whole `xTaskResumeAll'`
correctness theorem.  A following zero-premise source-factor child must connect
`resume_outer_generated_entry_prefix` to the actual generated function and its
complete post-decrement suffix.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `normalize_yield_count_abs_resume_outer_entry` | 0 | 0 |
| `resume_outer_generated_gate_state_shadow` | 0 | 0 |
| `canonicalize_scheduler_cursors_resume_outer_entry` | 0 | 0 |
| `core_wf_resume_outer_entry` | 0 | 0 |
| `cursor_general_core_wf_resume_outer_entry` | 0 | 0 |
| `scheduler_managed_scalar_rel_resume_outer_entry` | 2 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry` | 2 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_managed_count_positive` | 1 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_pending_guard` | 1 | 0 |
| `CursorGeneralStrongSchedulerSnapshotRel_outer_entry_phase` | 3 | 0 |
| `resume_outer_generated_entry_prefix_exact` | 1 | 0 |
| `CursorGeneralStrongSchedulerModularEndpointRel_generated_outer_entry_phase` | 3 | 0 |

The embedded ML audit checks all twelve theorem objects and rejects any
premise-count change or hidden hypothesis.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_After_Drain_Continuation`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  The repository wrapper ran it with one Isabelle job and a
600-second lifecycle budget.

The bounded first-error chronology was:

| run | exit | elapsed | first result |
| --- | ---: | ---: | --- |
| `20260812Tresume-managed-outer-entry-01-modular-prefix` | 1 | 274.290 s | the initial broad core frame did not normalize record updates |
| `20260812Tresume-managed-outer-entry-02-core-commute` | 1 | 268.469 s | the core record eta equality remained |
| `20260812Tresume-managed-outer-entry-03-core-record-case` | 1 | 270.782 s | the monolithic core simplification still obscured selector frames |
| `20260812Tresume-managed-outer-entry-04-core-frames` | 1 | 335.199 s | `time_wf` needed an explicit tick selector frame |
| `20260812Tresume-managed-outer-entry-05-time-frame` | 1 | 261.539 s | `current_wf` needed the explicit live-set frame |
| `20260812Tresume-managed-outer-entry-06-current-frame` | 1 | 268.145 s | the final core assembly needed the priority-function frame |
| `20260812Tresume-managed-outer-entry-07-priority-frame` | 1 | 268.721 s | cursor-general core still needed the real ring-shape frame |
| `20260812Tresume-managed-outer-entry-08-ring-shape-frame` | 1 | 264.371 s | snapshot current transport needed a separate old-current projection |
| `20260812Tresume-managed-outer-entry-09-current-frame-extract` | 1 | 266.621 s | the option case relation required explicit `None`/`Some` cases |
| `20260812Tresume-managed-outer-entry-10-current-option-cases` | 1 | 260.515 s | task count needed the overlay selector frame |
| `20260812Tresume-managed-outer-entry-11-overlay-task-count` | 1 | 267.219 s | the final seven phase witnesses were not packaged deterministically |
| `20260812Tresume-managed-outer-entry-12-explicit-phase-witness` | 0 | 261.698 s | green; leaf reported 5 s |

All runs were non-timeout runs with `quick_and_dirty=false`.  Runs 01-11
stopped at the first proof error.  The repairs only made record-selector
frames, option cases, overlay transport, and existential packaging explicit;
the final theorem statements and premise ledgers were not weakened.

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `80DC7C7761C0E6239049B93322CF75EEBC4B8979663D5CA3ADD410DE9170A63A` |
| `command.txt` | `450E42FA091782EDC839BA457C163345529EDE0258C1F66DDDC5624E1C2F42C3` |
| `status.txt` | `ED1463391C029BC37EDC99C14D6C6D6C7A06A85B33D35FA4733AE58A3E79BABC` |
| `stdout.log` | `68DBF16FCCF9FCC66C879CA53004C5F5FFD457405796405103EBAE68CECEB035` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

Final status:

- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=261.698`
- frozen-layout ELF:
  `DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`
- frozen-layout ledger:
  `CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`
- generated address configuration:
  `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`

## Exact remaining boundary

The child ends at the normalized managed phase immediately after the generated
critical-entry/decrement prefix.  It does not yet factor the real generated
function, run the managed pending loop from this cutpoint, compose the safe or
unsafe replay continuation, cover the nested-suspension branch, or establish
whole-operation sequential/concurrent contracts.

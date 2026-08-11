# Session handoff: cursor-general nested tick and Resume replay

Date: 2026-08-11
Branch: `agent/universal-scheduler-refinement`
Baseline HEAD at handoff preparation: `1663ad05ad4c9cd18d5c9685d366b3e5e622d5aa`
Public PR: <https://github.com/hellotommmy/freertos-v611-scheduler-isabelle/pull/2>

## Next-session must-read summary

The strongest checked result is now a cursor-general, managed-domain,
generated-source proof for `vTaskIncrementTick'` at a settled public boundary,
including modular 32-bit arithmetic, signed-overflow no-success
classification, boundary re-establishment, and arbitrary finite repeated tick
calls.  The next load-bearing connector is the missed-tick replay inside
`xTaskResumeAll`: the real source executes the tick while proof-port critical
depth and interrupt mask are `1/1`, whereas the checked public tick relation
requires `0/0`.  Do not weaken this by pretending the internal cutpoint is
public.  Start with the unregistered rel-spec overlay probe, machine-check its
small algebra, then prove semantic self-bisimulation of the named unlocked tick
source.  Only after that connect one replay body (`tick` then missed-count
decrement), add replay-horizon arithmetic safety and its no-success
counterpart, retain the `1/1` frame through pending drain, and build a
managed-domain Resume gate.  Keep the modular yield counter separate: a
`MAX_WORD` entry wraps and cannot refine nat `Suc` through the old scalar
relation.  No theorem in this handoff closes universal `xTaskResumeAll`, mixed
five-root traces, or generated concurrency.

## Checked baseline

- `CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete`
  is checker-green with `quick_and_dirty=false`.
- `CursorGeneralStrongVTaskIncrementTickPublicEntryRel_all_arithmetic_inputs`
  classifies every arithmetic input: the literal signed-overflow case has no
  successful generated run; all other unlocked cases and all suspended
  modular cases reach the public post.
- `cursor_general_vTaskIncrementTick_finite_trace` proves arbitrary finite
  repeated tick calls for a caller-supplied stable relation and a per-step
  arithmetic-enabled trace.
- Final evidence:
  - `runs/20260811Tcursor-general-tick-boundary-02/status.txt`: exit 0,
    QAD false, not timed out, 249.268 s.
  - `runs/20260811Tcursor-general-tick-trace-08/status.txt`: exit 0,
    QAD false, not timed out, 261.430 s.
- The checked milestone and its exact scope are recorded in
  `theories/scheduler_delayed_cursor_generalization/MILESTONE_2026-08-11_TICK_BOUNDARY_TRACE.md`.

## New static probes: not checker-green

Neither file below is registered in `theories/ROOT`; neither has been run by
Isabelle.  They are candidates, not accepted proof evidence.

1. `theories/scheduler_delayed_cursor_generalization/nested_tick_transport/rel_spec_probe/Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe.thy`

   - 209 lines.
   - Defines a two-field proof-port overlay and its graph relation.
   - Reduces `rel_spec`/`rel_spec_monad` to exact run-image commutation.
   - Gives bounded yield/gets/guard/modify/condition/bind closure rules.
   - Closes the suspended missed-word branch.
   - Leaves exactly
     `tick_port_overlay_bisim depth mask one_due_tick_unlocked_source`.

2. `theories/scheduler_delayed_cursor_generalization/nested_tick_overlay/Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay.thy`

   - 285 lines.
   - Packages a protected cursor-general entry relation and a generic
     `rel_spec_monad` to `runs_to` transfer.
   - Derives a protected tick theorem only under the explicit open premise
     `scheduler_port_overlay_tick_bisim depth mask`.

Suggested consolidation: checker the smaller rel-spec probe first, then keep
one canonical overlay vocabulary.  Avoid retaining two permanent copies of the
same algebra.

## Source-order facts that must remain explicit

For an outermost `xTaskResumeAll` call, the relevant concrete sequence is:

1. public entry has proof-port depth/mask `0/0`;
2. enter critical gives `1/1`;
3. decrement scheduler suspension depth;
4. drain every pending-ready task while retaining `1/1`;
5. while missed ticks remain: execute `vTaskIncrementTick'`, then decrement
   `uxMissedTicks`;
6. combine the local yield flag with `xMissedYield`, perform at most one
   proof-port yield;
7. exit critical restores `0/0` and return.

The generic replay theorem already exists:
`resume_missed_generated_loop_replays`.  Its two required bricks are a
one-body-step preservation theorem and exact concrete/abstract missed-count
agreement.

## Adversarial counterexamples: do not regress

- **Nested/public mismatch.** A state at `1/1` does not satisfy
  `scheduler_boundary_rel`; normalising it creates a shadow initial state, not
  an equality of actual states.  A semantic simulation is required.
- **A final frame is not non-read.** A modifies theorem can show the two port
  words are not written, but cannot show the source never branches on them.
- **One-step arithmetic definedness is not inductive.** With tick
  `0xFFFFFFFE`, overflow counter `INT_MAX`, and missed debt 2, the first replay
  is a successful non-wrap tick and the second reaches the signed guard
  failure on wrap.
- **Suspended replay does not progress.** Without
  `sa_suspend_depth a = 0`, the tick increments missed debt and the following
  decrement cancels it, contradicting the unlocked abstract replay step.
- **Managed is not live.** A retired task in the termination root makes
  `managed != sa_live`; the old live-domain Resume gate cannot represent it.
- **Yield is modular.** At `MAX_WORD`, the concrete proof-port yield counter
  wraps to zero while the old abstract `Suc` becomes `MAX+1`.  Use a modular
  yield relation; never add a no-wrap premise to exclude the legal state.

## Strict next build staircase

Use the Isabelle skill discipline: one build lane, `quick_and_dirty=false`,
one exclusive theory directory per rung, a small timeout first, and inspect the
first failed command before increasing any timeout.

1. **Nested tick overlay algebra.** Register only the rel-spec probe.  Accept
   when the overlay selectors, graph relation, run-image iff, and combinator
   closure are checker-green.  If a command times out, bisect within the probe;
   do not build the full scheduler session.
2. **Unlocked source self-bisimulation.** Prove
   `tick_port_overlay_bisim ... one_due_tick_unlocked_source` compositionally.
   The first checkpoint should be the generated list remove/insert callees;
   then the due-task while and terminal/future branches.
3. **Protected tick transfer.** Instantiate the checked public theorem through
   the bisimulation.  Postcondition must retain the exact input depth/mask and
   re-establish the protected entry at
   `task_increment_tick_modular_abs a`.
4. **One missed-body connector.** Add positive-debt word predecessor, exact
   count, `sa_suspend_depth=0`, and source order `tick; debt--`.  Accept only
   the exact `resume_missed_source_step_abs` post.
5. **Replay-horizon arithmetic.** Define safety over every remaining replay
   index, prove its shift preservation, instantiate
   `resume_missed_generated_loop_replays`, and add a no-success theorem for the
   first unsafe replay.
6. **Pending port frame.** Strengthen the pending generated loop and
   `xTaskResumeAll_drain_composed` continuation to retain running/depth/mask;
   do not rerun a large VCG if exact body state plus a small induction suffices.
7. **Managed Resume gate.** Generalise observation, family coverage, task
   count, termination, external Event roots, and arbitrary cursors from live
   to managed while pending tasks remain live.
8. **Resume outer closure.** Compose drain, replay, final modular yield, and
   critical exit.  Only then expose an all-branch public theorem and classify
   undefined replay states.

## Completion language for the next session

The repository proves a checker-green, cursor-general, single-root sequential
tick trace from an already established public boundary.  It does **not** yet
prove universal scheduler correctness, universal `xTaskResumeAll`, a mixed
five-root trace, boot reachability, or generated concurrent linearisation.
The earlier 45--47 percent figure is not a repository-native metric or a weighted
average of theories.  External Pro review supplied a provisional coarse ledger:
A 6/8 + B 2/5 + C 0/4 + D 1/3 = 9/20 = 45 percent.  Do not treat that denominator
as stable until A1--A8 are individually named.  The report separately retains a
stricter 35--40 percent common-boundary acceptance-closure estimate and a 45--50
percent reusable-infrastructure estimate.  Any update must state its denominator
and must not count unregistered static probes.  In particular,
`xTaskGetTickCount_refines` proves the tick return under a small
tick/depth/mask relation; it does not yet carry the full cursor-general scheduler
frame required by a common five-root public boundary.

## Repository hygiene

- Before this handoff the branch was synchronized with upstream at `1663ad0`.
- Read the audited report source and external-review digest before changing the
  percentage or claim language:
  - `docs/FREERTOS_V611_UNIVERSAL_PROGRESS_2026-08-11_ZH.tex`
  - `docs/PRO_REVIEW_2026-08-11_PROGRESS_AUDIT.md`
  - `output/pdf/freertos_v611_universal_progress_2026-08-11_zh.pdf`
- Do not add or delete these unrelated untracked files:
  - `output/pdf/freertos_v611_scheduler_proof_map_c0a9c20_zh.pdf`
  - `theories/scheduler_one_due_task_phases/reentry_gateH/tail_e3b2.txt`
- Do not claim the two nested-tick probe theories as green until their sessions
  finish with `quick_and_dirty=false`.

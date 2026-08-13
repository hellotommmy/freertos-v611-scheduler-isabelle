# Session handoff: nested replay safe loop -> first unsafe -> ResumeAll

Date: 2026-08-11

Branch: `agent/universal-scheduler-refinement`

Public PR: <https://github.com/hellotommmy/freertos-v611-scheduler-isabelle/pull/2>

## Start here

Do **not** restart at the old rel-spec probe. The proof has moved substantially
beyond `SESSION_HANDOFF_2026-08-11_NESTED_TICK.md`.

Pushed HEAD is `476e950263a75f6d64542453c2b3bb6b31fecb7a`, ahead/behind
`0/0`. The safe-loop checker task has finished successfully:

- task id: `019fee73-19f4-79d2-b01c-008347a69965`
- host: `local`
- completed work: green safe replay loop, theorem-object audit, commit and push

Before launching any new Isabelle process, inspect task/thread state and confirm
that no other lane is active. The next task must use a new exclusive child
session; do not reopen the now-green safe-loop parent.

## Never touch or stage

- literal directory `$out/`
- literal directory `$tmp/`
- `output/pdf/freertos_v611_scheduler_proof_map_c0a9c20_zh.pdf`
- `theories/scheduler_one_due_task_phases/reentry_gateH/tail_e3b2.txt`

Do not use name-wide process kills. Every build must use the repository wrapper,
one QAD=false lane, `parallel_proofs=0`, and the smallest exclusive child
session. Fix only the first checker error.

## Strongest checked frontier

The following route is now machine checked, not merely designed:

1. Cursor-general, managed-domain generated `vTaskIncrementTick'` at a settled
   public boundary, including modular suspended arithmetic and the literal
   signed-overflow no-success class.
2. Arbitrary finite repeated public tick calls under a caller-supplied stable
   relation and per-step enabledness.
3. Unconditional semantic self-bisimulation of the generated tick under a
   functional overlay that changes only proof-port critical depth and interrupt
   mask. This includes list remove/insert, Event dispatch, top-ready tail,
   generated due while/finally, unlocked prefix, and the whole tick source.
4. Closed protected transport: a real nested state at arbitrary depth/mask,
   especially `1/1`, can reuse the normalized public shadow without pretending
   the internal cutpoint is public `0/0`.
5. One exact missed replay body in real source order:

   ```text
   vTaskIncrementTick' ; uxMissedTicks--
   ```

   The general theorem has exactly four premises: protected entry, scheduler
   suspend depth zero, positive debt, and current arithmetic-definedness.
6. Recursive replay-horizon arithmetic plus an exact concrete/abstract bridge.
   The abstract overflow cast is deliberately
   `(of_nat (sa_overflows a) :: 32 signed word)`, not `32 word`; checker output
   exposed this real type bug despite identical-looking pretty printing.
7. Horizon-safe whole replay while. The final theorem has exactly three public
   premises: protected `1/1` entry, quiet scheduler, and full remaining-debt
   horizon. Positivity, current definedness, count alignment, and loop-step
   state are derived internally.

Safe-loop evidence:

- run `20260811Tnested-tick-replay-safe-loop-01-cold`
- exit 0, `quick_and_dirty=false`, not timed out
- 147.663 s wrapper time; leaf theory 3 s
- theory SHA-256
  `9EB3AABF1BBD89D49380D1C8A00071B11856041B035EFA1E5F31B6709258BB69`

Primary public theorem:
`resume_missed_generated_loop_protected_horizon_safe_1_1`.

## Exact next theorem: first unsafe replay

Do not try to prove the unsafe complement from `runs_to` alone. In this monad,
`runs_to` can hold for `run = bottom = Success {}` and therefore does not imply
that a successor is reachable. The next staircase must first create the missing
progress/reachability support.

Recommended exclusive child sessions:

1. `Nested_Tick_Replay_Progress`
   - prove `always_progress` compositionally for generated `vListRemove'`,
     `vListInsertEnd'`, Event dispatch, top-ready tail, after-generic, loop body,
     unlocked source, whole `vTaskIncrementTick'`, and
     `resume_missed_generated_body ()`;
   - exported theorem object must have zero hidden hypotheses and zero premises.

2. `Nested_Tick_Replay_Body_Outcomes`
   - overlay invariance of `succeeds`;
   - protected quiet + abstract arithmetic undefined implies replay body has no
     successful run;
   - protected entry + positive debt implies the missed-loop condition is true;
   - defined one-body execution yields an explicit `reaches ... (Result ())`
     successor by combining `Ex_reaches`, `always_progress`, and the checked
     body `runs_to` theorem.

3. `Nested_Tick_Replay_First_Unsafe`
   - pure first-bad-index lemma from the negation of the recursive horizon;
   - induction over that first bad index, using the explicit body successor for
     every safe prefix;
   - final theorem: protected entry + quiet + negated full horizon implies no
     successful run of the entire generated missed replay while.

Adversarial witness that the theorem must cover: tick `0xFFFFFFFE`, represented
overflow with signed value `INT_MAX`, debt 2. Replay 1 is no-wrap and succeeds;
replay 2 wraps and fails the signed overflow guard before the debt decrement.
There is no observable partial poststate for the failing Spec monad run.

## Then: pending drain and managed Resume gate

The old `resume_pending_gate_entry_rel` is not a subset of the desired general
relation. It embeds the old cursor policy, sets its domain to runnable live
tasks, and counts live tasks. With a nonempty termination list,
`managed != sa_live`, so reusing it would delete legal retired tasks.

Proceed in this order:

1. Define a tiny `resume_pending_control_frame` equating concrete
   `critical_depth`, `interrupts_disabled`, and `xSchedulerRunning`.
2. Use `resume_pending_generated_body_exact` and
   `resume_pending_ready_inserted_globals` in a list induction to preserve that
   frame through the pending loop; conjoin it with the existing drain theorem.
3. Export the outer continuation with the real protected values `1/1` and
   running `1`.
4. Build a parallel cursor-general managed Resume gate. It must quantify the
   decoder/families/count over `managed`, retain termination and protected
   external Event roots, but separately prove every pending task is in
   `sa_live`. Never assume `managed = live`.
5. From an empty managed pending gate, construct the protected tick entry at
   `1/1`; then invoke the safe/unsafe replay classification.
6. Handle the final yield with a modular word relation. The old abstract nat
   `Suc` is false at `MAX_WORD`; do not add a no-wrap premise.

Only after universal `xTaskResumeAll` closes should work return to arbitrary
positive `vTaskDelay`, unlocked `vTaskSwitchContext`, a shared five-root mixed
trace relation, and generated concurrent linearisation.

## Progress accounting and report

Do not raise completion by counting theories or sessions. Current honest
headlines remain:

- strict common-boundary acceptance closure: **35--40%**, near the upper end;
- reusable proof infrastructure: **45--50%**, near 50%;
- provisional semantic gate ledger: **9/20 = 45%**.

The overlay, body, horizon, and safe loop are major internal connectors but do
not yet cross a new top-level five-root acceptance gate.

Updated sources:

- `docs/FREERTOS_V611_UNIVERSAL_PROGRESS_2026-08-11_ZH.tex`
- `docs/PRO_REVIEW_2026-08-11_PROGRESS_AUDIT.md`
- `output/pdf/freertos_v611_universal_progress_2026-08-11_zh.pdf`

The external Pro review is advisory only. Local Isabelle kernel evidence wins.
The Pro-supplied eight-rung route has now completed overlay, protected tick,
one replay body, and the horizon-safe success half; first-unsafe and Resume
remain open.

# Tick-port overlay core-closure milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This milestone closes only the generic core-closure child of rung 2.  It does
not unfold `vTaskIncrementTick'`, `one_due_tick_unlocked_source`, or either
generated list primitive, and it does not claim the unlocked-source overlay
bisimulation.

## Checked results

- `tick_port_overlay` frames the six non-port selectors used by the generated
  unlocked tick: `t_hrs_'`, `xTickCount_'`, `pxDelayedTaskList_'`,
  `pxOverflowDelayedTaskList_'`, `xNumOfOverflows_'`, and
  `uxTopReadyPriority_'`.
- Each corresponding generated record updater commutes with the overlay for an
  arbitrary update function.
- `tick_port_overlay_bisim` is closed under arbitrary result-only `map_value`,
  and therefore under `liftE` and `finally`.
- `tick_port_overlay_bisim` is closed under `whileLoop` when its condition is
  overlay-invariant and every body instance is an overlay bisimulation.  The
  proof uses `rel_spec_monad_whileLoop`; it assumes neither termination nor a
  valid-list `runs_to` predicate.

No final-state modifies theorem is used as a substitute for read
noninterference.  No scheduler relation was weakened: managed and live domains
remain distinct, delayed-list cursors remain arbitrary when legal, word
arithmetic remains modular, and the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure`;
- direct parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe`;
- leaf side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- wrapper lane: `-j 1`, with a 300-second outer lifecycle bound;
- first Isabelle checker:
  `20260811Tnested-tick-core-02-cold`, exit 1, `timed_out=false`,
  38.26 s; all commands through `finally` checked and the first error was the
  unconstrained loop-value equality type in the `whileLoop` command;
- final green checker:
  `20260811Tnested-tick-core-03-while-type`, exit 0, `timed_out=false`,
  `quick_and_dirty=false`, wrapper 27.377 s and Isabelle leaf 3 s.

An earlier Windows PowerShell 5.1 wrapper invocation failed in the frozen
artifact pre-check before Isabelle started.  Its generated artifact failure
file was removed and the tracked artifact command ledger was restored; it is
not counted as a checker run.

SHA-256 evidence for the green checker:

- theory:
  `424EAC439887B5499DDDF780FBBD03BCFD091CBF0C7E7E43E54CEAABE62BE9BE`;
- command:
  `E9C0C8F17C33DC7D2FE0DEE633CC86C20D8063E890FF9571CDD90AF04C9B993B`;
- status:
  `71A1BB0D107DE90E562ECD8A1071D7F4537875F76DE8B85E4731A2AF01D999AD`;
- stdout:
  `5B7610048DD7E5F8FCD62D26DEAD9073D25C3BD2A46247E53B66F4794614CE93`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

## Exact next semantic rule

The first remaining leaf rule is the unconditional generated-remove
bisimulation, for arbitrary item pointer:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (Scheduler_V611_Delay_Translation.vListRemove' pxListItem)
```

It must be established by unfolding
`Scheduler_V611_Delay_Translation.vListRemove'_def` in a separate child.  A
valid-list `runs_to` theorem is not a universal bisimulation and cannot close
this rule.

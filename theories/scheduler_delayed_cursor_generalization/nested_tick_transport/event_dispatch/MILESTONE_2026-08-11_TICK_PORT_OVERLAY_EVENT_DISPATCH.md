# Tick-port overlay Event-dispatch milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This child closes only the named Event-role dispatch factor.  It does not
unfold the generated remove leaf, top-ready tail, any larger prefix, the loop
body, or the whole generated tick.

## Checked result

For arbitrary proof-port words and arbitrary TCB pointer, with no state or
branch precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_event_dispatch_source pxTCB)
```

The named source is exactly a condition on the physical Event-item container.
The overlay frames the condition's sole state read through `t_hrs_'`.  The true
branch reuses the unconditional generated `vListRemove'` bisimulation; the
false branch is `skip`.  Invalid pointer or heap states therefore select the
same branch and produce the same guard failure on both sides.  There is no
`pxTCB`, heap, list, pointer-validity, branch, success, termination, or
`runs_to` premise, and no modifies theorem is used as a non-read argument.

The theory also checks the final theorem object directly: both
`Thm.hyps_of` and `Thm.prems_of` must be empty or the session fails.  The green
run therefore records `hyps = 0` and `prems = 0`, rather than inferring this
only from the surface statement.

No scheduler relation was weakened: managed and live domains remain distinct,
legal cursors remain arbitrary, word arithmetic remains modular, and the
nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch`;
- direct parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End`;
- leaf side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- wrapper lane: `-j 1`, with a 300-second outer lifecycle bound;
- first cold checker:
  `20260811Tnested-tick-event-dispatch-01-cold`, exit 0,
  `timed_out=false`, `quick_and_dirty=false`, wrapper 39.316 s and Isabelle
  leaf 2 s;
- final checker including the empty-hyps/prems object audit:
  `20260811Tnested-tick-event-dispatch-02-empty-object`, exit 0,
  `timed_out=false`, `quick_and_dirty=false`, wrapper 29.083 s and Isabelle
  leaf 2 s.

SHA-256 evidence for the final green checker:

- theory:
  `DC4AA950F24F742789EA8E8663298EE7F22E4576CB6D23E7A59DA98D40C61F81`;
- command:
  `4C03E84632F62F8A792B7872A09CBEE7D6BA921D187D0614471E2937340E2449`;
- status:
  `FAEED1675870CCC658BDE0DC13E2EB8192F60A42315D7A3E27CAFD3B9C0A1910`;
- stdout:
  `2BB2F85452CEACFCC8F6C1AA6A56D04746E76EC04E1B9C26BCC3352C83F78CBE`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run artifact audit against baseline `34bc0da` found zero tracked
differences and zero new untracked files under
`artifacts/frozen_p2_layout/output`; `build_failure.txt` is absent.

## Exact next semantic rule

The first remaining named factor is:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_top_ready_tail_source pxTCB)
```

Only after that factor should the staircase compose
`one_due_tick_after_generic_source`, the loop body, `whileLoop`/`finally`, and
finally `tick_port_overlay_bisim depth irq_mask one_due_tick_unlocked_source`.

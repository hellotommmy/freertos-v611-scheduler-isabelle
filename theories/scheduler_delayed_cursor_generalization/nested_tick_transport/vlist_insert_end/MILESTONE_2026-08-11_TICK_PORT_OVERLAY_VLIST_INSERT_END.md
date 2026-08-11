# Tick-port overlay vListInsertEnd milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This is the next independent leaf of rung 2.  It opens only
`Scheduler_V611_Delay_Translation.vListInsertEnd'_def`; it does not unfold the
generated tick or claim any named unlocked prefix, loop body, or whole-source
overlay bisimulation.

## Checked result

For arbitrary proof-port words, list pointer, and new-item pointer, with no
state precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (Scheduler_V611_Delay_Translation.vListInsertEnd'
    pxList pxNewListItem)
```

The generated body has twelve source-order actions and eleven binds.  Every
state-dependent read is through `t_hrs_'`; all seven state writes are through
`t_hrs_'_update`.  The proof therefore uses only the checked `t_hrs` selector
frame, updater commutation, and the generic `bind`/`guard`/`gets`/`modify`
bisimulation rules.  Identical guards cover invalid-pointer states on both
sides, so there is no pointer-validity, list-validity, membership, cursor,
termination, or `runs_to` premise.  No modifies theorem substitutes for read
noninterference.

The final list count update remains the generated modular word increment.  No
scheduler relation was weakened: managed and live domains remain distinct,
legal cursors remain arbitrary, and the nested proof-port instance remains
`1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End`;
- direct parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove`;
- leaf side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- wrapper lane: `-j 1`, with a 300-second outer lifecycle bound;
- first cold checker and final green checker:
  `20260811Tnested-tick-vlist-insert-end-01-cold`, exit 0,
  `timed_out=false`, `quick_and_dirty=false`, wrapper 38.361 s and Isabelle
  leaf 2 s.

SHA-256 evidence for the green checker:

- theory:
  `5894D52DF69F3F20EBC4AD85F6E4F4F39BA24390EF3A2E11174791BDCB05F3E8`;
- command:
  `D22F4CFA5E003A459A3DBBB0D136C5EF9647D318366FBDFCE5CECAA973731DE5`;
- status:
  `D5AAC99253CDD53B1DBE1ABB3C8BAFDB405EFAEB54D0F8D9F3ECAAA599B487BC`;
- stdout:
  `67CD050F567C488ADBBBB8883075D32043E497F9278EF32A0569706F4C85C7F0`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run artifact audit against baseline `918c59e` found zero tracked
differences and zero new untracked files under
`artifacts/frozen_p2_layout/output`.

## Exact next semantic rule

The first remaining named unlocked role factor is:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_event_dispatch_source pxTCB)
```

It is the generated Event-role conditional (`vListRemove'` or `skip`).  Only
after this factor should the staircase proceed to
`one_due_tick_top_ready_tail_source`, `one_due_tick_after_generic_source`, the
loop body, `whileLoop`/`finally`, and finally
`tick_port_overlay_bisim depth irq_mask one_due_tick_unlocked_source`.

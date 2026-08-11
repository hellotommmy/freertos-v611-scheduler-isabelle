# Tick-port overlay vListRemove milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This is the second independent child of rung 2.  It opens only
`Scheduler_V611_Delay_Translation.vListRemove'_def`; it does not open the
generated tick or claim the unlocked-source overlay bisimulation.

## Checked result

For arbitrary proof-port words and arbitrary item pointer, with no state
precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (Scheduler_V611_Delay_Translation.vListRemove' pxItemToRemove)
```

The generated body has nine binds over guards, heap modifies, one heap read,
one condition, and `skip`.  Every state-dependent read is through `t_hrs_'`;
every state write is through `t_hrs_'_update`.  The proof therefore uses only
the checked selector/updater commutation facts and the generic bisimulation
closure rules.  It has no valid-list, membership, cursor, termination, or
`runs_to` premise and uses no modifies theorem as a non-read argument.

No scheduler relation was weakened: managed and live domains remain distinct,
legal delayed-list cursors remain arbitrary, word arithmetic remains modular,
and the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove`;
- direct parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure`;
- leaf side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- wrapper lane: `-j 1`, with a 300-second outer lifecycle bound;
- first cold checker:
  `20260811Tnested-tick-vlist-remove-01-cold`, exit 1,
  `timed_out=false`, 36.479 s; the first error was outer proof-method syntax,
  before any semantic subgoal was rejected;
- final green checker:
  `20260811Tnested-tick-vlist-remove-02-method`, exit 0,
  `timed_out=false`, `quick_and_dirty=false`, wrapper 28.368 s and Isabelle
  leaf 2 s.

SHA-256 evidence for the green checker:

- theory:
  `9636C95144ED706FE08F62689C8B4BD277D3E8C06B14CBA4861FF1209D134B58`;
- command:
  `F7D5EB60AFC16CB0C9B5DB3F80ECE06305EEA8762A1B1EBE99688D1725A5A26C`;
- status:
  `AA57708254674F9FEC2CDB632D7C557672210FD0B77B26AA7AFAF90C2D68376E`;
- stdout:
  `E8C5EDECF832095CD513F70412C5491978B68470AB6EE40605501B97C9A27AAE`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

## Exact next semantic rule

The first remaining leaf rule is the unconditional generated insert-end
bisimulation, for arbitrary list and item pointers:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (Scheduler_V611_Delay_Translation.vListInsertEnd'
    pxList pxNewListItem)
```

Only after that leaf is checked may the staircase continue through the named
prefix factors, delayed-task loop body, `whileLoop`/`finally`, and finally
`tick_port_overlay_bisim depth irq_mask one_due_tick_unlocked_source`.

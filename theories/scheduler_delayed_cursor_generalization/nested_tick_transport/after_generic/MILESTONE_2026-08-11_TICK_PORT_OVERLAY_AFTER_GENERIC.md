# Tick-port overlay after-Generic milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the named composition after the generated
Generic-item removal.  It does not enter the loop body, `whileLoop`, `finally`,
or the whole generated unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary TCB pointer, with no state,
pointer, heap, list, branch, or successful-execution precondition:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_after_generic_source pxTCB)
```

The source definition is exactly the already checked Event-role dispatch
followed by the already checked top-ready tail.  One application of relational
`bind` closure composes those unconditional self-bisimulations.  No local
subfactor, generated body copy, `runs_to` premise, pointer/list validity, or
success assumption is introduced; guard failures remain matched by the two
component theorems.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run therefore establishes `hyps = 0` and
`prems = 0` from the exported theorem object.  The theory contains no `oops`,
`sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-after-generic-01-cold`, exit 0,
  `timed_out=false`, wrapper 61.287 s, rebuilt parent 8 s, and leaf theory 2 s.

SHA-256 evidence for the green checker:

- theory:
  `0CF54BC9A4EF1DB27697A4A41598082C2271E8263A9B1569640D7428F24356D9`;
- command:
  `E52D8C80D8BB70E17926811F53EEEDB56FBC1D0C8F56B19FB1924E083E4BF117`;
- status:
  `CC953BD8A426FE7F8B78FF3EFEB83A5D98198DCB9148E21F56AFC09F4AAC7B3D`;
- stdout:
  `BFAEBB97302D61C49B1690174E7B1E1DEA40FFCC268A623A99583031CCE680A1`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline `7822796` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining named rule is:

```isabelle
tick_port_overlay_bisim depth irq_mask
  (one_due_tick_loop_body_source pxTCB)
```

That loop-body leaf, and only later `whileLoop`/`finally` and the whole unlocked
tick, remain outside this milestone.

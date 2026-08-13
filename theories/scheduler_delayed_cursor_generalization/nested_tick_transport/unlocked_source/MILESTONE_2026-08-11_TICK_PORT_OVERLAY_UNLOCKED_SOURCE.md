# Tick-port overlay unlocked-source milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes the universal overlay bisimulation of the complete
named unlocked tick source.  It deliberately does not add the outer
`vTaskIncrementTick'` public relational corollary.

## Checked result

For arbitrary proof-port words and arbitrary globals, with no
defined-arithmetic, readability, success, termination, pointer/list validity,
guard-success, branch, heap, or scheduler premise:

```isabelle
tick_port_overlay_bisim depth irq_mask
  one_due_tick_unlocked_source
```

The proof substitutes `one_due_tick_unlocked_source_factor` and uses one
relational bind.  Its head is the already checked unconditional prefix; for
every TCB pointer returned by that prefix, its tail is the already checked
unconditional named finally factor.  All exceptional, failed-guard, top, and
nonterminating behaviours remain represented on both sides; the theorem does
not replace them by a succeeds or termination premise.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-unlocked-source-01-cold`, exit 0,
  `timed_out=false`, wrapper 67.737 s, rebuilt parent 8 s, and leaf theory
  2 s.

SHA-256 evidence for the green checker:

- theory:
  `860C5A3F87ED3EB39A5CB6502FDCB514D673B877B22A00BE14A7D2C073D1567E`;
- command:
  `CE4C2297F3934E373DB4BA504F607E7E6154D82C5E27483758EBB0A06A42E600`;
- status:
  `317BA3300A94C963DDBFCA30975074A978CEC8EE3D96930ECA0BC94D2DB77E4C`;
- stdout:
  `4337DB6833C407FA53685591E9DBE952E3FC3F6A0940AEE30AD8909D2AD092F6`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline
`fd89a510ae580e1dd93b5f28820e668a393050f2` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining public relational rule is:

```isabelle
rel_spec_monad (tick_port_overlay_rel depth irq_mask) (=)
  Scheduler_V611_Delay_Translation.vTaskIncrementTick'
  Scheduler_V611_Delay_Translation.vTaskIncrementTick'
```

It can be derived through the existing outer-source bridge from this unlocked
source theorem, combining the unlocked and suspended branches.  That public
corollary remains outside this milestone.

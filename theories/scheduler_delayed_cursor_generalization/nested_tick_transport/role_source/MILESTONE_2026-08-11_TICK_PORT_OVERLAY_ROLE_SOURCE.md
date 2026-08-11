# Tick-port overlay role-source milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the universal overlay bisimulation of the
generated unlocked role-source factor.  It does not compose the complete
unlocked prefix or the whole generated unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary globals, with no no-wrap,
defined-arithmetic, guard-success, heap, pointer, list, branch, or scheduler
premise:

```isabelle
tick_port_overlay_bisim depth irq_mask
  generated_unlocked_tick_role_source
```

The proof follows the generated factor in exact source order:

1. modular `xTickCount + 1` update;
2. wrap condition on the updated tick word;
3. current delayed-root read;
4. current root assignment from the overflow root;
5. overflow root assignment from the saved current root;
6. the lower signed overflow-counter guard;
7. the upper signed overflow-counter guard;
8. modular `xNumOfOverflows + 1` update.

The false wrap branch remains `skip`.  The overlay frames every selector used
by the condition, root swap, and signed guards, and commutes with every update.
Thus each guard either succeeds on both sides or fails on both sides; no
defined/no-wrap premise is added.  Both increments retain their original word
semantics, and the two root writes retain their generated ordering through the
saved `pxTemp` value.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-role-source-01-cold`, exit 0,
  `timed_out=false`, wrapper 64.798 s, rebuilt parent 9 s, and leaf theory
  2 s.

SHA-256 evidence for the green checker:

- theory:
  `5DD6D1FF22AA8BF24D2A815A8EC769C5848C4E8FB978F05351ECC97AEEB91326`;
- command:
  `50021578205E11A12144335636F4F0A85DF8A9DBD8EC87C194085A0E3E7C8EF3`;
- status:
  `1F88BBDAF887A761CD75D6E90350A7D80476F903011FE636A3E9F420DFF22A92`;
- stdout:
  `8B045986EA9636B9958E3A8F4A1EFEE1DBADAF924B72A12763B1C51F8FB98569`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline
`9b9f3b13b1485a4bc287f00670f4a2f27ea8b31c` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining universal overlay rule is the complete named prefix:

```isabelle
tick_port_overlay_bisim depth irq_mask
  generated_unlocked_tick_prefix_source
```

It should be composed from `generated_unlocked_tick_prefix_source_split`, this
role-source theorem, and the already checked delayed-remainder theorem.  The
whole unlocked source remains outside this milestone.

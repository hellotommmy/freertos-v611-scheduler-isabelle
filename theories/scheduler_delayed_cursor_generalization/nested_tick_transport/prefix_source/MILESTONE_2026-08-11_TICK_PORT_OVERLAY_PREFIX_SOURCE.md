# Tick-port overlay prefix-source milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child closes only the universal overlay bisimulation of the
complete named unlocked prefix.  It does not prove the whole generated
unlocked tick.

## Checked result

For arbitrary proof-port words and arbitrary globals, with no
defined-arithmetic, readability, pointer/list validity, guard-success, branch,
heap, or scheduler premise:

```isabelle
tick_port_overlay_bisim depth irq_mask
  generated_unlocked_tick_prefix_source
```

The proof substitutes `generated_unlocked_tick_prefix_source_split` and uses
one relational bind.  Its head is the already checked unconditional role
source, and its tail is the already checked unconditional delayed remainder.
Consequently arithmetic-guard failure in the role source and pointer/list
guard failure in the remainder are both retained synchronously.  No
arithmetic-defined or readable `runs_to` theorem is used.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-prefix-source-01-cold`, exit 0,
  `timed_out=false`, wrapper 67.713 s, rebuilt parent 8 s, and leaf theory
  2 s.

SHA-256 evidence for the green checker:

- theory:
  `20092214CBDA1E7C584D38C9CC3F6D519EC3F21391A98B287682A238C9B07003`;
- command:
  `31DF8CC257DF9AA7E0D5E9163938F6ADD0E0B7D4312BEA762B5AFC24A2E914ED`;
- status:
  `5DFB54813DE863B69C5FBC450568ACEB2E0F52F9C051877A5ACAAFA5605B371B`;
- stdout:
  `5615D33AE8C95B5FE167C48DE26606AF73AB56680399FE5CA9695055F8CF91F8`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline
`be888930e55b674f1e23c817bc83550c49b4d3d1` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next semantic rule

The first remaining universal overlay rule is the whole unlocked source:

```isabelle
tick_port_overlay_bisim depth irq_mask
  one_due_tick_unlocked_source
```

It should be composed from `one_due_tick_unlocked_source_factor`, this prefix
theorem, and the already checked named finally-factor theorem.  That whole
source proof remains outside this milestone.

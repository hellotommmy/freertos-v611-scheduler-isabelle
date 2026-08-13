# Tick-port overlay whole-tick rel-spec milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This staircase child exports only the whole generated tick relational
specification under the canonical `tick_port_overlay_rel` name.  It does not
import the separate nested-tick overlay theory and does not derive a protected
entry corollary.

## Checked result

For arbitrary proof-port words, with no boundary, arithmetic-defined, success,
termination, pointer/list validity, heap, branch, or scheduler premise:

```isabelle
rel_spec_monad (tick_port_overlay_rel depth irq_mask) (=)
  Scheduler_V611_Delay_Translation.vTaskIncrementTick'
  Scheduler_V611_Delay_Translation.vTaskIncrementTick'
```

The proof directly instantiates
`vTaskIncrementTick_tick_port_overlay_bisim_from_unlocked` with the already
checked unconditional theorem
`one_due_tick_unlocked_source_tick_port_overlay_bisim`.  The bridge itself
combines the generated unlocked source with the generated suspended branch;
the whole function is not unfolded in this child.  Failed guards, top results,
exceptions, and nontermination remain covered by the relational semantics.

The final ML object audit fails the session unless both `Thm.hyps_of` and
`Thm.prems_of` are empty.  The green run establishes `hyps = 0` and
`prems = 0`; the theory contains no `oops`, `sorry`, or oracle shortcut.

No surrounding scheduler relation is weakened: managed and live domains stay
distinct, legal cursors stay arbitrary, word arithmetic stays modular, and
the nested proof-port instance remains `1/1`.

## Checker record

- exclusive child session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source`;
- child side sessions: none;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound;
- first checker:
  `20260811Tnested-tick-whole-rel-spec-01-cold`, exit 0,
  `timed_out=false`, wrapper 67.601 s, rebuilt parent 9 s, and leaf theory
  2 s.

SHA-256 evidence for the green checker:

- theory:
  `9EC3926795C7BB42799771C9C7BA84060C6C84D77AE86CB6CDB0ECC5BD06B5E3`;
- command:
  `80CB0769FBA993B2D1DB7E70E7FDF63D71DDE1E52CFE7FDC0F292618E7B0C332`;
- status:
  `9C51FA139FA0787BDB1A8F2D0977D3DF28236718050E02BA483FB07C4C8AF853`;
- stdout:
  `D4E7ED404F4A760C04EB54659C932AFB5FEA421B1F447D75EAD3EDBC63B59BBA`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline
`8afb7b035882593a914e25de81dd1ac7c5ff7800` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact next boundary

The protected-entry development uses the separately named predicate:

```isabelle
scheduler_port_overlay_tick_bisim depth mask
```

Before applying
`CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_complete`,
the canonical result checked here must be transferred to that overlay naming
without confusing or silently identifying the two definitions.  That naming
bridge and the protected-entry corollary remain outside this milestone.

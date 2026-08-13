# Nested tick overlay checker milestone

Status: **the complete tracked 285-line theory is machine-checked with
`quick_and_dirty = false`**.

This infrastructure rung registers and checks
`Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay`.  It validates the
protected relational transfer itself while deliberately retaining the
`scheduler_port_overlay_tick_bisim` premise.  It does not add the naming bridge
from the canonical whole-tick rel-spec and does not add a protected-entry
capstone corollary.

## Checked scope and premise ledger

The green session checks all four definitions and every proof through
`CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_complete`.
That public theorem is not weakened or replaced.  It retains exactly:

1. `scheduler_port_overlay_tick_bisim depth irq_mask`;
2. the protected entry relation, with the same managed, termination, and
   external domains;
3. conditional generated arithmetic definedness on the unlocked abstract
   branch.

Its conclusion still returns `Result ()` and reconstructs the same protected
entry relation at `task_increment_tick_modular_abs a`.  Managed and live
domains remain distinct, legal cursors remain arbitrary, word arithmetic stays
modular, and the nested proof-port instance remains `1/1`.

Two local repairs were required to make the previously unregistered tracked
theory parse:

- every proof variable named `mask` was alpha-renamed to `irq_mask`, avoiding
  collision with Isabelle's existing `mask` constant; both overlay parameters
  remain `32 word`, and no proposition is weakened;
- two `runs_to` propositions received explicit parentheses around their
  compound state/postcondition terms; the underlying propositions and proofs
  are unchanged.

No theorem premise, public conclusion, representation relation, or arithmetic
condition was removed.  The theory contains no `oops`, `sorry`, or oracle
shortcut.

## Session and checker record

- exclusive session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec`;
- explicit side session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure`;
- source directory: `scheduler_delayed_cursor_generalization/nested_tick_overlay`;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, with a 300-second wrapper lifecycle bound.

Bounded first-error staircase:

- `20260811Tnested-tick-overlay-01-cold`: exit 1, 169.658 s; first error was
  the line-16 `mask` constant/type collision;
- `20260811Tnested-tick-overlay-02-irq-mask`: exit 1, 150.627 s; first error
  moved to the line-156 compound `runs_to` proposition syntax;
- `20260811Tnested-tick-overlay-03-runs-to-syntax`: exit 1, 152.964 s; the
  generic transfer was accepted and the first error moved to the analogous
  line-244 local proposition;
- `20260811Tnested-tick-overlay-04-transferred-syntax`: exit 0,
  `timed_out=false`, wrapper 152.696 s, and leaf session 32 s.

The green leaf remained within its 60-second session budget.  The larger
wrapper time is attributable to the cold/side heap merge and is recorded as
infrastructure cost rather than proof-command timeout.

SHA-256 evidence for the green checker:

- theory:
  `958F903AE4F2D7880ECC6F7642D5B9020BEDC83BC5C7511A656CA5FFB59EC9E8`;
- command:
  `7ACEAD8DFE810B7D6E1D875B89B76B3BE9EEF8CE76EA0EE09F72869B1A2D6D54`;
- status:
  `7A916A4359115B503DA8B31DEC284282AB91C022C90935469C92F3FE533B80A8`;
- stdout:
  `0A74BDDFF17E5E63B940C243D4F9EC5BBC327BA28AB2FE70572C7E42CC5B6ACF`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The post-run audit against baseline
`982d7edb27363bb64325a0e0646a54038f60792f` found zero tracked differences
and zero new untracked files under `artifacts/frozen_p2_layout/output`;
`build_failure.txt` is absent.  The four protected untracked objects were not
modified.

## Exact remaining boundary

The checked protected transfer still intentionally requires:

```isabelle
scheduler_port_overlay_tick_bisim depth irq_mask
```

A later capstone must explicitly align the separately named scheduler overlay
relation with the canonical whole-tick rel-spec before discharging this
premise.  That bridge and protected-entry corollary are outside this rung.

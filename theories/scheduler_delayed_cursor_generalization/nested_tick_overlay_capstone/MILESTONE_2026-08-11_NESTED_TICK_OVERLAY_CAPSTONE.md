# Nested tick overlay capstone milestone

Status: **green with `quick_and_dirty = false`**.

This child closes the proof-port overlay naming gap and discharges the
`scheduler_port_overlay_tick_bisim` premise of the protected-entry transfer.
It does not enter the missed-tick body, replay loop, replay horizon, pending
loop, or Resume closure.

## Checked statements

The capstone first proves equality of the complete overlay functions:

```isabelle
scheduler_port_overlay = tick_port_overlay
```

It then proves the state-relation functions extensionally equal for arbitrary
proof-port words:

```isabelle
scheduler_port_overlay_rel depth irq_mask =
tick_port_overlay_rel depth irq_mask
```

The canonical whole-tick rel-spec therefore closes the scheduler-named
bisimulation without premises:

```isabelle
scheduler_port_overlay_tick_bisim depth irq_mask
```

Finally,
`CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_transport_closed`
retains exactly these two premises, in this order:

1. `CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
   D depth irq_mask c a managed termination external`;
2. `sa_suspend_depth a = 0 ⟹
   generated_unlocked_tick_arithmetic_defined c`.

Its conclusion is the original protected transfer conclusion: the generated
tick returns `Result ()` and re-establishes the same protected-entry relation
at `task_increment_tick_modular_abs a`, with the same depth, interrupt mask,
managed domain, termination ring, and external roots.

The checked ML theorem-object audit records:

| theorem | hidden hypotheses | premises |
| --- | ---: | ---: |
| `scheduler_port_overlay_tick_bisim_closed` | 0 | 0 |
| `...sequential_branch_transport_closed` | 0 | 2 |

Thus the capstone removes only the already discharged bisimulation premise.
It does not add pointer, list, cursor, success, termination, or no-wrap
premises.  Managed and live domains remain distinct, legal cursors remain
arbitrary, word arithmetic remains modular, and the nested critical proof-port
instance remains `1/1`.

## Session topology and checker

- exclusive session:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone`;
- sole parent:
  `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay`;
- side sessions: none;
- exclusive directory:
  `scheduler_delayed_cursor_generalization/nested_tick_overlay_capstone`;
- theory imports: the Nested Tick Overlay theory and the ancestor Whole Tick
  Rel Spec theory explicitly;
- session options: `document=false`, `quick_and_dirty=false`,
  `parallel_proofs=0`, `timeout=60`;
- checker lane: `-j 1`, under a 300-second wrapper lifecycle bound.

Green run:

- run id: `20260811Tnested-tick-overlay-capstone-01-cold`;
- status: `exit_code=0`, `timed_out=false`, wrapper 169.777 seconds;
- parent rebuild reported by Isabelle: 40 seconds;
- Capstone leaf: 3 seconds, within the 60-second session budget.

The long wrapper duration is therefore recorded as cold parent/infrastructure
cost, not as a slow Capstone proof command.

SHA-256 evidence:

- theory:
  `BA8E62BA4B372ED6F488ACE02DB6EAA26799B37B4D50F9225953C248797B2B50`;
- command:
  `CC1C406B4CA6EEDFE865B3D5C11146655486505122699EFA7262C6B4B70B1737`;
- status:
  `3079756666E7AF8890D5C7158C800FE310996374925ABFC34A8D865679933E9F`;
- stdout:
  `9852984DF0E713D49031F1C050DDB29E53056B00A18B25C3482D748D95705B9C`;
- stderr:
  `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6`.

The baseline for this rung was
`3b5c81c7e187fd8a2bc2187c80afeb84e040ebf2`.  Post-run artifact audit found
zero tracked differences and zero untracked files under
`artifacts/frozen_p2_layout/output`, and no `build_failure.txt`.  The four
protected untracked objects were not staged, deleted, or modified.

## Exact next boundary

The next semantic rung is the one missed-body connector: positive-debt word
predecessor and exact count, `sa_suspend_depth = 0`, source order `tick;
debt--`, and the exact `resume_missed_source_step_abs` postcondition.  No part
of that rung is proved here.

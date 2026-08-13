# Cursor-general managed arbitrary-while freeze

Status: **machine-checked with `quick_and_dirty = false` on 2026-08-10**.
All nine exclusive sessions are registered and completed green through
`20260810Tcursor-general-while-complete-04`.  The original static construction
notes below are retained as an audit trail.

## Public interface

- Input relation:
  `CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry due_tasks future pxTCB managed termination external K_G K_E`.
- Nonempty index:
  `cursor_general_due_prefix_managed_generated_head_index`.
- Derived terminal join:
  `cursor_general_due_prefix_managed_generated_terminal_post`.
- Stable public endpoint:
  `cursor_general_due_prefix_managed_generated_complete_public_post`.
- Final theorem:
  `CursorGeneralManagedDuePrefixGeneratedEntryRel_finally_complete_exact`.

The final theorem has exactly two premises: the unified entry relation and
`R = generated_scheduler_roots`.  It has no expected execution, selected
branch, desired successor state, fixed task, fixed priority, fixed tick, fixed
queue length, or cursor-policy premise.

The nonempty entry and every nonempty index contain exactly one existential
`C / branch / S / generic_raw / event_raw` tuple.  That tuple is shared by
`CursorGeneralDueLoopStrongHeadRel` and `due_prefix_managed_gate_inv`; its
abstract families are exactly `ods_generic_family S` and
`ods_event_family S`.  The zero entry contains a
`CursorGeneralStrongDuePrefixLoopHeadRel` and no Gate-H witness.

## Frozen ROOT order

Append these sessions in this exact order, after the cursor-general generated
due-step and generated-terminal rungs have been registered.  Each directory
is exclusive to one session.

```isabelle
session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Defs in "scheduler_delayed_cursor_generalization/generated_managed_while/defs" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Defs

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Index in "scheduler_delayed_cursor_generalization/generated_managed_while/index" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Defs +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Index

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero in "scheduler_delayed_cursor_generalization/generated_managed_while/zero" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Index +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Zero

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs in "scheduler_delayed_cursor_generalization/generated_managed_while/terminal_defs" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Finally
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts in "scheduler_delayed_cursor_generalization/generated_managed_while/terminal_facts" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public in "scheduler_delayed_cursor_generalization/generated_managed_while/terminal_public" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter in "scheduler_delayed_cursor_generalization/generated_managed_while/terminal_adapter" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While in "scheduler_delayed_cursor_generalization/generated_managed_while/while" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Complete in "scheduler_delayed_cursor_generalization/generated_managed_while/complete" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Managed_While_Complete
```

Build in the same order and stop at the first red session.  Do not launch
parallel Isabelle lanes.  A checker-green claim may be made only after all
nine sessions complete with `quick_and_dirty = false`.

## Static audit

- Nine theory files; each exclusive directory contains one theory.
- Line counts: 100, 278, 165, 78, 153, 49, 142, 151, and 187; all are below
  350 lines.
- No `sorry`, `oops`, `admit`, `axiomatization`, `oracle`, `sledgehammer`, or
  `quick_and_dirty` token occurs in a theory file.
- No word-bounded occurrence of the old `DueLoopStrongHeadRel`,
  `StrongDuePrefixLoopHeadRel`, `StrongSchedulerSnapshotRel`,
  `strong_managed_domain_rel`, or `tail_cursor_wf` occurs.
- No cursor clearing or scheduler-cursor canonicalisation occurs.
- No fixed word, task, priority, tick, address, or queue-size witness occurs.
- No trailing whitespace was found.

## Frozen theory hashes

| Rung | SHA-256 |
|---|---|
| defs | `D0AD93BBD8452AECEEBFE6EBE0F5F2D6AC1465F7CDBD825FC7AAC484D8B643D7` |
| index | `980B3EBA2D89FA53A5F43992D2634F54739718A2D9493D7B0753A2FB4C8C9954` |
| zero | `B2646D1E3671BAEB44A7431DC0F7F716B2BA4CB2365C61F34EF2E5D9D337C5F3` |
| terminal defs | `13D7C12CCB3751D8EB5B864492433AAA58CCA4B05D461A1EF6143E9F1576EF72` |
| terminal facts | `E20E0420E42E10B379170B26A2C1E1247168511ED6E16CB4BD9A8176FEA7F060` |
| terminal public | `0A879F136CE74EB0C9A68D8D6AA5FCA7E3C5DAF2FEB68F3AB1C53E5D124A777C` |
| terminal adapter | `E88F8370423E4EB7168DF4DE1C7C483BC7F5494DCAE8AB8AFB5B638FAE881BD2` |
| while | `4F802EF136ED194A42CD73160A53304AA26F230913893A44BC4B657C9445686E` |
| complete | `9754F008FA738B4EE2F41FD92574736D7AE5918E97131C5E22EE33EECCAF019A` |

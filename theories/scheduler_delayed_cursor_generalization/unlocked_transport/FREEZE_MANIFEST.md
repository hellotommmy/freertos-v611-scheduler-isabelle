# Cursor-general unlocked tick transport freeze

Status: **machine-checked with `quick_and_dirty = false` on 2026-08-10**.
All ten exclusive sessions are registered and completed green, ending with
`20260810Tcursor-general-unlocked-pipeline-capstone-01`.  The original static
construction notes below are retained as an audit trail.

## Scope and public interfaces

The staircase carries an arbitrary legal represented cursor through the real
generated unlocked tick prefix and into the cursor-general arbitrary managed
while.  The proof-only `canonicalize_scheduler_cursors` shadow occurs only in
the pure core/time rung.  It is never substituted for a real abstract family
under the same raw heap.

Principal interfaces:

- public precondition:
  `CursorGeneralStrongVTaskIncrementTickEntryRel`;
- snapshot transport:
  `CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_task_snapshot_transport`;
- exact real-family assembler:
  `CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel`;
- sibling-compatible loop input:
  `CursorGeneralManagedDuePrefixGeneratedEntryRel`;
- generated prefix theorem:
  `CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix`;
- prefix plus arbitrary managed while:
  `CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally`.

For a zero due prefix, the transported snapshot is
`CursorGeneralStrongSchedulerSnapshotRel`.  For a nonempty due prefix, it is
`CursorGeneralDueLoopSchedulerSnapshotRel`.  Both use the same
`generic_raw / generic_abs / event_raw / event_abs` values from the public
precondition.  The physical pointer bridge reads the represented root head,
not the traversal cursor.

The nonempty managed-entry constructor directly replays the canonical Gate-H
context from cursor-general coverage, role, observation, scalar, and exact
relabel facts.  It does not call a General-to-old adapter and does not impose
the historical delayed-None or tail-cursor policy.

## Exact ROOT order

Register the prerequisite cursor-general pointer bridge, generated due-step,
generated terminal, and all nine generated-managed-while sessions first.
Then append the following sessions in this exact order.  Every theory
directory is exclusive to one session.

```isabelle
session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry in "scheduler_delayed_cursor_generalization/unlocked_transport/pure_entry" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pure_Entry_Phase
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core in "scheduler_delayed_cursor_generalization/unlocked_transport/snapshot_core" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Snapshot_Transport
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks in "scheduler_delayed_cursor_generalization/unlocked_transport/snapshot_tasks" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context in "scheduler_delayed_cursor_generalization/unlocked_transport/managed_gate_context" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges
    EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Capstone
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure in "scheduler_delayed_cursor_generalization/unlocked_transport/managed_gate_pure" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw in "scheduler_delayed_cursor_generalization/unlocked_transport/managed_gate_raw" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs in "scheduler_delayed_cursor_generalization/unlocked_transport/managed_entry_defs" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Pointer_Bridge
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler in "scheduler_delayed_cursor_generalization/unlocked_transport/managed_entry_assembler" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone in "scheduler_delayed_cursor_generalization/unlocked_transport/prefix_capstone" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Exact
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone in "scheduler_delayed_cursor_generalization/unlocked_transport/pipeline_capstone" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Complete
  theories
    Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone
```

Build in the same order, one Isabelle lane only, and stop at the first red
session.  A checker-green claim is forbidden until every rung has completed
with `quick_and_dirty = false`.

## Static audit

- Ten theory files; each is below 350 lines.
- No `sorry`, `oops`, `admit`, `axiomatization`, `oracle`, `sledgehammer`, or
  `quick_and_dirty` token occurs in a theory file.
- No word-bounded old public `StrongVTaskIncrementTickEntryRel`,
  `StrongSchedulerSnapshotRel`, `DueLoopSchedulerSnapshotRel`,
  `DueLoopStrongHeadRel`, or `StrongDuePrefixLoopHeadRel` occurs.
- No General-to-old cursor-policy adapter is invoked.
- No fixed task, tick, priority, delayed-ring length, heap address, or cursor
  position occurs; the literal priority bound `4` is the frozen configuration
  bound already observed by `TaskObservationRel`.
- No trailing whitespace was found; every theory has one `begin` and one
  terminal `end`.

First expected checker risks are simplifier orientation for the proof-only
canonical tick-entry phase, and the exact imported theorem arity in the
direct General Gate-H replay.  These are proof-script risks, not semantic
weakening permissions.

## Frozen theory hashes

| Rung | Lines | SHA-256 |
|---|---:|---|
| pure entry | 262 | `2C7110771A9E12516A0B22E06CEF4ED112884E65892B4432EB24371A99543420` |
| snapshot core | 196 | `FC0B3ED44EA85D3D6DFD18F3D627A3B4DA82C7BECBE30671824BAAEACFFCE26C` |
| snapshot tasks | 115 | `8E7D7EB36755BCB1B6AE5641B0F184FB3BBBD1A6A8A8D63311A8EB7ED6BB0618` |
| managed Gate-H context | 244 | `777E76FCF4A742BF34C6E2FAFF79DC3DEAC9FBE52DEF74B008639F90D9DFE6EE` |
| managed Gate-H pure | 131 | `E7975E3A61FF7F9F8635AA3882CD2227CF526B81E182BB3DA73C314C66CAAE85` |
| managed Gate-H raw | 240 | `893D0F01BC934789E2A6CB3AB4853C175C0CB6A32D218FC49E9C21A1BD70537C` |
| managed entry definitions | 193 | `E5455A4799024148608C5676BEB399E6846D89240565CA7AC0848745BC973078` |
| managed entry assembler | 239 | `484E5CEA08867B9EE05176BF8086474237E54C55EEAB812B72766AC88F4889A4` |
| generated prefix capstone | 185 | `F4FFEFC39FAC6F3FE08C99025F75D3B2ABE127E423A272027F971EFB271398DF` |
| managed pipeline capstone | 129 | `152CB607A4A7C005DFBA9FB82B18C3FB17C4BF826F3B9493A3D2015365F546F9` |

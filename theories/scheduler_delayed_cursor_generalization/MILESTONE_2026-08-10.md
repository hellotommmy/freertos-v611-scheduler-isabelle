# Cursor-general generated tick milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This milestone removes the historical delayed/suspended/termination cursor
policy from the represented scheduler state used by the generated tick proof.
The proof-only canonical cursor shadow is confined to pure core/time lemmas;
the real raw families, abstract families, heaps, and public poststates retain
their represented cursor values.

## Checked chain

- pointer bridge: `20260810Tcursor-general-pointer-02`;
- six generated due-step sessions, ending in
  `20260810Tcursor-general-due-nonlast-04`;
- nine empty/future terminal sessions, ending in
  `20260810Tcursor-general-terminal-future-finally-01`;
- nine arbitrary managed-while sessions, ending in
  `20260810Tcursor-general-while-complete-04`;
- ten unlocked-prefix/transport sessions, ending in
  `20260810Tcursor-general-unlocked-pipeline-capstone-01`;
- outer generated tick connector:
  `20260810Tcursor-general-outer-tick-05`.

Every session uses `parallel_proofs = 0` and `quick_and_dirty = false`.

## Public results

- `CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_result_full`;
- `CursorGeneralManagedDuePrefixGeneratedEntryRel_finally_complete_exact`;
- `CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally`;
- `CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete`;
- `CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_all_arithmetic_inputs`.

The final arithmetic classification treats the literal generated signed
overflow guard failure as `not succeeds`; it does not pretend that undefined C
arithmetic has a successful result.  Suspended `uxMissedTicks` uses exact
32-bit modular increment, including `UINT_MAX -> 0`.

## Scope boundary

The result is universal over states admitted by the cursor-general entry
relation: task identities, priorities, ticks, list lengths, legal cursors,
heaps, roots, decoder, managed/retired partition, and Event branch remain
symbolic.  It is a sequential generated-source refinement for the frozen
FreeRTOS configuration.  It is not yet a separate boot/API reachability proof
for every concrete runtime state, and it does not claim interrupt-concurrent
linearisation.

Current leaf hashes:

- pointer bridge: `0B27AD5F1E507645F679D9AE913E907C9DD57BA7D5DDBC594BADF6BB3A04B532`;
- outer connector: `C8A283422A541496D92BE0A28C357D7BA671317DBC0943E01063E18CFB52D8D5`.

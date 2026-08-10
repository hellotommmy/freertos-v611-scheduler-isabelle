# Cursor-general public tick boundary and finite trace milestone

Status: **machine-checked with `quick_and_dirty = false`**.

This milestone promotes the cursor-general generated tick theorem from an
internal witness-bearing precondition to a settled public API boundary and
proves arbitrary finite repetition of that one generated source operation.

## Checked results

- `CursorGeneralStrongSchedulerPublicBoundaryRel` packages a complete
  cursor-general scheduler endpoint together with the pending-ready boundary
  invariant.  It describes a running, unmasked, zero-critical-depth public
  boundary; it is not an internal `xTaskResumeAll` replay cutpoint.
- `CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete`
  proves that every arithmetic-defined generated tick call reaches a public
  complete post and re-establishes the same boundary relation for
  `task_increment_tick_modular_abs`.
- `CursorGeneralStrongVTaskIncrementTickPublicEntryRel_all_arithmetic_inputs`
  retains the exact signed-overflow classification: the emitted undefined
  branch has no successful run, while all other unlocked cases and every
  suspended 32-bit modular case have the public post.
- `cursor_general_vTaskIncrementTick_finite_trace` proves arbitrary `n`-call
  composition for every caller-supplied stable relation `Rel` that implies the
  public boundary, supplies the necessary arithmetic-defined condition, and
  is preserved by the checked public post.  The abstract state is exactly
  `task_increment_tick_modular_steps_abs n a`.

No task, priority, tick, list length, list cursor, root, heap address, decoder,
or arithmetic branch is fixed by these statements.

## Checker record

- current boundary closure rebuilt as the parent of
  `20260811Tcursor-general-tick-trace-02`, `quick_and_dirty=false`, and
  finished in 17 s; the final green descendant below imports that exact heap;
- finite trace: `20260811Tcursor-general-tick-trace-08`, exit 0,
  `quick_and_dirty=false`; Isabelle leaf 3 s, wrapper total 261.430 s.

Leaf hashes:

- boundary closure:
  `D6EBCB8D1902C20A9765B30FFDF67B35E12CFCBD303D9E21876056E8ADFDD1CD`;
- finite trace:
  `3FCACF10A967F3709ECEC49EB3ECDA71AD661187A3564AEB8AA43B1A4F6C53DD`.

## Scope boundary

This is a single-root sequential public-boundary trace.  It does not add a
five-root call alphabet, prove `vTaskDelay`, `vTaskDelayUntil`, or
`vTaskSwitchContext` all-branch closure, discharge the nested-critical
`xTaskResumeAll` missed-tick replay, or establish interrupt-concurrent
linearisation.  It also does not claim allocator, task-construction, boot, or
scheduler-start reachability, which remain outside the frozen experiment
charter.

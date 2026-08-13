# Frozen cursor-general generated due-step replay

Status: **machine-checked with `quick_and_dirty = false` on 2026-08-10**.

The six exclusive sessions are registered in `theories/ROOT` and the bounded
build wrapper.  Runs `20260810Tcursor-general-due-bridges-01` through
`20260810Tcursor-general-due-nonlast-04` completed green in dependency order.
The original freeze/check plan below is retained as an audit trail.

## Frozen acceptance surface

The public generated nonlast theorem is:

`CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_result_full`.

It quantifies over arbitrary tasks, ticks, priorities, rings, cursor positions,
raw families, abstract families, heaps admitted by the relations, and both
Event branches.  Its only configuration-specific priority literal is the
existing four-ready-root bound inherited from `GenericRootUniverse`.

The reusable state theorem is:

`CursorGeneralDueLoopStrongHeadRel_managed_gate_result_full_state_core`.

Its entry tail is `Generic task # remaining`, with arbitrary `remaining` and
`future`.  The post phase and next node are definitionally
`due_prefix_exit_phase_of remaining future` and
`due_prefix_next_node_of remaining future`.  The sole extra control-local
premise relates that determined next-node option to a caller-provided
`post_pxTCB`.  Nonlast, last-empty, and last-future wrappers must derive this
pointer fact from their exact generated-source result; it is not permission to
assume a desired heap, family, branch, or abstract poststate.

The thin nonlast state specialization is:

`CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_full_state`.

For terminal reuse, instantiate the core as follows:

- empty: `remaining = []`, `future = []`, `post_pxTCB = NULL`;
- future: `remaining = []`,
  `future = Generic f # map Generic fs`,
  `post_pxTCB = sd_tcb_ptr D f`.

## Exact cursor/family ledger

The real raw post families are exactly:

- `one_due_reentry_generic_raw D C he generic_raw`;
- `one_due_event_raw_after_remove D C branch event_raw`.

The public post names the real abstract post families exactly:

- `one_due_generic_abs_after_insert C S`;
- `one_due_event_abs_after_remove C branch S`.

The checked ancestor equalities identify those with the family components of
`one_due_reentry_snapshot C branch S`.  These transformers apply the real
`list_remove_abs`/insert/Event updates, including the real cursor behavior.

`canonicalize_scheduler_cursors` occurs only in two small content-projection
helpers in the first rung.  There it extracts cursor-insensitive membership
and priority facts from the already-defined proof shadow.  It is never applied
to a raw family, abstract family, coverage relation, role projection, gate,
source state, or public poststate.

## Frozen files

| Rung | File | Lines | SHA-256 |
|---:|---|---:|---|
| G4a | `bridges/Scheduler_Delayed_Cursor_General_Due_Step_Bridges.thy` | 251 | `06D5EA264F704B516155782EDAAF395216712DE3B1208E30E1EE8F5181800D4F` |
| G4b | `role_wake/Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake.thy` | 236 | `CD2F9D05CC09A94DCB901C1C2E1EE74FA9566A4062FADC3D92411956383FA54` |
| G4c | `family_state/Scheduler_Delayed_Cursor_General_Due_Step_Family_State.thy` | 280 | `0B60F475CACE57BA3A8A77496C3967BDA8162DEB54A3D7DAFB7696D482FD2DA3` |
| G4d | `snapshot_state/Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State.thy` | 301 | `4EB201C96D0273E57182EF0B28240C84A67CBED5B424C4913DC97FEF16FD0029` |
| G4e | `strong_state_core/Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core.thy` | 168 | `2E9BBE27E05EE9430E38486EE2C72217D8C2B69D93BAD46A62F257C2C32B541B` |
| G4f | `nonlast_capstone/Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone.thy` | 203 | `B1B7CDBCB703FC1B3F7234ACB09B83B3E4901F8728D35B7D2C88790D2F7CD02C` |

No rung exceeds approximately 350 lines, and every theory has an exclusive
directory.

## Applied ROOT staircase

The following staircase was applied and checked:

```isabelle
session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges in "scheduler_delayed_cursor_generalization/generated_due_step/bridges" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  sessions
    EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Bridges

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake in "scheduler_delayed_cursor_generalization/generated_due_step/role_wake" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Family_State in "scheduler_delayed_cursor_generalization/generated_due_step/family_state" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Family_State

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State in "scheduler_delayed_cursor_generalization/generated_due_step/snapshot_state" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Family_State +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 180]
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core in "scheduler_delayed_cursor_generalization/generated_due_step/strong_state_core" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 120]
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core

session EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone in "scheduler_delayed_cursor_generalization/generated_due_step/nonlast_capstone" =
  EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core +
  options [document = false, quick_and_dirty = false, parallel_proofs = 0,
    timeout = 120]
  theories
    Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone
```

Before checking, the repository wrapper must separately register these six
session names and map them to the same local session root used by the existing
cursor-general preservation and managed generated-nonlast sessions.  That
wrapper change is deliberately outside this freeze.

## Exact first checker order

After applying the ROOT and wrapper registrations above, use one lane only:

1. static forbidden-token, trailing-whitespace, path/import, and quantifier
   scan over only these six `.thy` files;
2. `...Due_Step_Bridges` with a 300-second outer wrapper bound;
3. freeze that heap, then `...Due_Step_Role_Wake` with 300 seconds;
4. freeze that heap, then `...Due_Step_Family_State` with 300 seconds;
5. freeze that heap, then `...Due_Step_Snapshot_State` with 300 seconds;
6. freeze that heap, then `...Due_Step_Strong_State_Core` with 240 seconds;
7. freeze that heap, then `...Due_Step_Nonlast_Capstone` with 240 seconds;
8. inspect the exported theorem propositions and assumptions, then rerun the
   forbidden-token and exact-family/canonical-shadow audits.

On a red rung, repair only the first Isabelle diagnostic and rebuild only that
rung.  Do not raise the timeout before localizing the command.

## Static audit at freeze time

- `git diff --check` over this directory: no error;
- forbidden proof token scan over the six `.thy` files: no hit;
- no old `DueLoopStrongHeadRel` conclusion or old
  `strong_managed_domain_rel` use;
- the only old `due_loop_core_wf` terms are the proof-only canonical shadow in
  the membership/priority helpers;
- no literal task identity, tick, priority value, key, ring length, cursor
  position, heap, address, Event owner, or desired branch is fixed;
- no expected post relation, family, heap, successful run, or branch appears
  as a theorem premise;
- the nonlast result comes from the existing generated full-state theorem and
  `runs_to_weaken`, not from a successful-execution assumption.

These are static findings only, not proof checking.

## First checker risks

1. The first likely type/simplifier risk is transport of `membership_wf` from
   the proof shadow back to the real cursor-bearing state in G4a.
2. The next likely proof-shape risk is unpacking the long exact family-state
   conjunction across the G4c/G4d session boundary.
3. The re-entry abstract-family equalities are oriented explicitly in the
   capstone; a checker may require a targeted `sym`/rewrite rather than the
   frozen small `simp` call.
4. The copied full-family cutpoint conjunct index is intentionally identical
   to the green ancestor, but remains fragile if an imported predicate changes.
5. Cross-session instantiation of the generated source theorem may dominate
   the final rung even though no new VCG is opened.

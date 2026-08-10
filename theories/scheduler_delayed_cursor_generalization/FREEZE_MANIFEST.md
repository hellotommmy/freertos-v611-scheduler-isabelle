# Checked milestone manifest: cursor-general scheduler foundation

Checked date: 2026-08-10 (Asia/Taipei)

The three exclusive child sessions below have been checked with
`quick_and_dirty=false` and `parallel_proofs=0`.  This is a green foundation,
not yet the cursor-general public tick capstone: downstream generated-source
and arbitrary-while wrappers still need cursor-general counterparts.

## Frozen files

| File | Lines | SHA-256 |
|---|---:|---|
| `CURSOR_GENERALIZATION_DESIGN.md` | 251 | `98C36F2BEDA084A65261CFA7A79CD86A9AEC3E48F734D4A2A930A0B067D28143` |
| `invariants/Scheduler_Delayed_Cursor_General_Invariants.thy` | 711 | `404AC7AF839D2801BA3C8420A41B0E29EAE7B2C49A20C36DDA9BABDDB8692B3A` |
| `snapshots/Scheduler_Delayed_Cursor_General_Snapshots.thy` | 454 | `7ECF3F287E9793CCB9816309E15B4A074B1725F3B601816E5C38A62904E15337` |
| `preservation/Scheduler_Delayed_Cursor_General_Preservation.thy` | 299 | `CB4C8624684FB7FDF5C55DA6DA2E0424D7B9F001D87E70541CCD678F1C8356DD` |

## Principal declaration inventory

Cursor algebra and symbolic terminal equations:

- `list_remove_head_cursor_eq_none`
- `list_remove_head_cursor_frame`
- `remove_nodes_prefix_cursor`
- `remove_nodes_prefix_cursor_removed`
- `remove_nodes_prefix_cursor_future`
- `remove_nodes_whole_ring_cursor_none`
- `due_prefix_loop_inv_cursor_ledger`
- `due_prefix_loop_inv_entry_none_cursor_preserved`
- `due_prefix_loop_inv_processed_cursor_becomes_none`
- `due_prefix_loop_inv_future_cursor_preserved`
- `due_prefix_loop_inv_all_due_terminal_cursor_none`

Cursor-policy/content split:

- `role_content_wf`
- `cursor_general_role_wf`
- `cursor_general_core_wf`
- `cursor_general_due_loop_core_wf`
- `CursorGeneralStrongManagedDomainRel`

Proof-only canonical-shadow transport:

- `canonicalize_scheduler_cursors`
- `canonicalize_scheduler_cursors_put_current`
- `canonicalize_scheduler_cursors_add_ready`
- `canonicalize_scheduler_cursors_due_prefix_fold_state`
- `canonicalize_scheduler_cursors_due_prefix_result_step`
- `due_prefix_loop_inv_canonicalize_scheduler_cursors`
- `due_loop_time_wf_canonicalize_scheduler_cursors`
- `cursor_general_due_loop_terminal_core_wf`

General relation interfaces:

- `CursorGeneralStrongSchedulerSnapshotRel`
- `CursorGeneralStrongVTaskIncrementTickEntryRel`
- `CursorGeneralDueLoopSchedulerSnapshotRel`
- `CursorGeneralDueLoopStrongHeadRel`
- `CursorGeneralStrongDuePrefixLoopHeadRel`
- old-to-General adapters for every interface
- General-to-old adapters only under explicit old cursor policies
- `CursorGeneralDueLoopSchedulerSnapshotRel_terminal_strong`
- `CursorGeneralDueLoopStrongHeadRel_terminal_strong`

One-step and wrap preservation:

- `due_prefix_result_step_preserves_cursor_general_core_wf`
- `due_prefix_result_step_preserves_cursor_general_time_wf`
- `CursorGeneralDueLoopStrongHeadRel_result_step_preserves_wf`
- `cursor_general_core_wrap_old_current_cursor_none`
- `tick_role_entry_wrap_cursor_roles`
- `tick_role_entry_no_wrap_cursor_roles`

## Root-policy audit

The General relation does not impose a sentinel/tail cursor policy on ready,
delayed A/B, pending, suspended, termination, or protected external Event
roots.  Each root still has `xlist_wf` through `ring_shape_wf` or the relevant
Generic/Event family coverage, and raw/abstract cursors remain exactly linked
by `raw_xlist_view` and `xlist_relabel`.

The only old `core_wf`, `role_wf`, `due_loop_core_wf`, and
`strong_managed_domain_rel` occurrences in the frozen source are:

1. applied to `canonicalize_scheduler_cursors ...`, a proof-only shadow;
2. old-to-General conservative adapters; or
3. General-to-old specialization theorems with every old cursor policy stated
   explicitly.

No General conclusion is reconstructed as old `core_wf` or old
`StrongSchedulerSnapshotRel` without those specialization premises.

## Machine checks and static audit

- `20260810Tcursor-general-invariants-16`: exit 0, QAD=false, 52.528 s;
- `20260810Tcursor-general-snapshots-01`: exit 0, QAD=false, 65.516 s;
- `20260810Tcursor-general-preservation-09`: exit 0, QAD=false, 52.081 s;

- balanced theory `begin/end`, text blocks, and explicit `proof/qed` counts;
- no trailing whitespace;
- the repository-standard forbidden-proof-token scan returned no hit on the
  three `.thy` files;
- no fixed task, priority, tick, key, cursor position, list length, P2 witness,
  or concrete heap/address in a General theorem;
- physical source files split across three exclusive child-session
  directories with session-qualified parent imports;
- `ROOT` and `scripts/build-list-smoke.ps1` register only these isolated
  checker rungs; legacy green public capstones remain unchanged.

The unlocked branch condition `sa_suspend_depth = 0`, the configured priority
bound `< 4`, and wrap test `tick + 1 = 0` are semantic/configuration branches,
not fixed runtime witnesses.

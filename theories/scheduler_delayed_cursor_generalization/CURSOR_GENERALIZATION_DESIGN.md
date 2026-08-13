# Cursor-general unlocked-tick refinement design

Status: the three foundational sessions are registered and checker-green with
`quick_and_dirty=false`: invariants, relation snapshots, and one-step
core/time preservation.  The downstream generated arbitrary-while, unlocked
prefix, and public outer-tick capstones still target the legacy cursor policy;
they must be replayed before claiming all represented legal cursors at the
public theorem boundary.

## Why the old entry relation is not universal

`raw_xlist_view` equates the abstract cursor with the concrete `pxIndex`, and
`xlist_relabel` relabels that cursor pointwise.  Therefore the cursor in a
`StrongSchedulerSnapshotRel` is not an unobservable proof ghost.

The old chain contains these policies:

- `role_wf`: both delayed cursors are `None`;
- `role_wf`: pending and suspended cursors are canonical tails;
- `strong_managed_domain_rel`: the termination cursor is a canonical tail.

With the configured trace/debug APIs enabled, `vTaskList` and
`vTaskGetRunTimeStats` traverse ready, delayed, suspended, and termination
lists using `listGET_OWNER_OF_NEXT_ENTRY`.  A complete traversal beginning at
cursor `c` finishes at the successor of `c` (skipping the sentinel), not in
general at the sentinel or tail.  Thus legal API post-states can violate every
policy above while retaining `xlist_wf`.

This is a source-level reachability argument, not yet an Isabelle reachability
theorem for those APIs.  The proposed tick theorem remains relation-universal:
it covers every heap/state satisfying the cursor-general representation.  A
separate API-composition theorem should later establish that the debug API
post-state satisfies that relation.

## Exact semantic split

`role_content_wf` retains only:

- Generic/Event root kinds;
- ready-priority agreement;
- no cursor equation.

`cursor_general_core_wf` and `cursor_general_due_loop_core_wf` retain the real
`ring_shape_wf`, so a cursor is still legal: it is `None` or `Some c` for an
actual ring member.  No arbitrary/stale pointer is admitted.

`CursorGeneralStrongManagedDomainRel` retains finite managed-domain,
live-subset, termination `xlist_wf`, Generic kind, and exact retired-task set,
but drops the termination-tail policy.

All family coverage and relabelling predicates remain unchanged.  In
particular, they continue to equate concrete `pxIndex` and the real abstract
cursor exactly.

Root-by-root cursor audit of the proposed General relation:

- ready roots: `ring_shape_wf` + `GenericRootFamilyCoverage`; arbitrary legal
  cursor, unchanged from the old model;
- delayed A/B: `ring_shape_wf` + coverage; no `None` equation;
- pending Event root: `ring_shape_wf` + `EventRootFamilyCoverage`; no tail
  equation in the General relation;
- suspended Generic root: `ring_shape_wf` + coverage; no tail equation;
- termination Generic root: `CursorGeneralStrongManagedDomainRel` + coverage;
  no tail equation;
- every protected external Event root: `EventRootFamilyCoverage` reduces to
  `event_family_root_rep`, which requires `xlist_wf` and exact relabelling but
  has no cursor policy.

`scheduler_role_rel`, scalar/current/boundary relations, payload projections,
and managed task observations contain no hidden list-cursor policy.  The only
remaining `None` pins in `strong_one_due_snapshot_projection` are transaction
scratch options (`ods_captured_generic_key`, `ods_checked_event`), not list
cursors.

The functions `clear_delayed_cursors` and
`canonicalize_scheduler_cursors` are proof shadows only.  They never occur in
a source execution relation, raw family coverage, role projection, or public
post-state.

## Symbolic source-order traces

Let the current delayed ring at loop entry be

`due = [d1, ..., dk]`, `future = [f1, ..., fm]`,

with pairwise-distinct symbolic nodes and no fixed task, priority, tick, key,
or list length.

### Cursor equals the removed head

At a loop head with ring `di # suffix` and cursor `Some di`, `vListRemove`
tests true and writes the physical predecessor.  Because `di` is the ordered
list head, its predecessor is the sentinel.  The abstract transition is:

`Some di -> None`, ring `di # suffix -> suffix`.

All later head removals see cursor `None` and preserve it.

### Cursor is a later due node

If entry cursor is `Some dj`, every removal of `d1, ..., d(j-1)` takes the
false cursor branch and preserves `Some dj`.  When `dj` becomes the head, its
removal takes the true branch and sets the cursor to `None`.  Remaining due
removals preserve `None`.

### Cursor is a future node

If entry cursor is `Some fi`, no due removal targets `fi`.  Every cursor test
is false, so terminal future state retains `Some fi`.  This is the smallest
counterexample to reconstructing the old `role_wf` at a nonempty-future exit.

### Empty terminal

If `future = []`, `xlist_wf` says an entry `Some` cursor names some due node.
That node is eventually removed and the cursor becomes `None`.  Hence an
empty current delayed ring has cursor `None`, but this is a derived terminal
fact rather than an entry assumption.

### Wrap

Role entry swaps semantic current/overflow roles without modifying either
physical list object or cursor.  `time_wf` at maximum tick forces the old
current ring empty, and `xlist_wf` then derives its cursor `None`.  The new
current ring is the old overflow ring and inherits its arbitrary legal cursor.
The subsequent due-prefix ledger applies unchanged.

The exact universal formula proved in the isolated theory is:

`cursor(remove_nodes prefix q) = None`

iff the entry cursor is `None` or names a member of `prefix`; otherwise the
entry `Some` cursor is preserved.  The statement quantifies over the complete
prefix/suffix and node universe.

## Dependency impact

### Definitions that must gain cursor-general counterparts

1. `role_wf`, `core_wf` in `Scheduler_Abstract_Model.thy`.
2. `due_loop_core_wf`, `DueLoopSchedulerSnapshotRel`,
   `DueLoopStrongHeadRel` in `Scheduler_Due_Prefix_Strong_While_Connector.thy`.
3. `strong_managed_domain_rel`, `StrongSchedulerSnapshotRel` in
   `Scheduler_Due_Prefix_Strong_Snapshot_Core.thy`.
4. `StrongDuePrefixLoopHeadRel` in
   `Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat.thy`.
5. `StrongVTaskIncrementTickEntryRel` in
   `Scheduler_Tick_Entry_Strong_Rel.thy`.

The isolated `Scheduler_Delayed_Cursor_General_Snapshots.thy` supplies those
counterparts without editing the stable theories.

### Checked infrastructure that is already cursor-parametric

- `xlist_wf`, `list_remove_abs`, `list_remove_preserves_wf`;
- `raw_vListRemove_general_refines` and raw cursor transfer;
- `xlist_relabel_remove_cursor_preserved`;
- `remove_nodes`, due/future split, arbitrary-prefix fold algebra;
- generated head/owner read and physical pointer bridge;
- raw Generic/Event family coverage and removal preservation;
- `tick_role_entry_abs`, which frames physical list objects.

### One central semantic proof that really changes

`due_prefix_result_step_preserves_due_loop_core_wf` explicitly reconstructs
the two delayed cursor-`None` facts.  Its cursor-general counterpart must
instead prove actual delayed `xlist_wf` after removal.  The isolated
preservation theory does this through a canonical proof shadow plus the real
`list_remove_preserves_wf` theorem; it does not duplicate the large content
proof.

### Downstream relation plumbing that must be replayed

The following ladders mention the old Strong/DueLoop relations and therefore
need thin cursor-general copies/adapters, even though their heap/source facts
do not otherwise depend on cursor policy:

- strong result state assembler and generated-source capstone;
- terminal-empty and terminal-future state/source adapters;
- strong arbitrary-while index/terminal/complete lift;
- managed-gate nonlast, terminal, arbitrary-while, and ML public wrapper;
- unlocked tick snapshot transport, pointer bridge, managed-entry assembler,
  and prefix capstone;
- the final outer tick endpoint.

This is mostly predicate renaming plus use of the new one-step and terminal
lemmas.  It is not honest to claim the current old capstone covers `Some`
cursors until these descendants are rebuilt.

## Theorem ladder

1. **Cursor algebra:** exact head removal and arbitrary prefix cursor formula.
2. **Content/core split:** `role_content_wf`, cursor-general core/due-core, and
   old-policy specialization adapters.
3. **Managed domain:** cursor-general termination relation; old tail policy is
   a specialization only.
4. **Strong snapshots:** cursor-general Strong entry, DueLoop snapshot/head,
   and terminal Strong relation.
5. **One due step:** preserve real `ring_shape_wf`, cursor-general due-core,
   and due-loop time partition.
6. **Arbitrary prefix:** replay nonlast/terminal induction using the new head
   relation; derive future-cursor preservation and empty-terminal `None`.
7. **Unlocked prefix:** transport entry snapshot across tick/role update and
   connect actual physical head/owner to the generalized DueLoop entry.
8. **Public endpoint:** export one theorem over all represented legal cursors;
   retain the old quiescent theorem as a corollary under the old policies.
9. **Reachability composition:** separately prove debug API post-state ->
   cursor-general tick entry.  Do not label this complete until its generated
   source proof is green.

## Proposed exclusive-session staircase and first checker order

No `ROOT` or build-wrapper edit has been made.  The intended three-session
staircase is:

1. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Invariants`
   - exclusive directory: `scheduler_delayed_cursor_generalization/invariants`;
   - parent: `EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector`;
   - additional session dependency:
     `EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold`;
   - one theory: `Scheduler_Delayed_Cursor_General_Invariants`.
2. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Snapshots`
   - exclusive directory: `scheduler_delayed_cursor_generalization/snapshots`;
   - parent: the General Invariants session;
   - additional session dependency:
     `EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary`;
   - one theory: `Scheduler_Delayed_Cursor_General_Snapshots`.
3. `EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation`
   - exclusive directory:
     `scheduler_delayed_cursor_generalization/preservation`;
   - parent: the General Snapshots session;
   - one theory: `Scheduler_Delayed_Cursor_General_Preservation`.

The preservation theory's explicit import of
`Scheduler_Due_Prefix_Strong_Result_Components` is already in the ancestor
Strong-While-Connector heap; it should not be copied into the new session.

First checker order, single lane only:

1. static forbidden-pattern/import/path scan;
2. register and build only General Invariants (`quick_and_dirty=false`,
   `parallel_proofs=0`, 300 s session and bounded outer timeout);
3. repair only its first Isabelle failure, one command at a time; once green,
   freeze that heap;
4. register/build only General Snapshots against the frozen parent;
5. register/build only General Preservation against both frozen parents;
6. run theorem-object/forbidden-pattern audit on the three green leaves;
7. only then begin the downstream Strong/managed/unlocked replay.

Do not place all three theories in one directory/session: changing cursor
algebra would otherwise replay roughly the entire combined development on
every preservation edit.

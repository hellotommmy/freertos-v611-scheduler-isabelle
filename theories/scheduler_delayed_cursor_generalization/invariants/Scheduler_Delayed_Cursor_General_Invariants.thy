theory Scheduler_Delayed_Cursor_General_Invariants
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector.Scheduler_Due_Prefix_Strong_While_Connector"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold.Scheduler_Unlocked_Tick_Scaffold"
begin

text \<open>
  The V6.1.1 list cursor (pxIndex) is mutable traversal state.  Debug APIs such
  as vTaskList and vTaskGetRunTimeStats traverse delayed lists with
  listGET_OWNER_OF_NEXT_ENTRY and may therefore leave a non-sentinel cursor.
  The tick wake loop does not require a sentinel cursor: removing the current
  delayed head changes the cursor only when the cursor denotes that head.

  The same issue applies to the suspended and termination lists, which the
  debug APIs also traverse.  This theory therefore separates all semantic root
  content from cursor policy.  clear_delayed_cursors and the broader
  canonicalize_scheduler_cursors are proof projections only: neither
  is a source transition or is inserted between a raw heap and its abstract
  list family.
\<close>

definition clear_xlist_cursor ::
  "('id, 'key) xlist_abs \<Rightarrow> ('id, 'key) xlist_abs"
where
  "clear_xlist_cursor q = q\<lparr>cursor := None\<rparr>"

definition clear_delayed_cursors ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "clear_delayed_cursors s =
     s\<lparr>sa_delayed_a := clear_xlist_cursor (sa_delayed_a s),
       sa_delayed_b := clear_xlist_cursor (sa_delayed_b s)\<rparr>"

definition canonical_tail_cursor ::
  "('id, 'key) xlist_abs \<Rightarrow> ('id, 'key) xlist_abs"
where
  "canonical_tail_cursor q =
     q\<lparr>cursor :=
       (if ring q = [] then None else Some (last (ring q)))\<rparr>"

definition canonicalize_scheduler_cursors ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "canonicalize_scheduler_cursors s =
     (clear_delayed_cursors s)
       \<lparr>sa_pending := canonical_tail_cursor (sa_pending s),
        sa_suspended := canonical_tail_cursor (sa_suspended s)\<rparr>"

lemma clear_xlist_cursor_fields [simp]:
  "ring (clear_xlist_cursor q) = ring q"
  "cursor (clear_xlist_cursor q) = None"
  "item_key (clear_xlist_cursor q) = item_key q"
  by (simp_all add: clear_xlist_cursor_def)

lemma canonical_tail_cursor_fields [simp]:
  "ring (canonical_tail_cursor q) = ring q"
  "cursor (canonical_tail_cursor q) =
     (if ring q = [] then None else Some (last (ring q)))"
  "item_key (canonical_tail_cursor q) = item_key q"
  by (simp_all add: canonical_tail_cursor_def)

lemma canonical_tail_cursor_wf [simp]:
  "tail_cursor_wf (canonical_tail_cursor q)"
  by (simp add: tail_cursor_wf_def)

lemma canonical_tail_cursor_id:
  assumes tail: "tail_cursor_wf q"
  shows "canonical_tail_cursor q = q"
  using tail
  by (cases q)
     (auto simp: canonical_tail_cursor_def tail_cursor_wf_def)

lemma clear_delayed_cursors_frames [simp]:
  "sa_live (clear_delayed_cursors s) = sa_live s"
  "sa_priority (clear_delayed_cursors s) = sa_priority s"
  "sa_wake (clear_delayed_cursors s) = sa_wake s"
  "sa_event_waiting (clear_delayed_cursors s) = sa_event_waiting s"
  "sa_ready (clear_delayed_cursors s) = sa_ready s"
  "sa_pending (clear_delayed_cursors s) = sa_pending s"
  "sa_suspended (clear_delayed_cursors s) = sa_suspended s"
  "sa_tick (clear_delayed_cursors s) = sa_tick s"
  "sa_missed_ticks (clear_delayed_cursors s) = sa_missed_ticks s"
  "sa_suspend_depth (clear_delayed_cursors s) = sa_suspend_depth s"
  "sa_missed_yield (clear_delayed_cursors s) = sa_missed_yield s"
  "sa_top_ready (clear_delayed_cursors s) = sa_top_ready s"
  "sa_current (clear_delayed_cursors s) = sa_current s"
  "sa_current_role_a (clear_delayed_cursors s) = sa_current_role_a s"
  "sa_overflows (clear_delayed_cursors s) = sa_overflows s"
  "sa_yield_count (clear_delayed_cursors s) = sa_yield_count s"
  by (simp_all add: clear_delayed_cursors_def)

lemma clear_delayed_cursors_physical_rings [simp]:
  "sa_delayed_a (clear_delayed_cursors s) =
     clear_xlist_cursor (sa_delayed_a s)"
  "sa_delayed_b (clear_delayed_cursors s) =
     clear_xlist_cursor (sa_delayed_b s)"
  by (simp_all add: clear_delayed_cursors_def)

lemma clear_delayed_cursors_idempotent [simp]:
  "clear_delayed_cursors (clear_delayed_cursors s) =
     clear_delayed_cursors s"
  by (cases s)
     (simp add: clear_delayed_cursors_def clear_xlist_cursor_def)

lemma clear_delayed_cursors_id:
  assumes a: "cursor (sa_delayed_a s) = None"
    and b: "cursor (sa_delayed_b s) = None"
  shows "clear_delayed_cursors s = s"
  using assms
  by (cases s)
     (simp add: clear_delayed_cursors_def clear_xlist_cursor_def)

lemma current_delayed_ring_clear_delayed_cursors [simp]:
  "current_delayed_ring (clear_delayed_cursors s) =
     clear_xlist_cursor (current_delayed_ring s)"
  by (cases "sa_current_role_a s")
     (simp_all add: current_delayed_ring_def)

lemma overflow_delayed_ring_clear_delayed_cursors [simp]:
  "overflow_delayed_ring (clear_delayed_cursors s) =
     clear_xlist_cursor (overflow_delayed_ring s)"
  by (cases "sa_current_role_a s")
     (simp_all add: overflow_delayed_ring_def)

lemma clear_xlist_cursor_remove [simp]:
  "clear_xlist_cursor (list_remove_abs n q) =
     list_remove_abs n (clear_xlist_cursor q)"
  by (cases q)
     (simp add: clear_xlist_cursor_def list_remove_abs_def)

lemma clear_xlist_cursor_remove_nodes [simp]:
  "clear_xlist_cursor (remove_nodes ns q) =
     remove_nodes ns (clear_xlist_cursor q)"
  unfolding remove_nodes_def
  by (induction ns arbitrary: q) simp_all

lemma remove_nodes_clear_xlist_cursor_ring [simp]:
  "ring (remove_nodes ns (clear_xlist_cursor q)) =
     ring (remove_nodes ns q)"
proof -
  have commute:
    "ring (remove_nodes ns (clear_xlist_cursor q)) =
       ring (clear_xlist_cursor (remove_nodes ns q))"
    by (rule arg_cong[OF sym[OF clear_xlist_cursor_remove_nodes]])
  have field:
    "ring (clear_xlist_cursor (remove_nodes ns q)) =
       ring (remove_nodes ns q)"
    by (rule clear_xlist_cursor_fields(1))
  show ?thesis by (rule trans[OF commute field])
qed

lemma ordered_generic_delayed_ring_clear_xlist_cursor:
  assumes ordered: "ordered_generic_delayed_ring q"
  shows "ordered_generic_delayed_ring (clear_xlist_cursor q)"
  using ordered
  by (auto simp: ordered_generic_delayed_ring_def xlist_wf_def
      generic_ring_def)

lemma clear_delayed_cursors_put_current [simp]:
  "clear_delayed_cursors (put_current_delayed q s) =
     put_current_delayed (clear_xlist_cursor q)
       (clear_delayed_cursors s)"
  by (cases "sa_current_role_a s")
     (simp_all add: clear_delayed_cursors_def clear_xlist_cursor_def
        put_current_delayed_def)

lemma clear_delayed_cursors_add_ready [simp]:
  "clear_delayed_cursors (add_ready_node n s) =
     add_ready_node n (clear_delayed_cursors s)"
  by (cases n; cases s)
     (simp_all add: clear_delayed_cursors_def clear_xlist_cursor_def
        Let_def)

lemma clear_delayed_cursors_fold_add_ready [simp]:
  "clear_delayed_cursors (fold add_ready_node ns s) =
     fold add_ready_node ns (clear_delayed_cursors s)"
  by (induction ns arbitrary: s) simp_all

lemma clear_delayed_cursors_due_prefix_fold_state [simp]:
  "clear_delayed_cursors (due_prefix_fold_state entry processed) =
     due_prefix_fold_state (clear_delayed_cursors entry) processed"
  by (simp add: due_prefix_fold_state_def)

lemma clear_delayed_cursors_due_prefix_result_step [simp]:
  "clear_delayed_cursors
     (due_prefix_result_step_abs entry processed n) =
   due_prefix_result_step_abs (clear_delayed_cursors entry) processed n"
  by (simp add: due_prefix_result_step_abs_def)

lemma canonicalize_scheduler_cursors_frames [simp]:
  "sa_live (canonicalize_scheduler_cursors s) = sa_live s"
  "sa_priority (canonicalize_scheduler_cursors s) = sa_priority s"
  "sa_wake (canonicalize_scheduler_cursors s) = sa_wake s"
  "sa_event_waiting (canonicalize_scheduler_cursors s) = sa_event_waiting s"
  "sa_ready (canonicalize_scheduler_cursors s) = sa_ready s"
  "sa_tick (canonicalize_scheduler_cursors s) = sa_tick s"
  "sa_missed_ticks (canonicalize_scheduler_cursors s) = sa_missed_ticks s"
  "sa_suspend_depth (canonicalize_scheduler_cursors s) = sa_suspend_depth s"
  "sa_missed_yield (canonicalize_scheduler_cursors s) = sa_missed_yield s"
  "sa_top_ready (canonicalize_scheduler_cursors s) = sa_top_ready s"
  "sa_current (canonicalize_scheduler_cursors s) = sa_current s"
  "sa_current_role_a (canonicalize_scheduler_cursors s) = sa_current_role_a s"
  "sa_overflows (canonicalize_scheduler_cursors s) = sa_overflows s"
  "sa_yield_count (canonicalize_scheduler_cursors s) = sa_yield_count s"
  by (simp_all add: canonicalize_scheduler_cursors_def)

lemma canonicalize_scheduler_cursors_list_fields [simp]:
  "sa_delayed_a (canonicalize_scheduler_cursors s) =
     clear_xlist_cursor (sa_delayed_a s)"
  "sa_delayed_b (canonicalize_scheduler_cursors s) =
     clear_xlist_cursor (sa_delayed_b s)"
  "sa_pending (canonicalize_scheduler_cursors s) =
     canonical_tail_cursor (sa_pending s)"
  "sa_suspended (canonicalize_scheduler_cursors s) =
     canonical_tail_cursor (sa_suspended s)"
  by (simp_all add: canonicalize_scheduler_cursors_def)

lemma canonicalize_scheduler_cursors_id:
  assumes a: "cursor (sa_delayed_a s) = None"
    and b: "cursor (sa_delayed_b s) = None"
    and pending: "tail_cursor_wf (sa_pending s)"
    and suspended: "tail_cursor_wf (sa_suspended s)"
  shows "canonicalize_scheduler_cursors s = s"
proof -
  have clear: "clear_delayed_cursors s = s"
    by (rule clear_delayed_cursors_id[OF a b])
  have p: "canonical_tail_cursor (sa_pending s) = sa_pending s"
    by (rule canonical_tail_cursor_id[OF pending])
  have u: "canonical_tail_cursor (sa_suspended s) = sa_suspended s"
    by (rule canonical_tail_cursor_id[OF suspended])
  show ?thesis
    using clear p u
    by (cases s) (simp add: canonicalize_scheduler_cursors_def)
qed

lemma current_delayed_ring_canonicalize_scheduler_cursors [simp]:
  "current_delayed_ring (canonicalize_scheduler_cursors s) =
     clear_xlist_cursor (current_delayed_ring s)"
  by (cases "sa_current_role_a s")
     (simp_all add: current_delayed_ring_def)

lemma overflow_delayed_ring_canonicalize_scheduler_cursors [simp]:
  "overflow_delayed_ring (canonicalize_scheduler_cursors s) =
     clear_xlist_cursor (overflow_delayed_ring s)"
  by (cases "sa_current_role_a s")
     (simp_all add: overflow_delayed_ring_def)

lemma canonicalize_scheduler_cursors_put_current [simp]:
  "canonicalize_scheduler_cursors (put_current_delayed q s) =
     put_current_delayed (clear_xlist_cursor q)
       (canonicalize_scheduler_cursors s)"
  by (cases "sa_current_role_a s")
     (simp_all add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def clear_xlist_cursor_def
        canonical_tail_cursor_def put_current_delayed_def)

lemma canonicalize_scheduler_cursors_add_ready [simp]:
  "canonicalize_scheduler_cursors (add_ready_node n s) =
     add_ready_node n (canonicalize_scheduler_cursors s)"
  by (cases n; cases s)
     (simp_all add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def clear_xlist_cursor_def
        canonical_tail_cursor_def Let_def)

lemma canonicalize_scheduler_cursors_fold_add_ready [simp]:
  "canonicalize_scheduler_cursors (fold add_ready_node ns s) =
     fold add_ready_node ns (canonicalize_scheduler_cursors s)"
  by (induction ns arbitrary: s) simp_all

lemma canonicalize_scheduler_cursors_due_prefix_fold_state [simp]:
  "canonicalize_scheduler_cursors
     (due_prefix_fold_state entry processed) =
   due_prefix_fold_state (canonicalize_scheduler_cursors entry) processed"
  by (simp add: due_prefix_fold_state_def)

lemma canonicalize_scheduler_cursors_due_prefix_result_step [simp]:
  "canonicalize_scheduler_cursors
     (due_prefix_result_step_abs entry processed n) =
   due_prefix_result_step_abs
     (canonicalize_scheduler_cursors entry) processed n"
  by (simp add: due_prefix_result_step_abs_def)

text \<open>
  Exact arbitrary-length cursor ledger.  If the cursor is in the removed head
  prefix, it becomes the sentinel at the iteration that removes that node.  If
  it is in the untouched suffix, it is preserved.  No task identity, list
  length, key, priority, tick, or cursor position is fixed.
\<close>

lemma list_remove_head_cursor_eq_none:
  assumes ring: "ring q = n # rest"
    and at_head: "cursor q = Some n"
  shows "cursor (list_remove_abs n q) = None"
  using assms by (simp add: list_remove_abs_def)

lemma list_remove_head_cursor_frame:
  assumes ring: "ring q = n # rest"
    and not_head: "cursor q \<noteq> Some n"
  shows "cursor (list_remove_abs n q) = cursor q"
  using assms by (simp add: list_remove_abs_def)

lemma remove_nodes_prefix_cursor:
  assumes split: "ring q = removed_nodes @ remaining_nodes"
  shows
    "cursor (remove_nodes removed_nodes q) =
       (case cursor q of
          None \<Rightarrow> None
        | Some c \<Rightarrow>
            if c \<in> set removed_nodes then None else Some c)"
  using split
proof (induction removed_nodes arbitrary: q)
  case Nil
  then show ?case
    by (cases "cursor q") (simp_all add: remove_nodes_def)
next
  case (Cons n removed_nodes)
  have ring_q: "ring q = n # (removed_nodes @ remaining_nodes)"
    using Cons.prems by simp
  have ring_after:
    "ring (list_remove_abs n q) = removed_nodes @ remaining_nodes"
    using ring_q by (simp add: list_remove_abs_def)
  note tail = Cons.IH[OF ring_after]
  show ?case
    using tail ring_q
    by (cases "cursor q")
       (auto simp: remove_nodes_def list_remove_abs_def)
qed

corollary remove_nodes_prefix_cursor_removed:
  assumes split: "ring q = removed_nodes @ remaining_nodes"
    and cursor: "cursor q = Some c"
    and in_removed: "c \<in> set removed_nodes"
  shows "cursor (remove_nodes removed_nodes q) = None"
  using remove_nodes_prefix_cursor[OF split] cursor in_removed by simp

corollary remove_nodes_prefix_cursor_future:
  assumes split: "ring q = removed_nodes @ remaining_nodes"
    and cursor: "cursor q = Some c"
    and future: "c \<in> set remaining_nodes"
    and distinct: "distinct (removed_nodes @ remaining_nodes)"
  shows "cursor (remove_nodes removed_nodes q) = Some c"
proof -
  have "c \<notin> set removed_nodes"
    using future distinct by auto
  then show ?thesis
    using remove_nodes_prefix_cursor[OF split] cursor by simp
qed

corollary remove_nodes_whole_ring_cursor_none:
  assumes wf: "xlist_wf q"
    and ring: "ring q = removed_nodes"
  shows "cursor (remove_nodes removed_nodes q) = None"
proof (cases "cursor q")
  case None
  then show ?thesis
    using remove_nodes_prefix_cursor[of q removed_nodes "[]"] ring by simp
next
  case (Some c)
  have member: "c \<in> set removed_nodes"
    using wf Some ring by (simp add: xlist_wf_def)
  show ?thesis
    by (rule remove_nodes_prefix_cursor_removed[OF _ Some member])
       (use ring in simp)
qed

lemma due_prefix_fold_state_current_cursor:
  assumes split:
    "ring (current_delayed_ring entry) = processed @ remaining_nodes"
  shows
    "cursor (current_delayed_ring
       (due_prefix_fold_state entry processed)) =
       (case cursor (current_delayed_ring entry) of
          None \<Rightarrow> None
        | Some c \<Rightarrow>
            if c \<in> set processed then None else Some c)"
  using remove_nodes_prefix_cursor[OF split]
  by simp

lemma due_prefix_loop_inv_cursor_ledger:
  assumes loop:
    "due_prefix_loop_inv now entry processed remaining future current"
  shows
    "cursor (current_delayed_ring current) =
       (case cursor (current_delayed_ring entry) of
          None \<Rightarrow> None
        | Some c \<Rightarrow>
            if c \<in> set processed then None else Some c)"
proof -
  have current:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have ring:
    "ring (current_delayed_ring entry) =
       processed @ (remaining @ future)"
  proof -
    have due:
      "due_nodes now (current_delayed_ring entry) =
         processed @ remaining"
      by (rule due_prefix_loop_inv_due_splitD[OF loop])
    have whole:
      "ring (current_delayed_ring entry) =
         due_nodes now (current_delayed_ring entry) @ future"
      using loop
      by (simp add: due_prefix_loop_inv_def Let_def)
    show ?thesis using whole due by (simp add: append_assoc)
  qed
  show ?thesis
    using due_prefix_fold_state_current_cursor[OF ring] current by simp
qed

corollary due_prefix_loop_inv_entry_none_cursor_preserved:
  assumes loop:
    "due_prefix_loop_inv now entry processed remaining future current"
    and none: "cursor (current_delayed_ring entry) = None"
  shows "cursor (current_delayed_ring current) = None"
  using due_prefix_loop_inv_cursor_ledger[OF loop] none by simp

corollary due_prefix_loop_inv_processed_cursor_becomes_none:
  assumes loop:
    "due_prefix_loop_inv now entry processed remaining future current"
    and cursor: "cursor (current_delayed_ring entry) = Some n"
    and processed: "n \<in> set processed"
  shows "cursor (current_delayed_ring current) = None"
  using due_prefix_loop_inv_cursor_ledger[OF loop] cursor processed by simp

corollary due_prefix_loop_inv_future_cursor_preserved:
  assumes loop:
    "due_prefix_loop_inv now entry processed remaining future current"
    and cursor: "cursor (current_delayed_ring entry) = Some n"
    and future_member: "n \<in> set future"
  shows "cursor (current_delayed_ring current) = Some n"
proof -
  have ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
    using loop by (simp add: due_prefix_loop_inv_def Let_def)
  have distinct: "distinct (ring (current_delayed_ring entry))"
    using ordered
    by (simp add: ordered_generic_delayed_ring_def xlist_wf_def)
  have whole:
    "ring (current_delayed_ring entry) =
       processed @ (remaining @ future)"
  proof -
    have due:
      "due_nodes now (current_delayed_ring entry) = processed @ remaining"
      by (rule due_prefix_loop_inv_due_splitD[OF loop])
    have ring:
      "ring (current_delayed_ring entry) =
         due_nodes now (current_delayed_ring entry) @ future"
      using loop by (simp add: due_prefix_loop_inv_def Let_def)
    show ?thesis using ring due by (simp add: append_assoc)
  qed
  have not_processed: "n \<notin> set processed"
    using distinct whole future_member by auto
  show ?thesis
    using due_prefix_loop_inv_cursor_ledger[OF loop] cursor not_processed
    by simp
qed

corollary due_prefix_loop_inv_all_due_terminal_cursor_none:
  assumes loop:
    "due_prefix_loop_inv now entry processed [] [] current"
  shows "cursor (current_delayed_ring current) = None"
proof (cases "cursor (current_delayed_ring entry)")
  case None
  then show ?thesis
    by (rule due_prefix_loop_inv_entry_none_cursor_preserved[OF loop])
next
  case (Some n)
  have ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
    using loop by (simp add: due_prefix_loop_inv_def Let_def)
  have wf: "xlist_wf (current_delayed_ring entry)"
    using ordered by (simp add: ordered_generic_delayed_ring_def)
  have due:
    "due_nodes now (current_delayed_ring entry) = processed"
    using due_prefix_loop_inv_due_splitD[OF loop] by simp
  have ring:
    "ring (current_delayed_ring entry) = processed"
    using loop due by (simp add: due_prefix_loop_inv_def Let_def)
  have member: "n \<in> set processed"
    using wf Some ring by (simp add: xlist_wf_def)
  show ?thesis
    by (rule due_prefix_loop_inv_processed_cursor_becomes_none[
          OF loop Some member])
qed

text \<open>
  Cursor policies are separated from semantic root content.  In particular,
  role_content_wf contains no delayed=None, pending=tail, suspended=tail, or
  termination=tail condition.  The real-state ring_shape_wf is the only cursor
  requirement: None is legal, and Some c is legal exactly when c is a member.

  canonicalize_scheduler_cursors is a proof-only shadow satisfying the older
  policies.  It preserves every ring, payload and task observation.  Thus the
  definitions below are semantically the direct cursor-free core predicates,
  while retaining a compact bridge to the already checked old core lemmas.
\<close>

definition role_content_wf :: "'tid scheduler_abs \<Rightarrow> bool"
where
  "role_content_wf a \<longleftrightarrow>
     (\<forall>p<4.
        generic_ring (sa_ready a p) \<and>
        (\<forall>t\<in>generic_task_set (sa_ready a p).
           sa_priority a t = p)) \<and>
     generic_ring (sa_delayed_a a) \<and>
     generic_ring (sa_delayed_b a) \<and>
     event_ring (sa_pending a) \<and>
     generic_ring (sa_suspended a)"

definition cursor_general_role_wf :: "'tid scheduler_abs \<Rightarrow> bool"
where
  "cursor_general_role_wf a \<longleftrightarrow> role_content_wf a"

definition cursor_general_core_wf :: "'tid scheduler_abs \<Rightarrow> bool"
where
  "cursor_general_core_wf a \<longleftrightarrow>
     core_wf (canonicalize_scheduler_cursors a) \<and> ring_shape_wf a"

definition cursor_general_due_loop_core_wf ::
  "'tid scheduler_abs \<Rightarrow> bool"
where
  "cursor_general_due_loop_core_wf a \<longleftrightarrow>
     due_loop_core_wf (canonicalize_scheduler_cursors a) \<and>
     ring_shape_wf a"

lemma role_wf_canonicalize_scheduler_cursors_iff [simp]:
  "role_wf (canonicalize_scheduler_cursors a) \<longleftrightarrow>
   role_content_wf a"
  by (simp add: role_wf_def role_content_wf_def tail_cursor_wf_def
      generic_ring_def event_ring_def)

lemma cursor_general_role_wf_characterization:
  "cursor_general_role_wf a \<longleftrightarrow> role_content_wf a"
  by (simp add: cursor_general_role_wf_def)

lemma role_wf_imp_cursor_general_role_wf:
  assumes role: "role_wf a"
  shows "cursor_general_role_wf a"
  using role
  by (simp add: cursor_general_role_wf_def role_content_wf_def role_wf_def)

lemma cursor_general_role_wf_with_old_policy_imp_role_wf:
  assumes role: "cursor_general_role_wf a"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
  shows "role_wf a"
  using assms
  by (simp add: cursor_general_role_wf_def role_content_wf_def role_wf_def)

lemma core_wf_imp_cursor_general_core_wf:
  assumes core: "core_wf a"
  shows "cursor_general_core_wf a"
proof -
  have role: "role_wf a" and shape: "ring_shape_wf a"
    using core by (simp_all add: core_wf_def)
  have delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
    using role by (simp_all add: role_wf_def)
  have canonical: "canonicalize_scheduler_cursors a = a"
    by (rule canonicalize_scheduler_cursors_id[
          OF delayed_a delayed_b pending suspended])
  show ?thesis using core shape canonical
    by (simp add: cursor_general_core_wf_def)
qed

lemma cursor_general_core_wf_with_old_policy_imp_core_wf:
  assumes core: "cursor_general_core_wf a"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
  shows "core_wf a"
  using core canonicalize_scheduler_cursors_id[
      OF delayed_a delayed_b pending suspended]
  by (simp add: cursor_general_core_wf_def)

lemma due_loop_core_wf_imp_cursor_general:
  assumes core: "due_loop_core_wf a"
  shows "cursor_general_due_loop_core_wf a"
proof -
  have role: "role_wf a" and shape: "ring_shape_wf a"
    using core by (simp_all add: due_loop_core_wf_def)
  have delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
    using role by (simp_all add: role_wf_def)
  have canonical: "canonicalize_scheduler_cursors a = a"
    by (rule canonicalize_scheduler_cursors_id[
          OF delayed_a delayed_b pending suspended])
  show ?thesis using core shape canonical
    by (simp add: cursor_general_due_loop_core_wf_def)
qed

lemma cursor_general_due_loop_core_wf_with_old_policy_imp_old:
  assumes core: "cursor_general_due_loop_core_wf a"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
  shows "due_loop_core_wf a"
  using core canonicalize_scheduler_cursors_id[
      OF delayed_a delayed_b pending suspended]
  by (simp add: cursor_general_due_loop_core_wf_def)

lemma cursor_general_core_wf_ring_shapeD:
  "cursor_general_core_wf a \<Longrightarrow> ring_shape_wf a"
  by (simp add: cursor_general_core_wf_def)

lemma cursor_general_due_loop_core_wf_ring_shapeD:
  "cursor_general_due_loop_core_wf a \<Longrightarrow> ring_shape_wf a"
  by (simp add: cursor_general_due_loop_core_wf_def)

lemma due_prefix_loop_inv_canonicalize_scheduler_cursors:
  assumes loop:
    "due_prefix_loop_inv now entry processed remaining future current"
  shows
    "due_prefix_loop_inv now (canonicalize_scheduler_cursors entry) processed
       remaining future (canonicalize_scheduler_cursors current)"
proof -
  have ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
    using loop by (simp add: due_prefix_loop_inv_def Let_def)
  have ordered_shadow:
    "ordered_generic_delayed_ring
       (clear_xlist_cursor (current_delayed_ring entry))"
    by (rule ordered_generic_delayed_ring_clear_xlist_cursor[OF ordered])
  show ?thesis
    using loop ordered_shadow
    unfolding due_prefix_loop_inv_def ordered_generic_delayed_ring_def
      due_nodes_def due_future_nodes_def xlist_wf_def Let_def
    by auto
qed

lemma due_loop_time_wf_canonicalize_scheduler_cursors [simp]:
  "due_loop_time_wf now remaining future
      (canonicalize_scheduler_cursors a) \<longleftrightarrow>
   due_loop_time_wf now remaining future a"
  by (simp add: due_loop_time_wf_def delayed_key_agrees_def
      ready_task_set_def generic_task_set_def current_delayed_ring_def
      overflow_delayed_ring_def)

lemma time_wf_canonicalize_scheduler_cursors [simp]:
  "time_wf (canonicalize_scheduler_cursors a) \<longleftrightarrow> time_wf a"
  unfolding time_wf_def delayed_key_agrees_def ready_task_set_def
    generic_task_set_def current_delayed_ring_def overflow_delayed_ring_def
  by (cases "sa_current_role_a a")
     (simp_all only: canonicalize_scheduler_cursors_frames
       canonicalize_scheduler_cursors_list_fields clear_xlist_cursor_fields
       canonical_tail_cursor_fields if_True if_False)

lemma cursor_general_due_loop_terminal_core_wf:
  assumes core: "cursor_general_due_loop_core_wf a"
    and time: "due_loop_time_wf now [] future a"
    and tick: "sa_tick a = now"
  shows "cursor_general_core_wf a"
proof -
  have canonical_core:
    "due_loop_core_wf (canonicalize_scheduler_cursors a)"
    and shape: "ring_shape_wf a"
    using core
    by (simp_all add: cursor_general_due_loop_core_wf_def)
  have canonical_time:
    "due_loop_time_wf now [] future (canonicalize_scheduler_cursors a)"
    using time by simp
  have canonical_tick:
    "sa_tick (canonicalize_scheduler_cursors a) = now"
    using tick by simp
  have canonical_full:
    "core_wf (canonicalize_scheduler_cursors a)"
    by (rule due_loop_core_terminal_core_wf[
          OF canonical_core canonical_time canonical_tick])
  show ?thesis
    using canonical_full shape
    by (simp add: cursor_general_core_wf_def)
qed

lemma clear_delayed_cursors_tick_role_entry_abs [simp]:
  "clear_delayed_cursors (tick_role_entry_abs s) =
     tick_role_entry_abs (clear_delayed_cursors s)"
  by (cases s)
     (simp add: clear_delayed_cursors_def clear_xlist_cursor_def
        tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma canonicalize_scheduler_cursors_tick_role_entry_abs [simp]:
  "canonicalize_scheduler_cursors (tick_role_entry_abs s) =
     tick_role_entry_abs (canonicalize_scheduler_cursors s)"
  by (cases s)
     (simp add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def clear_xlist_cursor_def
        canonical_tail_cursor_def tick_role_entry_abs_def
        swap_delayed_roles_def Let_def)

lemma tick_role_entry_abs_delayed_cursor_frames [simp]:
  "cursor (sa_delayed_a (tick_role_entry_abs s)) =
     cursor (sa_delayed_a s)"
  "cursor (sa_delayed_b (tick_role_entry_abs s)) =
     cursor (sa_delayed_b s)"
  by (simp_all add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma tick_role_entry_abs_nonready_cursor_frames [simp]:
  "cursor (sa_pending (tick_role_entry_abs s)) = cursor (sa_pending s)"
  "cursor (sa_suspended (tick_role_entry_abs s)) = cursor (sa_suspended s)"
  by (simp_all add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)

end

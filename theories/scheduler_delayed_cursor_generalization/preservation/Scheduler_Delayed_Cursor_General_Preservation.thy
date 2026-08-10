theory Scheduler_Delayed_Cursor_General_Preservation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Snapshots.Scheduler_Delayed_Cursor_General_Snapshots"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector.Scheduler_Due_Prefix_Strong_Result_Components"
begin

text \<open>
  One arbitrary due-head step for the cursor-general core.  The large existing
  content proof is replayed only on the canonical proof shadow.  The real
  delayed cursor is handled separately by list_remove_preserves_wf; hence a
  future cursor is retained and a cursor equal to the removed head becomes the
  sentinel exactly as vListRemove specifies.
\<close>

theorem due_prefix_result_step_preserves_cursor_general_core_wf:
  assumes core: "cursor_general_due_loop_core_wf current"
    and loop:
      "due_prefix_loop_inv now entry processed
        (Generic task # remaining) future current"
    and pending_empty: "ring (sa_pending current) = []"
  shows
    "cursor_general_due_loop_core_wf
      (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?canonical = canonicalize_scheduler_cursors
  have canonical_core:
    "due_loop_core_wf (?canonical current)"
    and real_shape: "ring_shape_wf current"
    using core
    by (simp_all add: cursor_general_due_loop_core_wf_def)
  have canonical_loop:
    "due_prefix_loop_inv now (?canonical entry) processed
      (Generic task # remaining) future (?canonical current)"
    by (rule due_prefix_loop_inv_canonicalize_scheduler_cursors[OF loop])
  have canonical_pending:
    "ring (sa_pending (?canonical current)) = []"
    using pending_empty by simp
  have canonical_after:
    "due_loop_core_wf
      (due_prefix_result_step_abs (?canonical entry) processed
        (Generic task))"
    by (rule due_prefix_result_step_preserves_due_loop_core_wf[
          OF canonical_core canonical_loop canonical_pending])
  have canonical_after_real:
    "due_loop_core_wf (?canonical ?after)"
    using canonical_after by simp

  have current_eq:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have one_step:
    "?after =
       add_ready_node (Generic task)
         (put_current_delayed
           (list_remove_abs (Generic task)
             (current_delayed_ring current)) current)"
    by (rule due_prefix_result_step_is_one_generic_step[
          OF current_eq refl])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # remaining @ future"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have member:
    "Generic task \<in> set (ring (current_delayed_ring current))"
    using current_ring by simp

  have wf_a: "xlist_wf (sa_delayed_a current)"
    and wf_b: "xlist_wf (sa_delayed_b current)"
    and pending_current: "xlist_wf (sa_pending current)"
    and suspended_current: "xlist_wf (sa_suspended current)"
    using real_shape by (simp_all add: ring_shape_wf_def)
  have wf_current: "xlist_wf (current_delayed_ring current)"
    using wf_a wf_b
    by (simp add: current_delayed_ring_def split: if_splits)
  have removed_wf:
    "xlist_wf
      (list_remove_abs (Generic task) (current_delayed_ring current))"
    by (rule list_remove_preserves_wf[OF wf_current member])
  have after_a: "xlist_wf (sa_delayed_a ?after)"
    using removed_wf wf_a one_step
    by (cases "sa_current_role_a current")
       (simp_all add: put_current_delayed_def current_delayed_ring_def Let_def)
  have after_b: "xlist_wf (sa_delayed_b ?after)"
    using removed_wf wf_b one_step
    by (cases "sa_current_role_a current")
       (simp_all add: put_current_delayed_def current_delayed_ring_def Let_def)

  have canonical_shape: "ring_shape_wf (?canonical ?after)"
    using canonical_after_real
    by (simp add: due_loop_core_wf_def)
  have canonical_ready:
    "\<forall>p<4. xlist_wf (sa_ready (?canonical ?after) p)"
    using canonical_shape by (simp add: ring_shape_wf_def)
  have ready_frame:
    "sa_ready (?canonical ?after) = sa_ready ?after"
    by (rule canonicalize_scheduler_cursors_frames(5))
  have ready:
    "\<forall>p<4. xlist_wf (sa_ready ?after p)"
  proof (intro allI impI)
    fix p :: nat
    assume bound: "p < 4"
    have canonical_p:
      "xlist_wf (sa_ready (?canonical ?after) p)"
      using canonical_ready bound by blast
    have point:
      "sa_ready (?canonical ?after) p = sa_ready ?after p"
      by (rule fun_cong[OF ready_frame])
    show "xlist_wf (sa_ready ?after p)"
      using canonical_p by (simp only: point)
  qed
  have pending: "xlist_wf (sa_pending ?after)"
    using pending_current one_step
    by (cases "sa_current_role_a current")
       (simp_all add: put_current_delayed_def current_delayed_ring_def Let_def)
  have suspended: "xlist_wf (sa_suspended ?after)"
    using suspended_current one_step
    by (cases "sa_current_role_a current")
       (simp_all add: put_current_delayed_def current_delayed_ring_def Let_def)
  have real_after_shape: "ring_shape_wf ?after"
    using ready after_a after_b pending suspended
    by (simp add: ring_shape_wf_def)
  show ?thesis
    using canonical_after_real real_after_shape
    by (simp add: cursor_general_due_loop_core_wf_def)
qed

theorem due_prefix_result_step_preserves_cursor_general_time_wf:
  assumes core: "cursor_general_due_loop_core_wf current"
    and time:
      "due_loop_time_wf now (Generic task # remaining) future current"
    and loop:
      "due_prefix_loop_inv now entry processed
        (Generic task # remaining) future current"
  shows
    "due_loop_time_wf now remaining future
      (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  let ?canonical = canonicalize_scheduler_cursors
  have canonical_core:
    "due_loop_core_wf (?canonical current)"
    using core
    by (simp add: cursor_general_due_loop_core_wf_def)
  have canonical_time:
    "due_loop_time_wf now (Generic task # remaining) future
      (?canonical current)"
    using time by simp
  have canonical_loop:
    "due_prefix_loop_inv now (?canonical entry) processed
      (Generic task # remaining) future (?canonical current)"
    by (rule due_prefix_loop_inv_canonicalize_scheduler_cursors[OF loop])
  have after:
    "due_loop_time_wf now remaining future
      (due_prefix_result_step_abs (?canonical entry) processed
        (Generic task))"
    by (rule due_prefix_result_step_preserves_due_loop_time_wf[
          OF canonical_core canonical_time canonical_loop])
  have shadow_after:
    "due_loop_time_wf now remaining future
      (?canonical
        (due_prefix_result_step_abs entry processed (Generic task)))"
    using after
    by (simp only: canonicalize_scheduler_cursors_due_prefix_result_step)
  show ?thesis
    using shadow_after
    by (simp only: due_loop_time_wf_canonicalize_scheduler_cursors)
qed

corollary CursorGeneralDueLoopStrongHeadRel_result_step_preserves_wf:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
  shows
    "cursor_general_due_loop_core_wf
       (due_prefix_result_step_abs entry processed (Generic task)) \<and>
     due_loop_time_wf now remaining future
       (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now (Generic task # remaining) future"
    by (rule CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong])
  have core: "cursor_general_due_loop_core_wf current"
    and time:
      "due_loop_time_wf now (Generic task # remaining) future current"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have exit:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have pending_empty: "ring (sa_pending current) = []"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have core_after:
    "cursor_general_due_loop_core_wf
      (due_prefix_result_step_abs entry processed (Generic task))"
    by (rule due_prefix_result_step_preserves_cursor_general_core_wf[
          OF core loop pending_empty])
  have time_after:
    "due_loop_time_wf now remaining future
      (due_prefix_result_step_abs entry processed (Generic task))"
    by (rule due_prefix_result_step_preserves_cursor_general_time_wf[
          OF core time loop])
  show ?thesis using core_after time_after by simp
qed

text \<open>
  Entry/wrap cursor facts.  Role entry changes only tick/role scalars and swaps
  which physical delayed root is called current.  It never writes any list
  cursor.  On wrap the old current ring is empty under time_wf and therefore
  has cursor None by xlist_wf; the new current ring is the old overflow ring
  and may carry any legal cursor.
\<close>

lemma cursor_general_core_wrap_old_current_cursor_none:
  assumes core: "cursor_general_core_wf s"
    and wrap: "sa_tick s + 1 = 0"
  shows "cursor (current_delayed_ring s) = None"
proof -
  have canonical_core: "core_wf (canonicalize_scheduler_cursors s)"
    and shape: "ring_shape_wf s"
    using core by (simp_all add: cursor_general_core_wf_def)
  have real_empty: "ring (current_delayed_ring s) = []"
  proof (rule ccontr)
    assume nonempty: "ring (current_delayed_ring s) \<noteq> []"
    then obtain n ns where ring:
      "ring (current_delayed_ring s) = n # ns"
      by (cases "ring (current_delayed_ring s)") auto
    have role:
      "role_wf (canonicalize_scheduler_cursors s)"
      and time: "time_wf (canonicalize_scheduler_cursors s)"
      using canonical_core by (simp_all add: core_wf_def)
    have real_time: "time_wf s"
      using time by (simp only: time_wf_canonicalize_scheduler_cursors)
    have generic:
      "generic_ring (current_delayed_ring s)"
      using role
      by (cases "sa_current_role_a s")
         (simp_all add: role_wf_def current_delayed_ring_def
            generic_ring_def)
    then obtain task where node: "n = Generic task"
      using ring by (auto simp: generic_ring_def)
    have member:
      "task \<in> generic_task_set (current_delayed_ring s)"
      using ring node by (auto simp: generic_task_set_def)
    have temporal:
      "case sa_wake s task of
         None \<Rightarrow> False
       | Some k \<Rightarrow> sa_tick s < k"
      using real_time member
      by (auto simp: time_wf_def generic_task_set_def)
    then obtain k where strict: "sa_tick s < k"
      by (cases "sa_wake s task") auto
    have maximum: "sa_tick s = (-1 :: 32 word)"
      by (rule max_word_wrap[OF wrap])
    have "k \<le> sa_tick s" using maximum by simp
    then show False using strict by auto
  qed
  have wf: "xlist_wf (current_delayed_ring s)"
    using shape
    by (cases "sa_current_role_a s")
       (simp_all add: ring_shape_wf_def current_delayed_ring_def)
  show ?thesis
    using wf real_empty
    by (cases "cursor (current_delayed_ring s)")
       (auto simp: xlist_wf_def)
qed

lemma tick_role_entry_wrap_cursor_roles:
  assumes wrap: "sa_tick s + 1 = 0"
  shows
    "cursor (current_delayed_ring (tick_role_entry_abs s)) =
       cursor (overflow_delayed_ring s) \<and>
     cursor (overflow_delayed_ring (tick_role_entry_abs s)) =
       cursor (current_delayed_ring s)"
  using wrap
  by (simp add: tick_role_entry_abs_def swap_delayed_roles_def
      current_delayed_ring_def overflow_delayed_ring_def Let_def)

lemma tick_role_entry_no_wrap_cursor_roles:
  assumes no_wrap: "sa_tick s + 1 \<noteq> 0"
  shows
    "cursor (current_delayed_ring (tick_role_entry_abs s)) =
       cursor (current_delayed_ring s) \<and>
     cursor (overflow_delayed_ring (tick_role_entry_abs s)) =
       cursor (overflow_delayed_ring s)"
  using no_wrap
  by (simp add: tick_role_entry_abs_def current_delayed_ring_def
      overflow_delayed_ring_def Let_def)

end

theory Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core.Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core"
begin

corollary CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_task_snapshot_case:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
    and due: "tick_due_sequence_abs a = map Generic due_tasks"
    and future:
      "due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic future"
  shows
    "case due_tasks of
       [] \<Rightarrow>
         CursorGeneralStrongSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         CursorGeneralDueLoopSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
           (map Generic (task # due_tail)) (map Generic future)"
  using CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_snapshot_case[
      OF before unlocked arithmetic_defined]
    due future
  by (cases due_tasks) simp_all

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_task_snapshot_transport:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "\<exists>due_tasks future.
       tick_due_sequence_abs a = map Generic due_tasks \<and>
       due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) =
           map Generic future \<and>
       (case due_tasks of
          [] \<Rightarrow>
            CursorGeneralStrongSchedulerSnapshotRel D
              (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
              managed termination external generic_raw generic_abs event_raw
              event_abs K_G K_E S
        | task # due_tail \<Rightarrow>
            CursorGeneralDueLoopSchedulerSnapshotRel D
              (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
              managed termination external generic_raw generic_abs event_raw
              event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
              (map Generic (task # due_tail)) (map Generic future))"
proof -
  have stable:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using before
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have core: "cursor_general_core_wf a"
    using stable
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have phase:
    "due_loop_time_wf (sa_tick (tick_role_entry_abs a))
       (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
    by (rule cursor_general_core_wf_tick_role_entry_due_loop_time[OF core])
  have due_generic:
    "\<forall>n\<in>set (tick_due_sequence_abs a). \<exists>t. n = Generic t"
    using phase by (auto simp: due_loop_time_wf_def)
  have future_generic:
    "\<forall>n\<in>set
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a))).
       \<exists>t. n = Generic t"
    using phase by (auto simp: due_loop_time_wf_def)
  obtain due_tasks where due:
    "tick_due_sequence_abs a = map Generic due_tasks"
    using all_generic_nodes_map[OF due_generic] by blast
  obtain future where future:
    "due_future_nodes (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring (tick_role_entry_abs a)) = map Generic future"
    using all_generic_nodes_map[OF future_generic] by blast
  have snapshots:
    "case due_tasks of
       [] \<Rightarrow>
         CursorGeneralStrongSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         CursorGeneralDueLoopSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
           (map Generic (task # due_tail)) (map Generic future)"
    by (rule
      CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_task_snapshot_case[
        OF before unlocked arithmetic_defined due future])
  show ?thesis
    apply (rule exI[where x=due_tasks])
    apply (rule exI[where x=future])
    using due future snapshots by blast
qed

end

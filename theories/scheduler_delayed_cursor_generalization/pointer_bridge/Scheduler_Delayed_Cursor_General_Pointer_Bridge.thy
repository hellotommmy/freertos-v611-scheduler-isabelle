theory Scheduler_Delayed_Cursor_General_Pointer_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Snapshots.Scheduler_Delayed_Cursor_General_Snapshots"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pointer_Bridge.Scheduler_Unlocked_Tick_Pointer_Bridge"
begin

text \<open>
  The generated tick prefix reads the owner of the physical delayed-list head.
  It does not traverse from pxIndex.  Consequently the checked physical
  pointer bridge depends on the represented ring, count, owner, and root role,
  but places no restriction on any represented list cursor.
\<close>

lemma CursorGeneralStrongSchedulerSnapshotRel_current_pointer_bridge:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have coverage:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs M K_G"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
    and role: "scheduler_role_rel generated_scheduler_roots c a"
    and observation:
      "scheduler_managed_task_observation_rel D ?h a M"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    by (rule unlocked_tick_managed_physical_pointer_bridge[
          OF coverage role projection observation split])
qed

lemma CursorGeneralDueLoopSchedulerSnapshotRel_current_pointer_bridge:
  assumes snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future_nodes"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have coverage:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs M K_G"
    and projection:
      "strong_generic_role_projection a termination generic_abs"
    and role: "scheduler_role_rel generated_scheduler_roots c a"
    and observation:
      "scheduler_managed_task_observation_rel D ?h a M"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  show ?thesis
    by (rule unlocked_tick_managed_physical_pointer_bridge[
          OF coverage role projection observation split])
qed

theorem cursor_general_unlocked_tick_entry_snapshot_pointer_bridge:
  assumes snapshot:
    "case due_tasks of
       [] \<Rightarrow>
         CursorGeneralStrongSchedulerSnapshotRel D c a M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         CursorGeneralDueLoopSchedulerSnapshotRel D c a M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
           now (map Generic (task # due_tail)) (map Generic future)"
    and split:
      "ring (current_delayed_ring a) =
       map Generic due_tasks @ map Generic future"
  shows
    "generated_current_delayed_readable c \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result c)"
proof (cases due_tasks)
  case Nil
  have stable:
    "CursorGeneralStrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using snapshot Nil by simp
  show ?thesis
    by (rule CursorGeneralStrongSchedulerSnapshotRel_current_pointer_bridge[
          OF stable split])
next
  case (Cons task due_tail)
  have loop:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now (map Generic (task # due_tail)) (map Generic future)"
    using snapshot Cons by simp
  show ?thesis
    by (rule CursorGeneralDueLoopSchedulerSnapshotRel_current_pointer_bridge[
          OF loop split])
qed

end

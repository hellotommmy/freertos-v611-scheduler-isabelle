theory Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Decrement_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone.Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone"
begin

text \<open>
  A generated missed-replay body decrements uxMissedTicks only after its tick.
  This child isolates the exact cursor-general representation frame for that
  scalar update.  Family witnesses, managed-domain coverage, roots, cursors,
  and every non-counter scalar remain unchanged.
\<close>

lemma scheduler_current_rel_uxMissedTicks_update [simp]:
  "scheduler_current_rel D
      (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
      (a\<lparr>sa_missed_ticks := n\<rparr>) =
   scheduler_current_rel D c a"
  unfolding scheduler_current_rel_def
  apply (simp only: scheduler_globals_current_missed_tick_update)
  by simp

lemma CursorGeneralStrongSchedulerSnapshotRel_missed_tick_countD:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_missed_tick_updateI:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and count:
    "unat (f (Scheduler_V611_Parse.globals.uxMissedTicks_' c)) = n"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using snapshot count
  unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
  by (simp add:
      CursorGeneralStrongManagedDomainRel_def
      strong_generic_role_projection_def strong_event_role_projection_def
      strong_wake_payload_projection_def strong_one_due_snapshot_projection_def
      scheduler_role_rel_def scheduler_managed_scalar_rel_def
      managed_scheduler_view_def scheduler_scalar_rel_def
      scheduler_boundary_rel_def
      TaskObservationRel_def scheduler_managed_task_observation_rel_def)

lemma CursorGeneralStrongVTaskIncrementTickEntryRel_missed_tick_updateI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and count:
    "unat (f (Scheduler_V611_Parse.globals.uxMissedTicks_' c)) = n"
  shows
    "CursorGeneralStrongVTaskIncrementTickEntryRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "tick_entry_pending_wf a"
    using entry
    by (simp_all add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have snapshot':
    "CursorGeneralStrongSchedulerSnapshotRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_missed_tick_updateI[
          where f=f and n=n, OF snapshot count])
  have pending': "tick_entry_pending_wf (a\<lparr>sa_missed_ticks := n\<rparr>)"
    using pending by (simp add: tick_entry_pending_wf_def)
  show ?thesis
    using snapshot' pending'
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
qed

lemma CursorGeneralStrongVTaskIncrementTickPublicEntryRel_missed_tick_countD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
  shows
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where full:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF entry] .
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using full
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  show ?thesis
    by (rule CursorGeneralStrongSchedulerSnapshotRel_missed_tick_countD[
          OF snapshot])
qed

lemma CursorGeneralStrongVTaskIncrementTickPublicEntryRel_missed_tick_updateI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
    and count:
    "unat (f (Scheduler_V611_Parse.globals.uxMissedTicks_' c)) = n"
  shows
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where full:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF entry] .
  have full':
    "CursorGeneralStrongVTaskIncrementTickEntryRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongVTaskIncrementTickEntryRel_missed_tick_updateI[
          where f=f and n=n, OF full count])
  show ?thesis
    unfolding CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    by (rule full')
qed

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_countD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
proof -
  obtain c0 where c:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  have count:
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c0) =
       sa_missed_ticks a"
    by (rule
      CursorGeneralStrongVTaskIncrementTickPublicEntryRel_missed_tick_countD[
        OF public])
  show ?thesis using c count by simp
qed

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_updateI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and count:
    "unat (f (Scheduler_V611_Parse.globals.uxMissedTicks_' c)) = n"
  shows
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external"
proof -
  obtain c0 where c:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  have shadow_count:
    "unat (f (Scheduler_V611_Parse.globals.uxMissedTicks_' c0)) = n"
    using count c by simp
  have public':
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c0)
       (a\<lparr>sa_missed_ticks := n\<rparr>) managed termination external"
    by (rule
      CursorGeneralStrongVTaskIncrementTickPublicEntryRel_missed_tick_updateI[
        where f=f and n=n, OF public shadow_count])
  show ?thesis
    unfolding CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def
    apply (rule exI[where x=
      "Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c0"])
    using c public'
    by (simp add: scheduler_port_overlay_missed_tick_update)
qed

lemma resume_missed_word_predecessor:
  fixes w :: "32 word"
  assumes count: "unat w = sa_missed_ticks a"
    and positive: "0 < sa_missed_ticks a"
  shows "unat (w - 1) = sa_missed_ticks a - 1"
proof -
  have nonzero: "w \<noteq> 0"
    using count positive by auto
  have predecessor: "Suc (unat (w - 1)) = unat w"
    by (rule Suc_unat_minus_one[OF nonzero])
  show ?thesis using count predecessor positive by arith
qed

corollary
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_decrement_missed_tick:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and positive: "0 < sa_missed_ticks a"
  shows
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
         (\<lambda>w. w - 1) c)
       (a\<lparr>sa_missed_ticks := sa_missed_ticks a - 1\<rparr>)
       managed termination external"
proof -
  have count:
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_countD[
        OF entry])
  have predecessor:
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c - 1) =
       sa_missed_ticks a - 1"
    by (rule resume_missed_word_predecessor[OF count positive])
  show ?thesis
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_updateI[
        where f="\<lambda>w. w - 1" and n="sa_missed_ticks a - 1",
        OF entry predecessor])
qed

end

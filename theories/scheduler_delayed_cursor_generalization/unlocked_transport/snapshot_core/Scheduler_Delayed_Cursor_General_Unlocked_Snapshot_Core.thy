theory Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry.Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Snapshot_Transport.Scheduler_Unlocked_Tick_Snapshot_Transport"
begin

text \<open>
  Complete snapshot transport for the arithmetic/role prefix.  Only the
  well-formedness and managed-domain conjuncts differ from the historical
  transport theorem.  Every heap-backed family, including its exact cursor,
  is the same real family before and after the prefix.
\<close>

lemma CursorGeneralStrongManagedDomainRel_tick_role_entry:
  assumes domain:
    "CursorGeneralStrongManagedDomainRel a termination managed"
  shows
    "CursorGeneralStrongManagedDomainRel
       (tick_role_entry_abs a) termination managed"
  using domain
  by (simp add: CursorGeneralStrongManagedDomainRel_def
      tick_role_entry_abs_def swap_delayed_roles_def Let_def)

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_due_loop_snapshot:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "CursorGeneralDueLoopSchedulerSnapshotRel D
       (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
       managed termination external generic_raw generic_abs event_raw
       event_abs K_G K_E S
       (sa_tick (tick_role_entry_abs a)) (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))"
proof -
  let ?entry_c = "scheduler_tick_role_entry_state c"
  let ?entry = "tick_role_entry_abs a"
  let ?now = "sa_tick ?entry"
  let ?due = "tick_due_sequence_abs a"
  let ?future =
    "due_future_nodes ?now (current_delayed_ring ?entry)"
  let ?old_h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?new_h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?entry_c)"
  have stable:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using before
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have core: "cursor_general_core_wf a"
    and domain0:
      "CursorGeneralStrongManagedDomainRel a termination managed"
    and generic0:
      "GenericRootFamilyCoverage D ?old_h GenericRootUniverse
        generic_raw generic_abs managed K_G"
    and event0:
      "EventRootFamilyCoverage external D ?old_h event_raw event_abs
        managed K_E"
    and generic_projection0:
      "strong_generic_role_projection a termination generic_abs"
    and event_projection0:
      "strong_event_role_projection a managed external event_abs"
    and wake_projection0: "strong_wake_payload_projection a K_G"
    and observation0:
      "scheduler_managed_task_observation_rel D ?old_h a managed"
    and snapshot_projection0:
      "strong_one_due_snapshot_projection a generic_abs event_abs K_G K_E S"
    and role0: "scheduler_role_rel generated_scheduler_roots c a"
    and scalar0: "scheduler_managed_scalar_rel c a managed"
    and current0: "scheduler_current_rel D c a"
    and boundary0: "scheduler_boundary_rel c"
    and cross0:
      "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e (event_raw e) = {}"
    using stable
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have phase:
    "cursor_general_due_loop_core_wf ?entry \<and>
     due_loop_time_wf ?now ?due ?future ?entry"
    using cursor_general_core_wf_tick_role_entry_canonical_phase[OF core]
    by blast
  have domain:
    "CursorGeneralStrongManagedDomainRel ?entry termination managed"
    by (rule CursorGeneralStrongManagedDomainRel_tick_role_entry[OF domain0])
  have generic:
    "GenericRootFamilyCoverage D ?new_h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    using generic0 by simp
  have event:
    "EventRootFamilyCoverage external D ?new_h event_raw event_abs
       managed K_E"
    using event0 by simp
  have generic_projection:
    "strong_generic_role_projection ?entry termination generic_abs"
    by (rule strong_generic_role_projection_tick_role_entry[OF
          generic_projection0])
  have event_projection:
    "strong_event_role_projection ?entry managed external event_abs"
    by (rule strong_event_role_projection_tick_role_entry[OF
          event_projection0])
  have wake_projection: "strong_wake_payload_projection ?entry K_G"
    by (rule strong_wake_payload_projection_tick_role_entry[OF
          wake_projection0])
  have observation:
    "scheduler_managed_task_observation_rel D ?new_h ?entry managed"
  proof -
    have framed:
      "scheduler_managed_task_observation_rel D ?old_h ?entry managed"
      by (rule scheduler_managed_task_observation_rel_tick_role_entry[OF
            observation0])
    show ?thesis using framed by simp
  qed
  have snapshot_projection:
    "strong_one_due_snapshot_projection ?entry generic_abs event_abs
       K_G K_E S"
    by (rule strong_one_due_snapshot_projection_tick_role_entry[OF
          snapshot_projection0])
  have tick: "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a"
    using scalar0
    by (simp add: scheduler_managed_scalar_rel_def scheduler_scalar_rel_def
        managed_scheduler_view_def)
  have role: "scheduler_role_rel generated_scheduler_roots ?entry_c ?entry"
    by (rule scheduler_tick_role_entry_preserves_role_rel[OF role0 tick])
  have scalar: "scheduler_managed_scalar_rel ?entry_c ?entry managed"
    by (rule scheduler_managed_scalar_rel_tick_role_entry[OF scalar0])
  have current: "scheduler_current_rel D ?entry_c ?entry"
    by (rule scheduler_current_rel_tick_role_entry[OF current0])
  have boundary: "scheduler_boundary_rel ?entry_c"
    by (rule scheduler_boundary_rel_tick_role_entry[OF boundary0])
  show ?thesis
    unfolding CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def
    using phase domain generic event generic_projection event_projection
      wake_projection observation snapshot_projection role scalar current
      boundary cross0 unlocked arithmetic_defined
    by blast
qed

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_snapshot_case:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "case tick_due_sequence_abs a of
       [] \<Rightarrow>
         CursorGeneralStrongSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
     | n # ns \<Rightarrow>
         CursorGeneralDueLoopSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
           (sa_tick (tick_role_entry_abs a)) (n # ns)
           (due_future_nodes (sa_tick (tick_role_entry_abs a))
             (current_delayed_ring (tick_role_entry_abs a)))"
proof -
  note loop =
    CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_due_loop_snapshot[
      OF before unlocked arithmetic_defined]
  show ?thesis
  proof (cases "tick_due_sequence_abs a")
    case Nil
    have terminal:
      "CursorGeneralDueLoopSchedulerSnapshotRel D
         (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S (sa_tick (tick_role_entry_abs a)) []
         (due_future_nodes (sa_tick (tick_role_entry_abs a))
           (current_delayed_ring (tick_role_entry_abs a)))"
      using loop Nil by simp
    have stable:
      "CursorGeneralStrongSchedulerSnapshotRel D
         (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S"
      by (rule CursorGeneralDueLoopSchedulerSnapshotRel_terminal_strong[
            OF terminal refl])
    show ?thesis using Nil stable by simp
  next
    case (Cons n ns)
    show ?thesis using Cons loop by simp
  qed
qed

end

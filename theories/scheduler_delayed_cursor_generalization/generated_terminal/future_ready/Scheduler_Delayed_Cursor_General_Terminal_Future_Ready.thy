theory Scheduler_Delayed_Cursor_General_Terminal_Future_Ready
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally.Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally"
begin

lemma cursor_general_managed_task_observation_live_projection:
  assumes observation:
    "scheduler_managed_task_observation_rel D h a managed"
    and domain:
      "CursorGeneralStrongManagedDomainRel a termination managed"
  shows "TaskObservationRel D h a"
proof -
  have managed_observation:
    "TaskObservationRel D h (managed_scheduler_view a managed)"
    using observation
    by (simp add: scheduler_managed_task_observation_rel_def)
  have finite_managed: "finite managed"
    and live_subset: "sa_live a \<subseteq> managed"
    using domain
    by (simp_all add: CursorGeneralStrongManagedDomainRel_def)
  have finite_live: "finite (sa_live a)"
    by (rule finite_subset[OF live_subset finite_managed])
  show ?thesis
    unfolding TaskObservationRel_def
  proof (rule conjI)
    show "finite (sa_live a)" by (rule finite_live)
  next
    show "\<forall>t\<in>sa_live a.
      c_guard (sd_tcb_ptr D t) \<and>
      c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
      c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
      sa_priority a t < 4 \<and>
      unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
      Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val h (sd_tcb_ptr D t)) < 4 \<and>
      Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
        (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
          PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
            (sd_tcb_ptr D t) \<and>
      Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
        (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
          PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
            (sd_tcb_ptr D t)"
    proof (intro ballI)
      fix t
      assume live: "t \<in> sa_live a"
      have managed: "t \<in> managed"
        by (rule subsetD[OF live_subset live])
      have managed_live:
        "t \<in> sa_live (managed_scheduler_view a managed)"
        using managed by (simp add: managed_scheduler_view_def)
      note observed = TaskObservationRel_liveD[
        OF managed_observation managed_live]
      have observed':
        "c_guard (sd_tcb_ptr D t) \<and>
         c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
         c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
         sa_priority a t < 4 \<and>
         unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
         Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val h (sd_tcb_ptr D t)) < 4 \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
           (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
             PTR_COERCE(
               Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
               (sd_tcb_ptr D t) \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
           (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
             PTR_COERCE(
               Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
               (sd_tcb_ptr D t)"
        using observed by (simp add: managed_scheduler_view_def)
      show
        "c_guard (sd_tcb_ptr D t) \<and>
         c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
         c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
         sa_priority a t < 4 \<and>
         unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
         Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val h (sd_tcb_ptr D t)) < 4 \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
           (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
             PTR_COERCE(
               Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
               (sd_tcb_ptr D t) \<and>
         Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
           (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
             PTR_COERCE(
               Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
               (sd_tcb_ptr D t)"
        by (rule observed')
    qed
  qed
qed

text \<open>
  Only the abstract core/time component is inspected through its canonical
  proof shadow below.  The real raw family, real abstract family, and concrete
  heap remain exactly those in the cursor-general snapshot.
\<close>

lemma CursorGeneralStrongDuePrefixLoopHeadRel_managed_terminal_future_ready:
  assumes head:
    "CursorGeneralStrongDuePrefixLoopHeadRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] (Generic f # map Generic fs)
       phase next pxTCB"
  shows "due_prefix_future_source_ready D c now current f (K_G f)"
proof -
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and exit:
      "due_prefix_exit_inv now entry processed []
         (Generic f # map Generic fs) current phase next"
    and abstract_tick: "sa_tick current = now"
    using head
    by (simp_all add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
  have base:
    "due_prefix_loop_inv now entry processed []
       (Generic f # map Generic fs) current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have ring:
    "ring (current_delayed_ring current) = Generic f # map Generic fs"
    using due_prefix_loop_inv_ringD[OF base] by simp
  have member:
    "Generic f \<in> set (ring (current_delayed_ring current))"
    using ring by simp
  have core: "cursor_general_core_wf current"
    and domain:
      "CursorGeneralStrongManagedDomainRel current termination managed"
    and coverage:
      "GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         GenericRootUniverse generic_raw generic_abs managed K_G"
    and wake: "strong_wake_payload_projection current K_G"
    and managed_observation:
      "scheduler_managed_task_observation_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) current managed"
    and scalar: "scheduler_managed_scalar_rel c current managed"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have shadow: "core_wf (canonicalize_scheduler_cursors current)"
    using core by (simp add: cursor_general_core_wf_def)
  have shadow_member:
    "Generic f \<in> set (ring
       (current_delayed_ring (canonicalize_scheduler_cursors current)))"
    using member by simp
  have live: "f \<in> sa_live current"
    using core_wf_current_delayed_member_live[OF shadow shadow_member]
    by simp
  have live_subset: "sa_live current \<subseteq> managed"
    using domain by (simp add: CursorGeneralStrongManagedDomainRel_def)
  have managed_task: "f \<in> managed"
    by (rule subsetD[OF live_subset live])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) current"
    by (rule cursor_general_managed_task_observation_live_projection[
          OF managed_observation domain])
  have tick:
    "Scheduler_V611_Parse.globals.xTickCount_' c = now"
    using scalar abstract_tick
    by (simp add: scheduler_managed_scalar_rel_def scheduler_scalar_rel_def
        managed_scheduler_view_def)
  have physical_key:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = K_G f"
    using GenericRootFamilyCoverage_physical_keyD[OF coverage managed_task]
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  have wake_from_ring:
    "sa_wake current f =
       Some (item_key (current_delayed_ring current) (Generic f))"
    using core_wf_current_delayed_key[OF shadow shadow_member] by simp
  have delayed_member:
    "f \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using member
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have wake_from_payload: "sa_wake current f = Some (K_G f)"
    using wake live delayed_member
    by (simp add: strong_wake_payload_projection_def)
  have key_eq:
    "item_key (current_delayed_ring current) (Generic f) = K_G f"
    using wake_from_ring wake_from_payload by simp
  have future_key:
    "now < item_key (current_delayed_ring current) (Generic f)"
    using due_prefix_future_head_exception_exit[OF base] by simp
  have future: "now < K_G f" using future_key key_eq by simp
  show ?thesis
    using observation live tick physical_key future
    by (simp add: due_prefix_future_source_ready_def)
qed

end

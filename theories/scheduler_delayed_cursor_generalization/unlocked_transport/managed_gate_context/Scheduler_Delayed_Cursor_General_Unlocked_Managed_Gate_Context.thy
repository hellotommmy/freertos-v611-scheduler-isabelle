theory Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks.Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges.Scheduler_Delayed_Cursor_General_Due_Step_Bridges"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Capstone.Scheduler_Due_Prefix_Managed_Gate_Capstone"
begin

lemma CursorGeneralDueLoopStrongHeadRel_due_head_live:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
  shows "task \<in> sa_live current"
proof -
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now (Generic task # remaining) future"
    by (rule CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong])
  have exit:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using current_ring
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have general_core: "cursor_general_due_loop_core_wf current"
    using snapshot
    by (simp add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have membership: "membership_wf current"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF general_core])
  show ?thesis
    using membership delayed
    by (auto simp: membership_wf_def Let_def)
qed

lemma CursorGeneralDueLoopStrongHeadRel_canonical_all_ready_destinations:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_all_ready_destinations
       (due_prefix_canonical_managed_context R c current managed
         external K_E task)"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have observation:
    "TaskObservationRel D ?h (managed_scheduler_view current managed)"
    and role: "scheduler_role_rel generated_scheduler_roots c current"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def Let_def)
  show ?thesis
    unfolding one_due_all_ready_destinations_def
  proof (intro ballI)
    fix t
    assume managed: "t \<in> odc_live ?C"
    have managed': "t \<in> managed" using managed by simp
    note observed = TaskObservationRel_liveD[OF observation]
    have priority_bound: "sa_priority current t < 4"
      using observed[of t] managed'
      by (simp add: managed_scheduler_view_def)
    have target:
      "abi_list_ptr (sr_ready R (sa_priority current t))
         \<in> GenericRootUniverse"
      using GenericRootUniverse_readyI[OF priority_bound] roots by simp
    have different:
      "abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) \<noteq>
       abi_list_ptr (sr_ready R (sa_priority current t))"
      using role roots
        generated_ready_raw_root_neq_delayed_a[OF priority_bound]
        generated_ready_raw_root_neq_delayed_b[OF priority_bound]
      by (cases "sa_current_role_a current")
         (auto simp: scheduler_role_rel_def)
    show
      "odc_ready_root ?C (odc_priority ?C t) \<in> odc_generic_roots ?C \<and>
       odc_delayed_root ?C \<noteq>
         odc_ready_root ?C (odc_priority ?C t)"
      using target different by simp
  qed
qed

lemma CursorGeneralDueLoopStrongHeadRel_canonical_context_wf:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_context_wf
       (due_prefix_canonical_managed_context R c current managed
         external K_E task)"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have domain:
    "CursorGeneralStrongManagedDomainRel current termination managed"
    and role: "scheduler_role_rel generated_scheduler_roots c current"
    and event_coverage:
      "EventRootFamilyCoverage external D
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
        event_raw event_abs managed K_E"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have finite_managed: "finite managed"
    and live_subset: "sa_live current \<subseteq> managed"
    using domain
    by (simp_all add: CursorGeneralStrongManagedDomainRel_def)
  have task_live: "task \<in> sa_live current"
    by (rule CursorGeneralDueLoopStrongHeadRel_due_head_live[OF strong])
  have task_managed: "task \<in> managed"
    by (rule subsetD[OF live_subset task_live])
  have delayed_root:
    "abi_list_ptr
       (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)
       \<in> GenericRootUniverse"
  proof (cases "sa_current_role_a current")
    case True
    then show ?thesis
      using role GenericRootUniverse_delayed_aI
      by (simp add: scheduler_role_rel_def)
  next
    case False
    then show ?thesis
      using role GenericRootUniverse_delayed_bI
      by (simp add: scheduler_role_rel_def)
  qed
  have external_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
  have finite_event: "finite (EventRootUniverse external)"
    by (rule EventRootUniverse_finite[OF external_wf])
  have destinations: "one_due_all_ready_destinations ?C"
    by (rule
      CursorGeneralDueLoopStrongHeadRel_canonical_all_ready_destinations[
        OF strong roots])
  have task_destination:
    "odc_ready_root ?C (odc_priority ?C task)
        \<in> odc_generic_roots ?C \<and>
     odc_delayed_root ?C \<noteq>
        odc_ready_root ?C (odc_priority ?C task)"
    by (rule one_due_all_ready_destinationsD[OF destinations])
       (use task_managed in simp)
  have pending:
    "abi_list_ptr (sr_pending R) \<in> EventRootUniverse external"
    using roots EventRootUniverse_pendingI
    by (simp add: GeneratedPendingEventRoot_def)
  show ?thesis
    unfolding one_due_context_wf_def
    using finite_managed task_managed delayed_root finite_event
      task_destination pending
    by (simp add: one_due_target_root_def)
qed

lemma CursorGeneralDueLoopStrongHeadRel_canonical_managed_cross_ledger:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current managed
       external K_E task"
  shows
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"
proof -
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have exit:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    and tick: "sa_tick current = now"
    using strong by (simp_all add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have role: "scheduler_role_rel generated_scheduler_roots c current"
    and generic_role:
      "strong_generic_role_projection current termination generic_abs"
    and event_role:
      "strong_event_role_projection current managed external event_abs"
    and snapshot_generic: "ods_generic_family S = generic_abs"
    and snapshot_event: "ods_event_family S = event_abs"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using role generic_role snapshot_generic
    by (cases "sa_current_role_a current")
       (simp_all add: C_def scheduler_role_rel_def
          strong_generic_role_projection_def current_delayed_ring_def)
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    using event_role snapshot_event
    by (simp add: strong_event_role_projection_def)
  have pending_before: "ring (sa_pending current) = []"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have pending:
    "ring (ods_event_family S (odc_pending_root C)) = []"
    using pending_projection pending_before roots
    by (simp add: C_def GeneratedPendingEventRoot_def)
  have destinations: "one_due_all_ready_destinations C"
    unfolding C_def
    by (rule
      CursorGeneralDueLoopStrongHeadRel_canonical_all_ready_destinations[
        OF strong roots])
  show ?thesis
    using loop tick delayed destinations pending
    by (simp add: C_def)
qed

end

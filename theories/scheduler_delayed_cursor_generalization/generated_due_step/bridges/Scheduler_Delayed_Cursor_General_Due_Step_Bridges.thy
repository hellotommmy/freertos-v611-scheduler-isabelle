theory Scheduler_Delayed_Cursor_General_Due_Step_Bridges
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation.Scheduler_Delayed_Cursor_General_Preservation"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source.Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source"
begin

text \<open>
  Content-only projections from the cursor-general core.  The canonical state
  is used solely to recover cursor-insensitive membership and priority facts.
  No raw or abstract family is rewritten to that proof shadow.
\<close>

lemma cursor_general_due_loop_core_wf_membershipD:
  assumes core: "cursor_general_due_loop_core_wf a"
  shows "membership_wf a"
proof -
  have shadow:
    "due_loop_core_wf (canonicalize_scheduler_cursors a)"
    using core by (simp add: cursor_general_due_loop_core_wf_def)
  have membership:
    "membership_wf (canonicalize_scheduler_cursors a)"
    using shadow by (simp add: due_loop_core_wf_def)
  show ?thesis
    using membership
    unfolding membership_wf_def ready_task_set_def generic_task_set_def
      event_task_set_def Let_def
    by simp
qed

lemma cursor_general_due_loop_core_wf_priorityD:
  assumes core: "cursor_general_due_loop_core_wf a"
    and live: "task \<in> sa_live a"
  shows "sa_priority a task < 4"
proof -
  have shadow:
    "due_loop_core_wf (canonicalize_scheduler_cursors a)"
    using core by (simp add: cursor_general_due_loop_core_wf_def)
  show ?thesis
    using shadow live by (simp add: due_loop_core_wf_def)
qed

lemma CursorGeneralDueLoopStrongHeadRel_managed_gate_root_alignment:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots)) \<and>
     one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority current task)) \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C = GeneratedPendingEventRoot"
proof -
  have local:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  note exact = one_due_gateH_exact_rootsD[OF local]
  have scheduler_role:
    "scheduler_role_rel generated_scheduler_roots c current"
    using strong
    by (simp add: CursorGeneralDueLoopStrongHeadRel_def
        CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have task_local: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have priority:
    "odc_priority C task = sa_priority current task"
    using local task_local selector
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
  have exact_delayed:
      "odc_delayed_root C =
       abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
    using exact by blast
  have exact_target:
      "one_due_target_root C =
       abi_list_ptr (sr_ready R (odc_priority C (odc_task C)))"
    using exact by blast
  have exact_distinct:
      "odc_delayed_root C \<noteq> one_due_target_root C"
    using exact by blast
  have exact_pending:
      "odc_pending_root C = abi_list_ptr (sr_pending R)"
    using exact by blast
  have role_delayed:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
       (if sa_current_role_a current
        then sr_delayed_a generated_scheduler_roots
        else sr_delayed_b generated_scheduler_roots)"
    using scheduler_role by (simp add: scheduler_role_rel_def)
  have aligned_delayed:
      "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
    using exact_delayed role_delayed by simp
  have aligned_target:
      "one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots
           (sa_priority current task))"
    using exact_target priority selector roots by simp
  have aligned_pending:
      "odc_pending_root C = GeneratedPendingEventRoot"
    using exact_pending roots
    by (simp add: GeneratedPendingEventRoot_def)
  show ?thesis
    using aligned_delayed aligned_target exact_distinct aligned_pending
    by blast
qed

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_full_family_cutpoints:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_full_family_cutpoints external D managed C S
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw branch"
proof -
  have local:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have core: "cursor_general_due_loop_core_wf current"
    and generic_coverage:
      "GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         GenericRootUniverse generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         event_raw event_abs managed K_E"
    and event_role:
      "strong_event_role_projection current managed external event_abs"
    and projection:
      "strong_one_due_snapshot_projection current generic_abs event_abs
         K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have generic_family: "ods_generic_family S = generic_abs"
    and event_family: "ods_event_family S = event_abs"
    and generic_payload: "ods_generic_payload S = K_G"
    and event_payload: "ods_event_payload S = K_E"
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
  have generic_coverage_S:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw (ods_generic_family S)
       managed (ods_generic_payload S)"
    using generic_coverage generic_family generic_payload by simp
  have event_coverage_S:
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       event_raw (ods_event_family S) managed (ods_event_payload S)"
    using event_coverage event_family event_payload by simp
  have live_subset: "odc_live C \<subseteq> managed"
    using local
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
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
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using current_ring
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have membership: "membership_wf current"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF core])
  have task_live: "task \<in> sa_live current"
    using membership task_delayed
    by (auto simp: membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    by (rule cursor_general_due_loop_core_wf_priorityD[OF core task_live])
  have alignment:
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots)) \<and>
     one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority current task)) \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C = GeneratedPendingEventRoot"
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_root_alignment[
          OF strong gate selector roots])
  have source_global: "odc_delayed_root C \<in> GenericRootUniverse"
  proof (cases "sa_current_role_a current")
    case True
    then show ?thesis
      using alignment GenericRootUniverse_delayed_aI by simp
  next
    case False
    then show ?thesis
      using alignment GenericRootUniverse_delayed_bI by simp
  qed
  have target_global: "one_due_target_root C \<in> GenericRootUniverse"
    using alignment GenericRootUniverse_readyI[OF priority_bound] by simp
  have pending_before: "ring (sa_pending current) = []"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have event_role_S:
    "strong_event_role_projection current managed external
       (ods_event_family S)"
    using event_role event_family by simp
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    by (rule strong_event_role_pendingD[OF event_role_S])
  have pending_empty:
    "ring (ods_event_family S GeneratedPendingEventRoot) = []"
    using pending_before pending_projection by simp
  show ?thesis
    by (rule one_due_full_family_cutpoint_composition[
          OF local live_subset generic_coverage_S event_coverage_S
             source_global target_global pending_empty])
qed

end

theory Scheduler_Due_Prefix_Managed_Gate_Strong_Bridges
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source.Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source"
begin

text \<open>
  These are the three semantic bridges that cannot be obtained by instantiating
  their legacy counterparts: those counterparts first identify odc_live with
  the runnable state.  Here odc_live is the managed decoder domain, while
  runnable membership of the due head is derived independently from the real
  delayed ring.
\<close>

lemma DueLoopStrongHeadRel_managed_gate_root_alignment:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
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
    by (simp add: DueLoopStrongHeadRel_def DueLoopSchedulerSnapshotRel_def
        Let_def)
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

lemma DueLoopStrongHeadRel_managed_gate_full_family_cutpoints:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
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
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have core: "due_loop_core_wf current"
    and generic_coverage:
      "GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         GenericRootUniverse generic_raw (ods_generic_family S)
         managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         event_raw (ods_event_family S) managed K_E"
    and event_role:
      "strong_event_role_projection current managed external
         (ods_event_family S)"
    using snapshot
    by (simp_all add: DueLoopSchedulerSnapshotRel_def Let_def)
  have payloads:
    "ods_generic_payload S = K_G \<and> ods_event_payload S = K_E"
    using DueLoopStrongHeadRel_shared_snapshot_projectionD[OF strong]
    by blast
  have generic_coverage_S:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw (ods_generic_family S)
       managed (ods_generic_payload S)"
    using generic_coverage payloads by simp
  have event_coverage_S:
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       event_raw (ods_event_family S) managed (ods_event_payload S)"
    using event_coverage payloads by simp
  have live_subset: "odc_live C \<subseteq> managed"
    using local
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
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
  have task_live: "task \<in> sa_live current"
    using core task_delayed
    by (auto simp: due_loop_core_wf_def membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    using core task_live by (simp add: due_loop_core_wf_def)
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
    by (rule DueLoopStrongHeadRel_managed_gate_root_alignment[
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
    using strong by (simp add: DueLoopStrongHeadRel_def)
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    by (rule strong_event_role_pendingD[OF event_role])
  have pending_empty:
    "ring (ods_event_family S GeneratedPendingEventRoot) = []"
    using pending_before pending_projection by simp
  show ?thesis
    by (rule one_due_full_family_cutpoint_composition[
          OF local live_subset generic_coverage_S event_coverage_S
             source_global target_global pending_empty])
qed

theorem DueLoopStrongHeadRel_managed_gate_generic_role_projection:
  assumes strong:
      "DueLoopStrongHeadRel D c current managed termination external
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
    "strong_generic_role_projection
       (due_prefix_result_step_abs entry processed (Generic task))
       termination
       (ods_generic_family (one_due_reentry_snapshot C branch S))"
proof -
  have local:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  have current:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have task_local: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have priority:
    "odc_priority C task = sa_priority current task"
    using local task_local selector
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
  have alignment:
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots)) \<and>
     one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots
           (sa_priority current task)) \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C = GeneratedPendingEventRoot"
    by (rule DueLoopStrongHeadRel_managed_gate_root_alignment[
          OF strong gate selector roots])
  have source:
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
    using alignment by simp
  have target:
    "one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority current task))"
    using alignment by simp
  have core: "due_loop_core_wf current"
    using strong
    by (simp add: DueLoopStrongHeadRel_def
        DueLoopSchedulerSnapshotRel_def Let_def)
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # remaining @ future"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_current_member:
      "Generic task \<in> set (ring (current_delayed_ring current))"
    using current_ring by simp
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
             generic_task_set (sa_delayed_b current)"
    using task_current_member
    by (cases "sa_current_role_a current")
       (simp_all add: generic_task_set_def current_delayed_ring_def)
  have task_live: "task \<in> sa_live current"
    using core task_delayed
    by (auto simp: due_loop_core_wf_def membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    using core task_live by (simp add: due_loop_core_wf_def)
  have pre_role:
    "strong_generic_role_projection current termination generic_abs"
    and pre_wake: "strong_wake_payload_projection current K_G"
    and snapshot_generic: "ods_generic_family S = generic_abs"
    and snapshot_payload: "ods_generic_payload S = K_G"
    using strong
    by (simp_all add: DueLoopStrongHeadRel_def
        DueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have role_S:
    "strong_generic_role_projection current termination
       (ods_generic_family S)"
    using pre_role snapshot_generic by simp
  have wake_task: "sa_wake current task = Some (K_G task)"
    using pre_wake task_live task_delayed
    by (simp add: strong_wake_payload_projection_def)
  have key:
    "ods_generic_payload S task =
       (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w)"
    using snapshot_payload wake_task by simp
  show ?thesis
    by (rule strong_generic_role_projection_one_due_reentry[
          OF current role_S priority_bound selector source target key])
qed

end

theory Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Family_State.Scheduler_Delayed_Cursor_General_Due_Step_Family_State"
begin

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_result_scheduler_snapshot:
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
    "let after =
           due_prefix_result_step_abs entry processed (Generic task);
         h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
         hg = one_due_generic_remove_heap D C h0;
         he = one_due_event_remove_heap D C branch hg;
         generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
         event_raw' =
           one_due_event_raw_after_remove D C branch event_raw;
         S' = one_due_reentry_snapshot C branch S;
         post_c = one_due_tick_ready_inserted_state
           D C branch generic_raw c
     in CursorGeneralDueLoopSchedulerSnapshotRel D post_c after
          managed termination external
          generic_raw' (ods_generic_family S')
          event_raw' (ods_event_family S') K_G K_E S'
          now remaining future"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw_g =
    "one_due_generic_raw_after_remove D C generic_raw"
  let ?hi = "one_due_ready_insert_heap D C ?generic_raw_g ?he"
  let ?post_h = "one_due_ready_insert_heap D C generic_raw ?he"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  let ?post_c =
    "one_due_tick_ready_inserted_state D C branch generic_raw c"

  have local:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have core_before: "cursor_general_due_loop_core_wf current"
    and event_role_before:
      "strong_event_role_projection current managed external event_abs"
    and observation_before:
      "scheduler_managed_task_observation_rel D ?h0 current managed"
    and concrete_role_before:
      "scheduler_role_rel generated_scheduler_roots c current"
    and scalar_before:
      "scheduler_managed_scalar_rel c current managed"
    and current_before: "scheduler_current_rel D c current"
    and boundary_before: "scheduler_boundary_rel c"
    and projection:
      "strong_one_due_snapshot_projection current generic_abs event_abs
         K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have event_family: "ods_event_family S = event_abs"
    and generic_payload: "ods_generic_payload S = K_G"
    and event_payload: "ods_event_payload S = K_E"
    and top_before: "ods_top S = sa_top_ready current"
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
  have event_role_S:
    "strong_event_role_projection current managed external
       (ods_event_family S)"
    using event_role_before event_family by simp

  note family_state =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_result_family_state[
      OF strong gate selector roots, unfolded Let_def]
  have core_after: "cursor_general_due_loop_core_wf ?after"
    and time_after: "due_loop_time_wf now remaining future ?after"
    and domain_after:
      "CursorGeneralStrongManagedDomainRel ?after termination managed"
    and frame: "due_prefix_abstract_control_frame current ?after"
    and generic_post_c:
      "GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
         GenericRootUniverse ?generic_raw' (ods_generic_family ?S')
         managed K_G"
    and event_post_c:
      "EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
         ?event_raw' (ods_event_family ?S') managed K_E"
    and cross_post:
      "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (?generic_raw' g) \<inter>
           raw_xlist_storage e (?event_raw' e) = {}"
    and generic_role_after:
      "strong_generic_role_projection ?after termination
         (ods_generic_family ?S')"
    and event_role_after:
      "strong_event_role_projection ?after managed external
         (ods_event_family ?S')"
    and wake_after: "strong_wake_payload_projection ?after K_G"
    using family_state by blast+

  have exit_before:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop_before:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit_before])
  have current_eq: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop_before])
  have task_C: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have context_managed: "odc_live C = managed"
    using local
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
  have task_managed: "odc_task C \<in> managed"
    using task_C context_managed by simp
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop_before] by simp
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using current_ring
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have membership: "membership_wf current"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF core_before])
  have task_live: "task \<in> sa_live current"
    using membership task_delayed
    by (auto simp: membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    by (rule cursor_general_due_loop_core_wf_priorityD[
          OF core_before task_live])
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
  have source_target_ne:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using alignment by blast
  have source_member:
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using one_due_gateH_pure_entryD[OF local]
    by (simp add: one_due_entry_rel_def)
  have pending_before: "ring (sa_pending current) = []"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    by (rule strong_event_role_pendingD[OF event_role_S])
  have pending_family_empty:
    "ring (ods_event_family S GeneratedPendingEventRoot) = []"
    using pending_before pending_projection by simp
  have families:
    "one_due_full_family_cutpoints external D managed C S ?h0
       generic_raw event_raw branch"
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_full_family_cutpoints[
          OF strong gate selector roots])
  have heap_frame: "?hi = ?post_h"
    by (rule one_due_ready_insert_heap_removed_target_frame[
          OF source_target_ne])

  have observation0:
    "TaskObservationRel D ?h0
       (managed_scheduler_view current managed)"
    using observation_before
    by (simp add: scheduler_managed_task_observation_rel_def)
  have observations:
    "TaskObservationRel D ?he
       (managed_scheduler_view current managed) \<and>
     TaskObservationRel D ?hi
       (managed_scheduler_view current managed)"
    by (rule one_due_full_family_cutpoints_managed_observation[
          OF observation0 families task_managed source_global
             source_member target_global pending_family_empty])
  have observation_he:
    "scheduler_managed_task_observation_rel D ?he current managed"
    using observations
    by (simp add: scheduler_managed_task_observation_rel_def)
  have observation_after_h:
    "scheduler_managed_task_observation_rel D ?post_h ?after managed"
  proof -
    have at_hi:
      "TaskObservationRel D ?hi
         (managed_scheduler_view ?after managed)"
      by (rule TaskObservationRel_managed_view_control_frame[
            OF conjunct2[OF observations] frame])
    show ?thesis
      using at_hi heap_frame
      by (simp add: scheduler_managed_task_observation_rel_def)
  qed
  have observation_post_c:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
       ?after managed"
    using observation_after_h by simp

  have context_priority:
    "odc_priority C (odc_task C) = sa_priority current task"
    using local task_C selector
    by (simp add: one_due_gateH_entry_rel_def Let_def
        managed_scheduler_view_def)
  have top_after:
    "sa_top_ready ?after =
       max (sa_top_ready current) (odc_priority C (odc_task C))"
    using due_prefix_result_step_generic_state_eq[
      OF current_eq, where task=task]
      context_priority selector
    by (cases "sa_current_role_a current")
       (simp_all add: Let_def)
  have snapshot_after:
    "strong_one_due_snapshot_projection ?after
       (ods_generic_family ?S') (ods_event_family ?S')
       K_G K_E ?S'"
    by (rule strong_one_due_snapshot_projection_reentry[
          OF generic_payload event_payload top_before top_after])
  have concrete_role_after:
    "scheduler_role_rel generated_scheduler_roots ?post_c ?after"
    by (rule one_due_tick_ready_inserted_state_role_rel[
          OF concrete_role_before frame])
  have scalar_after:
    "scheduler_managed_scalar_rel ?post_c ?after managed"
    by (rule one_due_tick_ready_inserted_state_managed_scalar_rel[
          OF scalar_before current_eq _ task_managed observation_he])
       (use selector in simp)
  have concrete_current_after:
    "scheduler_current_rel D ?post_c ?after"
    by (rule one_due_tick_ready_inserted_state_current_rel[
          OF current_before frame])
  have concrete_boundary_after: "scheduler_boundary_rel ?post_c"
    by (rule one_due_tick_ready_inserted_state_boundary_rel[
          OF boundary_before])

  have scheduler_snapshot_after:
    "CursorGeneralDueLoopSchedulerSnapshotRel D ?post_c ?after
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now remaining future"
    unfolding CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def
    apply (intro conjI)
    subgoal by (rule core_after)
    subgoal by (rule time_after)
    subgoal by (rule domain_after)
    subgoal by (rule generic_post_c)
    subgoal by (rule event_post_c)
    subgoal by (rule generic_role_after)
    subgoal by (rule event_role_after)
    subgoal by (rule wake_after)
    subgoal by (rule observation_post_c)
    subgoal by (rule snapshot_after)
    subgoal by (rule concrete_role_after)
    subgoal by (rule scalar_after)
    subgoal by (rule concrete_current_after)
    subgoal by (rule concrete_boundary_after)
    subgoal by (rule cross_post)
    done
  show ?thesis
    using scheduler_snapshot_after by (simp add: Let_def)
qed

end

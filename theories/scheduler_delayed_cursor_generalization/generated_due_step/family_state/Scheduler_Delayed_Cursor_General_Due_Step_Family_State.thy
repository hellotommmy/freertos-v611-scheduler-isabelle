theory Scheduler_Delayed_Cursor_General_Due_Step_Family_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake.Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake"
begin

text \<open>
  Exact post-family and abstract-state package for one arbitrary due head.
  The successor tail is wholly symbolic.  All family predicates below use the
  generated post heap and the real re-entry families, including their real
  cursors.
\<close>

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_result_family_state:
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
     in cursor_general_due_loop_core_wf after \<and>
        due_loop_time_wf now remaining future after \<and>
        CursorGeneralStrongManagedDomainRel after termination managed \<and>
        due_prefix_abstract_control_frame current after \<and>
        GenericRootFamilyCoverage D
          (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' post_c))
          GenericRootUniverse generic_raw' (ods_generic_family S')
          managed K_G \<and>
        EventRootFamilyCoverage external D
          (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' post_c))
          event_raw' (ods_event_family S') managed K_E \<and>
        (\<forall>g\<in>GenericRootUniverse.
          \<forall>e\<in>EventRootUniverse external.
            raw_xlist_storage g (generic_raw' g) \<inter>
              raw_xlist_storage e (event_raw' e) = {}) \<and>
        strong_generic_role_projection after termination
          (ods_generic_family S') \<and>
        strong_event_role_projection after managed external
          (ods_event_family S') \<and>
        strong_wake_payload_projection after K_G"
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
  have domain_before:
      "CursorGeneralStrongManagedDomainRel current termination managed"
    and event_role_before:
      "strong_event_role_projection current managed external event_abs"
    and projection:
      "strong_one_due_snapshot_projection current generic_abs event_abs
         K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have event_family: "ods_event_family S = event_abs"
    and generic_payload: "ods_generic_payload S = K_G"
    and event_payload: "ods_event_payload S = K_E"
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
  have event_role_S:
    "strong_event_role_projection current managed external
       (ods_event_family S)"
    using event_role_before event_family by simp

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
  have frame: "due_prefix_abstract_control_frame current ?after"
    by (rule due_prefix_result_step_control_frame[OF current_eq])
  have post_wf:
    "cursor_general_due_loop_core_wf ?after \<and>
     due_loop_time_wf now remaining future ?after"
    by (rule CursorGeneralDueLoopStrongHeadRel_result_step_preserves_wf[
          OF strong])
  have core_after: "cursor_general_due_loop_core_wf ?after"
    and time_after: "due_loop_time_wf now remaining future ?after"
    using post_wf by blast+
  have domain_after:
    "CursorGeneralStrongManagedDomainRel ?after termination managed"
    using domain_before frame
    by (simp add: CursorGeneralStrongManagedDomainRel_def
        due_prefix_abstract_control_frame_def)

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
  have core_before: "cursor_general_due_loop_core_wf current"
    using snapshot
    by (simp add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have membership: "membership_wf current"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF core_before])
  have task_live: "task \<in> sa_live current"
    using membership task_delayed
    by (auto simp: membership_wf_def Let_def)

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
  have source_target_ne:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using alignment by blast
  have families:
    "one_due_full_family_cutpoints external D managed C S ?h0
       generic_raw event_raw branch"
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_full_family_cutpoints[
          OF strong gate selector roots])
  have heap_frame: "?hi = ?post_h"
    by (rule one_due_ready_insert_heap_removed_target_frame[
          OF source_target_ne])

  note family_fact0 =
    families[unfolded one_due_full_family_cutpoints_def Let_def]
  note family_fact1 = conjunct2[OF family_fact0]
  note family_fact2 = conjunct2[OF family_fact1]
  note family_fact3 = conjunct2[OF family_fact2]
  note family_fact4 = conjunct2[OF family_fact3]
  note family_fact5 = conjunct2[OF family_fact4]
  note family_fact6 = conjunct2[OF family_fact5]
  note family_fact7 = conjunct2[OF family_fact6]
  note family_fact8 = conjunct2[OF family_fact7]
  note family_fact9 = conjunct2[OF family_fact8]
  note family_fact10 = conjunct2[OF family_fact9]
  note family_fact11 = conjunct2[OF family_fact10]
  note family_fact12 = conjunct2[OF family_fact11]
  note family_fact13 = conjunct2[OF family_fact12]
  note family_fact14 = conjunct2[OF family_fact13]
  have generic_hi:
    "GenericRootFamilyCoverage D ?hi GenericRootUniverse
       ?generic_raw' (one_due_generic_abs_after_insert C S)
       managed (ods_generic_payload S)"
    by (rule conjunct1[OF family_fact14])
  note family_fact15 = conjunct2[OF family_fact14]
  have event_hi:
    "EventRootFamilyCoverage external D ?hi
       ?event_raw' (one_due_event_abs_after_remove C branch S)
       managed (ods_event_payload S)"
    by (rule conjunct1[OF family_fact15])
  note family_fact16 = conjunct2[OF family_fact15]
  have cross_hi:
    "one_due_family_cross_storage external ?generic_raw' ?event_raw'"
    by (rule conjunct1[OF family_fact16])
  have generic_abs:
    "one_due_generic_abs_after_insert C S = ods_generic_family ?S'"
    by (rule one_due_generic_abs_after_insert_is_reentry)
  have event_abs:
    "one_due_event_abs_after_remove C branch S = ods_event_family ?S'"
    by (rule one_due_event_abs_after_remove_is_reentry)
  have generic_post:
    "GenericRootFamilyCoverage D ?post_h GenericRootUniverse
       ?generic_raw' (ods_generic_family ?S') managed K_G"
    using generic_hi heap_frame generic_payload generic_abs by simp
  have event_post:
    "EventRootFamilyCoverage external D ?post_h
       ?event_raw' (ods_event_family ?S') managed K_E"
    using event_hi heap_frame event_payload event_abs by simp
  have cross_post:
    "\<forall>g\<in>GenericRootUniverse.
      \<forall>e\<in>EventRootUniverse external.
        raw_xlist_storage g (?generic_raw' g) \<inter>
          raw_xlist_storage e (?event_raw' e) = {}"
    using cross_hi
    by (simp add: one_due_family_cross_storage_def)

  have generic_role_after:
    "strong_generic_role_projection ?after termination
       (ods_generic_family ?S')"
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_generic_role_projection[
          OF strong gate selector roots])
  have waiting_after:
    "sa_event_waiting ?after =
       sa_event_waiting current - {odc_task C}"
    using due_prefix_result_step_generic_state_eq[
      OF current_eq, where task=task] selector
    by (cases "sa_current_role_a current")
       (simp_all add: Let_def)
  have event_role_after:
    "strong_event_role_projection ?after managed external
       (ods_event_family ?S')"
    by (rule one_due_full_family_cutpoints_event_role_projection[
          OF families task_managed event_role_S frame waiting_after])
       (use task_live selector in simp)
  have wake_after: "strong_wake_payload_projection ?after K_G"
    by (rule cursor_general_due_loop_wake_projection_from_generic_family[
          OF core_after time_after domain_after generic_post
             generic_role_after])
  have generic_post_c:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
       GenericRootUniverse ?generic_raw' (ods_generic_family ?S')
       managed K_G"
    using generic_post by simp
  have event_post_c:
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
       ?event_raw' (ods_event_family ?S') managed K_E"
    using event_post by simp

  show ?thesis
    unfolding Let_def
    apply (intro conjI)
    subgoal by (rule core_after)
    subgoal by (rule time_after)
    subgoal by (rule domain_after)
    subgoal by (rule frame)
    subgoal by (rule generic_post_c)
    subgoal by (rule event_post_c)
    subgoal by (rule cross_post)
    subgoal by (rule generic_role_after)
    subgoal by (rule event_role_after)
    subgoal by (rule wake_after)
    done
qed

end

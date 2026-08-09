theory Scheduler_Due_Prefix_Strong_Terminal_Future_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone.Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone"
begin

text \<open>
  Stable endpoint carried by the last due Result step when the delayed ring has
  an arbitrary nonempty future suffix.  All witnesses below are deterministic
  functions of the entry witnesses.  In particular, the strong snapshot and
  the source-ready observation share one post heap, one Generic family, one
  Event family, and one one-due snapshot.
\<close>

definition DueLoopStrongTerminalFutureState ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "DueLoopStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       before t \<longleftrightarrow>
     (let after =
          due_prefix_result_step_abs entry processed (Generic task);
          h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before);
          hg = one_due_generic_remove_heap D C h0;
          he = one_due_event_remove_heap D C branch hg;
          generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
          event_raw' =
            one_due_event_raw_after_remove D C branch event_raw;
          S' = one_due_reentry_snapshot C branch S;
          post_c = one_due_tick_ready_inserted_state
            D C branch generic_raw before
      in t = post_c \<and>
         StrongDuePrefixLoopHeadRel D t after managed termination external
           generic_raw' (ods_generic_family S')
           event_raw' (ods_event_family S') K_G K_E S'
           now entry (processed @ [Generic task]) []
           (Generic f # map Generic fs)
           FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
         due_prefix_future_source_ready D t now after f (K_G f))"

text \<open>
  Future readiness is derivable from any stable strong terminal head; it is not
  a source-success or expected-post assumption.  This generalises the old
  zero-due helper to arbitrary processed prefixes and arbitrary endpoints.
\<close>

lemma StrongDuePrefixLoopHeadRel_terminal_future_ready:
  assumes head:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] (Generic f # map Generic fs)
       phase next pxTCB"
  shows "due_prefix_future_source_ready D c now current f (K_G f)"
proof -
  note strong = StrongDuePrefixLoopHeadRel_snapshotD[OF head]
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF head]
  have base:
    "due_prefix_loop_inv now entry processed []
       (Generic f # map Generic fs) current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have ring:
    "ring (current_delayed_ring current) =
       Generic f # map Generic fs"
    using due_prefix_loop_inv_ringD[OF base] by simp
  have member:
    "Generic f \<in> set (ring (current_delayed_ring current))"
    using ring by simp
  have core: "core_wf current"
    by (rule StrongSchedulerSnapshotRel_coreD[OF strong])
  have live: "f \<in> sa_live current"
    by (rule core_wf_current_delayed_member_live[OF core member])
  have domain:
    "strong_managed_domain_rel current termination managed"
    by (rule StrongSchedulerSnapshotRel_domainD[OF strong])
  have live_subset: "sa_live current \<subseteq> managed"
    using domain by (simp add: strong_managed_domain_rel_def)
  have managed_task: "f \<in> managed"
    by (rule subsetD[OF live_subset live])
  have managed_observation:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       current managed"
    by (rule StrongSchedulerSnapshotRel_managed_observationD[OF strong])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) current"
    by (rule scheduler_managed_task_observation_live_projection[
          OF managed_observation domain])
  have scalar_pins:
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick current \<and>
     unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth current \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks current \<and>
     Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield current then 1 else 0) \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready current \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows current) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card managed \<and>
     unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) =
       sa_yield_count current"
    by (rule StrongSchedulerSnapshotRel_scalar_pinsD[OF strong])
  have abstract_tick: "sa_tick current = now"
    by (rule StrongDuePrefixLoopHeadRel_tickD[OF head])
  have tick: "Scheduler_V611_Parse.globals.xTickCount_' c = now"
    using scalar_pins abstract_tick by simp
  have physical_key:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = K_G f"
    using StrongSchedulerSnapshotRel_generic_payloadD[
      OF strong managed_task]
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  have wake_from_ring:
    "sa_wake current f =
       Some (item_key (current_delayed_ring current) (Generic f))"
    by (rule core_wf_current_delayed_key[OF core member])
  have delayed_member:
    "f \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using member
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have wake_from_payload: "sa_wake current f = Some (K_G f)"
    using StrongSchedulerSnapshotRel_wakeD[OF strong live]
      delayed_member by simp
  have key_eq:
    "item_key (current_delayed_ring current) (Generic f) = K_G f"
    using wake_from_ring wake_from_payload by simp
  have future_key:
    "now < item_key (current_delayed_ring current) (Generic f)"
    using due_prefix_future_head_exception_exit[OF base] by simp
  have future: "now < K_G f"
    using future_key key_eq by simp
  show ?thesis
    using observation live tick physical_key future
    by (simp add: due_prefix_future_source_ready_def)
qed

theorem DueLoopStrongHeadRel_last_future_result_full_state:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "DueLoopStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       c (one_due_tick_ready_inserted_state D C branch generic_raw c)"
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
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have core_before: "due_loop_core_wf current"
    and time_before:
      "due_loop_time_wf now [Generic task]
         (Generic f # map Generic fs) current"
    and domain_before:
      "strong_managed_domain_rel current termination managed"
    and generic_role_before:
      "strong_generic_role_projection current termination
         (ods_generic_family S)"
    and event_role_before:
      "strong_event_role_projection current managed external
         (ods_event_family S)"
    and observation_before:
      "scheduler_managed_task_observation_rel D ?h0 current managed"
    and concrete_role_before:
      "scheduler_role_rel generated_scheduler_roots c current"
    and scalar_before:
      "scheduler_managed_scalar_rel c current managed"
    and current_before: "scheduler_current_rel D c current"
    and boundary_before: "scheduler_boundary_rel c"
    using snapshot
    by (simp_all add: DueLoopSchedulerSnapshotRel_def Let_def)
  have snapshot_fields:
    "ods_generic_payload S = K_G \<and>
     ods_event_payload S = K_E \<and>
     ods_top S = sa_top_ready current"
    using DueLoopStrongHeadRel_shared_snapshot_projectionD[OF strong]
    by blast

  note exit_before = DueLoopStrongHeadRel_exitD[OF strong]
  have loop_before:
    "due_prefix_loop_inv now entry processed [Generic task]
       (Generic f # map Generic fs) current"
    by (rule due_prefix_exit_inv_baseD[OF exit_before])
  have current_eq: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop_before])
  have frame: "due_prefix_abstract_control_frame current ?after"
    by (rule due_prefix_result_step_control_frame[OF current_eq])
  have loop_after:
    "due_prefix_loop_inv now entry (processed @ [Generic task]) []
       (Generic f # map Generic fs) ?after"
    by (rule due_prefix_result_step_preserves_inv[OF loop_before])
  have exit_after:
    "due_prefix_exit_inv now entry (processed @ [Generic task]) []
       (Generic f # map Generic fs) ?after
       FutureExit (Some (Generic f))"
    using loop_after by (simp add: due_prefix_exit_inv_def)
  have post_wf:
    "due_loop_core_wf ?after \<and>
     due_loop_time_wf now [] (Generic f # map Generic fs) ?after"
    by (rule DueLoopStrongHeadRel_result_step_preserves_due_loop_wf[
          OF strong])
  have core_after: "due_loop_core_wf ?after"
    and time_after:
      "due_loop_time_wf now [] (Generic f # map Generic fs) ?after"
    using post_wf by blast+
  have domain_after:
    "strong_managed_domain_rel ?after termination managed"
    using domain_before frame
    by (simp add: strong_managed_domain_rel_def
        due_prefix_abstract_control_frame_def)

  have task_C: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have live_eq: "odc_live C = sa_live current"
    by (rule one_due_gateH_live_absD[OF local])
  have task_live: "task \<in> sa_live current"
    using task_C live_eq selector by simp
  have task_managed: "odc_task C \<in> managed"
    using domain_before task_C live_eq
    by (auto simp: strong_managed_domain_rel_def)
  have priority_bound: "sa_priority current task < 4"
    using core_before task_live
    by (simp add: due_loop_core_wf_def)
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
    by (rule DueLoopStrongHeadRel_shared_gate_root_alignment[
          OF strong gate selector roots])
  have source_global: "odc_delayed_root C \<in> GenericRootUniverse"
  proof (cases "sa_current_role_a current")
    case True
    have source_eq:
        "odc_delayed_root C =
         abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
      using alignment True by simp
    show ?thesis using source_eq GenericRootUniverse_delayed_aI by simp
  next
    case False
    have source_eq:
        "odc_delayed_root C =
         abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
      using alignment False by simp
    show ?thesis using source_eq GenericRootUniverse_delayed_bI by simp
  qed
  have target_global: "one_due_target_root C \<in> GenericRootUniverse"
    using alignment GenericRootUniverse_readyI[OF priority_bound] by simp
  have source_target_ne:
    "odc_delayed_root C \<noteq> one_due_target_root C"
    using alignment by blast
  have context_priority:
    "odc_priority C (odc_task C) = sa_priority current task"
    using local task_C selector
    by (simp add: one_due_gateH_entry_rel_def Let_def)
  have source_member:
    "Generic (odc_task C) \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using one_due_gateH_pure_entryD[OF local]
    by (simp add: one_due_entry_rel_def)

  have pending_before: "ring (sa_pending current) = []"
    using strong by (simp add: DueLoopStrongHeadRel_def)
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    by (rule strong_event_role_pendingD[OF event_role_before])
  have pending_family_empty:
    "ring (ods_event_family S GeneratedPendingEventRoot) = []"
    using pending_before pending_projection by simp
  have families:
    "one_due_full_family_cutpoints external D managed C S ?h0
       generic_raw event_raw branch"
    by (rule DueLoopStrongHeadRel_one_due_full_family_cutpoints[
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
  have generic_payload: "ods_generic_payload S = K_G"
    by (rule conjunct1[OF snapshot_fields])
  have snapshot_tail:
    "ods_event_payload S = K_E \<and>
     ods_top S = sa_top_ready current"
    by (rule conjunct2[OF snapshot_fields])
  have event_payload: "ods_event_payload S = K_E"
    by (rule conjunct1[OF snapshot_tail])
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
    by (rule DueLoopStrongHeadRel_result_step_generic_role_projection[
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
          OF families task_managed event_role_before frame waiting_after])
       (use task_live selector in simp)
  have wake_after: "strong_wake_payload_projection ?after K_G"
    by (rule due_loop_wake_projection_from_generic_family[
          OF core_after time_after domain_after generic_post
             generic_role_after])

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
          OF conjunct1[OF snapshot_fields]
             conjunct1[OF conjunct2[OF snapshot_fields]]
             conjunct2[OF conjunct2[OF snapshot_fields]]
             top_after])

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
  have tick_before: "sa_tick current = now"
    and quiet_before: "sa_suspend_depth current = 0"
    using strong by (simp_all add: DueLoopStrongHeadRel_def)
  have tick_after: "sa_tick ?after = now"
    and quiet_after: "sa_suspend_depth ?after = 0"
    and pending_after: "ring (sa_pending ?after) = []"
    using frame tick_before quiet_before pending_before
    by (simp_all add: due_prefix_abstract_control_frame_def)

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
  have observation_post_c:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?post_c))
       ?after managed"
    using observation_after_h by simp
  have loop_snapshot_after:
    "DueLoopSchedulerSnapshotRel D ?post_c ?after managed termination
       external ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now [] (Generic f # map Generic fs)"
    unfolding DueLoopSchedulerSnapshotRel_def Let_def
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
  have stable_snapshot_after:
    "StrongSchedulerSnapshotRel D ?post_c ?after managed termination
       external ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'"
    by (rule DueLoopSchedulerSnapshotRel_terminal_strong[
          OF loop_snapshot_after tick_after])
  have terminal_head:
    "StrongDuePrefixLoopHeadRel D ?post_c ?after managed termination
       external ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) []
       (Generic f # map Generic fs)
       FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
    unfolding StrongDuePrefixLoopHeadRel_def
    apply (intro conjI)
    subgoal by (rule stable_snapshot_after)
    subgoal by (rule exit_after)
    subgoal by (rule tick_after)
    subgoal by (rule quiet_after)
    subgoal by (rule pending_after)
    subgoal by (simp add: strong_due_next_ptr_rel_def)
    done
  have ready:
    "due_prefix_future_source_ready D ?post_c now ?after f (K_G f)"
    by (rule StrongDuePrefixLoopHeadRel_terminal_future_ready[
          OF terminal_head])
  show ?thesis
    unfolding DueLoopStrongTerminalFutureState_def Let_def
    using terminal_head ready by simp
qed

end

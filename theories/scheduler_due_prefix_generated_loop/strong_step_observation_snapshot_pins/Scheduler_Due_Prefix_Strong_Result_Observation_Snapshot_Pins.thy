theory Scheduler_Due_Prefix_Strong_Result_Observation_Snapshot_Pins
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Event_Semantics.Scheduler_Due_Prefix_Strong_Result_Event_Semantics"
    "EAL6_FreeRTOS_V611_Scheduler_Managed_Task_Observation_Cutpoints.Scheduler_Managed_Task_Observation_Cutpoints"
begin

text \<open>
  TaskObservationRel observes only its live domain and the priority function
  from the abstract record.  A due Result step preserves both.  This bridge is
  deliberately stated for the managed view, so tasks represented by the
  termination root remain observed.
\<close>

lemma TaskObservationRel_managed_view_control_frame:
  assumes observation:
    "TaskObservationRel D h (managed_scheduler_view before managed)"
    and frame: "due_prefix_abstract_control_frame before after"
  shows "TaskObservationRel D h (managed_scheduler_view after managed)"
  using observation frame
  by (simp add: TaskObservationRel_def managed_scheduler_view_def
      due_prefix_abstract_control_frame_def)

corollary scheduler_managed_task_observation_control_frame:
  assumes observation:
    "scheduler_managed_task_observation_rel D h before managed"
    and frame: "due_prefix_abstract_control_frame before after"
  shows "scheduler_managed_task_observation_rel D h after managed"
  using TaskObservationRel_managed_view_control_frame[of D h before managed after]
    observation frame
  by (simp add: scheduler_managed_task_observation_rel_def)

text \<open>
  The managed-observation checker uses a branch-free optional Event removal,
  selected directly from pvContainer.  The full-family ledger proves that
  this selector is extensionally the very same Gate-H branch used by the
  generated source step.  Consequently its observation at hi is an
  observation of the exact generated post heap, not of a second successor.
\<close>

lemma managed_due_generic_remove_heap_one_due:
  "managed_due_generic_remove_heap D (odc_task C) h =
     one_due_generic_remove_heap D C h"
  by (simp add: managed_due_generic_remove_heap_def
      one_due_generic_remove_heap_def one_due_generic_raw_ptr_def
      generic_item_raw_ptr_def)

lemma managed_due_generic_raw_after_remove_one_due:
  "managed_due_generic_raw_after_remove D (odc_task C)
       (odc_delayed_root C) generic_raw =
     one_due_generic_raw_after_remove D C generic_raw"
  by (simp add: managed_due_generic_raw_after_remove_def
      one_due_generic_raw_after_remove_is_family_remove)

lemma managed_due_ready_insert_heap_one_due:
  "managed_due_ready_insert_heap D (odc_task C)
       (one_due_target_root C)
       (one_due_generic_raw_after_remove D C generic_raw) he =
     one_due_ready_insert_heap D C
       (one_due_generic_raw_after_remove D C generic_raw) he"
  by (simp add: managed_due_ready_insert_heap_def
      one_due_ready_insert_heap_def one_due_generic_raw_ptr_def
      generic_item_raw_ptr_def)

lemma one_due_ready_insert_heap_removed_target_frame:
  assumes distinct:
    "odc_delayed_root C \<noteq> one_due_target_root C"
  shows
    "one_due_ready_insert_heap D C
       (one_due_generic_raw_after_remove D C generic_raw) he =
     one_due_ready_insert_heap D C generic_raw he"
  using distinct
  by (simp add: one_due_ready_insert_heap_def
      one_due_generic_raw_after_remove_def fun_upd_def)

lemma one_due_full_family_cutpoints_managed_event_heap_eq:
  assumes families:
      "one_due_full_family_cutpoints external D managed C S h
         generic_raw event_raw branch"
  shows
    "managed_due_optional_event_remove_heap D (odc_task C)
       (one_due_generic_remove_heap D C h) =
     one_due_event_remove_heap D C branch
       (one_due_generic_remove_heap D C h)"
proof -
  let ?hg = "one_due_generic_remove_heap D C h"
  have witness:
    "one_due_family_branch_witness D C ?hg event_raw external branch"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  have event_hg:
    "EventRootFamilyCoverage external D ?hg event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  show ?thesis
  proof (cases branch)
    case DueEventNull
    have container:
      "pvContainer_C
        (h_val ?hg (event_item_raw_ptr D (odc_task C))) = NULL"
      using witness DueEventNull
      by (simp add: one_due_family_branch_witness_def)
    show ?thesis
      using DueEventNull container
      by (simp add: managed_due_optional_event_remove_heap_def
          one_due_event_remove_heap_def)
  next
    case (DueEventLinked owner)
    have owner_external: "owner \<in> external"
      and container:
        "pvContainer_C
          (h_val ?hg (event_item_raw_ptr D (odc_task C))) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
      using witness DueEventLinked
      by (simp_all add: one_due_family_branch_witness_def)
    have owner_root: "owner \<in> EventRootUniverse external"
      by (rule EventRootUniverse_externalI[OF owner_external])
    have owner_guard: "c_guard owner"
      using EventRootFamilyCoverage_external_wfD[OF event_hg]
        owner_root
      by (simp add: EventExternalRootInputWF_def)
    have owner_nonnull:
      "PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<noteq> NULL"
      using c_guard_NULL[OF owner_guard] by simp
    show ?thesis
      using DueEventLinked container owner_nonnull
      by (simp add: managed_due_optional_event_remove_heap_def
          one_due_event_remove_heap_def)
  qed
qed

lemma one_due_full_family_cutpoints_managed_observation:
  assumes observation:
      "TaskObservationRel D h (managed_scheduler_view current managed)"
    and families:
      "one_due_full_family_cutpoints external D managed C S h
         generic_raw event_raw branch"
    and task: "odc_task C \<in> managed"
    and source_global: "odc_delayed_root C \<in> GenericRootUniverse"
    and source_member:
      "Generic (odc_task C) \<in>
         set (ring (ods_generic_family S (odc_delayed_root C)))"
    and target_global: "one_due_target_root C \<in> GenericRootUniverse"
    and pending_empty:
      "ring (ods_event_family S GeneratedPendingEventRoot) = []"
  shows
    "TaskObservationRel D
       (one_due_event_remove_heap D C branch
         (one_due_generic_remove_heap D C h))
       (managed_scheduler_view current managed) \<and>
     TaskObservationRel D
       (one_due_ready_insert_heap D C
         (one_due_generic_raw_after_remove D C generic_raw)
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C h)))
       (managed_scheduler_view current managed)"
proof -
  have generic_coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  have event_coverage:
    "EventRootFamilyCoverage external D h event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  note cutpoints = managed_TaskObservationRel_exact_cutpoints[
    OF observation generic_coverage event_coverage task source_global
       source_member target_global pending_empty]
  have event_heap:
    "managed_due_optional_event_remove_heap D (odc_task C)
       (one_due_generic_remove_heap D C h) =
     one_due_event_remove_heap D C branch
       (one_due_generic_remove_heap D C h)"
    by (rule one_due_full_family_cutpoints_managed_event_heap_eq[
          OF families])
  show ?thesis
    using cutpoints event_heap
    by (simp add: managed_due_generic_remove_heap_one_due
        managed_due_generic_raw_after_remove_one_due
        managed_due_ready_insert_heap_one_due Let_def)
qed

corollary one_due_full_family_cutpoints_post_managed_observation:
  assumes observation:
      "TaskObservationRel D h (managed_scheduler_view before managed)"
    and families:
      "one_due_full_family_cutpoints external D managed C S h
         generic_raw event_raw branch"
    and task: "odc_task C \<in> managed"
    and source_global: "odc_delayed_root C \<in> GenericRootUniverse"
    and source_member:
      "Generic (odc_task C) \<in>
         set (ring (ods_generic_family S (odc_delayed_root C)))"
    and target_global: "one_due_target_root C \<in> GenericRootUniverse"
    and pending_empty:
      "ring (ods_event_family S GeneratedPendingEventRoot) = []"
    and frame: "due_prefix_abstract_control_frame before after"
  shows
    "scheduler_managed_task_observation_rel D
       (one_due_ready_insert_heap D C
         (one_due_generic_raw_after_remove D C generic_raw)
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C h)))
       after managed"
proof -
  have current_observation:
    "TaskObservationRel D
       (one_due_ready_insert_heap D C
         (one_due_generic_raw_after_remove D C generic_raw)
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C h)))
       (managed_scheduler_view before managed)"
    using one_due_full_family_cutpoints_managed_observation[
      OF observation families task source_global source_member
         target_global pending_empty]
    by blast
  have after_observation:
    "TaskObservationRel D
       (one_due_ready_insert_heap D C
         (one_due_generic_raw_after_remove D C generic_raw)
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C h)))
       (managed_scheduler_view after managed)"
    by (rule TaskObservationRel_managed_view_control_frame[
          OF current_observation frame])
  show ?thesis
    using after_observation
    by (simp add: scheduler_managed_task_observation_rel_def)
qed

text \<open>
  Wake projection is not a new transition invariant.  Once the post abstract
  state has phase-accurate time/membership well-formedness and its complete
  Generic family is related with the same total key observation K_G, the
  projection follows by the four-way live-task partition: ready, delayed-A,
  delayed-B, or suspended.
\<close>

lemma due_loop_wake_projection_from_generic_family:
  assumes core: "due_loop_core_wf a"
    and time: "due_loop_time_wf now remaining future a"
    and domain: "strong_managed_domain_rel a termination managed"
    and coverage:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and role:
      "strong_generic_role_projection a termination generic_abs"
  shows "strong_wake_payload_projection a K_G"
proof -
  let ?R = "ready_task_set a"
  let ?A = "generic_task_set (sa_delayed_a a)"
  let ?B = "generic_task_set (sa_delayed_b a)"
  let ?S = "generic_task_set (sa_suspended a)"
  let ?ra =
    "abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
  let ?rb =
    "abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
  have partition: "?R \<union> ?A \<union> ?B \<union> ?S = sa_live a"
    and R_A: "?R \<inter> ?A = {}"
    and R_B: "?R \<inter> ?B = {}"
    and R_S: "?R \<inter> ?S = {}"
    and A_B: "?A \<inter> ?B = {}"
    and A_S: "?A \<inter> ?S = {}"
    and B_S: "?B \<inter> ?S = {}"
    using core
    by (simp_all add: due_loop_core_wf_def membership_wf_def Let_def)
  have agree_a: "delayed_key_agrees a (sa_delayed_a a)"
    and agree_b: "delayed_key_agrees a (sa_delayed_b a)"
    and inactive: "\<forall>t\<in>?R \<union> ?S. sa_wake a t = None"
    using time by (simp_all add: due_loop_time_wf_def)
  have live_subset: "sa_live a \<subseteq> managed"
    using domain by (simp add: strong_managed_domain_rel_def)
  have role_a: "generic_abs ?ra = sa_delayed_a a"
    and role_b: "generic_abs ?rb = sa_delayed_b a"
    using role by (simp_all add: strong_generic_role_projection_def)
  have root_a: "?ra \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_delayed_aI)
  have root_b: "?rb \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_delayed_bI)
  show ?thesis
    unfolding strong_wake_payload_projection_def
  proof (intro ballI)
    fix t
    assume live: "t \<in> sa_live a"
    have managed: "t \<in> managed"
      by (rule subsetD[OF live_subset live])
    have task_cases: "t \<in> ?R \<or> t \<in> ?A \<or> t \<in> ?B \<or> t \<in> ?S"
      using partition live by blast
    consider (Ready) "t \<in> ?R"
      | (DelayedA) "t \<in> ?A"
      | (DelayedB) "t \<in> ?B"
      | (Suspended) "t \<in> ?S"
      using task_cases by blast
    then show
      "sa_wake a t =
        (if t \<in> ?A \<union> ?B then Some (K_G t) else None)"
    proof cases
      case Ready
      have wake: "sa_wake a t = None"
        using inactive Ready by blast
      have not_a: "t \<notin> ?A" using R_A Ready by blast
      have not_b: "t \<notin> ?B" using R_B Ready by blast
      show ?thesis using wake not_a not_b by simp
    next
      case DelayedA
      have wake:
        "sa_wake a t = Some (item_key (sa_delayed_a a) (Generic t))"
        using agree_a DelayedA
        by (simp add: delayed_key_agrees_def)
      have member:
        "Generic t \<in> set (ring (generic_abs ?ra))"
        using DelayedA role_a by (simp add: generic_task_set_def)
      have key: "item_key (generic_abs ?ra) (Generic t) = K_G t"
        by (rule GenericRootFamilyCoverage_abstract_keyD[
              OF coverage managed root_a member])
      show ?thesis using DelayedA wake key role_a by simp
    next
      case DelayedB
      have wake:
        "sa_wake a t = Some (item_key (sa_delayed_b a) (Generic t))"
        using agree_b DelayedB
        by (simp add: delayed_key_agrees_def)
      have member:
        "Generic t \<in> set (ring (generic_abs ?rb))"
        using DelayedB role_b by (simp add: generic_task_set_def)
      have key: "item_key (generic_abs ?rb) (Generic t) = K_G t"
        by (rule GenericRootFamilyCoverage_abstract_keyD[
              OF coverage managed root_b member])
      show ?thesis using DelayedB wake key role_b by simp
    next
      case Suspended
      have wake: "sa_wake a t = None"
        using inactive Suspended by blast
      have not_a: "t \<notin> ?A" using A_S Suspended by blast
      have not_b: "t \<notin> ?B" using B_S Suspended by blast
      show ?thesis using wake not_a not_b by simp
    qed
  qed
qed

text \<open>
  The re-entry snapshot already contains the exact post families.  Once the
  total payload observations and the one changing top-ready scalar are
  identified, its remaining projection clauses are definitional: both
  transient registers are reset to None.
\<close>

lemma strong_one_due_snapshot_projection_reentry:
  assumes generic_payload: "ods_generic_payload S = K_G"
    and event_payload: "ods_event_payload S = K_E"
    and top_before: "ods_top S = sa_top_ready before"
    and top_after:
      "sa_top_ready after =
         max (sa_top_ready before) (odc_priority C (odc_task C))"
  shows
    "strong_one_due_snapshot_projection after
       (ods_generic_family (one_due_reentry_snapshot C branch S))
       (ods_event_family (one_due_reentry_snapshot C branch S))
       K_G K_E (one_due_reentry_snapshot C branch S)"
  using generic_payload event_payload top_before top_after
  by (simp add: strong_one_due_snapshot_projection_def
      one_due_reentry_snapshot_payloads one_due_reentry_snapshot_top
      one_due_reentry_snapshot_registers)

text \<open>
  The complete generated globals equality makes the unchanged role/current/
  boundary pins small projections.  They are kept separate from the top-ready
  scalar proof because that scalar intentionally changes in this source step.
\<close>

lemma one_due_tick_ready_inserted_state_role_rel:
  assumes role: "scheduler_role_rel generated_scheduler_roots before current"
    and frame: "due_prefix_abstract_control_frame current after"
  shows
    "scheduler_role_rel generated_scheduler_roots
       (one_due_tick_ready_inserted_state D C branch generic_raw before) after"
  using role frame
  by (simp add: scheduler_role_rel_def
      one_due_tick_ready_inserted_state_def scheduler_mem_state_def
      due_prefix_abstract_control_frame_def Let_def)

lemma one_due_tick_ready_inserted_state_current_rel:
  assumes current_rel: "scheduler_current_rel D before current"
    and frame: "due_prefix_abstract_control_frame current after"
  shows
    "scheduler_current_rel D
       (one_due_tick_ready_inserted_state D C branch generic_raw before) after"
  using current_rel frame
  by (simp add: scheduler_current_rel_def
      one_due_tick_ready_inserted_state_def scheduler_mem_state_def
      due_prefix_abstract_control_frame_def Let_def
      split: option.splits)

lemma one_due_tick_ready_inserted_state_boundary_rel:
  assumes boundary: "scheduler_boundary_rel before"
  shows
    "scheduler_boundary_rel
       (one_due_tick_ready_inserted_state D C branch generic_raw before)"
  using boundary
  by (simp add: scheduler_boundary_rel_def
      one_due_tick_ready_inserted_state_def scheduler_mem_state_def Let_def)

lemma one_due_tick_ready_inserted_state_managed_scalar_rel:
  assumes scalar:
    "scheduler_managed_scalar_rel before current managed"
    and current:
      "current = due_prefix_fold_state entry processed"
    and after:
      "after = due_prefix_result_step_abs entry processed
         (Generic (odc_task C))"
    and task: "odc_task C \<in> managed"
    and observation:
      "scheduler_managed_task_observation_rel D
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before))))
         current managed"
  shows
    "scheduler_managed_scalar_rel
       (one_due_tick_ready_inserted_state D C branch generic_raw before)
       after managed"
proof -
  let ?he =
    "one_due_event_remove_heap D C branch
      (one_due_generic_remove_heap D C
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before)))"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  let ?pri =
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
      (h_val ?he ?tp)"
  have observed:
    "TaskObservationRel D ?he (managed_scheduler_view current managed)"
    using observation
    by (simp add: scheduler_managed_task_observation_rel_def)
  have task_live:
    "odc_task C \<in> sa_live (managed_scheduler_view current managed)"
    using task by (simp add: managed_scheduler_view_def)
  have priority:
    "unat ?pri = sa_priority current (odc_task C)"
    using TaskObservationRel_liveD[OF observed task_live]
    by (simp add: managed_scheduler_view_def)
  have frame: "due_prefix_abstract_control_frame current after"
    using due_prefix_result_step_control_frame[
      OF current, where n="Generic (odc_task C)"] after by simp
  have top_after:
    "sa_top_ready after =
       max (sa_top_ready current) (sa_priority current (odc_task C))"
    using due_prefix_result_step_generic_state_eq[
      OF current, where task="odc_task C"] after
    by (simp add: Let_def)
  show ?thesis
  proof (cases
      "Scheduler_V611_Parse.globals.uxTopReadyPriority_' before < ?pri")
    case True
    show ?thesis
      using scalar frame top_after priority True
      by (simp add: scheduler_managed_scalar_rel_def scheduler_scalar_rel_def
           managed_scheduler_view_def due_prefix_abstract_control_frame_def
           one_due_tick_ready_inserted_state_def scheduler_mem_state_def
           Let_def max_def word_less_nat_alt)
  next
    case False
    show ?thesis
      using scalar frame top_after priority False
      by (simp add: scheduler_managed_scalar_rel_def scheduler_scalar_rel_def
           managed_scheduler_view_def due_prefix_abstract_control_frame_def
           one_due_tick_ready_inserted_state_def scheduler_mem_state_def
           Let_def max_def not_less word_less_nat_alt)
  qed
qed

end

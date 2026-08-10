theory Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges.Scheduler_Delayed_Cursor_General_Due_Step_Bridges"
begin

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_generic_role_projection:
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
  have exit:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
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
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_root_alignment[
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
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now (Generic task # remaining) future"
    by (rule CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong])
  have core: "cursor_general_due_loop_core_wf current"
    and pre_role:
      "strong_generic_role_projection current termination generic_abs"
    and pre_wake: "strong_wake_payload_projection current K_G"
    and projection:
      "strong_one_due_snapshot_projection current generic_abs event_abs
         K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
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
  have membership: "membership_wf current"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF core])
  have task_live: "task \<in> sa_live current"
    using membership task_delayed
    by (auto simp: membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    by (rule cursor_general_due_loop_core_wf_priorityD[OF core task_live])
  have snapshot_generic: "ods_generic_family S = generic_abs"
    and snapshot_payload: "ods_generic_payload S = K_G"
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
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

text \<open>
  Wake reconstruction uses only the cursor-insensitive membership partition,
  the exact post families, and the total payload observation.  In particular,
  the real abstract family is not replaced by a canonical family over the same
  raw heap.
\<close>

lemma cursor_general_due_loop_wake_projection_from_generic_family:
  assumes core: "cursor_general_due_loop_core_wf a"
    and time: "due_loop_time_wf now remaining future a"
    and domain: "CursorGeneralStrongManagedDomainRel a termination managed"
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
  have membership: "membership_wf a"
    by (rule cursor_general_due_loop_core_wf_membershipD[OF core])
  have partition: "?R \<union> ?A \<union> ?B \<union> ?S = sa_live a"
    and R_A: "?R \<inter> ?A = {}"
    and R_B: "?R \<inter> ?B = {}"
    and R_S: "?R \<inter> ?S = {}"
    and A_B: "?A \<inter> ?B = {}"
    and A_S: "?A \<inter> ?S = {}"
    and B_S: "?B \<inter> ?S = {}"
    using membership
    by (simp_all add: membership_wf_def Let_def)
  have agree_a: "delayed_key_agrees a (sa_delayed_a a)"
    and agree_b: "delayed_key_agrees a (sa_delayed_b a)"
    and inactive: "\<forall>t\<in>?R \<union> ?S. sa_wake a t = None"
    using time by (simp_all add: due_loop_time_wf_def)
  have live_subset: "sa_live a \<subseteq> managed"
    using domain by (simp add: CursorGeneralStrongManagedDomainRel_def)
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

end

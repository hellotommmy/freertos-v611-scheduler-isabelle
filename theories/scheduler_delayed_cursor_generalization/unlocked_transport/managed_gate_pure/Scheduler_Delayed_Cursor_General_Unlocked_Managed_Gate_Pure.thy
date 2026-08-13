theory Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context.Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context"
begin

lemma CursorGeneralDueLoopStrongHeadRel_canonical_one_due_entry:
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
    "one_due_entry_rel C (one_due_canonical_event_branch C S) S"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have context_wf: "one_due_context_wf C"
    unfolding C_def
    by (rule CursorGeneralDueLoopStrongHeadRel_canonical_context_wf[
          OF strong roots])
  have generic0:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    and event0:
      "EventRootFamilyCoverage external D ?h event_raw event_abs managed K_E"
    and snapshot_fields:
      "ods_generic_family S = generic_abs \<and>
       ods_event_family S = event_abs \<and>
       ods_generic_payload S = K_G \<and>
       ods_event_payload S = K_E \<and>
       ods_top S = sa_top_ready current \<and>
       ods_captured_generic_key S = None \<and>
       ods_checked_event S = None"
    using snapshot
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have generic:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    using generic0 snapshot_fields by simp
  have event:
    "EventRootFamilyCoverage external D ?h event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    using event0 snapshot_fields by simp
  have family_shape: "one_due_family_shape C S"
    apply (rule full_family_coverage_one_due_family_shape[OF generic event])
    using snapshot_fields
    by (simp_all add: C_def)
  note cross =
    CursorGeneralDueLoopStrongHeadRel_canonical_managed_cross_ledger[
      OF strong roots, folded C_def]
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    using cross by blast
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using cross by blast
  have pending:
    "ring (ods_event_family S (odc_pending_root C)) = []"
    using cross by blast
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have delayed_ring:
    "ring (ods_generic_family S (odc_delayed_root C)) =
       Generic task # (remaining @ future)"
    using delayed current_ring by simp
  have delayed_root: "odc_delayed_root C \<in> GenericRootUniverse"
    using context_wf
    by (auto simp: one_due_context_wf_def C_def)
  have task_managed: "task \<in> managed"
    using one_due_context_task_liveD[OF context_wf]
    by (simp add: C_def)
  have task_member:
    "Generic task \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using delayed_ring by simp
  have task_key:
    "item_key (ods_generic_family S (odc_delayed_root C))
       (Generic task) = ods_generic_payload S task"
    by (rule GenericRootFamilyCoverage_abstract_keyD[
          OF generic task_managed delayed_root task_member])
  have current_eq: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have due_entry:
    "item_key (current_delayed_ring entry) (Generic task) \<le> now"
    using due_prefix_loop_inv_result_head[OF loop] by blast
  have due_current:
    "item_key (current_delayed_ring current) (Generic task) \<le> now"
    using due_entry current_eq by simp
  have context_tick: "odc_tick C = now"
    using cross by blast
  have task_due: "ods_generic_payload S task \<le> odc_tick C"
    using task_key delayed due_current context_tick by simp
  have branch:
    "one_due_event_branch_at C S (one_due_canonical_event_branch C S)"
    by (rule one_due_canonical_event_branch_at[OF pending])
  have top: "ods_top S = odc_entry_top C"
    using snapshot_fields by (simp add: C_def)
  have task_sel: "odc_task C = task"
    by (simp add: C_def)
  have fresh_phase:
    "ods_captured_generic_key S = None \<and>
     ods_checked_event S = None"
    using snapshot_fields by simp
  show ?thesis
    unfolding one_due_entry_rel_def
    apply (intro conjI)
    subgoal by (rule context_wf)
    subgoal by (rule family_shape)
    subgoal
      apply (rule exI[where x="remaining @ future"])
      using delayed_ring task_sel by simp
    subgoal using task_member task_sel by simp
    subgoal using task_key task_sel by simp
    subgoal using task_due task_sel by simp
    subgoal by (rule branch)
    subgoal by (rule top)
    subgoal using fresh_phase by simp
    subgoal using fresh_phase by simp
    done
qed

end

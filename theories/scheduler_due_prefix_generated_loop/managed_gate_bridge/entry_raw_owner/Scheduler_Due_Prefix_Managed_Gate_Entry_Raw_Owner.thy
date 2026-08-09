theory Scheduler_Due_Prefix_Managed_Gate_Entry_Raw_Owner
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Family_Cross.Scheduler_Due_Prefix_Managed_Gate_Family_Cross"
begin

lemma DueLoopStrongHeadRel_canonical_one_due_entry:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current managed
       external K_E task"
  shows
    "one_due_entry_rel C (one_due_canonical_event_branch C S) S"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have context_wf: "one_due_context_wf C"
    unfolding C_def
    by (rule DueLoopStrongHeadRel_canonical_context_wf[OF strong roots])
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
    by (simp_all add: DueLoopSchedulerSnapshotRel_def
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
    apply (rule full_family_coverage_one_due_family_shape[
          OF generic event])
    using snapshot_fields
    by (simp_all add: C_def)
  note cross = DueLoopStrongHeadRel_canonical_managed_cross_ledger[
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
    "one_due_event_branch_at C S
       (one_due_canonical_event_branch C S)"
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

text \<open>
  Two small coverage destructors isolate the only nontrivial raw-list facts
  needed by Gate-H.  They are deliberately independent of the due-loop result:
  complete Generic coverage already says that every raw member is a managed
  Generic item, and that an abstract member has one physical owner root.
\<close>

lemma GenericRootFamilyCoverage_one_due_raw_subset:
  assumes coverage:
    "GenericRootFamilyCoverage D h roots raw_fam abs_fam managed K_G"
    and root: "r \<in> roots"
  shows
    "set (ring (raw_fam r)) \<subseteq>
       one_due_generic_raw_set managed D"
proof -
  have rep:
    "generic_family_root_rep D raw_fam abs_fam managed r"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage root])
  show ?thesis
    using rep
    by (simp add: generic_family_root_rep_def
        generic_item_raw_set_def one_due_generic_raw_set_def
        generic_item_raw_ptr_def one_due_generic_raw_ptr_def)
qed

lemma GenericRootFamilyCoverage_delay_owner_entry:
  assumes coverage:
    "GenericRootFamilyCoverage D h roots raw_fam abs_fam managed K_G"
    and task: "t \<in> managed"
    and owner: "owner \<in> roots"
    and member: "Generic t \<in> set (ring (abs_fam owner))"
  shows
    "scheduler_delay_owner_entry_rel h roots raw_fam owner
       (one_due_generic_raw_ptr D t)"
proof -
  let ?p = "generic_item_raw_ptr D t"
  have raw_member: "?p \<in> set (ring (raw_fam owner))"
    by (rule iffD2[OF GenericRootFamilyCoverage_member_iff[
          OF coverage task owner] member])
  have members: "raw_family_members roots raw_fam ?p = {owner}"
  proof (rule set_eqI)
    fix r
    show "r \<in> raw_family_members roots raw_fam ?p \<longleftrightarrow>
          r \<in> {owner}"
    proof
      assume r_member: "r \<in> raw_family_members roots raw_fam ?p"
      have r_root: "r \<in> roots"
        and raw_r: "?p \<in> set (ring (raw_fam r))"
        using r_member by (auto simp: raw_family_members_def)
      have "r = owner"
        by (rule GenericRootFamilyCoverage_unique_rootD[
              OF coverage r_root owner raw_r raw_member])
      then show "r \<in> {owner}" by simp
    next
      assume "r \<in> {owner}"
      then show "r \<in> raw_family_members roots raw_fam ?p"
        using owner raw_member by (simp add: raw_family_members_def)
    qed
  qed
  have container:
    "pvContainer_C (h_val h ?p) = PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    by (rule iffD1[OF GenericRootFamilyCoverage_container_iff[
          OF coverage task owner] raw_member])
  show ?thesis
    using owner members raw_member container
    by (simp add: scheduler_delay_owner_entry_rel_def
        one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
qed

theorem DueLoopStrongHeadRel_canonical_gateH_entry:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current managed
       external K_E task"
    and
    "branch \<equiv> one_due_canonical_event_branch
       (due_prefix_canonical_managed_context R c current managed
         external K_E task) S"
  shows
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed) C branch S
       generic_raw event_raw"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have coverage0:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    and event0:
    "EventRootFamilyCoverage external D ?h event_raw event_abs managed K_E"
    and observation:
    "TaskObservationRel D ?h
       (managed_scheduler_view current managed)"
    and scalar:
    "scheduler_managed_scalar_rel c current managed"
    and snapshot_fields:
    "ods_generic_family S = generic_abs \<and>
     ods_event_family S = event_abs \<and>
     ods_generic_payload S = K_G \<and>
     ods_event_payload S = K_E"
    and cross:
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e (event_raw e) = {}"
    using snapshot
    by (simp_all add: DueLoopSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def
        strong_one_due_snapshot_projection_def Let_def)
  have coverage:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw (ods_generic_family S) managed
       (ods_generic_payload S)"
    using coverage0 snapshot_fields by simp
  have laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  have generic_pre:
    "scheduler_family_pre_rel ?h GenericRootUniverse
       generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have raw_subset:
    "\<forall>r\<in>GenericRootUniverse.
       set (ring (generic_raw r)) \<subseteq>
         one_due_generic_raw_set managed D"
  proof (intro ballI)
    fix r
    assume root: "r \<in> GenericRootUniverse"
    show
      "set (ring (generic_raw r)) \<subseteq>
         one_due_generic_raw_set managed D"
      by (rule GenericRootFamilyCoverage_one_due_raw_subset[
            OF coverage root])
  qed
  have relabel:
    "\<forall>r\<in>GenericRootUniverse.
       xlist_relabel (sd_node_decode D) (generic_raw r)
         (ods_generic_family S r)"
  proof (intro ballI)
    fix r
    assume root: "r \<in> GenericRootUniverse"
    show
      "xlist_relabel (sd_node_decode D) (generic_raw r)
         (ods_generic_family S r)"
      by (rule GenericRootFamilyCoverage_relabelD[OF coverage root])
  qed
  have pure: "one_due_entry_rel C branch S"
    unfolding C_def branch_def
    by (rule DueLoopStrongHeadRel_canonical_one_due_entry[
          OF strong roots])
  have context_wf: "one_due_context_wf C"
    using pure by (simp add: one_due_entry_rel_def)
  have task_managed: "task \<in> managed"
    using one_due_context_task_liveD[OF context_wf]
    by (simp add: C_def)
  have delayed_root: "odc_delayed_root C \<in> GenericRootUniverse"
    using context_wf
    by (auto simp: one_due_context_wf_def C_def)
  have delayed_member:
    "Generic task \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using pure by (simp add: one_due_entry_rel_def C_def)
  have owner:
    "scheduler_delay_owner_entry_rel ?h GenericRootUniverse generic_raw
       (odc_delayed_root C) (one_due_generic_raw_ptr D task)"
    by (rule GenericRootFamilyCoverage_delay_owner_entry[
          OF coverage task_managed delayed_root delayed_member])
  have insert_geometry:
    "raw_family_insert_geometry GenericRootUniverse generic_raw
       (one_due_generic_raw_ptr D task)"
    using GenericRootFamilyCoverage_managed_view_insert_geometry[
      OF coverage observation task_managed]
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  have event_rel:
    "scheduler_event_root_family_rel D ?h (EventRootUniverse external)
       GeneratedPendingEventRoot event_raw (ods_event_family S)
       managed (ods_event_payload S)"
    using EventRootFamilyCoverage_relD[OF event0] snapshot_fields by simp
  have physical_keys:
    "\<forall>t\<in>managed.
       raw_key_at ?h (one_due_generic_raw_ptr D t) =
         ods_generic_payload S t"
    using GenericRootFamilyCoverage_physical_keyD[OF coverage]
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  have root_disjoint:
    "GenericRootUniverse \<inter> EventRootUniverse external = {}"
    using EventRootFamilyCoverage_generic_roots_disjointD[OF event0]
    by blast
  have tick_pin:
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick current"
    and top_pin:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready current"
    using scalar
    by (simp_all add: scheduler_managed_scalar_rel_def
        scheduler_scalar_rel_def managed_scheduler_view_def)
  show ?thesis
    unfolding one_due_gateH_entry_rel_def Let_def
    apply (intro conjI)
    subgoal by (rule pure)
    subgoal by (rule observation)
    subgoal using laws by (simp add: C_def)
    subgoal by (simp add: C_def managed_scheduler_view_def)
    subgoal by (simp add: C_def managed_scheduler_view_def)
    subgoal using tick_pin by (simp add: C_def)
    subgoal using top_pin by (simp add: C_def)
    subgoal by (simp add: C_def)
    subgoal using roots by (simp add: C_def GeneratedPendingEventRoot_def)
    subgoal by (simp add: C_def)
    subgoal using generic_pre by (simp add: C_def)
    subgoal using raw_subset by (simp add: C_def)
    subgoal using relabel by (simp add: C_def)
    subgoal using owner by (simp add: C_def)
    subgoal using insert_geometry by (simp add: C_def)
    subgoal using event_rel roots snapshot_fields
      by (simp add: C_def GeneratedPendingEventRoot_def)
    subgoal using physical_keys by (simp add: C_def)
    subgoal using root_disjoint by (simp add: C_def)
    subgoal using cross by (simp add: C_def)
    done
qed

end

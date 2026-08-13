theory Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure.Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure"
begin

theorem CursorGeneralDueLoopStrongHeadRel_canonical_gateH_entry:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
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
  note snapshot = CursorGeneralDueLoopStrongHeadRel_snapshotD[OF strong]
  have coverage0:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    and event0:
      "EventRootFamilyCoverage external D ?h event_raw event_abs managed K_E"
    and observation:
      "TaskObservationRel D ?h (managed_scheduler_view current managed)"
    and scalar: "scheduler_managed_scalar_rel c current managed"
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
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def
        strong_one_due_snapshot_projection_def Let_def)
  have coverage:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    using coverage0 snapshot_fields by simp
  have laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  have generic_pre:
    "scheduler_family_pre_rel ?h GenericRootUniverse generic_raw managed D"
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
    by (rule CursorGeneralDueLoopStrongHeadRel_canonical_one_due_entry[
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

theorem CursorGeneralDueLoopStrongHeadRel_canonical_managed_gate:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current managed
       external K_E task"
    and
    "branch \<equiv> one_due_canonical_event_branch
       (due_prefix_canonical_managed_context R c current managed
         external K_E task) S"
  shows
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # remaining) future current managed C branch S
       generic_raw event_raw"
proof -
  have gateH:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed) C branch S
       generic_raw event_raw"
    unfolding C_def branch_def
    by (rule CursorGeneralDueLoopStrongHeadRel_canonical_gateH_entry[
          OF strong roots])
  have ledger:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"
    unfolding C_def
    by (rule
      CursorGeneralDueLoopStrongHeadRel_canonical_managed_cross_ledger[
        OF strong roots])
  show ?thesis
    using gateH ledger
    by (simp add: due_prefix_managed_gate_inv_def)
qed

corollary CursorGeneralDueLoopStrongHeadRel_managed_gate_witness:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "\<exists>C branch.
       odc_task C = task \<and>
       due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed C branch S
         generic_raw event_raw"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  let ?branch = "one_due_canonical_event_branch ?C S"
  have gate:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # remaining) future current managed ?C ?branch S
       generic_raw event_raw"
    by (rule CursorGeneralDueLoopStrongHeadRel_canonical_managed_gate[
          OF strong roots])
  show ?thesis
    apply (rule exI[where x=
      "due_prefix_canonical_managed_context R c current managed
         external K_E task"])
    apply (rule exI[where x=
      "one_due_canonical_event_branch
         (due_prefix_canonical_managed_context R c current managed
           external K_E task) S"])
    apply (rule conjI)
    subgoal by simp
    by (rule gate)
qed

end

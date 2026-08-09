theory Scheduler_Due_Prefix_Managed_Gate_Family_Cross
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Defs_Context.Scheduler_Due_Prefix_Managed_Gate_Defs_Context"
begin

lemma full_family_coverage_one_due_family_shape:
  assumes generic:
    "GenericRootFamilyCoverage D h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    and event:
    "EventRootFamilyCoverage external D h event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    and generic_roots:
      "odc_generic_roots C = GenericRootUniverse"
    and event_roots:
      "odc_event_roots C = EventRootUniverse external"
    and live: "odc_live C = managed"
    and event_payload: "odc_K_E C = ods_event_payload S"
  shows "one_due_family_shape C S"
proof -
  note generic_laws = GenericRootFamilyCoverage_decoder_lawsD[OF generic]
  note event_rel = EventRootFamilyCoverage_relD[OF event]
  show ?thesis
    unfolding one_due_family_shape_def
  proof (intro conjI)
    show
      "\<forall>r\<in>odc_generic_roots C.
         xlist_wf (ods_generic_family S r) \<and>
         generic_ring (ods_generic_family S r) \<and>
         set (ring (ods_generic_family S r)) \<subseteq>
           Generic ` odc_live C"
    proof (intro ballI)
      fix r
      assume root: "r \<in> odc_generic_roots C"
      have root': "r \<in> GenericRootUniverse"
        using root generic_roots by simp
      have wf: "xlist_wf (ods_generic_family S r)"
        and generic_ring: "generic_ring (ods_generic_family S r)"
        using GenericRootFamilyCoverage_root_repD[OF generic root']
        by (simp_all add: generic_family_root_rep_def)
      have subset:
        "set (ring (ods_generic_family S r)) \<subseteq>
           Generic ` odc_live C"
      proof
        fix n
        assume member: "n \<in> set (ring (ods_generic_family S r))"
        obtain p where decoded:
            "sd_node_decode D p = Some n"
          using xlist_relabel_decoder_right_closed[
            OF GenericRootFamilyCoverage_relabelD[OF generic root'] member]
          by blast
        have owner: "node_owner n \<in> managed"
          using generic_laws decoded
          by (auto simp: universal_decoder_laws_def)
        obtain t where node: "n = Generic t"
          using generic_ring member
          by (auto simp: generic_ring_def)
        show "n \<in> Generic ` odc_live C"
          using owner node live by auto
      qed
      show
        "xlist_wf (ods_generic_family S r) \<and>
         generic_ring (ods_generic_family S r) \<and>
         set (ring (ods_generic_family S r)) \<subseteq>
           Generic ` odc_live C"
        using wf generic_ring subset by blast
    qed
  next
    show
      "\<forall>r\<in>odc_event_roots C.
         xlist_wf (ods_event_family S r) \<and>
         event_ring (ods_event_family S r) \<and>
         set (ring (ods_event_family S r)) \<subseteq>
           Event ` odc_live C"
    proof (intro ballI)
      fix r
      assume root: "r \<in> odc_event_roots C"
      have root': "r \<in> EventRootUniverse external"
        using root event_roots by simp
      have wf: "xlist_wf (ods_event_family S r)"
        by (rule scheduler_event_root_family_abs_wfD[OF event_rel root'])
      have ring: "event_ring (ods_event_family S r)"
        by (rule scheduler_event_root_family_event_ringD[OF event_rel root'])
      have subset:
        "set (ring (ods_event_family S r)) \<subseteq>
           Event ` odc_live C"
      proof
        fix n
        assume member: "n \<in> set (ring (ods_event_family S r))"
        obtain t where node: "n = Event t"
          using ring member by (auto simp: event_ring_def)
        have "t \<in> managed"
          by (rule scheduler_event_root_family_abstract_task_liveD[
                OF event_rel root'])
             (use member node in simp)
        then show "n \<in> Event ` odc_live C"
          using node live by auto
      qed
      show
        "xlist_wf (ods_event_family S r) \<and>
         event_ring (ods_event_family S r) \<and>
         set (ring (ods_event_family S r)) \<subseteq>
           Event ` odc_live C"
        using wf ring subset by blast
    qed
  next
    show
      "\<forall>r\<in>odc_generic_roots C. \<forall>s\<in>odc_generic_roots C.
         r \<noteq> s \<longrightarrow>
         set (ring (ods_generic_family S r)) \<inter>
           set (ring (ods_generic_family S s)) = {}"
    proof (intro ballI impI)
      fix r s
      assume r: "r \<in> odc_generic_roots C"
        and s: "s \<in> odc_generic_roots C"
        and different: "r \<noteq> s"
      have r': "r \<in> GenericRootUniverse"
        and s': "s \<in> GenericRootUniverse"
        using r s generic_roots by simp_all
      show
        "set (ring (ods_generic_family S r)) \<inter>
           set (ring (ods_generic_family S s)) = {}"
      proof (rule ccontr)
        assume nonempty:
          "set (ring (ods_generic_family S r)) \<inter>
             set (ring (ods_generic_family S s)) \<noteq> {}"
        then obtain n where nr:
            "n \<in> set (ring (ods_generic_family S r))"
          and ns: "n \<in> set (ring (ods_generic_family S s))"
          by blast
        have generic_ring: "generic_ring (ods_generic_family S r)"
          using GenericRootFamilyCoverage_root_repD[OF generic r']
          by (simp add: generic_family_root_rep_def)
        obtain t where node: "n = Generic t"
          using generic_ring nr by (auto simp: generic_ring_def)
        have t_managed: "t \<in> managed"
        proof -
          obtain p where decoded: "sd_node_decode D p = Some (Generic t)"
            using xlist_relabel_decoder_right_closed[
              OF GenericRootFamilyCoverage_relabelD[OF generic r'] nr]
              node by blast
          show ?thesis
            using generic_laws decoded
            by (auto simp: universal_decoder_laws_def)
        qed
        have raw_r:
          "generic_item_raw_ptr D t \<in> set (ring (generic_raw r))"
          using GenericRootFamilyCoverage_member_iff[
            OF generic t_managed r'] nr node by simp
        have raw_s:
          "generic_item_raw_ptr D t \<in> set (ring (generic_raw s))"
          using GenericRootFamilyCoverage_member_iff[
            OF generic t_managed s'] ns node by simp
        have "r = s"
          by (rule GenericRootFamilyCoverage_unique_rootD[
                OF generic r' s' raw_r raw_s])
        then show False using different by contradiction
      qed
    qed
  next
    show
      "\<forall>r\<in>odc_event_roots C. \<forall>s\<in>odc_event_roots C.
         r \<noteq> s \<longrightarrow>
         set (ring (ods_event_family S r)) \<inter>
           set (ring (ods_event_family S s)) = {}"
    proof (intro ballI impI)
      fix r s
      assume r: "r \<in> odc_event_roots C"
        and s: "s \<in> odc_event_roots C"
        and different: "r \<noteq> s"
      have r': "r \<in> EventRootUniverse external"
        and s': "s \<in> EventRootUniverse external"
        using r s event_roots by simp_all
      show
        "set (ring (ods_event_family S r)) \<inter>
           set (ring (ods_event_family S s)) = {}"
      proof (rule ccontr)
        assume nonempty:
          "set (ring (ods_event_family S r)) \<inter>
             set (ring (ods_event_family S s)) \<noteq> {}"
        then obtain n where nr:
            "n \<in> set (ring (ods_event_family S r))"
          and ns: "n \<in> set (ring (ods_event_family S s))"
          by blast
        have ring: "event_ring (ods_event_family S r)"
          by (rule scheduler_event_root_family_event_ringD[OF event_rel r'])
        obtain t where node: "n = Event t"
          using ring nr by (auto simp: event_ring_def)
        have "r = s"
          by (rule scheduler_event_root_family_abstract_unique_rootD[
                OF event_rel r' s'])
             (use nr ns node in simp_all)
        then show False using different by contradiction
      qed
    qed
  next
    show
      "\<forall>r\<in>odc_generic_roots C. \<forall>t\<in>odc_live C.
         Generic t \<in> set (ring (ods_generic_family S r)) \<longrightarrow>
         item_key (ods_generic_family S r) (Generic t) =
           ods_generic_payload S t"
      using GenericRootFamilyCoverage_abstract_keyD[OF generic]
        generic_roots live by blast
  next
    show
      "\<forall>r\<in>odc_event_roots C. \<forall>t\<in>odc_live C.
         Event t \<in> set (ring (ods_event_family S r)) \<longrightarrow>
         item_key (ods_event_family S r) (Event t) =
           ods_event_payload S t"
      using scheduler_event_root_family_abstract_keyD[OF event_rel]
        event_roots live by blast
  next
    show "\<forall>t\<in>odc_live C. ods_event_payload S t = odc_K_E C t"
      using live event_payload by simp
  qed
qed

lemma DueLoopStrongHeadRel_canonical_managed_cross_ledger:
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
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have tick: "sa_tick current = now"
    using strong by (simp add: DueLoopStrongHeadRel_def)
  have role: "scheduler_role_rel generated_scheduler_roots c current"
    and generic_role:
      "strong_generic_role_projection current termination generic_abs"
    and event_role:
      "strong_event_role_projection current managed external event_abs"
    and snapshot_generic: "ods_generic_family S = generic_abs"
    and snapshot_event: "ods_event_family S = event_abs"
    using snapshot
    by (simp_all add: DueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using role generic_role snapshot_generic
    by (cases "sa_current_role_a current")
       (simp_all add: C_def scheduler_role_rel_def
          strong_generic_role_projection_def current_delayed_ring_def)
  have pending_projection:
    "ods_event_family S GeneratedPendingEventRoot = sa_pending current"
    using event_role snapshot_event
    by (simp add: strong_event_role_projection_def)
  have pending_before: "ring (sa_pending current) = []"
    using strong by (simp add: DueLoopStrongHeadRel_def)
  have pending:
    "ring (ods_event_family S (odc_pending_root C)) = []"
    using pending_projection pending_before roots
    by (simp add: C_def GeneratedPendingEventRoot_def)
  have destinations: "one_due_all_ready_destinations C"
    unfolding C_def
    by (rule DueLoopStrongHeadRel_canonical_all_ready_destinations[
          OF strong roots])
  show ?thesis
    using loop tick delayed destinations pending
    by (simp add: C_def)
qed

end

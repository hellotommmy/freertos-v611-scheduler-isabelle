theory Scheduler_Due_Prefix_Strong_Result_Shared_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector.Scheduler_Due_Prefix_Strong_Result_Components"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Full_Family_Cutpoint_Composition.Scheduler_One_Due_Full_Family_Cutpoint_Composition"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Tick_Exact_Globals.Scheduler_One_Due_Tick_Exact_Globals"
begin

text \<open>
  Shared-witness post for one non-last generated due-loop Result step.  The
  successor Gate-H package and the whole-scheduler strong relation use the
  same computed Generic family, Event family and phase snapshot.  In
  particular, neither side is allowed to choose a second existential family
  that merely represents the same runnable fragment.

  The post also retains the exact generated globals record.  This equality is
  the source-order anchor for the four physical heap cutpoints; it is not an
  expected-state premise.
\<close>

definition DueLoopSharedResultPost ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid \<Rightarrow> 'tid \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "DueLoopSharedResultPost D R now entry processed task u remaining future
       current C branch S generic_raw event_raw K_G K_E
       managed termination external before r t \<longleftrightarrow>
     (let after =
          due_prefix_result_step_abs entry processed (Generic task);
          h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before);
          hg = one_due_generic_remove_heap D C h0;
          he = one_due_event_remove_heap D C branch hg;
          generic_raw' =
            one_due_reentry_generic_raw D C he generic_raw;
          event_raw' =
            one_due_event_raw_after_remove D C branch event_raw;
          S' = one_due_reentry_snapshot C branch S
      in r = Result (sd_tcb_ptr D u) \<and>
         t = one_due_tick_ready_inserted_state
               D C branch generic_raw before \<and>
         (\<exists>branch'.
           due_prefix_gate_inv D R t now entry
             (processed @ [Generic task])
             (Generic u # remaining) future after
             (one_due_reentry_context C u) branch'
             S' generic_raw' event_raw') \<and>
         DueLoopStrongHeadRel D t after managed termination external
           generic_raw' (ods_generic_family S')
           event_raw' (ods_event_family S') K_G K_E S'
           now entry (processed @ [Generic task])
           (Generic u # remaining) future
           DueGate (Some (Generic u)) (sd_tcb_ptr D u))"

lemma DueLoopStrongHeadRel_shared_snapshot_projectionD:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "ods_generic_family S = generic_abs \<and>
     ods_event_family S = event_abs \<and>
     ods_generic_payload S = K_G \<and>
     ods_event_payload S = K_E \<and>
     ods_top S = sa_top_ready current \<and>
     ods_captured_generic_key S = None \<and>
     ods_checked_event S = None"
  using strong
  by (simp add: DueLoopStrongHeadRel_def DueLoopSchedulerSnapshotRel_def
      strong_one_due_snapshot_projection_def Let_def)

lemma DueLoopStrongHeadRel_shared_gate_root_alignment:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
         (Generic task # remaining) future current
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
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  note exact = one_due_gateH_exact_rootsD[OF local]
  have scheduler_role:
    "scheduler_role_rel generated_scheduler_roots c current"
    using strong
    by (simp add: DueLoopStrongHeadRel_def DueLoopSchedulerSnapshotRel_def
        Let_def)
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have priority:
    "odc_priority C task = sa_priority current task"
    using local task_live selector
    by (simp add: one_due_gateH_entry_rel_def Let_def)
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

lemma DueLoopStrongHeadRel_one_due_full_family_cutpoints:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
         (Generic task # remaining) future current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_full_family_cutpoints external D managed C S
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       generic_raw event_raw branch"
proof -
  have local:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have domain: "strong_managed_domain_rel current termination managed"
    and core: "due_loop_core_wf current"
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
  have task_C: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have live_eq: "odc_live C = sa_live current"
    by (rule one_due_gateH_live_absD[OF local])
  have live_subset: "odc_live C \<subseteq> managed"
    using domain live_eq
    by (simp add: strong_managed_domain_rel_def)
  have task_live: "task \<in> sa_live current"
    using task_C live_eq selector by simp
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

end

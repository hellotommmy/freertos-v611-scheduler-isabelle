theory Scheduler_Resume_Managed_Ready_Insert_Relational
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Fragment.Scheduler_Resume_Managed_Ready_Fragment"
begin

text \<open>
  Managed relational cutpoint after the source-faithful ready insertion.  The
  pre-insert global-unlink fact is consumed as freshness: the post item is now
  linked at its ready root and is deliberately not called globally unlinked.
\<close>

theorem CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       GenericRootUniverse
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       managed K_G \<and>
     EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       managed K_E \<and>
     scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       a managed \<and>
     (\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g
             (resume_pending_drained_generic_fam
               C D t c generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}) \<and>
     resume_pending_loop_phase_inv C P [] (t # rest)
       RP_ReadyInserted (resume_pending_drained_snapshot C t P) \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
       rps_top (resume_pending_drained_snapshot C t P)"
proof -
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])

  let ?hG = "resume_pending_generic_remove_heap D t c"
  let ?rawG = "resume_pending_generic_raw_after C D t generic_raw"
  let ?rawE = "resume_pending_event_raw_after C D t event_raw"
  let ?PG =
    "resume_pending_generic_unlink_state C t
       (resume_pending_event_unlink_state C t P)"
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?hR =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?cR)"
  let ?rawR = "resume_pending_drained_generic_fam C D t c generic_raw"
  let ?PR = "resume_pending_drained_snapshot C t P"
  let ?target = "rpc_ready_root C (rpc_priority C t)"

  have head:
    "t \<in> rpc_live C \<and>
     rpc_priority C t < 4 \<and>
     rpc_generic_owner C t \<in> rpc_generic_roots C \<and>
     ?target \<in> rpc_generic_roots C \<and>
     rpc_generic_owner C t \<noteq> ?target"
    by (rule resume_pending_entry_head_facts[OF pure tasks])
  have t_context: "t \<in> rpc_live C"
    using head by blast
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have target_context: "?target \<in> rpc_generic_roots C"
    using head by blast
  have target: "?target \<in> GenericRootUniverse"
    using target_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)

  have generic_before:
    "GenericRootFamilyCoverage D ?hG GenericRootUniverse
       ?rawG (rps_generic_family ?PG) managed K_G"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_generic_coverageD[
        OF phase tasks])
  have event_before:
    "EventRootFamilyCoverage external D ?hG
       ?rawE (rps_event_family ?PG) managed K_E"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_event_coverageD[
        OF phase tasks])
  have observation_before0:
    "scheduler_managed_task_observation_rel D ?hG a managed"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_observationD[
        OF phase tasks])
  have observation_before:
    "TaskObservationRel D ?hG (managed_scheduler_view a managed)"
    using observation_before0
    by (simp add: scheduler_managed_task_observation_rel_def)

  have ptr_eq:
    "generic_item_raw_ptr D t = resume_pending_generic_raw_ptr D t"
    by (simp add: generic_item_raw_ptr_def
        resume_pending_generic_raw_ptr_def)
  have unlinked0:
    "raw_family_globally_unlinked ?hG GenericRootUniverse ?rawG
       (resume_pending_generic_raw_ptr D t)"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_globally_unlinkedD[
        OF phase tasks])
  have unlinked:
    "raw_family_globally_unlinked ?hG GenericRootUniverse ?rawG
       (generic_item_raw_ptr D t)"
    using unlinked0 ptr_eq by simp
  have absent:
    "raw_family_members GenericRootUniverse ?rawG
       (generic_item_raw_ptr D t) = {}"
    using unlinked
    by (simp add: raw_family_globally_unlinked_def)

  have pre:
    "scheduler_family_pre_rel ?hG GenericRootUniverse ?rawG managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_before])
  have family: "raw_family_rel ?hG GenericRootUniverse ?rawG"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have geometry:
    "raw_family_insert_geometry GenericRootUniverse ?rawG
       (generic_item_raw_ptr D t)"
    by (rule GenericRootFamilyCoverage_managed_view_insert_geometry[
        OF generic_before observation_before t_managed])
  have fresh:
    "raw_fresh_for_insert ?target (ring (?rawG ?target))
       (generic_item_raw_ptr D t)"
    by (rule raw_family_globally_unlinked_fresh_for_target[
        OF family unlinked target geometry])

  have top_heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
       (resume_pending_top_raised_state D t c)) = ?hG"
    by (simp add: resume_pending_top_raised_state_def Let_def)
  have ready_heap:
    "?hR =
       raw_insert_concrete_heap ?hG ?target (?rawG ?target)
         (generic_item_raw_ptr D t)"
    using top_heap ptr_eq
    by (simp add: resume_pending_ready_inserted_heap)
  have raw_after:
    "scheduler_family_insert_end_raw ?hG ?rawG ?target
       (generic_item_raw_ptr D t) = ?rawR"
    using ptr_eq
    by (simp add: resume_pending_drained_generic_fam_def)
  have generic_abs_after:
    "generic_family_insert_end_abs
       (rps_generic_family ?PG) ?target t K_G =
       rps_generic_family ?PR"
    using alignment
    by (simp add: resume_pending_drained_snapshot_def
        resume_pending_ready_insert_state_def
        resume_pending_raise_top_state_def
        generic_family_insert_end_abs_def
        resume_pending_managed_phase_alignment_def Let_def)
  have event_abs_after:
    "rps_event_family ?PG = rps_event_family ?PR"
    by (simp add: resume_pending_drained_snapshot_def
        resume_pending_ready_insert_state_def
        resume_pending_raise_top_state_def Let_def)

  have generic_post0:
    "GenericRootFamilyCoverage D
       (raw_insert_concrete_heap ?hG ?target (?rawG ?target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw ?hG ?rawG ?target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs
         (rps_generic_family ?PG) ?target t K_G)
       managed K_G"
    by (rule GenericRootFamilyCoverage_insert_end_preserved[
        OF generic_before target t_managed absent fresh])
  have generic_post:
    "GenericRootFamilyCoverage D ?hR GenericRootUniverse
       ?rawR (rps_generic_family ?PR) managed K_G"
    using generic_post0 ready_heap raw_after generic_abs_after
    by simp

  have event_post0:
    "EventRootFamilyCoverage external D
       (raw_insert_concrete_heap ?hG ?target (?rawG ?target)
         (generic_item_raw_ptr D t))
       ?rawE (rps_event_family ?PG) managed K_E"
    by (rule Generic_insert_end_frames_Event_coverage[
        OF generic_before event_before target t_managed fresh])
  have event_post:
    "EventRootFamilyCoverage external D ?hR
       ?rawE (rps_event_family ?PR) managed K_E"
    using event_post0 ready_heap event_abs_after by simp

  have pre_view:
    "scheduler_family_pre_rel ?hG GenericRootUniverse ?rawG
       (sa_live (managed_scheduler_view a managed)) D"
    using pre by (simp add: managed_scheduler_view_def)
  have p_managed:
    "generic_item_raw_ptr D t \<in>
       universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF t_managed])
  have p_managed_view:
    "generic_item_raw_ptr D t \<in>
       universal_managed_nodes
         (sa_live (managed_scheduler_view a managed)) D"
    using p_managed by (simp add: managed_scheduler_view_def)
  have observation_post0:
    "TaskObservationRel D
       (raw_insert_concrete_heap ?hG ?target (?rawG ?target)
         (generic_item_raw_ptr D t))
       (managed_scheduler_view a managed)"
    by (rule TaskObservationRel_insert_end_preserved[
        OF observation_before pre_view target fresh p_managed_view])
  have observation_post:
    "scheduler_managed_task_observation_rel D ?hR a managed"
    using observation_post0 ready_heap
    by (simp add: scheduler_managed_task_observation_rel_def)

  have cross_post:
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (?rawR g) \<inter>
           raw_xlist_storage e (?rawE e) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage_all[
        OF generic_post event_post])

  have generic_phase:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_GenericUnlinked ?PG"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_unlinkedD[
        OF phase tasks])
  have top_phase:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_TopRaised (resume_pending_raise_top_state C t ?PG)"
    by (rule resume_pending_loop_phase_inv_top_step[OF generic_phase])
  have ready_phase0:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_ReadyInserted
       (resume_pending_ready_insert_state C t
         (resume_pending_raise_top_state C t ?PG))"
    by (rule resume_pending_loop_phase_inv_ready_step[OF top_phase])
  have ready_phase:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_ReadyInserted ?PR"
    using ready_phase0
    by (simp add: resume_pending_drained_snapshot_def)

  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  obtain c0 where overlay:
      "c = scheduler_port_overlay
         (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c0 a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have scalar0: "scheduler_managed_scalar_rel c0 a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have shadow_top:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c0) =
       sa_top_ready a"
    using scalar0
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  have entry_top:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       rpc_entry_top C"
    using overlay shadow_top alignment
    by (simp add: scheduler_port_overlay_def
        resume_pending_managed_phase_alignment_def)

  have t_view:
    "t \<in> sa_live (managed_scheduler_view a managed)"
    using t_managed by (simp add: managed_scheduler_view_def)
  have observed:
    "sa_priority (managed_scheduler_view a managed) t < 4 \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t))) =
       sa_priority (managed_scheduler_view a managed) t \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t)) < 4"
    using TaskObservationRel_liveD[OF observation_before t_view]
    by blast
  have head_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t))) = rpc_priority C t"
    using observed alignment
    by (simp add: managed_scheduler_view_def
        resume_pending_managed_phase_alignment_def)

  let ?base = "scheduler_mem_state ?hG c"
  let ?top_word =
    "Scheduler_V611_Parse.globals.uxTopReadyPriority_' ?base"
  let ?priority_word =
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?base))
         (sd_tcb_ptr D t))"
  have base_top:
    "?top_word =
       Scheduler_V611_Parse.globals.uxTopReadyPriority_' c"
    by (simp add: scheduler_mem_state_def)
  have top_nat: "unat ?top_word = rpc_entry_top C"
    using entry_top base_top by simp
  have priority_nat:
    "unat ?priority_word = rpc_priority C t"
    using head_priority by simp
  have compare:
    "(?top_word < ?priority_word) =
       (rpc_entry_top C < rpc_priority C t)"
    using top_nat priority_nat by (simp add: word_less_nat_alt)
  have raised_top:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_top_raised_state D t c)) =
       max (rpc_entry_top C) (rpc_priority C t)"
    unfolding resume_pending_top_raised_state_def Let_def
    using top_nat priority_nat compare
    by (auto simp: max_def split: if_splits)

  have abstract_entry_top: "rps_top P = rpc_entry_top C"
    using pure by (simp add: resume_pending_entry_rel_def)
  have abstract_ready_top:
    "rps_top ?PR =
       max (rpc_entry_top C) (rpc_priority C t)"
    using resume_pending_drained_snapshot_scalars[of C t P]
      abstract_entry_top
    by simp
  have top_post:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' ?cR) =
       rps_top ?PR"
    using raised_top abstract_ready_top
    by (simp add: resume_pending_ready_inserted_top)

  show ?thesis
    using generic_post event_post observation_post cross_post
      ready_phase top_post
    by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       GenericRootUniverse
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       managed K_G"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       managed K_E"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       a managed"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_cross_storageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g
             (resume_pending_drained_generic_fam
               C D t c generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insertedD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_ReadyInserted (resume_pending_drained_snapshot C t P)"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_topD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_'
       (resume_pending_ready_inserted_state D C t generic_raw c)) =
       rps_top (resume_pending_drained_snapshot C t P)"
  using CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational[
      OF phase tasks]
  by blast

ML \<open>
  fun audit_exact label th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length (Thm.prems_of th) = 2 then ()
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed ready-insert relational capstone"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_relational}
  val _ = audit_exact "managed ready-insert Generic coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD}
  val _ = audit_exact "managed ready-insert Event coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD}
  val _ = audit_exact "managed ready-insert observation"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD}
  val _ = audit_exact "managed ready-insert cross storage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_cross_storageD}
  val _ = audit_exact "managed ready-insert phase"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insertedD}
  val _ = audit_exact "managed ready-insert top"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_topD}
\<close>

end

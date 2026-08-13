theory Scheduler_Resume_Managed_Event_Remove_Relational
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove.Scheduler_Resume_Managed_Event_Remove"
begin

text \<open>
  The Event unlink cutpoint is deliberately relational rather than a rebuilt
  scheduler snapshot.  The exact Event removal preserves complete Event and
  Generic coverage, managed task observations, their cross-kind storage
  separation, and the generated RP_EventUnlinked phase.  No legacy Resume
  gate or managed/live identification is used.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "EventRootFamilyCoverage external D
       (resume_pending_event_remove_heap D t c)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t P))
       managed K_E \<and>
     GenericRootFamilyCoverage D
       (resume_pending_event_remove_heap D t c)
       GenericRootUniverse generic_raw generic_abs managed K_G \<and>
     scheduler_managed_task_observation_rel D
       (resume_pending_event_remove_heap D t c) a managed \<and>
     (\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}) \<and>
     resume_pending_loop_phase_inv C P [] (t # rest)
       RP_EventUnlinked (resume_pending_event_unlink_state C t P)"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  obtain c0 where overlay:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast

  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0)"
  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?ep = "rpc_pending_root C"
  let ?rawE = "resume_pending_event_raw_after C D t event_raw"
  let ?PE = "resume_pending_event_unlink_state C t P"
  let ?absE = "rps_event_family ?PE"

  have heap_eq:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) = ?h"
    using overlay by simp
  have generic_coverage:
      "GenericRootFamilyCoverage D ?h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D ?h
         event_raw event_abs managed K_E"
    and observation:
      "TaskObservationRel D ?h (managed_scheduler_view a managed)"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def Let_def)
  have event_rel:
    "scheduler_event_root_family_rel D ?h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF event_coverage])
  have external_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
  have t_live: "t \<in> sa_live a"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD[OF phase]
      tasks by auto
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_domainD[OF gate])
  have t_managed: "t \<in> managed"
    using domain t_live
    by (auto simp: CursorGeneralStrongManagedDomainRel_def)
  have abstract_member:
    "Event t \<in> set (ring (event_abs GeneratedPendingEventRoot))"
    using pure alignment tasks
    by (simp add: resume_pending_entry_rel_def
        resume_pending_managed_phase_alignment_def)
  have raw_member:
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw GeneratedPendingEventRoot))"
    using scheduler_event_root_family_member_iff[
        OF event_rel t_managed EventRootUniverse_pendingI]
      abstract_member
    by blast

  have heap_after:
    "raw_remove_concrete_heap ?h (event_item_raw_ptr D t) = ?hE"
    using heap_eq by (simp add: resume_pending_event_remove_heap_def)
  have raw_after:
    "event_remove_raw_family event_raw GeneratedPendingEventRoot
       (event_item_raw_ptr D t) = ?rawE"
    using alignment
    by (simp add: resume_pending_event_raw_after_def
        resume_pending_managed_phase_alignment_def)
  have abs_after:
    "event_remove_abs_family event_abs GeneratedPendingEventRoot t = ?absE"
    using resume_pending_event_abs_after[where C=C and t=t and S=P]
      alignment
    by (simp add: resume_pending_managed_phase_alignment_def)

  have event_post_rel0:
    "scheduler_event_root_family_rel D
       (raw_remove_concrete_heap ?h (event_item_raw_ptr D t))
       (EventRootUniverse external) GeneratedPendingEventRoot
       (event_remove_raw_family event_raw GeneratedPendingEventRoot
          (event_item_raw_ptr D t))
       (event_remove_abs_family event_abs GeneratedPendingEventRoot t)
       managed K_E"
    by (rule scheduler_event_root_family_remove_preserved[
        OF event_rel EventRootUniverse_pendingI t_managed raw_member])
  have event_post0:
    "EventRootFamilyCoverage external D
       (raw_remove_concrete_heap ?h (event_item_raw_ptr D t))
       (event_remove_raw_family event_raw GeneratedPendingEventRoot
          (event_item_raw_ptr D t))
       (event_remove_abs_family event_abs GeneratedPendingEventRoot t)
       managed K_E"
    using external_wf event_post_rel0
    by (simp add: EventRootFamilyCoverage_def)
  have event_post:
    "EventRootFamilyCoverage external D ?hE ?rawE ?absE managed K_E"
    using event_post0 heap_after raw_after abs_after by simp

  have generic_post0:
    "GenericRootFamilyCoverage D
       (raw_remove_concrete_heap ?h (event_item_raw_ptr D t))
       GenericRootUniverse generic_raw generic_abs managed K_G"
    by (rule Event_remove_frames_Generic_coverage[
        OF generic_coverage event_coverage EventRootUniverse_pendingI
          t_managed raw_member])
  have generic_post:
    "GenericRootFamilyCoverage D ?hE GenericRootUniverse
       generic_raw generic_abs managed K_G"
    using generic_post0 heap_eq
    by (simp add: resume_pending_event_remove_heap_def)

  have event_pre:
    "scheduler_family_pre_rel ?h (EventRootUniverse external)
       event_raw managed D"
    by (rule scheduler_event_root_family_preD[OF event_rel])
  have event_pre_view:
    "scheduler_family_pre_rel ?h (EventRootUniverse external)
       event_raw (sa_live (managed_scheduler_view a managed)) D"
    using event_pre by (simp add: managed_scheduler_view_def)
  have observation_post0:
    "TaskObservationRel D
       (raw_remove_concrete_heap ?h (event_item_raw_ptr D t))
       (managed_scheduler_view a managed)"
    by (rule TaskObservationRel_remove_preserved[
        OF observation event_pre_view EventRootUniverse_pendingI raw_member])
  have observation_post:
    "scheduler_managed_task_observation_rel D ?hE a managed"
    using observation_post0 heap_after
    by (simp add: scheduler_managed_task_observation_rel_def)

  have cross_post:
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e (?rawE e) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage_all[
        OF generic_post event_post])

  have initial:
    "resume_pending_loop_phase_inv C P [] (rpc_tasks C) RP_LoopHead P"
    by (rule resume_pending_loop_phase_inv_initial[OF pure])
  have loop_head:
    "resume_pending_loop_phase_inv C P [] (t # rest) RP_LoopHead P"
    using initial tasks by simp
  have event_unlinked:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_EventUnlinked ?PE"
    by (rule resume_pending_loop_phase_inv_event_step[OF loop_head])

  show ?thesis
    using event_post generic_post observation_post cross_post event_unlinked
    by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_event_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "EventRootFamilyCoverage external D
       (resume_pending_event_remove_heap D t c)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_event_unlink_state C t P))
       managed K_E"
  using CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_generic_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "GenericRootFamilyCoverage D
       (resume_pending_event_remove_heap D t c)
       GenericRootUniverse generic_raw generic_abs managed K_G"
  using CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_observationD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_managed_task_observation_rel D
       (resume_pending_event_remove_heap D t c) a managed"
  using CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_cross_storageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}"
  using CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_event_unlinkedD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_EventUnlinked (resume_pending_event_unlink_state C t P)"
  using CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational[
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

  val _ = audit_exact "managed Event-remove relational capstone"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_relational}
  val _ = audit_exact "managed Event-remove Event coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_event_coverageD}
  val _ = audit_exact "managed Event-remove Generic coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_generic_coverageD}
  val _ = audit_exact "managed Event-remove observation"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_observationD}
  val _ = audit_exact "managed Event-remove cross storage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_cross_storageD}
  val _ = audit_exact "managed Event-unlinked phase"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_event_unlinkedD}
\<close>

end

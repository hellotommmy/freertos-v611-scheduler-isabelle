theory Scheduler_Resume_Managed_Generic_Remove_Relational
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_After_Event.Scheduler_Resume_Managed_Generic_Remove_After_Event"
begin

text \<open>
  The Generic-unlinked cutpoint remains relational.  It updates complete
  Generic coverage, frames complete Event coverage and managed observation,
  reconstructs cross-kind storage separation, records global absence of the
  removed Generic item, and advances the generated phase.  The explicit
  globally-unlinked fact is the freshness interface needed by ready insertion.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "GenericRootFamilyCoverage D
       (resume_pending_generic_remove_heap D t c)
       GenericRootUniverse
       (resume_pending_generic_raw_after C D t generic_raw)
       (rps_generic_family
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t P)))
       managed K_G \<and>
     EventRootFamilyCoverage external D
       (resume_pending_generic_remove_heap D t c)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t P)))
       managed K_E \<and>
     scheduler_managed_task_observation_rel D
       (resume_pending_generic_remove_heap D t c) a managed \<and>
     (\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g
             (resume_pending_generic_raw_after C D t generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}) \<and>
     raw_family_globally_unlinked
       (resume_pending_generic_remove_heap D t c)
       GenericRootUniverse
       (resume_pending_generic_raw_after C D t generic_raw)
       (resume_pending_generic_raw_ptr D t) \<and>
     resume_pending_loop_phase_inv C P [] (t # rest)
       RP_GenericUnlinked
       (resume_pending_generic_unlink_state C t
         (resume_pending_event_unlink_state C t P))"
proof -
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])

  let ?hE = "resume_pending_event_remove_heap D t c"
  let ?hG = "resume_pending_generic_remove_heap D t c"
  let ?owner = "rpc_generic_owner C t"
  let ?p = "resume_pending_generic_raw_ptr D t"
  let ?rawG = "resume_pending_generic_raw_after C D t generic_raw"
  let ?PE = "resume_pending_event_unlink_state C t P"
  let ?PG = "resume_pending_generic_unlink_state C t ?PE"
  let ?absG = "rps_generic_family ?PG"
  let ?rawE = "resume_pending_event_raw_after C D t event_raw"
  let ?absE = "rps_event_family ?PG"

  have t_context: "t \<in> rpc_live C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have owner_root_context: "?owner \<in> rpc_generic_roots C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have owner_root: "?owner \<in> GenericRootUniverse"
    using owner_root_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have abstract_member0:
    "Generic t \<in> set (ring (rps_generic_family P ?owner))"
    using pure tasks
    by (simp add: resume_pending_entry_rel_def)
  have abstract_member:
    "Generic t \<in> set (ring (generic_abs ?owner))"
    using abstract_member0 alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have generic_before:
    "GenericRootFamilyCoverage D ?hE GenericRootUniverse
       generic_raw generic_abs managed K_G"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_generic_coverageD[
        OF phase tasks])
  have event_before:
    "EventRootFamilyCoverage external D ?hE
       ?rawE (rps_event_family ?PE) managed K_E"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_event_coverageD[
        OF phase tasks])
  have observation_before:
    "scheduler_managed_task_observation_rel D ?hE a managed"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_observationD[
        OF phase tasks])
  have raw_member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?owner))"
    by (rule iffD2[OF GenericRootFamilyCoverage_member_iff[
        OF generic_before t_managed owner_root] abstract_member])

  have heap_after:
    "raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t) = ?hG"
    by (simp add: resume_pending_generic_remove_heap_def
        resume_pending_generic_raw_ptr_def generic_item_raw_ptr_def)
  have raw_after:
    "scheduler_family_remove_raw generic_raw ?owner
       (generic_item_raw_ptr D t) = ?rawG"
    by (simp add: resume_pending_generic_raw_after_def
        resume_pending_generic_raw_ptr_def generic_item_raw_ptr_def)
  have abs_after:
    "scheduler_family_remove_abs generic_abs ?owner (Generic t) = ?absG"
    using resume_pending_generic_abs_after[where C=C and t=t and S=P]
      alignment
    by (simp add: resume_pending_managed_phase_alignment_def
        resume_pending_event_unlink_state_def)
  have event_abs_after:
    "rps_event_family ?PE = ?absE"
    by (simp add: resume_pending_generic_unlink_state_def)

  have generic_post0:
    "GenericRootFamilyCoverage D
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_remove_raw generic_raw ?owner
         (generic_item_raw_ptr D t))
       (scheduler_family_remove_abs generic_abs ?owner (Generic t))
       managed K_G"
    by (rule GenericRootFamilyCoverage_remove_preserved[
        OF generic_before owner_root t_managed raw_member])
  have generic_post:
    "GenericRootFamilyCoverage D ?hG GenericRootUniverse
       ?rawG ?absG managed K_G"
    using generic_post0 heap_after raw_after abs_after by simp

  have event_post0:
    "EventRootFamilyCoverage external D
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       ?rawE (rps_event_family ?PE) managed K_E"
    by (rule Generic_remove_frames_Event_coverage[
        OF generic_before event_before owner_root t_managed raw_member])
  have event_post:
    "EventRootFamilyCoverage external D ?hG ?rawE ?absE managed K_E"
    using event_post0 heap_after event_abs_after by simp

  have generic_pre:
    "scheduler_family_pre_rel ?hE GenericRootUniverse
       generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_before])
  have generic_pre_view:
    "scheduler_family_pre_rel ?hE GenericRootUniverse generic_raw
       (sa_live (managed_scheduler_view a managed)) D"
    using generic_pre by (simp add: managed_scheduler_view_def)
  have observation0:
    "TaskObservationRel D ?hE (managed_scheduler_view a managed)"
    using observation_before
    by (simp add: scheduler_managed_task_observation_rel_def)
  have observation_post0:
    "TaskObservationRel D
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       (managed_scheduler_view a managed)"
    by (rule TaskObservationRel_remove_preserved[
        OF observation0 generic_pre_view owner_root raw_member])
  have observation_post:
    "scheduler_managed_task_observation_rel D ?hG a managed"
    using observation_post0 heap_after
    by (simp add: scheduler_managed_task_observation_rel_def)

  have cross_post:
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g (?rawG g) \<inter>
           raw_xlist_storage e (?rawE e) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage_all[
        OF generic_post event_post])

  have pre_and_unlinked:
    "scheduler_family_pre_rel
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_remove_raw generic_raw ?owner
         (generic_item_raw_ptr D t)) managed D \<and>
     raw_family_globally_unlinked
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_remove_raw generic_raw ?owner
         (generic_item_raw_ptr D t))
       (generic_item_raw_ptr D t)"
    by (rule scheduler_family_remove_pre_rel_and_unlinked[
        OF generic_pre owner_root raw_member])
  have unlinked0:
    "raw_family_globally_unlinked
       (raw_remove_concrete_heap ?hE (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_remove_raw generic_raw ?owner
         (generic_item_raw_ptr D t))
       (generic_item_raw_ptr D t)"
    using pre_and_unlinked by blast
  have unlinked:
    "raw_family_globally_unlinked ?hG GenericRootUniverse ?rawG ?p"
    using unlinked0 heap_after raw_after
    by (simp add: resume_pending_generic_raw_ptr_def
        generic_item_raw_ptr_def)

  have event_phase:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_EventUnlinked ?PE"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_event_unlinkedD[
        OF phase tasks])
  have generic_phase:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_GenericUnlinked ?PG"
    by (rule resume_pending_loop_phase_inv_generic_step[OF event_phase])

  show ?thesis
    using generic_post event_post observation_post cross_post unlinked
      generic_phase
    by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_generic_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "GenericRootFamilyCoverage D
       (resume_pending_generic_remove_heap D t c)
       GenericRootUniverse
       (resume_pending_generic_raw_after C D t generic_raw)
       (rps_generic_family
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t P)))
       managed K_G"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_event_coverageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "EventRootFamilyCoverage external D
       (resume_pending_generic_remove_heap D t c)
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t P)))
       managed K_E"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_observationD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_managed_task_observation_rel D
       (resume_pending_generic_remove_heap D t c) a managed"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_cross_storageD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>e\<in>EventRootUniverse external.
         raw_xlist_storage g
             (resume_pending_generic_raw_after C D t generic_raw g) \<inter>
           raw_xlist_storage e
             (resume_pending_event_raw_after C D t event_raw e) = {}"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_globally_unlinkedD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "raw_family_globally_unlinked
       (resume_pending_generic_remove_heap D t c)
       GenericRootUniverse
       (resume_pending_generic_raw_after C D t generic_raw)
       (resume_pending_generic_raw_ptr D t)"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
      OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generic_unlinkedD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_GenericUnlinked
       (resume_pending_generic_unlink_state C t
         (resume_pending_event_unlink_state C t P))"
  using CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational[
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

  val _ = audit_exact "managed Generic-remove relational capstone"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational}
  val _ = audit_exact "managed Generic-remove Generic coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_generic_coverageD}
  val _ = audit_exact "managed Generic-remove Event coverage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_event_coverageD}
  val _ = audit_exact "managed Generic-remove observation"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_observationD}
  val _ = audit_exact "managed Generic-remove cross storage"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_cross_storageD}
  val _ = audit_exact "managed Generic-remove globally unlinked"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_globally_unlinkedD}
  val _ = audit_exact "managed Generic-unlinked phase"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generic_unlinkedD}
\<close>

end

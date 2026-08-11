theory Scheduler_Resume_Managed_Reentry_Abstract_Snapshot
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Event_Role.Scheduler_Resume_Managed_Reentry_Event_Role"
begin

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_abstract_snapshotD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "cursor_general_core_wf (resume_one_pending_abs t a) \<and>
     CursorGeneralStrongManagedDomainRel
       (resume_one_pending_abs t a) termination managed \<and>
     strong_generic_role_projection
       (resume_one_pending_abs t a) termination
       (rps_generic_family (resume_pending_drained_snapshot C t P)) \<and>
     strong_event_role_projection
       (resume_one_pending_abs t a) managed external
       (rps_event_family (resume_pending_drained_snapshot C t P)) \<and>
     strong_wake_payload_projection (resume_one_pending_abs t a) K_G \<and>
     strong_one_due_snapshot_projection
       (resume_one_pending_abs t a)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))"
proof -
  note core =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_coreD[
      OF phase tasks]
  note domain =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domainD[
      OF phase]
  note generic_role =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_generic_roleD[
      OF phase tasks]
  note event_role =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_event_roleD[
      OF phase tasks]
  note wake =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_wakeD[
      OF phase]
  note one_due =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_one_due_projectionD[
      OF phase tasks]
  show ?thesis
    using core domain generic_role event_role wake one_due by blast
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "managed reentry abstract snapshot" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_abstract_snapshotD}
\<close>

end

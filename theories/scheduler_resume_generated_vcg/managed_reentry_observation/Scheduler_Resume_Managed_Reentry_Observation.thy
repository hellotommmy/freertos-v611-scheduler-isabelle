theory Scheduler_Resume_Managed_Reentry_Observation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Abstract_Snapshot.Scheduler_Resume_Managed_Reentry_Abstract_Snapshot"
begin

lemma scheduler_managed_task_observation_rel_resume_one_pending_abs_iff [simp]:
  "scheduler_managed_task_observation_rel D h
       (resume_one_pending_abs t a) managed \<longleftrightarrow>
   scheduler_managed_task_observation_rel D h a managed"
  using resume_one_pending_abs_components[of t a]
  by (simp add: scheduler_managed_task_observation_rel_def
      TaskObservationRel_def managed_scheduler_view_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observationD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_one_pending_abs t a) managed"
proof -
  note observation =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD[
      OF phase tasks]
  show ?thesis
    using observation by simp
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observed_snapshotD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "cursor_general_core_wf (resume_one_pending_abs t a) \<and>
     CursorGeneralStrongManagedDomainRel
       (resume_one_pending_abs t a) termination managed \<and>
     scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (resume_pending_ready_inserted_state D C t generic_raw c)))
       (resume_one_pending_abs t a) managed \<and>
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
         (resume_pending_drained_snapshot C t P)) \<and>
     resume_pending_snapshot_of_one_due
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P)) =
       resume_pending_drained_snapshot C t P"
proof -
  note abstract_snapshot =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_abstract_snapshotD[
      OF phase tasks]
  note observation =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observationD[
      OF phase tasks]
  note roundtrip =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_snapshot_roundtripD[
      OF phase tasks]
  show ?thesis
    using abstract_snapshot observation roundtrip by blast
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

  val _ = audit_exact "managed observation transport iff" 0
    @{thm scheduler_managed_task_observation_rel_resume_one_pending_abs_iff}
  val _ = audit_exact "managed reentry observation" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observationD}
  val _ = audit_exact "managed reentry observed snapshot" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observed_snapshotD}
\<close>

end

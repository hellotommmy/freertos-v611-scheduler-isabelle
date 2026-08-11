theory Scheduler_Resume_Managed_Reentry_Snapshot
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Concrete_Shadow.Scheduler_Resume_Managed_Reentry_Concrete_Shadow"
begin

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_public_snapshotD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) managed termination external
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))"
proof -
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?c0R =
    "scheduler_port_overlay (0 :: 32 word) (0 :: 32 word) ?cR"
  let ?after = "resume_one_pending_abs t a"
  let ?PR = "resume_pending_drained_snapshot C t P"
  let ?GR = "resume_pending_drained_generic_fam C D t c generic_raw"
  let ?ER = "resume_pending_event_raw_after C D t event_raw"
  let ?SR = "resume_pending_one_due_of_snapshot ?PR"

  note abstract_snapshot =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_abstract_snapshotD[
      OF phase tasks]
  note genericR =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD[
      OF phase tasks]
  note eventR =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD[
      OF phase tasks]
  note cross =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_cross_storageD[
      OF phase tasks]
  note concrete =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_concrete_shadowD[
      OF phase tasks]
  have generic0:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?c0R))
       GenericRootUniverse ?GR (rps_generic_family ?PR) managed K_G"
    using genericR by simp
  have event0:
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?c0R))
       ?ER (rps_event_family ?PR) managed K_E"
    using eventR by simp
  show ?thesis
    unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
    using abstract_snapshot generic0 event0 cross concrete
    by blast
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_protected_snapshotD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D (1 :: 32 word) (1 :: 32 word)
       (resume_pending_ready_inserted_state D C t generic_raw c)
       (resume_one_pending_abs t a) managed termination external
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))"
proof -
  note public =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_public_snapshotD[
      OF phase tasks]
  note concrete =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_concrete_shadowD[
      OF phase tasks]
  have overlay:
    "resume_pending_ready_inserted_state D C t generic_raw c =
       scheduler_port_overlay (1 :: 32 word) (1 :: 32 word)
         (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
           (resume_pending_ready_inserted_state D C t generic_raw c))"
    using concrete by blast
  show ?thesis
    by (rule CursorGeneralStrongProtectedSchedulerSnapshotRelI[
          OF overlay public])
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

  val _ = audit_exact "managed reentry public snapshot" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_public_snapshotD}
  val _ = audit_exact "managed reentry protected snapshot" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_protected_snapshotD}
\<close>

end

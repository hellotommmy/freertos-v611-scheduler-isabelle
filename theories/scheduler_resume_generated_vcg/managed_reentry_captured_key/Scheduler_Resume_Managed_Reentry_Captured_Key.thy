theory Scheduler_Resume_Managed_Reentry_Captured_Key
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Core.Scheduler_Resume_Managed_Reentry_Core"
begin

lemma CursorGeneralStrongResumePendingManagedGateRel_captured_keyD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> set (resume_pending_managed_tasks a)"
  shows "pending_generic_key_abs t a = K_G t"
proof -
  note owner =
    CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD[
      OF gate task]
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have role:
      "strong_generic_role_projection a termination generic_abs"
    and projection:
      "strong_one_due_snapshot_projection
         a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have owner_key:
    "item_key
       (generic_abs (resume_pending_managed_owner a t)) (Generic t) = K_G t"
    using owner projection
    by (simp add: strong_one_due_snapshot_projection_def)
  show ?thesis
    using owner_key role
    by (auto simp: pending_generic_key_abs_def
        resume_pending_managed_owner_def strong_generic_role_projection_def
        split: if_splits)
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_captured_keyD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "pending_generic_key_abs t a = rpc_K_G C t \<and>
     pending_generic_key_abs t a = K_G t"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have task_C: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have task: "t \<in> set (resume_pending_managed_tasks a)"
    using task_C alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have key: "pending_generic_key_abs t a = K_G t"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_captured_keyD[
        OF gate task])
  show ?thesis
    using key alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
qed

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

  val _ = audit_exact "managed gate captured key"
    @{thm CursorGeneralStrongResumePendingManagedGateRel_captured_keyD}
  val _ = audit_exact "managed phase captured key"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_captured_keyD}
\<close>

end

theory Scheduler_Resume_Managed_Head_TCB_Guard
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Head_Commit.Scheduler_Resume_Managed_Loop_Head_Commit"
begin

text \<open>
  The generated pending body begins with a guard on the supplied head TCB.
  The managed scheduler observation makes this address guard explicit without
  a legacy gate or an extra pointer premise.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_head_tcb_guardD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows "c_guard (sd_tcb_ptr D t)"
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
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0)"
  have observation0:
    "scheduler_managed_task_observation_rel D ?h0 a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have observation:
    "TaskObservationRel D ?h0 (managed_scheduler_view a managed)"
    using observation0
    by (simp add: scheduler_managed_task_observation_rel_def)
  have t_context: "t \<in> rpc_live C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have t_view:
    "t \<in> sa_live (managed_scheduler_view a managed)"
    using t_managed by (simp add: managed_scheduler_view_def)
  show ?thesis
    using TaskObservationRel_liveD[OF observation t_view] by blast
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_tcb_guard:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "guard (\<lambda>_. c_guard (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s. r = Result () \<and> s = c\<rbrace>"
proof -
  have guard_t: "c_guard (sd_tcb_ptr D t)"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_head_tcb_guardD[
        OF phase tasks])
  show ?thesis
    apply runs_to_vcg
    using guard_t by simp_all
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

  val _ = audit_exact "managed head TCB guard"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_head_tcb_guardD}
  val _ = audit_exact "managed generated head TCB guard"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_tcb_guard}
\<close>

end

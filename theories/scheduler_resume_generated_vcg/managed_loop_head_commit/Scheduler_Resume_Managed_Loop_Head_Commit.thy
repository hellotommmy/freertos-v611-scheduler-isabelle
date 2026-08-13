theory Scheduler_Resume_Managed_Loop_Head_Commit
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Next_Head_Read.Scheduler_Resume_Managed_Next_Head_Read"
begin

text \<open>
  Commit one fully classified pending task from the yield-checked cutpoint to
  the next loop head.  The source next-head read is state preserving, so the
  abstract current snapshot is the same yield-check state.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_loop_head_after_oneD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [t] rest RP_LoopHead
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P))"
proof -
  have checked:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_YieldChecked
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P))"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_yield_checkedD[
        OF phase tasks])
  note committed = resume_pending_loop_phase_inv_commit[OF checked]
  show ?thesis using committed by simp
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_loop_head_after_oneD}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed loop-head commit has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed loop-head commit premise ledger changed"
\<close>

end

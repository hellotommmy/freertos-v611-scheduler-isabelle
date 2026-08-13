theory Scheduler_Resume_Managed_Body_Reentry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Gate_Phase.Scheduler_Resume_Managed_Reentry_Gate_Phase"
begin

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_reentry_exact:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_body (sd_tcb_ptr D t, y) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result
         (resume_pending_next_head_tcb D rest,
          if rpc_current_priority C \<le> rpc_priority C t
          then (1 :: int) else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c \<and>
       CursorGeneralStrongResumePendingManagedPhaseRel D s
         (resume_one_pending_abs t a) managed termination external
         (resume_pending_drained_generic_fam C D t c generic_raw)
         (rps_generic_family (resume_pending_drained_snapshot C t P))
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_drained_snapshot C t P))
         K_G K_E
         (resume_pending_one_due_of_snapshot
           (resume_pending_drained_snapshot C t P))
         (resume_pending_drained_context C t rest)
         (resume_pending_drained_snapshot C t P) \<and>
       rpc_tasks (resume_pending_drained_context C t rest) = rest
     \<rbrace>"
proof -
  note body =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_exact[
      where y=y, OF phase tasks]
  note reentry =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_phaseD[
      OF phase tasks]
  have tail:
    "rpc_tasks (resume_pending_drained_context C t rest) = rest"
    using resume_pending_drained_context_components[of C t rest] by blast
  show ?thesis
  apply (rule runs_to_weaken[OF body])
  using reentry tail
  by (clarsimp split del: if_split)
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_reentry_exact}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed body reentry has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed body reentry premise ledger changed"
\<close>

end

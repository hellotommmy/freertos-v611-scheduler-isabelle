theory Scheduler_Resume_Managed_Yield_Relational
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Fragment.Scheduler_Resume_Managed_Yield_Fragment"
begin

text \<open>
  Relational classification of the generated yield comparison.  The abstract
  cut advances from ready-inserted to yield-checked, while the loop-carried
  word accumulates a prior nonzero value independently of the current task's
  yield flag.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_YieldChecked
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P)) \<and>
     rps_local_yield
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P)) =
       (rpc_current_priority C \<le> rpc_priority C t) \<and>
     (((if rpc_current_priority C \<le> rpc_priority C t
          then (1 :: int) else y) \<noteq> 0) =
       ((y \<noteq> 0) \<or>
        rps_local_yield
          (resume_pending_yield_check_state C t
            (resume_pending_drained_snapshot C t P))))"
proof -
  let ?PR = "resume_pending_drained_snapshot C t P"
  let ?PY = "resume_pending_yield_check_state C t ?PR"
  have ready:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_ReadyInserted ?PR"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insertedD[
        OF phase tasks])
  have checked:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_YieldChecked ?PY"
    by (rule resume_pending_loop_phase_inv_yield_step[OF ready])
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have entry_local: "\<not> rps_local_yield P"
    using pure by (simp add: resume_pending_entry_rel_def)
  have ready_local: "\<not> rps_local_yield ?PR"
    using resume_pending_drained_snapshot_scalars[of C t P] entry_local
    by blast
  have local:
    "rps_local_yield ?PY =
       (rpc_current_priority C \<le> rpc_priority C t)"
    using ready_local
    by (simp add: resume_pending_yield_check_state_def)
  have word:
    "(((if rpc_current_priority C \<le> rpc_priority C t
          then (1 :: int) else y) \<noteq> 0) =
       ((y \<noteq> 0) \<or> rps_local_yield ?PY))"
    using local by auto
  show ?thesis using checked local word by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_yield_checkedD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_YieldChecked
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P))"
  using CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational[
      where y="0 :: int", OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_yield_localD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "rps_local_yield
       (resume_pending_yield_check_state C t
         (resume_pending_drained_snapshot C t P)) =
       (rpc_current_priority C \<le> rpc_priority C t)"
  using CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational[
      where y="0 :: int", OF phase tasks]
  by blast

lemma CursorGeneralStrongResumePendingManagedPhaseRel_yield_word_encodingD:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "(((if rpc_current_priority C \<le> rpc_priority C t
          then (1 :: int) else y) \<noteq> 0) =
       ((y \<noteq> 0) \<or>
        rps_local_yield
          (resume_pending_yield_check_state C t
            (resume_pending_drained_snapshot C t P))))"
  using CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational[
      where y=y, OF phase tasks]
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

  val _ = audit_exact "managed yield relational capstone"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_yield_relational}
  val _ = audit_exact "managed yield-checked phase"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_yield_checkedD}
  val _ = audit_exact "managed yield local flag"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_yield_localD}
  val _ = audit_exact "managed yield word encoding"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_yield_word_encodingD}
\<close>

end

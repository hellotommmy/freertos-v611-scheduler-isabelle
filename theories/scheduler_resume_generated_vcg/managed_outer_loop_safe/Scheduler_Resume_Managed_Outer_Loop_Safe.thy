theory Scheduler_Resume_Managed_Outer_Loop_Safe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry_Factor.Scheduler_Resume_Managed_Outer_Entry_Factor"
begin

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_safe:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    and count:
      "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c"
    and pending_guard: "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and horizon:
      "let drained = drain_pending_abs a
       in resume_missed_replay_horizon_safe
            (sa_missed_ticks drained) drained"
  shows
    "let drained = drain_pending_abs a;
         pending_y = (if resume_pending_requires_yield a
                      then (1 :: int) else 0);
         replayed = replay_missed_abs (sa_missed_ticks drained) drained;
         local_y = (if 0 < sa_missed_ticks drained
                    then (1 :: int) else pending_y);
         requested = resume_managed_yield_requested local_y replayed;
         caller = resume_managed_yield_caller_abs local_y replayed;
         final_a = resume_managed_yield_final_abs local_y replayed
     in resume_outer_generated_entry_suffix \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result (if requested then (1 :: int) else 0) \<and>
          YieldAbs requested caller requested final_a \<and>
          CursorGeneralStrongSchedulerModularEndpointRel
            D t final_a managed termination external\<rbrace>"
proof -
  have horizon0:
    "resume_missed_replay_horizon_safe
       (sa_missed_ticks (drain_pending_abs a)) (drain_pending_abs a)"
    using horizon by (simp only: Let_def)
  note head =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_uniform[
      OF phase]
  note loop =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_pure[
      where y=0, OF phase]
  have guarded:
    "guard (\<lambda>s. c_guard Scheduler_V611_Parse.xPendingReadyList_') \<bullet> c
     \<lbrace>\<lambda>r s. r = Result () \<and> s = c\<rbrace>"
    apply runs_to_vcg
    by (rule pending_guard)
  have suspended_true:
    "(Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0) = True"
    using suspended by simp
  show ?thesis
    unfolding Let_def resume_outer_generated_entry_suffix_def
    apply (rule runs_to_bind_res)
    apply (simp only: runs_to_condition_iff)
    apply (simp only: suspended_true if_True)
    apply (simp only: count if_True)
    apply (rule runs_to_bind_res)
    apply (rule runs_to_weaken[OF guarded])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_bind_res)
    apply (rule runs_to_weaken[OF head])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_bind_res)
    apply (rule runs_to_weaken[OF loop])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken)
     apply (rule
       CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_bare_continuation[
         unfolded Let_def])
       apply assumption
      apply assumption
     apply (rule horizon0)
    apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken)
     apply (rule
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_exit_critical)
     apply assumption
    apply (clarsimp simp: runs_to_iff)
    done
qed

theorem
  CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_safe:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and outermost: "sa_suspend_depth a = 1"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
    and horizon:
      "let entry = resume_outer_entry_abs a;
           normalized_entry = normalize_yield_count_abs entry;
           drained = drain_pending_abs normalized_entry
       in resume_missed_replay_horizon_safe
            (sa_missed_ticks drained) drained"
  shows
    "let entry = resume_outer_entry_abs a;
         normalized_entry = normalize_yield_count_abs entry;
         drained = drain_pending_abs normalized_entry;
         pending_y = (if resume_pending_requires_yield normalized_entry
                      then (1 :: int) else 0);
         replayed = replay_missed_abs (sa_missed_ticks drained) drained;
         local_y = (if 0 < sa_missed_ticks drained
                    then (1 :: int) else pending_y);
         requested = resume_managed_yield_requested local_y replayed;
         caller = resume_managed_yield_caller_abs local_y replayed;
         final_a = resume_managed_yield_final_abs local_y replayed
     in Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result (if requested then (1 :: int) else 0) \<and>
          YieldAbs requested caller requested final_a \<and>
          CursorGeneralStrongSchedulerModularEndpointRel
            D t final_a managed termination external\<rbrace>"
proof -
  let ?entry = "resume_outer_entry_abs a"
  let ?normalized_entry = "normalize_yield_count_abs ?entry"
  have horizon0:
    "resume_missed_replay_horizon_safe
       (sa_missed_ticks (drain_pending_abs ?normalized_entry))
       (drain_pending_abs ?normalized_entry)"
    using horizon by (simp only: Let_def)
  have horizon_internal:
    "resume_missed_replay_horizon_safe
       (sa_missed_ticks
         (drain_pending_abs
           (resume_outer_entry_abs (normalize_yield_count_abs a))))
       (drain_pending_abs
         (resume_outer_entry_abs (normalize_yield_count_abs a)))"
    using horizon0 by (simp only: normalize_yield_count_abs_resume_outer_entry)
  note prefix =
    CursorGeneralStrongSchedulerModularEndpointRel_generated_outer_entry_phase[
      OF endpoint outermost current_safe, unfolded Let_def]
  show ?thesis
    unfolding Let_def xTaskResumeAll_generated_entry_prefix_factor
    apply (rule runs_to_bind_res)
    apply (rule runs_to_weaken[OF prefix])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken)
     apply (rule
       CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_safe[
         unfolded Let_def])
         apply assumption
        apply assumption
       apply assumption
      apply assumption
     apply (rule horizon_internal)
    by (simp only: normalize_yield_count_abs_resume_outer_entry)
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
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed normalized outer suffix safe" 5
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_safe}
  val _ = audit_exact "managed normalized public outer safe" 4
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_safe}
\<close>

end

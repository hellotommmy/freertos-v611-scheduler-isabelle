theory Scheduler_Resume_Managed_Replay_Split
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Capstone.Scheduler_Resume_Managed_Loop_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe"
begin

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_safe:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and horizon:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "whileLoop resume_missed_generated_cond
       resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>a'.
       r = Result () \<and>
       (CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
          D (1 :: 32 word) (1 :: 32 word) t a'
          managed termination external \<and>
        sa_suspend_depth a' = 0 \<and>
        resume_missed_replay_horizon_safe (sa_missed_ticks a') a') \<and>
       a' = replay_missed_abs (sa_missed_ticks a) a \<and>
       sa_missed_ticks a' = 0\<rbrace>"
proof -
  note tick =
    CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD[
      OF phase empty]
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    using tick by blast
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase]
  have quiet: "sa_suspend_depth a = 0"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  note safe =
    resume_missed_generated_loop_protected_horizon_safe_1_1[
      OF protected quiet horizon]
  show ?thesis
    using safe
    by (simp only:
        resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs)
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_unsafe_no_run:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and unsafe:
      "\<not> resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) c"
proof -
  note tick =
    CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD[
      OF phase empty]
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    using tick by blast
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase]
  have quiet: "sa_suspend_depth a = 0"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  show ?thesis
    by (rule
      resume_missed_generated_loop_protected_horizon_unsafe_no_run_1_1[
        OF protected quiet unsafe])
qed

ML \<open>
  fun audit_exact label th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length (Thm.prems_of th) = 3 then ()
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed horizon-safe missed replay"
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_safe}
  val _ = audit_exact "managed horizon-unsafe missed replay no-run"
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_unsafe_no_run}
\<close>

end

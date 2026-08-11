theory Scheduler_Resume_Managed_After_Drain_Continuation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Exit.Scheduler_Resume_Managed_Modular_Exit"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Outer_Compose.Scheduler_Resume_Generated_Outer_Compose"
begin

definition resume_managed_replay_choice ::
  "int \<Rightarrow> (int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_managed_replay_choice y =
     condition
       (\<lambda>s. 0 < Scheduler_V611_Parse.globals.uxMissedTicks_' s)
       (do {
          whileLoop resume_missed_generated_cond
            resume_missed_generated_body ();
          return 1
        })
       (return y)"

lemma resume_after_drain_continuation_factor:
  "resume_after_drain_continuation y =
     bind (resume_managed_replay_choice y)
       (\<lambda>local_y. resume_managed_yield_branch local_y)"
  unfolding resume_after_drain_continuation_def
    resume_managed_replay_choice_def resume_managed_yield_branch_def
  by (rule refl)

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_replay_choice_horizon_safe:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and horizon:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "let replayed = replay_missed_abs (sa_missed_ticks a) a;
         local_y = (if 0 < sa_missed_ticks a then (1 :: int) else y)
     in resume_managed_replay_choice y \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result local_y \<and>
          CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
            D (1 :: 32 word) (1 :: 32 word) t replayed
            managed termination external\<rbrace>"
proof -
  let ?replayed = "replay_missed_abs (sa_missed_ticks a) a"
  let ?local_y = "if 0 < sa_missed_ticks a then (1 :: int) else y"
  note tick =
    CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD[
      OF phase empty]
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    using tick by blast
  have modular0:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_modularI[
        OF protected])
  have count:
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_countD[
        OF protected])
  have guard_eq:
    "(0 < Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       (0 < sa_missed_ticks a)"
  proof -
    let ?w = "Scheduler_V611_Parse.globals.uxMissedTicks_' c"
    have "(0 < ?w) = (?w \<noteq> 0)"
      by (simp add: word_gt_0)
    also have "... = (unat ?w \<noteq> 0)"
      by (simp add: unat_eq_zero)
    also have "... = (0 < unat ?w)"
      by simp
    also have "... = (0 < sa_missed_ticks a)"
      using count by simp
    finally show ?thesis .
  qed
  note replay0 =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_safe[
      OF phase empty horizon]
  have replay:
    "whileLoop resume_missed_generated_cond
       resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) t ?replayed
         managed termination external\<rbrace>"
    apply (rule runs_to_weaken[OF replay0])
    apply clarsimp
    apply (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_modularI)
    by assumption
  have target:
    "resume_managed_replay_choice y \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result ?local_y \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) t ?replayed
         managed termination external\<rbrace>"
  proof (cases "0 < sa_missed_ticks a")
    case True
    have guard_true:
      "0 < Scheduler_V611_Parse.globals.uxMissedTicks_' c"
      using guard_eq True by simp
    have local_y: "?local_y = (1 :: int)"
      using True by simp
    have true_branch:
      "(do {
          whileLoop resume_missed_generated_cond
            resume_missed_generated_body ();
          return 1
        }) \<bullet> c
       \<lbrace>\<lambda>r t.
         r = Result (1 :: int) \<and>
         CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
           D (1 :: 32 word) (1 :: 32 word) t ?replayed
           managed termination external\<rbrace>"
      apply (rule runs_to_bind)
      apply (rule runs_to_weaken[OF replay])
      by clarsimp
    show ?thesis
      unfolding resume_managed_replay_choice_def
      apply (simp only: runs_to_condition_iff)
      apply (simp only: guard_true if_True)
      apply (rule runs_to_weaken[OF true_branch])
      using local_y
      by clarsimp
  next
    case False
    have guard_false:
      "\<not> (0 < Scheduler_V611_Parse.globals.uxMissedTicks_' c)"
      using guard_eq False by simp
    have zero: "sa_missed_ticks a = 0"
      using False by simp
    have replayed_eq: "?replayed = a"
      using zero by simp
    have local_y_eq: "?local_y = y"
      using False by simp
    show ?thesis
      unfolding resume_managed_replay_choice_def
      apply (simp only: runs_to_condition_iff)
      apply (simp only: guard_false if_False)
      apply runs_to_vcg
      subgoal premises positive
        using zero positive by simp
      subgoal premises positive
        using zero positive by simp
      using modular0 by assumption
  qed
  show ?thesis
    unfolding Let_def
    by (rule target)
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_bare_continuation:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and horizon:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "let replayed = replay_missed_abs (sa_missed_ticks a) a;
         local_y = (if 0 < sa_missed_ticks a then (1 :: int) else y);
         requested = resume_managed_yield_requested local_y replayed;
         caller = resume_managed_yield_caller_abs local_y replayed;
         final_a = resume_managed_yield_final_abs local_y replayed
     in resume_after_drain_continuation y \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result (if requested then (1 :: int) else 0) \<and>
          YieldAbs requested caller requested final_a \<and>
          CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
            D (1 :: 32 word) (1 :: 32 word) t final_a
            managed termination external\<rbrace>"
proof -
  let ?replayed = "replay_missed_abs (sa_missed_ticks a) a"
  let ?local_y = "if 0 < sa_missed_ticks a then (1 :: int) else y"
  have choice:
    "resume_managed_replay_choice y \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result ?local_y \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) t ?replayed
         managed termination external\<rbrace>"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_replay_choice_horizon_safe[
        where y=y, OF phase empty horizon]
    by (simp only: Let_def)
  show ?thesis
    unfolding Let_def
    apply (simp only: resume_after_drain_continuation_factor)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF choice])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken)
     apply (rule
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_yield_branch)
     apply assumption
    by blast
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_continuation_with_exit:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and horizon:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "let replayed = replay_missed_abs (sa_missed_ticks a) a;
         local_y = (if 0 < sa_missed_ticks a then (1 :: int) else y);
         requested = resume_managed_yield_requested local_y replayed;
         caller = resume_managed_yield_caller_abs local_y replayed;
         final_a = resume_managed_yield_final_abs local_y replayed
     in (do {
           result \<leftarrow> resume_after_drain_continuation y;
           ret \<leftarrow>
             Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
           return result
         }) \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result (if requested then (1 :: int) else 0) \<and>
          YieldAbs requested caller requested final_a \<and>
          CursorGeneralStrongSchedulerModularEndpointRel
            D t final_a managed termination external\<rbrace>"
proof -
  let ?replayed = "replay_missed_abs (sa_missed_ticks a) a"
  let ?local_y = "if 0 < sa_missed_ticks a then (1 :: int) else y"
  let ?requested =
    "resume_managed_yield_requested ?local_y ?replayed"
  let ?caller =
    "resume_managed_yield_caller_abs ?local_y ?replayed"
  let ?final_a =
    "resume_managed_yield_final_abs ?local_y ?replayed"
  have bare:
    "resume_after_drain_continuation y \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (if ?requested then (1 :: int) else 0) \<and>
       YieldAbs ?requested ?caller ?requested ?final_a \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) t ?final_a
         managed termination external\<rbrace>"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_bare_continuation[
        where y=y, OF phase empty horizon]
    by (simp only: Let_def)
  show ?thesis
    unfolding Let_def
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF bare])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken)
     apply (rule
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_exit_critical)
     apply assumption
    by (clarsimp simp: runs_to_iff)
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_bare_continuation_horizon_unsafe_no_run:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and unsafe:
      "\<not> resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows "\<not> succeeds (resume_after_drain_continuation y) c"
proof -
  note tick =
    CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD[
      OF phase empty]
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    using tick by blast
  have positive: "0 < sa_missed_ticks a"
    using unsafe by (cases "sa_missed_ticks a") simp_all
  have named_guard: "resume_missed_generated_cond () c"
    by (rule resume_missed_generated_cond_protected_positive[
      OF protected positive])
  have guard:
    "0 < Scheduler_V611_Parse.globals.uxMissedTicks_' c"
    using named_guard
    by (simp add: resume_missed_generated_cond_def)
  note no_loop =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_missed_loop_horizon_unsafe_no_run[
      OF phase empty unsafe]
  have no_choice:
    "\<not> succeeds (resume_managed_replay_choice y) c"
    using guard no_loop
    by (simp add: resume_managed_replay_choice_def succeeds_bind
        succeeds_condition_iff)
  show ?thesis
    using no_choice
    by (simp add: resume_after_drain_continuation_factor succeeds_bind)
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_continuation_with_exit_horizon_unsafe_no_run:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
    and unsafe:
      "\<not> resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "\<not> succeeds
       (do {
          result \<leftarrow> resume_after_drain_continuation y;
          ret \<leftarrow>
            Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
          return result
        }) c"
proof -
  have bare:
    "\<not> succeeds (resume_after_drain_continuation y) c"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_bare_continuation_horizon_unsafe_no_run[
        where y=y, OF phase empty unsafe])
  show ?thesis using bare by (simp add: succeeds_bind)
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ = if null (Thm.hyps_of th) then ()
              else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ = if actual = expected then ()
              else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "after-drain source factor" 0
    @{thm resume_after_drain_continuation_factor}
  val _ = audit_exact "managed safe replay choice" 3
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_replay_choice_horizon_safe}
  val _ = audit_exact "managed safe bare continuation" 3
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_bare_continuation}
  val _ = audit_exact "managed safe continuation with exit" 3
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_safe_continuation_with_exit}
  val _ = audit_exact "managed unsafe bare continuation" 3
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_bare_continuation_horizon_unsafe_no_run}
  val _ = audit_exact "managed unsafe continuation with exit" 3
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_continuation_with_exit_horizon_unsafe_no_run}
\<close>

end

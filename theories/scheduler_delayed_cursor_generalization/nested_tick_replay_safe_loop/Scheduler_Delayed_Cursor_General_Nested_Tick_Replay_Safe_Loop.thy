theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge"
begin

text \<open>
  A horizon-safe missed-tick replay remains at the protected proof-port
  cutpoint.  The loop relation below retains the complete cursor-general
  scheduler representation, pins the proof-port depth and interrupt mask to
  the actual nested values 1/1, keeps the scheduler quiet, and carries exactly
  the arithmetic horizon still required by the remaining concrete debt.
\<close>

lemma resume_missed_source_steps_abs_eq_replay_missed_abs:
  assumes debt: "sa_missed_ticks a = n"
  shows
    "resume_missed_source_steps_abs n a = replay_missed_abs n a"
  using debt
proof (induction n arbitrary: a)
  case 0
  show ?case by simp
next
  case (Suc n)
  have after_debt:
    "sa_missed_ticks (resume_missed_source_step_abs a) = n"
    using Suc.prems
    by (simp add: resume_missed_source_step_abs_missed_ticks)
  have after_state:
    "resume_missed_source_step_abs a =
       (tick_unlocked_abs a)\<lparr>sa_missed_ticks := n\<rparr>"
    using Suc.prems
    by (simp add: resume_missed_source_step_abs_def)
  have induction_step:
    "resume_missed_source_steps_abs n
       (resume_missed_source_step_abs a) =
     replay_missed_abs n (resume_missed_source_step_abs a)"
    by (rule Suc.IH[OF after_debt])
  show ?case
    using induction_step after_state by simp
qed

corollary
  resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs:
  "resume_missed_source_steps_abs (sa_missed_ticks a) a =
   replay_missed_abs (sa_missed_ticks a) a"
  by (rule resume_missed_source_steps_abs_eq_replay_missed_abs) simp

theorem resume_missed_generated_loop_protected_horizon_safe_1_1:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    and quiet: "sa_suspend_depth a = 0"
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
       a' = resume_missed_source_steps_abs (sa_missed_ticks a) a \<and>
       sa_missed_ticks a' = 0\<rbrace>"
proof -
  let ?Rel =
    "\<lambda>c a.
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) c a
         managed termination external \<and>
       sa_suspend_depth a = 0 \<and>
       resume_missed_replay_horizon_safe (sa_missed_ticks a) a"

  have step:
    "\<And>c a. ?Rel c a \<Longrightarrow> 0 < sa_missed_ticks a \<Longrightarrow>
       resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. r = Result () \<and>
          ?Rel t (resume_missed_source_step_abs a)\<rbrace>"
  proof -
    fix c a
    assume rel: "?Rel c a"
      and positive: "0 < sa_missed_ticks a"
    have protected:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) c a
         managed termination external"
      using rel by simp
    have quiet_before: "sa_suspend_depth a = 0"
      using rel by simp
    have horizon_before:
      "resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
      using rel by simp
    have shifted:
      "resume_tick_arithmetic_defined_abs a \<and>
       resume_missed_replay_horizon_safe
         (sa_missed_ticks (resume_missed_source_step_abs a))
         (resume_missed_source_step_abs a)"
      by (rule resume_missed_replay_horizon_safe_positive_shift[
            OF positive horizon_before])
    have abstract_defined: "resume_tick_arithmetic_defined_abs a"
      using shifted by simp
    have horizon_after:
      "resume_missed_replay_horizon_safe
         (sa_missed_ticks (resume_missed_source_step_abs a))
         (resume_missed_source_step_abs a)"
      using shifted by simp
    have arithmetic_iff:
      "generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
       resume_tick_arithmetic_defined_abs a"
      by (rule
        CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_arithmetic_defined_iff[
          OF protected])
    have concrete_defined:
      "generated_unlocked_tick_arithmetic_defined c"
      using arithmetic_iff abstract_defined by simp
    have body:
      "resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t.
         r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
           D (1 :: 32 word) (1 :: 32 word) t
           (resume_missed_source_step_abs a)
           managed termination external\<rbrace>"
      by (rule resume_missed_generated_body_protected_step_1_1[
            OF protected quiet_before positive concrete_defined])
    have quiet_after:
      "sa_suspend_depth (resume_missed_source_step_abs a) = 0"
      using quiet_before
      by (simp add: resume_missed_source_step_abs_def)
    show
      "resume_missed_generated_body () \<bullet> c
       \<lbrace>\<lambda>r t. r = Result () \<and>
          ?Rel t (resume_missed_source_step_abs a)\<rbrace>"
    proof (rule runs_to_weaken[OF body])
      fix r t
      assume post:
        "r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
           D (1 :: 32 word) (1 :: 32 word) t
           (resume_missed_source_step_abs a)
           managed termination external"
      show
        "r = Result () \<and>
         ?Rel t (resume_missed_source_step_abs a)"
        using post quiet_after horizon_after by simp
    qed
  qed

  have count:
    "\<And>c a. ?Rel c a \<Longrightarrow>
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
         sa_missed_ticks a"
  proof -
    fix c a
    assume rel: "?Rel c a"
    have protected:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) c a
         managed termination external"
      using rel by simp
    show
      "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
         sa_missed_ticks a"
      by (rule
        CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_countD[
          OF protected])
  qed

  have initial: "?Rel c a"
    using entry quiet horizon by simp
  show ?thesis
    by (rule resume_missed_generated_loop_replays[
          where Rel = ?Rel, OF step count initial])
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length prems = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString (length prems))
    in () end

  val _ = audit_exact "source steps versus replay" 1
    @{thm resume_missed_source_steps_abs_eq_replay_missed_abs}
  val _ = audit_exact "initial-debt source steps versus replay" 0
    @{thm
      resume_missed_source_steps_abs_initial_debt_eq_replay_missed_abs}
  val _ = audit_exact "protected 1/1 horizon-safe replay loop" 3
    @{thm resume_missed_generated_loop_protected_horizon_safe_1_1}
\<close>

end

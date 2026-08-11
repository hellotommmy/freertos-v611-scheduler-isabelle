theory Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Body_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Decrement_Frame.Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Decrement_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Missed_Loop.Scheduler_Resume_Generated_Missed_Loop"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Frame.Scheduler_Resume_Missed_Tick_Replay_Frame"
begin

text \<open>
  This child closes exactly one source-ordered missed-replay body step.  The
  generated tick runs first; only its successful protected post is then
  followed by the concrete modular word predecessor on uxMissedTicks.  No
  replay loop, horizon argument, or termination claim is made here.
\<close>

theorem resume_missed_generated_body_protected_step:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and positive: "0 < sa_missed_ticks a"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (resume_missed_source_step_abs a)
         managed termination external\<rbrace>"
proof -
  have tick:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (task_increment_tick_modular_abs a)
         managed termination external\<rbrace>"
    apply (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_transport_closed[
        OF entry])
    using arithmetic_defined by simp
  have missed_after_tick:
    "sa_missed_ticks (task_increment_tick_modular_abs a) =
       sa_missed_ticks a"
    using quiet
    by (simp add: task_increment_tick_modular_abs_def)
  have abstract_step:
    "(task_increment_tick_modular_abs a)\<lparr>
        sa_missed_ticks :=
          sa_missed_ticks (task_increment_tick_modular_abs a) - 1\<rparr> =
       resume_missed_source_step_abs a"
    using quiet
    by (simp add: task_increment_tick_modular_abs_def
        resume_missed_source_step_abs_def)
  have decrement:
    "\<And>t.
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (task_increment_tick_modular_abs a)
         managed termination external \<Longrightarrow>
       modify (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
         (\<lambda>w. w - 1)) \<bullet> t
       \<lbrace>\<lambda>r u.
         r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
           D depth irq_mask u (resume_missed_source_step_abs a)
           managed termination external\<rbrace>"
  proof -
    fix t
    assume relation:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (task_increment_tick_modular_abs a)
         managed termination external"
    have positive':
      "0 < sa_missed_ticks (task_increment_tick_modular_abs a)"
      using positive missed_after_tick by simp
    have frame:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask
         (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
           (\<lambda>w. w - 1) t)
         ((task_increment_tick_modular_abs a)\<lparr>
           sa_missed_ticks :=
             sa_missed_ticks (task_increment_tick_modular_abs a) - 1\<rparr>)
         managed termination external"
      by (rule
        CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_decrement_missed_tick[
          OF relation positive'])
    show
      "modify (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
         (\<lambda>w. w - 1)) \<bullet> t
       \<lbrace>\<lambda>r u.
         r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
           D depth irq_mask u (resume_missed_source_step_abs a)
           managed termination external\<rbrace>"
      apply runs_to_vcg
      using frame abstract_step by simp
  qed
  show ?thesis
    unfolding resume_missed_generated_body_def
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF tick])
     apply clarsimp
    apply (rule runs_to_weaken)
     apply (rule decrement)
     apply assumption
    by simp
qed

corollary resume_missed_generated_body_protected_step_1_1:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and positive: "0 < sa_missed_ticks a"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) t
         (resume_missed_source_step_abs a)
         managed termination external\<rbrace>"
  by (rule resume_missed_generated_body_protected_step[
        OF entry quiet positive arithmetic_defined])

ML \<open>
  val body_step = @{thm resume_missed_generated_body_protected_step}
  val body_step_1_1 = @{thm resume_missed_generated_body_protected_step_1_1}

  fun audit_0_4 label th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        (case prems of
           [_, _, _, _] => ()
         | _ => error
             (label ^ " expected exactly four premises, found " ^
              Int.toString (length prems)))
    in () end

  val _ = audit_0_4 "missed-body protected step" body_step
  val _ = audit_0_4 "missed-body protected 1/1 step" body_step_1_1
\<close>

end

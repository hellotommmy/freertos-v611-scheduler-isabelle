theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress"
begin

text \<open>
  This child converts the generated replay body's checked partial-correctness
  result into an explicit reachable successor when tick arithmetic is defined,
  and classifies the complementary first unsafe body as having no successful
  run.  Positive missed debt is needed to enter the while loop, but not to show
  that the body itself cannot succeed on an arithmetic-undefined quiet state.
\<close>

lemma vTaskIncrementTick_scheduler_port_overlay_succeeds_iff:
  "succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick'
       (scheduler_port_overlay depth irq_mask c) \<longleftrightarrow>
   succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c"
proof -
  have bisim:
    "rel_spec_monad (scheduler_port_overlay_rel depth irq_mask) (=)
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
    using scheduler_port_overlay_tick_bisim_closed[of depth irq_mask]
    by (simp add: scheduler_port_overlay_tick_bisim_def)
  show ?thesis
    apply (rule rel_spec_monad_succeeds_iff[OF bisim])
    by (simp add: scheduler_port_overlay_rel_def)
qed

theorem
  resume_missed_generated_body_protected_abstract_undefined_no_run:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and undefined: "\<not> resume_tick_arithmetic_defined_abs a"
  shows "\<not> succeeds (resume_missed_generated_body ()) c"
proof -
  have concrete_undefined:
    "\<not> generated_unlocked_tick_arithmetic_defined c"
    using
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_arithmetic_defined_iff[
        OF entry]
      undefined
    by simp
  obtain c0 where concrete:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where full:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF public] .
  have shadow_undefined:
    "\<not> generated_unlocked_tick_arithmetic_defined c0"
    using concrete_undefined concrete by simp
  have shadow_no_run:
    "\<not> succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c0"
    by (rule
      CursorGeneralStrongVTaskIncrementTickEntryRel_unlocked_arithmetic_undefined_no_run[
        OF full quiet shadow_undefined])
  have overlay_succeeds:
    "succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c \<longleftrightarrow>
     succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c0"
    using concrete
      vTaskIncrementTick_scheduler_port_overlay_succeeds_iff[
        of depth irq_mask c0]
    by simp
  have tick_no_run:
    "\<not> succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c"
    using shadow_no_run overlay_succeeds by simp
  show ?thesis
    unfolding resume_missed_generated_body_def
    using tick_no_run
    by (simp add: succeeds_bind)
qed

theorem resume_missed_generated_cond_protected_positive:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and positive: "0 < sa_missed_ticks a"
  shows "resume_missed_generated_cond () c"
proof -
  have count:
    "unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_missed_tick_countD[
        OF entry])
  have counter_positive:
    "Scheduler_V611_Parse.globals.uxMissedTicks_' c \<noteq> 0"
    using count positive
    by (metis unat_eq_zero neq0_conv)
  show ?thesis
    using counter_positive
    by (simp add: resume_missed_generated_cond_def word_neq_0_conv)
qed

theorem
  resume_missed_generated_loop_protected_immediate_abstract_undefined_no_run:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and positive: "0 < sa_missed_ticks a"
    and undefined: "\<not> resume_tick_arithmetic_defined_abs a"
  shows
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) c"
proof -
  have condition_true: "resume_missed_generated_cond () c"
    by (rule resume_missed_generated_cond_protected_positive[OF entry positive])
  have body_no_run:
    "\<not> succeeds (resume_missed_generated_body ()) c"
    by (rule
      resume_missed_generated_body_protected_abstract_undefined_no_run[
        OF entry quiet undefined])
  show ?thesis
    apply (subst whileLoop_unroll)
    using condition_true body_no_run
    by (simp add: succeeds_bind)
qed

theorem
  resume_missed_generated_body_protected_abstract_defined_reaches:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and positive: "0 < sa_missed_ticks a"
    and defined: "resume_tick_arithmetic_defined_abs a"
  shows
    "\<exists>t.
       reaches (resume_missed_generated_body ()) c (Result ()) t \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (resume_missed_source_step_abs a)
         managed termination external"
proof -
  have concrete_defined:
    "generated_unlocked_tick_arithmetic_defined c"
    using
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_arithmetic_defined_iff[
        OF entry]
      defined
    by simp
  have run:
    "resume_missed_generated_body () \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (resume_missed_source_step_abs a)
         managed termination external\<rbrace>"
    by (rule resume_missed_generated_body_protected_step[
          OF entry quiet positive concrete_defined])
  obtain r t where reach:
    "reaches (resume_missed_generated_body ()) c r t"
    using Ex_reaches[OF run resume_missed_generated_body_always_progress]
    by blast
  have post:
    "r = Result () \<and>
     CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask t (resume_missed_source_step_abs a)
       managed termination external"
    by (rule runs_toD2[OF run reach])
  show ?thesis using reach post by auto
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

  val _ = audit_exact "whole-tick overlay succeeds iff" 0
    @{thm vTaskIncrementTick_scheduler_port_overlay_succeeds_iff}
  val _ = audit_exact "abstract-undefined replay body no-run" 3
    @{thm
      resume_missed_generated_body_protected_abstract_undefined_no_run}
  val _ = audit_exact "positive protected replay condition" 2
    @{thm resume_missed_generated_cond_protected_positive}
  val _ = audit_exact "immediate abstract-undefined replay loop no-run" 4
    @{thm
      resume_missed_generated_loop_protected_immediate_abstract_undefined_no_run}
  val _ = audit_exact "abstract-defined replay body reachable successor" 4
    @{thm
      resume_missed_generated_body_protected_abstract_defined_reaches}
\<close>

end

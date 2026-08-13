theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes"
begin

text \<open>
  Negating the recursive arithmetic horizon exposes a first bad replay index.
  The prefix horizon at that index is exactly the assertion that every earlier
  body is arithmetic-defined.  The operational induction below advances those
  earlier bodies only through explicit reachable successors, then applies the
  immediate-unsafe classification at the first bad state.
\<close>

lemma resume_missed_replay_horizon_unsafe_first:
  assumes unsafe: "\<not> resume_missed_replay_horizon_safe n a"
  shows
    "\<exists>i<n.
       resume_missed_replay_horizon_safe i a \<and>
       \<not> resume_tick_arithmetic_defined_abs
         (resume_missed_source_steps_abs i a)"
  using unsafe
proof (induction n arbitrary: a)
  case 0
  show ?case using 0 by simp
next
  case (Suc n)
  show ?case
  proof (cases "resume_tick_arithmetic_defined_abs a")
    case False
    show ?thesis
      using False
      by (intro exI[where x=0]) simp
  next
    case True
    have tail_unsafe:
      "\<not> resume_missed_replay_horizon_safe n
         (resume_missed_source_step_abs a)"
      using Suc.prems True by simp
    obtain i where bound: "i < n"
      and prefix:
        "resume_missed_replay_horizon_safe i
          (resume_missed_source_step_abs a)"
      and bad:
        "\<not> resume_tick_arithmetic_defined_abs
          (resume_missed_source_steps_abs i
            (resume_missed_source_step_abs a))"
      using Suc.IH[OF tail_unsafe] by blast
    have prefix_successor:
      "resume_missed_replay_horizon_safe (Suc i) a"
      using True prefix by simp
    have bad_successor:
      "\<not> resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs (Suc i) a)"
      using bad by simp
    show ?thesis
      apply (rule exI[where x="Suc i"])
      using bound prefix_successor bad_successor by simp
  qed
qed

theorem
  resume_missed_generated_loop_protected_first_unsafe_index_no_run:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and prefix: "resume_missed_replay_horizon_safe i a"
    and bad:
      "\<not> resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i a)"
    and bound: "i < sa_missed_ticks a"
  shows
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) c"
  using entry quiet prefix bad bound
proof (induction i arbitrary: c a)
  case 0
  have positive: "0 < sa_missed_ticks a"
    using "0.prems"(5) by simp
  have undefined: "\<not> resume_tick_arithmetic_defined_abs a"
    using "0.prems"(4) by simp
  show ?case
    by (rule
      resume_missed_generated_loop_protected_immediate_abstract_undefined_no_run[
        OF "0.prems"(1) "0.prems"(2) positive undefined])
next
  case (Suc i)
  have positive: "0 < sa_missed_ticks a"
    using Suc.prems(5) by simp
  have head_defined: "resume_tick_arithmetic_defined_abs a"
    using Suc.prems(3) by simp
  have tail_prefix:
    "resume_missed_replay_horizon_safe i
       (resume_missed_source_step_abs a)"
    using Suc.prems(3) by simp
  have tail_bad:
    "\<not> resume_tick_arithmetic_defined_abs
      (resume_missed_source_steps_abs i
        (resume_missed_source_step_abs a))"
    using Suc.prems(4) by simp
  have tail_quiet:
    "sa_suspend_depth (resume_missed_source_step_abs a) = 0"
    using Suc.prems(2)
    by (simp add: resume_missed_source_step_abs_def)
  have tail_bound:
    "i < sa_missed_ticks (resume_missed_source_step_abs a)"
    using Suc.prems(5)
    by (simp add: resume_missed_source_step_abs_missed_ticks)
  obtain t where body_reach:
      "reaches (resume_missed_generated_body ()) c (Result ()) t"
    and tail_entry:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth irq_mask t (resume_missed_source_step_abs a)
         managed termination external"
    using
      resume_missed_generated_body_protected_abstract_defined_reaches[
        OF Suc.prems(1) Suc.prems(2) positive head_defined]
    by blast
  have tail_no_run:
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) t"
    by (rule Suc.IH[
          OF tail_entry tail_quiet tail_prefix tail_bad tail_bound])
  have condition_true: "resume_missed_generated_cond () c"
    by (rule resume_missed_generated_cond_protected_positive[
          OF Suc.prems(1) positive])
  show ?case
  proof
    assume loop_success:
      "succeeds
         (whileLoop resume_missed_generated_cond
            resume_missed_generated_body ()) c"
    have bind_success:
      "succeeds
         (bind (resume_missed_generated_body ())
           (whileLoop resume_missed_generated_cond
             resume_missed_generated_body)) c"
      using loop_success condition_true
      by (subst (asm) whileLoop_unroll) simp
    have continuation_success:
      "succeeds
         (whileLoop resume_missed_generated_cond
            resume_missed_generated_body ()) t"
      using bind_success body_reach
      by (auto simp: succeeds_bind)
    show False using tail_no_run continuation_success by blast
  qed
qed

theorem
  resume_missed_generated_loop_protected_horizon_unsafe_no_run:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and unsafe:
      "\<not> resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) c"
proof -
  obtain i where bound: "i < sa_missed_ticks a"
    and prefix: "resume_missed_replay_horizon_safe i a"
    and bad:
      "\<not> resume_tick_arithmetic_defined_abs
        (resume_missed_source_steps_abs i a)"
    using resume_missed_replay_horizon_unsafe_first[OF unsafe] by blast
  show ?thesis
    by (rule
      resume_missed_generated_loop_protected_first_unsafe_index_no_run[
        OF entry quiet prefix bad bound])
qed

corollary
  resume_missed_generated_loop_protected_horizon_unsafe_no_run_1_1:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    and quiet: "sa_suspend_depth a = 0"
    and unsafe:
      "\<not> resume_missed_replay_horizon_safe (sa_missed_ticks a) a"
  shows
    "\<not> succeeds
       (whileLoop resume_missed_generated_cond
          resume_missed_generated_body ()) c"
  by (rule
    resume_missed_generated_loop_protected_horizon_unsafe_no_run[
      OF entry quiet unsafe])

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

  val _ = audit_exact "first unsafe abstract replay index" 1
    @{thm resume_missed_replay_horizon_unsafe_first}
  val _ = audit_exact "protected first-unsafe-index replay no-run" 5
    @{thm
      resume_missed_generated_loop_protected_first_unsafe_index_no_run}
  val _ = audit_exact "protected horizon-unsafe replay no-run" 3
    @{thm resume_missed_generated_loop_protected_horizon_unsafe_no_run}
  val _ = audit_exact "protected 1/1 horizon-unsafe replay no-run" 3
    @{thm
      resume_missed_generated_loop_protected_horizon_unsafe_no_run_1_1}
\<close>

end

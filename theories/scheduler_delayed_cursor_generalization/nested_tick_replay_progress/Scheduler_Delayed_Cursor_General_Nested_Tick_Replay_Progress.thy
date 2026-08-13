theory Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop.Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop"
begin

text \<open>
  The Spec monad's @{const always_progress} predicate excludes only the
  bottom computation.  A generated guard failure is therefore progress, as
  is a divergent @{const whileLoop} represented by top.  The compositional
  ladder below proves this property without a scheduler relation, pointer
  validity, arithmetic-definedness, success, or loop-termination premise.
\<close>

lemma vListRemove_always_progress:
  "always_progress
     (Scheduler_V611_Delay_Translation.vListRemove' pxItemToRemove)"
  unfolding Scheduler_V611_Delay_Translation.vListRemove'_def
  by (intro always_progress_intros)

lemma vListInsertEnd_always_progress:
  "always_progress
     (Scheduler_V611_Delay_Translation.vListInsertEnd'
       pxList pxNewListItem)"
  unfolding Scheduler_V611_Delay_Translation.vListInsertEnd'_def
  by (intro always_progress_intros)

lemma one_due_tick_event_dispatch_always_progress:
  "always_progress (one_due_tick_event_dispatch_source pxTCB)"
  unfolding one_due_tick_event_dispatch_source_def
  by (intro always_progress_intros vListRemove_always_progress)

lemma one_due_tick_delayed_remainder_always_progress:
  "always_progress one_due_tick_delayed_remainder"
  unfolding one_due_tick_delayed_remainder_def
  by (intro always_progress_intros)

lemma one_due_tick_top_ready_tail_always_progress:
  "always_progress (one_due_tick_top_ready_tail_source pxTCB)"
  apply (subst one_due_tail_source_split)
  by (intro always_progress_intros
      vListInsertEnd_always_progress
      one_due_tick_delayed_remainder_always_progress)

lemma one_due_tick_after_generic_always_progress:
  "always_progress (one_due_tick_after_generic_source pxTCB)"
  unfolding one_due_tick_after_generic_source_def
  by (intro always_progress_intros
      one_due_tick_event_dispatch_always_progress
      one_due_tick_top_ready_tail_always_progress)

lemma one_due_tick_loop_body_always_progress:
  "always_progress (one_due_tick_loop_body_source pxTCB)"
  unfolding one_due_tick_loop_body_source_def
  by (intro always_progress_intros
      vListRemove_always_progress
      one_due_tick_after_generic_always_progress)

lemma one_due_tick_while_factor_always_progress:
  "always_progress
     (whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source initial)"
  by (intro always_progress_intros
      one_due_tick_loop_body_always_progress)

lemma due_prefix_generated_finally_loop_always_progress:
  "always_progress (due_prefix_generated_finally_loop initial)"
  unfolding due_prefix_generated_finally_loop_def
    due_prefix_generated_bare_loop_def
  by (intro always_progress_intros
      one_due_tick_while_factor_always_progress)

lemma generated_unlocked_tick_role_source_always_progress:
  "always_progress generated_unlocked_tick_role_source"
  unfolding generated_unlocked_tick_role_source_def
  by (intro always_progress_intros)

lemma generated_unlocked_tick_prefix_source_always_progress:
  "always_progress generated_unlocked_tick_prefix_source"
  apply (subst generated_unlocked_tick_prefix_source_split)
  by (intro always_progress_intros
      generated_unlocked_tick_role_source_always_progress
      one_due_tick_delayed_remainder_always_progress)

lemma one_due_tick_unlocked_source_always_progress:
  "always_progress one_due_tick_unlocked_source"
  apply (subst one_due_tick_unlocked_source_factor)
  by (intro always_progress_intros
      generated_unlocked_tick_prefix_source_always_progress
      due_prefix_generated_finally_loop_always_progress)

theorem vTaskIncrementTick_always_progress:
  "always_progress
     Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
  apply (subst one_due_vTaskIncrementTick_named_outer_source)
  by (intro always_progress_intros
      one_due_tick_unlocked_source_always_progress)

theorem resume_missed_generated_body_always_progress:
  "always_progress (resume_missed_generated_body ())"
  unfolding resume_missed_generated_body_def
  by (intro always_progress_intros
      vTaskIncrementTick_always_progress)

ML \<open>
  fun audit_closed label th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if null prems then ()
        else error (label ^ " has premises")
    in () end

  val _ = audit_closed "whole generated tick progress"
    @{thm vTaskIncrementTick_always_progress}
  val _ = audit_closed "missed replay body progress"
    @{thm resume_missed_generated_body_always_progress}
\<close>

end

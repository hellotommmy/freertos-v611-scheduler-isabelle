theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source"
begin

text \<open>
  This child closes only the complete named unlocked source.  The exact outer
  factorisation composes the already checked unconditional prefix with the
  already checked unconditional named finally factor for its returned TCB
  pointer.  No execution-success, arithmetic, readability, pointer, or
  termination premise is introduced.
\<close>

theorem one_due_tick_unlocked_source_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     one_due_tick_unlocked_source"
  apply (subst one_due_tick_unlocked_source_factor)
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     by (rule generated_unlocked_tick_prefix_source_tick_port_overlay_bisim)
  subgoal for pxTCB
    by (rule due_prefix_generated_finally_loop_tick_port_overlay_bisim)
  done

ML \<open>
  val unlocked_source_bisim =
    @{thm one_due_tick_unlocked_source_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of unlocked_source_bisim) then ()
    else error "unlocked-source overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of unlocked_source_bisim) then ()
    else error "unlocked-source overlay bisim has premises"
\<close>

end

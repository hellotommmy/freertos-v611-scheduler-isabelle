theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail"
begin

text \<open>
  The named after-Generic source is exactly the Event-role dispatch followed
  by the top-ready tail.  Both factors are unconditional overlay
  self-bisimulations, so relational bind composition needs no pointer, heap,
  list, branch, or successful-execution premise.
\<close>

theorem one_due_tick_after_generic_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (one_due_tick_after_generic_source pxTCB)"
  unfolding one_due_tick_after_generic_source_def
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     by (rule one_due_tick_event_dispatch_tick_port_overlay_bisim)
  subgoal
    by (rule one_due_tick_top_ready_tail_tick_port_overlay_bisim)
  done

ML \<open>
  val after_generic_bisim =
    @{thm one_due_tick_after_generic_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of after_generic_bisim) then ()
    else error "after-Generic overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of after_generic_bisim) then ()
    else error "after-Generic overlay bisim has premises"
\<close>

end

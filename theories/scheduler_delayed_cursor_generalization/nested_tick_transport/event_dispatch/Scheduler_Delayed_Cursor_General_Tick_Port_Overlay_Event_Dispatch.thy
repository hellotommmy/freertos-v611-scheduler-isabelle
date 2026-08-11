theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End"
begin

text \<open>
  The Event-role dispatch reads only the physical Event-item container through
  the scheduler heap.  The proof-port overlay frames that heap read exactly.
  Its linked branch is the unconditional generated remove leaf; its unlinked
  branch is the generated skip.  Thus no branch, pointer, heap, or list premise
  is needed.
\<close>

theorem one_due_tick_event_dispatch_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (one_due_tick_event_dispatch_source pxTCB)"
  unfolding one_due_tick_event_dispatch_source_def
  apply (rule tick_port_overlay_bisim_condition)
  subgoal
    by (simp add: one_due_tick_event_guard_def)
  subgoal
    by (rule vListRemove_tick_port_overlay_bisim)
  subgoal
    by (rule tick_port_overlay_bisim_yield)
  done

ML \<open>
  val event_dispatch_bisim =
    @{thm one_due_tick_event_dispatch_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of event_dispatch_bisim) then ()
    else error "event-dispatch overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of event_dispatch_bisim) then ()
    else error "event-dispatch overlay bisim has premises"
\<close>

end

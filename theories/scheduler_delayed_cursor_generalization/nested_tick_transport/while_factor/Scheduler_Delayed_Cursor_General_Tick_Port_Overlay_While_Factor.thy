theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body"
begin

text \<open>
  This is only the relational while factor.  The generic closure fixes
  accumulator relation equality on TCB pointers, state relation
  @{term "tick_port_overlay_rel depth irq_mask"}, and exception/result
  equality.  The guard depends only on the accumulator, so it is invariant
  under every state overlay.  No termination, non-null initial cursor, or body
  success claim is required by the relational rule.
\<close>

theorem one_due_tick_while_factor_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
       one_due_tick_loop_body_source initial)"
  apply (rule tick_port_overlay_bisim_whileLoop)
   subgoal by (rule refl)
  subgoal by (rule one_due_tick_loop_body_tick_port_overlay_bisim)
  done

ML \<open>
  val while_factor_bisim =
    @{thm one_due_tick_while_factor_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of while_factor_bisim) then ()
    else error "while-factor overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of while_factor_bisim) then ()
    else error "while-factor overlay bisim has premises"
\<close>

end

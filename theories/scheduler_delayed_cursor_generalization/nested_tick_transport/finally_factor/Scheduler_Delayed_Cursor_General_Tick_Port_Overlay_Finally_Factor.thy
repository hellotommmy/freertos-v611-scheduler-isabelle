theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor"
begin

text \<open>
  This is only the relational finally factor.  The while loop has unit
  exceptions and a TCB-pointer normal result.  Binding its normal result to
  skip retains unit exceptions and changes the normal result to unit, so the
  resulting monad has exactly the equal exception/result types required by
  the generic finally closure.  No termination, non-null initial cursor, or
  success premise is introduced.
\<close>

theorem one_due_tick_finally_factor_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (finally (do {
        pxTCB \<leftarrow> whileLoop (\<lambda>pxTCB _. pxTCB \<noteq> NULL)
          one_due_tick_loop_body_source initial;
        skip
      }))"
  apply (rule tick_port_overlay_bisim_finally)
  apply (rule tick_port_overlay_bisim_bind)
   subgoal by (rule one_due_tick_while_factor_tick_port_overlay_bisim)
  subgoal by (rule tick_port_overlay_bisim_yield)
  done

corollary due_prefix_generated_finally_loop_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (due_prefix_generated_finally_loop initial)"
  unfolding due_prefix_generated_finally_loop_def
    due_prefix_generated_bare_loop_def
  by (rule one_due_tick_finally_factor_tick_port_overlay_bisim)

ML \<open>
  val finally_factor_bisim =
    @{thm one_due_tick_finally_factor_tick_port_overlay_bisim}
  val named_finally_factor_bisim =
    @{thm due_prefix_generated_finally_loop_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of finally_factor_bisim) then ()
    else error "finally-factor overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of finally_factor_bisim) then ()
    else error "finally-factor overlay bisim has premises"
  val _ =
    if null (Thm.hyps_of named_finally_factor_bisim) then ()
    else error "named finally-factor overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of named_finally_factor_bisim) then ()
    else error "named finally-factor overlay bisim has premises"
\<close>

end

theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source"
begin

text \<open>
  This child composes exactly the two named factors in the generated prefix
  split.  Both component bisimulations are unconditional, so role-source
  arithmetic-guard failure and delayed-remainder pointer/list guard failure
  remain synchronised without defined-arithmetic, readability, or validity
  assumptions.
\<close>

theorem generated_unlocked_tick_prefix_source_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     generated_unlocked_tick_prefix_source"
  apply (subst generated_unlocked_tick_prefix_source_split)
  apply (rule tick_port_overlay_bisim_bind)
   subgoal
     by (rule generated_unlocked_tick_role_source_tick_port_overlay_bisim)
  subgoal
    by (rule one_due_tick_delayed_remainder_tick_port_overlay_bisim)
  done

ML \<open>
  val prefix_source_bisim =
    @{thm generated_unlocked_tick_prefix_source_tick_port_overlay_bisim}
  val _ =
    if null (Thm.hyps_of prefix_source_bisim) then ()
    else error "prefix-source overlay bisim has hidden hypotheses"
  val _ =
    if null (Thm.prems_of prefix_source_bisim) then ()
    else error "prefix-source overlay bisim has premises"
\<close>

end

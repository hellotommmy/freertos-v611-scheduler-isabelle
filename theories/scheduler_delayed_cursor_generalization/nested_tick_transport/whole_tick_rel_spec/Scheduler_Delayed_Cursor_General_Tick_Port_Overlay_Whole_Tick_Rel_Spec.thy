theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source"
begin

text \<open>
  This child exports only the whole generated tick relational specification.
  The existing outer-source bridge combines its already proved suspended
  branch with the unconditional unlocked-source theorem.  The generated
  function is not unfolded here, and no boundary, arithmetic, success, or
  termination premise is introduced.
\<close>

theorem vTaskIncrementTick_tick_port_overlay_rel_spec:
  "rel_spec_monad (tick_port_overlay_rel depth irq_mask) (=)
     Scheduler_V611_Delay_Translation.vTaskIncrementTick'
     Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
  by (rule vTaskIncrementTick_tick_port_overlay_bisim_from_unlocked[
        OF one_due_tick_unlocked_source_tick_port_overlay_bisim])

ML \<open>
  val whole_tick_rel_spec =
    @{thm vTaskIncrementTick_tick_port_overlay_rel_spec}
  val _ =
    if null (Thm.hyps_of whole_tick_rel_spec) then ()
    else error "whole-tick overlay rel-spec has hidden hypotheses"
  val _ =
    if null (Thm.prems_of whole_tick_rel_spec) then ()
    else error "whole-tick overlay rel-spec has premises"
\<close>

end

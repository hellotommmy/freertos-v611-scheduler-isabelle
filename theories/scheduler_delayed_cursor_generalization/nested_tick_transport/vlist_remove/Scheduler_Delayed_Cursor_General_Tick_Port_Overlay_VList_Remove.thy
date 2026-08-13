theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure"
begin

text \<open>
  The generated remove body reads scheduler memory only through @{const
  Scheduler_V611_Parse.globals.t_hrs_'} and writes it only through the
  corresponding record updater.  Since both operations commute with the
  proof-port overlay, the result below is a universal self-bisimulation: it
  has no valid-list, membership, cursor, termination, or runs-to premise.
\<close>

theorem vListRemove_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (Scheduler_V611_Delay_Translation.vListRemove' pxItemToRemove)"
  unfolding Scheduler_V611_Delay_Translation.vListRemove'_def
  apply (intro
      tick_port_overlay_bisim_bind
      tick_port_overlay_bisim_guard
      tick_port_overlay_bisim_gets
      tick_port_overlay_bisim_modify
      tick_port_overlay_bisim_condition
      tick_port_overlay_bisim_yield)
  apply (all \<open>simp add: tick_port_overlay_core_updates\<close>)
  done

end

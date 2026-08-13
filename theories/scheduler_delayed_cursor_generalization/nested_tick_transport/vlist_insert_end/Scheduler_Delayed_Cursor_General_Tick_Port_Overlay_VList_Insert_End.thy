theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove"
begin

text \<open>
  The generated insert-end body reads scheduler memory only through @{const
  Scheduler_V611_Parse.globals.t_hrs_'} and performs every state write through
  its record updater.  Consequently this self-bisimulation is independent of
  list validity, pointer validity, membership, cursor position, and execution
  success: identical guards cover all failing states on both sides.
\<close>

theorem vListInsertEnd_tick_port_overlay_bisim:
  "tick_port_overlay_bisim depth irq_mask
     (Scheduler_V611_Delay_Translation.vListInsertEnd'
       pxList pxNewListItem)"
  unfolding Scheduler_V611_Delay_Translation.vListInsertEnd'_def
  apply (intro
      tick_port_overlay_bisim_bind
      tick_port_overlay_bisim_guard
      tick_port_overlay_bisim_gets
      tick_port_overlay_bisim_modify)
  apply (all \<open>simp add: tick_port_overlay_core_updates\<close>)
  done

end

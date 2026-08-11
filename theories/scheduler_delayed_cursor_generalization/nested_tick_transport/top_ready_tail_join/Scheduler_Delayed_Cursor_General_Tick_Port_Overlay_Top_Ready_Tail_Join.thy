theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Factors.Scheduler_Unlocked_Tick_Prefix_Source_Factors"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch.Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch"
begin

text \<open>
  This compatibility heap joins the source-factor split with the checked
  proof-port overlay leaves once.  The semantic top-ready child inherits this
  merged context without replaying the cold side-session import.
\<close>

end

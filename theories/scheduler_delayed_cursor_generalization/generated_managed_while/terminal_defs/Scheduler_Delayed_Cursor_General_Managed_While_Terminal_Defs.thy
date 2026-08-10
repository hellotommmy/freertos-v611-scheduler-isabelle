theory Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero.Scheduler_Delayed_Cursor_General_Managed_While_Zero"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Finally.Scheduler_Delayed_Cursor_General_Terminal_Future_Finally"
begin

text \<open>
  Cursor-general terminal join for the managed arbitrary-prefix induction.
  Empty and future exits retain the exact last-head tuple furnished by the
  corresponding generated leaf.  The stable endpoint is cursor-general and
  never routed through the historical tail-cursor policy.
\<close>

definition cursor_general_due_prefix_managed_generated_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "cursor_general_due_prefix_managed_generated_terminal_post D now entry
       all_due future managed termination external K_G K_E r t \<longleftrightarrow>
     (case future of
        [] \<Rightarrow>
          (\<exists>processed task C branch S generic_raw event_raw before.
            all_due = processed @ [Generic task] \<and>
            r = Result NULL \<and>
            CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
              processed task C branch S generic_raw event_raw K_G K_E managed
              termination external before t)
      | f # fs \<Rightarrow>
          (\<exists>processed task C branch S generic_raw event_raw before.
            all_due = processed @ [Generic task] \<and>
            r = Exn () \<and>
            CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
              processed task f fs C branch S generic_raw event_raw K_G K_E
              managed termination external before t \<and>
            due_prefix_generated_terminal_post D now entry all_due
              (f # fs) (Exn ()) t))"

definition cursor_general_due_prefix_managed_generated_terminal_head_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "cursor_general_due_prefix_managed_generated_terminal_head_post D now entry
       all_due future managed termination external K_G K_E t \<longleftrightarrow>
     (\<exists>pxTCB generic_raw event_raw S.
       CursorGeneralStrongDuePrefixLoopHeadRel D t
         (due_prefix_fold_state entry all_due)
         managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry all_due [] (map Generic future)
         (due_prefix_exit_phase_of [] (map Generic future))
         (due_prefix_next_node_of [] (map Generic future)) pxTCB)"

definition cursor_general_due_prefix_managed_generated_complete_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "cursor_general_due_prefix_managed_generated_complete_public_post D now
       entry due_tasks future before managed termination external K_G K_E t
       \<longleftrightarrow>
     due_prefix_generated_complete_public_post D now entry due_tasks future
       before t \<and>
     cursor_general_due_prefix_managed_generated_terminal_head_post D now
       entry (map Generic due_tasks) future managed termination external
       K_G K_E t"

end

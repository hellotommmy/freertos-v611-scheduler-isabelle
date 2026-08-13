theory Scheduler_Delayed_Cursor_General_Managed_While_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone.Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally.Scheduler_Due_Prefix_Generated_While_Finally"
begin

text \<open>
  Cursor-general managed induction package for an arbitrary finite due prefix.
  A nonempty head contains exactly one shared context, Event branch, snapshot,
  and pair of raw families.  The real abstract families are the families of
  that same snapshot; no cursor is cleared or re-existentialised separately.
\<close>

definition cursor_general_due_prefix_managed_generated_head_index ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "cursor_general_due_prefix_managed_generated_head_index D R now entry
       all_due future processed task due_tail pxTCB c managed termination
       external K_G K_E \<longleftrightarrow>
     all_due = processed @ map Generic (task # due_tail) \<and>
     (\<exists>C branch S generic_raw event_raw.
       odc_task C = task \<and>
       pxTCB = sd_tcb_ptr D task \<and>
       CursorGeneralDueLoopStrongHeadRel D c
         (due_prefix_fold_state entry processed)
         managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry processed (map Generic (task # due_tail))
         (map Generic future) DueGate (Some (Generic task)) pxTCB \<and>
       due_prefix_managed_gate_inv D R c now entry processed
         (map Generic (task # due_tail)) (map Generic future)
         (due_prefix_fold_state entry processed) managed
         C branch S generic_raw event_raw)"

text \<open>
  Unified external entry.  The zero branch is an already-stable cursor-general
  head and has no Gate-H witness.  The nonempty branch has one shared tuple;
  in particular there is no desired successor state or branch premise.
\<close>

definition CursorGeneralManagedDuePrefixGeneratedEntryRel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry due_tasks
       future pxTCB managed termination external K_G K_E \<longleftrightarrow>
     (case due_tasks of
        [] \<Rightarrow>
          (\<exists>S generic_raw event_raw.
            CursorGeneralStrongDuePrefixLoopHeadRel D c entry managed
              termination external generic_raw (ods_generic_family S)
              event_raw (ods_event_family S) K_G K_E S
              now entry [] [] (map Generic future)
              (due_prefix_exit_phase_of [] (map Generic future))
              (due_prefix_next_node_of [] (map Generic future)) pxTCB)
      | task # due_tail \<Rightarrow>
          (\<exists>C branch S generic_raw event_raw.
            odc_task C = task \<and>
            pxTCB = sd_tcb_ptr D task \<and>
            CursorGeneralDueLoopStrongHeadRel D c entry managed termination
              external generic_raw (ods_generic_family S)
              event_raw (ods_event_family S) K_G K_E S
              now entry [] (map Generic (task # due_tail))
              (map Generic future) DueGate (Some (Generic task)) pxTCB \<and>
            due_prefix_managed_gate_inv D R c now entry []
              (map Generic (task # due_tail)) (map Generic future)
              entry managed C branch S generic_raw event_raw))"

definition cursor_general_due_prefix_managed_generated_zero_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "cursor_general_due_prefix_managed_generated_zero_post D now entry future
       before managed termination external K_G K_E t \<longleftrightarrow>
     t = before \<and>
     due_prefix_generated_zero_public_post D now entry future before t \<and>
     (\<exists>pxTCB S generic_raw event_raw.
       CursorGeneralStrongDuePrefixLoopHeadRel D t entry managed termination
         external generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry [] [] (map Generic future)
         (due_prefix_exit_phase_of [] (map Generic future))
         (due_prefix_next_node_of [] (map Generic future)) pxTCB)"

end

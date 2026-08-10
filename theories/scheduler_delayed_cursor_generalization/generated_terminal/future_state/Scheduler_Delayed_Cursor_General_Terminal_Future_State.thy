theory Scheduler_Delayed_Cursor_General_Terminal_Future_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready.Scheduler_Delayed_Cursor_General_Terminal_Future_Ready"
begin

definition CursorGeneralDueLoopManagedStrongTerminalFutureState ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry processed
       task f fs C branch S generic_raw event_raw K_G K_E managed termination
       external before t \<longleftrightarrow>
     (let after = due_prefix_result_step_abs entry processed (Generic task);
          h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before);
          hg = one_due_generic_remove_heap D C h0;
          he = one_due_event_remove_heap D C branch hg;
          generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
          event_raw' = one_due_event_raw_after_remove D C branch event_raw;
          S' = one_due_reentry_snapshot C branch S;
          post_c = one_due_tick_ready_inserted_state
            D C branch generic_raw before
      in t = post_c \<and>
         CursorGeneralStrongDuePrefixLoopHeadRel D t after managed termination
           external generic_raw' (ods_generic_family S')
           event_raw' (ods_event_family S') K_G K_E S'
           now entry (processed @ [Generic task]) []
           (Generic f # map Generic fs)
           FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
         due_prefix_future_source_ready D t now after f (K_G f))"

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_full_state:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry processed
       task f fs C branch S generic_raw event_raw K_G K_E managed termination
       external c (one_due_tick_ready_inserted_state
         D C branch generic_raw c)"
proof -
  have strong_cons:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # [])
       (Generic f # map Generic fs) phase next pxTCB"
    using strong by simp
  have gate_cons:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # []) (Generic f # map Generic fs) current managed
       C branch S generic_raw event_raw"
    using gate by simp
  have ptr:
    "strong_due_next_ptr_rel D
       (due_prefix_next_node_of [] (Generic f # map Generic fs))
       (sd_tcb_ptr D f)"
    by (simp add: strong_due_next_ptr_rel_def)
  note due =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_result_full_state_core[
      OF strong_cons gate_cons selector roots ptr]
  note due0 = due[unfolded Let_def]
  have terminal:
    "let after = due_prefix_result_step_abs entry processed (Generic task);
         h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
         hg = one_due_generic_remove_heap D C h0;
         he = one_due_event_remove_heap D C branch hg;
         generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
         event_raw' = one_due_event_raw_after_remove D C branch event_raw;
         S' = one_due_reentry_snapshot C branch S;
         post_c = one_due_tick_ready_inserted_state D C branch generic_raw c
     in CursorGeneralStrongDuePrefixLoopHeadRel D post_c after managed
          termination external generic_raw' (ods_generic_family S')
          event_raw' (ods_event_family S') K_G K_E S'
          now entry (processed @ [Generic task]) []
          (Generic f # map Generic fs)
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
    using CursorGeneralDueLoopStrongHeadRel_terminal_strong[OF due0]
    by (simp add: Let_def)
  note terminal0 = terminal[unfolded Let_def]
  have ready:
    "due_prefix_future_source_ready D
       (one_due_tick_ready_inserted_state D C branch generic_raw c) now
       (due_prefix_result_step_abs entry processed (Generic task)) f (K_G f)"
    by (rule
      CursorGeneralStrongDuePrefixLoopHeadRel_managed_terminal_future_ready[
        OF terminal0])
  show ?thesis
    unfolding CursorGeneralDueLoopManagedStrongTerminalFutureState_def Let_def
    using terminal0 ready by simp
qed

end

theory Scheduler_Delayed_Cursor_General_Terminal_Empty_State
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core.Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core"
begin

text \<open>
  The last-empty specialization of the arbitrary-tail cursor-general state
  assembler.  The real raw and abstract families are passed through unchanged
  at entry; the post families are the exact source-order reentry families.
\<close>

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_full_state:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [Generic task] [] phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
         [Generic task] [] current managed C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "let after =
         due_prefix_result_step_abs entry processed (Generic task);
         h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
         hg = one_due_generic_remove_heap D C h0;
         he = one_due_event_remove_heap D C branch hg;
         generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
         event_raw' = one_due_event_raw_after_remove D C branch event_raw;
         S' = one_due_reentry_snapshot C branch S;
         post_c = one_due_tick_ready_inserted_state D C branch generic_raw c
     in CursorGeneralDueLoopStrongHeadRel D post_c after managed termination
          external generic_raw' (ods_generic_family S')
          event_raw' (ods_event_family S') K_G K_E S'
          now entry (processed @ [Generic task]) [] [] EmptyExit None NULL \<and>
        CursorGeneralStrongDuePrefixLoopHeadRel D post_c after managed
          termination external generic_raw' (ods_generic_family S')
          event_raw' (ods_event_family S') K_G K_E S'
          now entry (processed @ [Generic task]) [] [] EmptyExit None NULL"
proof -
  have strong_cons:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # []) [] phase next pxTCB"
    using strong by simp
  have gate_cons:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # []) [] current managed C branch S
       generic_raw event_raw"
    using gate by simp
  have ptr:
    "strong_due_next_ptr_rel D (due_prefix_next_node_of [] []) NULL"
    by (simp add: strong_due_next_ptr_rel_def)
  note due =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_result_full_state_core[
      OF strong_cons gate_cons selector roots ptr]
  note due0 = due[unfolded Let_def]
  have stable:
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
          now entry (processed @ [Generic task]) [] [] EmptyExit None NULL"
    using CursorGeneralDueLoopStrongHeadRel_terminal_strong[OF due0]
    by (simp add: Let_def)
  show ?thesis using due stable by (simp add: Let_def)
qed

end

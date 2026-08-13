theory Scheduler_Delayed_Cursor_General_Terminal_Empty_Result
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_State.Scheduler_Delayed_Cursor_General_Terminal_Empty_State"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Terminal.Scheduler_Due_Prefix_Managed_Gate_Terminal_Bodies"
begin

definition CursorGeneralDueLoopManagedSharedLastEmptyEndpoint ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow>
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
  "CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
       task C branch S generic_raw event_raw K_G K_E managed termination
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
         one_due_tick_body_post D C branch generic_raw before
           (Result NULL) t \<and>
         due_prefix_exit_inv now entry
           (processed @ [Generic task]) [] [] after EmptyExit None \<and>
         due_prefix_terminal_source_rel D [] after EmptyExit None NULL \<and>
         due_prefix_generated_terminal_post D now entry
           (processed @ [Generic task]) [] (Result NULL) t \<and>
         CursorGeneralDueLoopStrongHeadRel D t after managed termination
           external generic_raw' (ods_generic_family S')
           event_raw' (ods_event_family S') K_G K_E S'
           now entry (processed @ [Generic task]) [] []
           EmptyExit None NULL \<and>
         CursorGeneralStrongDuePrefixLoopHeadRel D t after managed termination
           external generic_raw' (ods_generic_family S')
           event_raw' (ods_event_family S') K_G K_E S'
           now entry (processed @ [Generic task]) [] []
           EmptyExit None NULL)"

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_result_full:
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
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. r = Result NULL \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t\<rbrace>"
proof -
  have gate_C:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] [] current managed
       C branch S generic_raw event_raw"
    using gate selector by simp
  have source:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result NULL \<and>
        one_due_tick_body_post D C branch generic_raw c (Result NULL) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) [] []
          (due_prefix_result_step_abs entry processed (Generic task))
          EmptyExit None \<and>
        due_prefix_terminal_source_rel D []
          (due_prefix_result_step_abs entry processed (Generic task))
          EmptyExit None NULL) \<and>
       t = one_due_tick_ready_inserted_state
         D C branch generic_raw c\<rbrace>"
    using due_prefix_managed_generated_last_due_empty_body_full_state[
      OF gate_C roots] selector by simp
  have state_strong:
    "let after = due_prefix_result_step_abs entry processed (Generic task);
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
    by (rule
      CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_full_state[
        OF strong gate selector roots])
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "(r = Result NULL \<and>
        one_due_tick_body_post D C branch generic_raw c (Result NULL) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) [] []
          (due_prefix_result_step_abs entry processed (Generic task))
          EmptyExit None \<and>
        due_prefix_terminal_source_rel D []
          (due_prefix_result_step_abs entry processed (Generic task))
          EmptyExit None NULL) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c"
    note left = conjunct1[OF post]
    note state_eq = conjunct2[OF post]
    note r_eq = conjunct1[OF left]
    note tail1 = conjunct2[OF left]
    note body_post = conjunct1[OF tail1]
    note tail2 = conjunct2[OF tail1]
    note exit_post = conjunct1[OF tail2]
    note terminal_rel = conjunct2[OF tail2]
    have terminal_post:
      "due_prefix_generated_terminal_post D now entry
         (processed @ [Generic task]) [] (Result NULL) t"
      unfolding due_prefix_generated_terminal_post_def
      apply (rule exI[where x=
        "due_prefix_result_step_abs entry processed (Generic task)"])
      apply (rule exI[where x=EmptyExit])
      apply (rule exI[where x=None])
      apply (rule exI[where x=
        "NULL :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr"])
      apply (rule exI[where x=C])
      apply (rule exI[where x=branch])
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=c])
      using r_eq body_post exit_post terminal_rel state_eq by simp
    note pair = state_strong[unfolded Let_def]
    note due = conjunct1[OF pair]
    note stable = conjunct2[OF pair]
    show
      "r = Result NULL \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t"
      unfolding CursorGeneralDueLoopManagedSharedLastEmptyEndpoint_def Let_def
      using r_eq state_eq body_post exit_post terminal_rel terminal_post due
        stable
      by simp
  qed
qed

end

theory Scheduler_Delayed_Cursor_General_Terminal_Future_Result
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_State.Scheduler_Delayed_Cursor_General_Terminal_Future_State"
begin

definition CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost ::
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
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost D now entry
       processed task f fs C branch S generic_raw event_raw K_G K_E managed
       termination external before r t \<longleftrightarrow>
     r = Result (sd_tcb_ptr D f) \<and>
     one_due_tick_body_post D C branch generic_raw before
       (Result (sd_tcb_ptr D f)) t \<and>
     due_prefix_terminal_source_rel D (Generic f # map Generic fs)
       (due_prefix_result_step_abs entry processed (Generic task))
       FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
     CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry processed
       task f fs C branch S generic_raw event_raw K_G K_E managed termination
       external before t"

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_result_full:
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
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost D now entry
        processed task f fs C branch S generic_raw event_raw K_G K_E managed
        termination external c\<rbrace>"
proof -
  have gate_C:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs) current managed
       C branch S generic_raw event_raw"
    using gate selector by simp
  have source:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) [] (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed (Generic task))
          FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed (Generic task))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c\<rbrace>"
    using due_prefix_managed_generated_last_due_future_body_full_state[
      OF gate_C roots] selector by simp
  have strong_state:
    "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry processed
       task f fs C branch S generic_raw event_raw K_G K_E managed termination
       external c (one_due_tick_ready_inserted_state
         D C branch generic_raw c)"
    by (rule
      CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_full_state[
        OF strong gate selector roots])
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "(r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic task]) [] (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed (Generic task))
          FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed (Generic task))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c"
    have state:
      "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
         processed task f fs C branch S generic_raw event_raw K_G K_E managed
         termination external c t"
      using strong_state post by simp
    show
      "CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost D now entry
         processed task f fs C branch S generic_raw event_raw K_G K_E managed
         termination external c r t"
      unfolding CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost_def
    proof (intro conjI)
      show "r = Result (sd_tcb_ptr D f)" using post by blast
      show "one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t"
        using post by blast
      show "due_prefix_terminal_source_rel D (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed (Generic task))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
        using post by blast
      show "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
          processed task f fs C branch S generic_raw event_raw K_G K_E managed
          termination external c t"
        by (rule state)
    qed
  qed
qed

end

theory Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare.Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare"
begin

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_finally_full:
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
    "due_prefix_generated_finally_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. r = Result () \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>_ t.
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t\<rbrace>"
  proof (rule runs_to_weaken[OF
      CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_bare_loop_full[
        OF strong gate selector roots]])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result NULL \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t"
    show
      "CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t"
      using post by simp
  qed
  show ?thesis by (rule due_prefix_generated_finally_normalises[OF bare])
qed

end

theory Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Result.Scheduler_Delayed_Cursor_General_Terminal_Empty_Result"
begin

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_bare_loop_full:
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
    "due_prefix_generated_bare_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. r = Result NULL \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c t\<rbrace>"
proof -
  have head_nonnull: "sd_tcb_ptr D task \<noteq> NULL"
    using due_prefix_managed_gate_inv_head_nonnull[OF gate] selector by simp
  note body =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_result_full[
      OF strong gate selector roots]
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       Result (sd_tcb_ptr D task) = Result NULL \<and>
       CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
         task C branch S generic_raw event_raw K_G K_E managed termination
         external c c"
      using head_nonnull by simp
    show
      "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>\<lambda>q u. q = Result NULL \<and>
               CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
                 processed task C branch S generic_raw event_raw K_G K_E
                 managed termination external c u\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           Exn e = Result NULL \<and>
           CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
             processed task C branch S generic_raw event_raw K_G K_E managed
             termination external c t)\<rbrace>"
    proof -
      assume guard: "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c"
      show ?thesis
      proof (rule runs_to_weaken[OF body])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "r = Result NULL \<and>
           CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
             processed task C branch S generic_raw event_raw K_G K_E managed
             termination external c t"
        have loop_null:
          "whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source NULL \<bullet> t
           \<lbrace>\<lambda>q u. q = Result NULL \<and>
             CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
               processed task C branch S generic_raw event_raw K_G K_E managed
               termination external c u\<rbrace>"
          apply (subst runs_to_whileLoop_cond_fail)
           apply simp
          apply runs_to_vcg
          using post by simp
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>p _. p \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>\<lambda>q u. q = Result NULL \<and>
                 CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
                   processed task C branch S generic_raw event_raw K_G K_E
                   managed termination external c u\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             Exn e = Result NULL \<and>
             CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
               processed task C branch S generic_raw event_raw K_G K_E managed
               termination external c t)"
          using post loop_null by auto
      qed
    qed
  qed
qed

end

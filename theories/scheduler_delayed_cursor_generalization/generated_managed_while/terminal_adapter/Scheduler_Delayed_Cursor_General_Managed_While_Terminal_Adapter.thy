theory Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public.Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public"
begin

text \<open>
  Last-index adapter.  The shared tuple is opened once from the symbolic
  cursor-general index.  Each source branch is discharged by the matching
  cursor-general generated terminal leaf.
\<close>

theorem cursor_general_due_prefix_managed_generated_last_index_bare:
  assumes index:
    "cursor_general_due_prefix_managed_generated_head_index D R now entry
       all_due future processed task [] pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>cursor_general_due_prefix_managed_generated_terminal_post D now
       entry all_due future managed termination external K_G K_E\<rbrace>"
proof -
  obtain C branch S generic_raw event_raw where
      ledger: "all_due = processed @ [Generic task]"
    and selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and strong:
      "CursorGeneralDueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task] (map Generic future)
        DueGate (Some (Generic task)) pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed [Generic task]
        (map Generic future) (due_prefix_fold_state entry processed) managed
        C branch S generic_raw event_raw"
    using index
    by (auto simp:
        cursor_general_due_prefix_managed_generated_head_index_def)
  show ?thesis
  proof (cases future)
    case future_empty: Nil
    have strong_empty:
      "CursorGeneralDueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task] []
        DueGate (Some (Generic task)) pxTCB"
      using strong future_empty by simp
    have gate_empty:
      "due_prefix_managed_gate_inv D R c now entry processed [Generic task] []
        (due_prefix_fold_state entry processed) managed
        C branch S generic_raw event_raw"
      using gate future_empty by simp
    note terminal =
      CursorGeneralDueLoopStrongHeadRel_managed_gate_last_empty_bare_loop_full[
        OF strong_empty gate_empty selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Result NULL \<and>
         CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry
           processed task C branch S generic_raw event_raw K_G K_E managed
           termination external c t"
      show
        "cursor_general_due_prefix_managed_generated_terminal_post D now entry
           all_due future managed termination external K_G K_E r t"
        unfolding
          cursor_general_due_prefix_managed_generated_terminal_post_def
        apply (simp only: future_empty list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post by simp
    qed
  next
    case future_cons: (Cons f fs)
    have strong_future:
      "CursorGeneralDueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task]
        (Generic f # map Generic fs)
        DueGate (Some (Generic task)) pxTCB"
      using strong future_cons by simp
    have gate_future:
      "due_prefix_managed_gate_inv D R c now entry processed [Generic task]
        (Generic f # map Generic fs)
        (due_prefix_fold_state entry processed) managed
        C branch S generic_raw event_raw"
      using gate future_cons by simp
    note terminal =
      CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_bare_loop_full[
        OF strong_future gate_future selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Exn () \<and>
         CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
           processed task f fs C branch S generic_raw event_raw K_G K_E
           managed termination external c t \<and>
         due_prefix_generated_terminal_post D now entry
           (processed @ [Generic task]) (f # fs) (Exn ()) t"
      show
        "cursor_general_due_prefix_managed_generated_terminal_post D now entry
           all_due future managed termination external K_G K_E r t"
        unfolding
          cursor_general_due_prefix_managed_generated_terminal_post_def
        apply (simp only: future_cons list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post by simp
    qed
  qed
qed

end

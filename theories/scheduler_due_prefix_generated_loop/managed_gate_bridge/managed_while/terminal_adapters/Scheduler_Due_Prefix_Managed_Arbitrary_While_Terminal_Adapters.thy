theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Adapters
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Interface.Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Interface"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Terminal.Scheduler_Due_Prefix_Managed_Gate_Terminal_Future"
begin

text \<open>
  The managed terminal predicates were proved without importing the legacy
  terminal sessions.  They are definitionally the same endpoint contracts;
  these two one-way adapters expose that fact only after the execution leaves
  have been established.  Neither adapter adds a Gate-H or post-state premise.
\<close>

lemma DueLoopManagedSharedLastEmptyEndpoint_legacyI:
  assumes endpoint:
    "DueLoopManagedSharedLastEmptyEndpoint D now entry processed task C
       branch S generic_raw event_raw K_G K_E managed termination external
       before t"
  shows
    "DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
       generic_raw event_raw K_G K_E managed termination external before t"
proof -
  from endpoint show ?thesis
    unfolding DueLoopManagedSharedLastEmptyEndpoint_def
      DueLoopSharedLastEmptyEndpoint_def .
qed

lemma DueLoopManagedStrongTerminalFutureState_legacyI:
  assumes state:
    "DueLoopManagedStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       before t"
  shows
    "DueLoopStrongTerminalFutureState D now entry processed task f fs C
       branch S generic_raw event_raw K_G K_E managed termination external
       before t"
proof -
  from state show ?thesis
    unfolding DueLoopManagedStrongTerminalFutureState_def
      DueLoopStrongTerminalFutureState_def .
qed

lemma due_prefix_managed_strong_generated_terminal_post_publicD:
  assumes nonempty: "due_tasks \<noteq> []"
    and ledger: "all_due = map Generic due_tasks"
    and terminal:
      "due_prefix_managed_strong_generated_terminal_post D now entry all_due
         future managed termination external K_G K_E r t"
  shows
    "due_prefix_strong_generated_complete_public_post D now entry due_tasks
       future before managed termination external K_G K_E t"
proof -
  have old:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
    using terminal
    by (simp add: due_prefix_managed_strong_generated_terminal_post_def)
  show ?thesis
    by (rule due_prefix_strong_generated_terminal_post_publicD[
          OF nonempty ledger old])
qed

text \<open>
  Last-index adapter.  C, the Event branch, the snapshot and both raw families
  are opened from the managed symbolic index; none is supplied by the caller.
  Empty and future suffixes are kept as the two exact generated control leaves.
\<close>

theorem due_prefix_managed_strong_generated_last_index_bare:
  assumes index:
    "due_prefix_managed_strong_generated_head_index D R now entry all_due
       future processed task [] pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_managed_strong_generated_terminal_post D now entry
       all_due future managed termination external K_G K_E\<rbrace>"
proof -
  obtain C branch S generic_raw event_raw where
      ledger: "all_due = processed @ [Generic task]"
    and selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and strong:
      "DueLoopStrongHeadRel D c
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
    by (auto simp: due_prefix_managed_strong_generated_head_index_def)
  show ?thesis
  proof (cases future)
    case future_empty: Nil
    have strong_empty:
      "DueLoopStrongHeadRel D c
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
      DueLoopStrongHeadRel_managed_gate_last_empty_bare_loop_full[
        OF strong_empty gate_empty selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Result NULL \<and>
         DueLoopManagedSharedLastEmptyEndpoint D now entry processed task C
           branch S generic_raw event_raw K_G K_E managed termination external
           c t"
      have managed_endpoint:
        "DueLoopManagedSharedLastEmptyEndpoint D now entry processed task C
           branch S generic_raw event_raw K_G K_E managed termination external
           c t"
        using post by simp
      have legacy:
        "DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
           generic_raw event_raw K_G K_E managed termination external c t"
        by (rule DueLoopManagedSharedLastEmptyEndpoint_legacyI[
              OF managed_endpoint])
      show
        "due_prefix_managed_strong_generated_terminal_post D now entry all_due
           future managed termination external K_G K_E r t"
        unfolding due_prefix_managed_strong_generated_terminal_post_def
          due_prefix_strong_generated_terminal_post_def
        apply (simp only: future_empty list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post legacy by simp
    qed
  next
    case future_cons: (Cons f fs)
    have strong_future:
      "DueLoopStrongHeadRel D c
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
      DueLoopStrongHeadRel_managed_gate_last_future_bare_loop_full[
        OF strong_future gate_future selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Exn () \<and>
         DueLoopManagedStrongTerminalFutureState D now entry processed task f fs
           C branch S generic_raw event_raw K_G K_E managed termination external
           c t \<and>
         due_prefix_generated_terminal_post D now entry
           (processed @ [Generic task]) (f # fs) (Exn ()) t"
      have managed_state:
        "DueLoopManagedStrongTerminalFutureState D now entry processed task f fs
           C branch S generic_raw event_raw K_G K_E managed termination external
           c t"
        using post by simp
      have legacy_state:
        "DueLoopStrongTerminalFutureState D now entry processed task f fs C
           branch S generic_raw event_raw K_G K_E managed termination external
           c t"
        by (rule DueLoopManagedStrongTerminalFutureState_legacyI[
              OF managed_state])
      show
        "due_prefix_managed_strong_generated_terminal_post D now entry all_due
           future managed termination external K_G K_E r t"
        unfolding due_prefix_managed_strong_generated_terminal_post_def
          due_prefix_strong_generated_terminal_post_def
        apply (simp only: future_cons list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post legacy_state by simp
    qed
  qed
qed

end

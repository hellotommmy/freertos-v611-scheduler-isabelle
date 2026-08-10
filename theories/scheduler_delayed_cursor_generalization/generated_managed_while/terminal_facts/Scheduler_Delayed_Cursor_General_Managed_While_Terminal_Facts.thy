theory Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs.Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs"
begin

lemma cursor_general_due_prefix_managed_generated_terminal_post_controlD:
  assumes terminal:
    "cursor_general_due_prefix_managed_generated_terminal_post D now entry
       all_due future managed termination external K_G K_E r t"
  shows
    "(future = [] \<and> r = Result NULL) \<or>
     (\<exists>f fs. future = f # fs \<and> r = Exn ())"
  using terminal
  by (cases future)
     (auto simp:
       cursor_general_due_prefix_managed_generated_terminal_post_def)

lemma cursor_general_due_prefix_managed_generated_terminal_post_weakD:
  assumes terminal:
    "cursor_general_due_prefix_managed_generated_terminal_post D now entry
       all_due future managed termination external K_G K_E r t"
  shows "due_prefix_generated_terminal_post D now entry all_due future r t"
proof (cases future)
  case Nil
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and result: "r = Result NULL"
    and endpoint:
      "CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
        task C branch S generic_raw event_raw K_G K_E managed termination
        external before t"
    using terminal Nil
    by (auto simp:
        cursor_general_due_prefix_managed_generated_terminal_post_def)
  note endpoint0 = endpoint[
    unfolded CursorGeneralDueLoopManagedSharedLastEmptyEndpoint_def Let_def]
  note endpoint1 = conjunct2[OF endpoint0]
  note endpoint2 = conjunct2[OF endpoint1]
  note endpoint3 = conjunct2[OF endpoint2]
  note endpoint4 = conjunct2[OF endpoint3]
  have weak:
    "due_prefix_generated_terminal_post D now entry
       (processed @ [Generic task]) [] (Result NULL) t"
    by (rule conjunct1[OF endpoint4])
  show ?thesis using weak ledger result Nil by simp
next
  case (Cons f fs)
  show ?thesis
    using terminal Cons
    by (auto simp:
        cursor_general_due_prefix_managed_generated_terminal_post_def)
qed

lemma cursor_general_due_prefix_managed_generated_terminal_post_headD:
  assumes terminal:
    "cursor_general_due_prefix_managed_generated_terminal_post D now entry
       all_due future managed termination external K_G K_E r t"
  shows
    "cursor_general_due_prefix_managed_generated_terminal_head_post D now
       entry all_due future managed termination external K_G K_E t"
proof (cases future)
  case Nil
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and endpoint:
      "CursorGeneralDueLoopManagedSharedLastEmptyEndpoint D now entry processed
        task C branch S generic_raw event_raw K_G K_E managed termination
        external before t"
    using terminal Nil
    by (auto simp:
        cursor_general_due_prefix_managed_generated_terminal_post_def)
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  note endpoint0 = endpoint[
    unfolded CursorGeneralDueLoopManagedSharedLastEmptyEndpoint_def Let_def]
  note endpoint1 = conjunct2[OF endpoint0]
  note endpoint2 = conjunct2[OF endpoint1]
  note endpoint3 = conjunct2[OF endpoint2]
  note endpoint4 = conjunct2[OF endpoint3]
  note endpoint5 = conjunct2[OF endpoint4]
  have stable:
    "CursorGeneralStrongDuePrefixLoopHeadRel D t
       (due_prefix_result_step_abs entry processed (Generic task))
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) [] [] EmptyExit None NULL"
    by (rule conjunct2[OF endpoint5])
  have fold:
    "due_prefix_result_step_abs entry processed (Generic task) =
       due_prefix_fold_state entry all_due"
    using ledger by (simp add: due_prefix_result_step_abs_def)
  show ?thesis
    unfolding
      cursor_general_due_prefix_managed_generated_terminal_head_post_def
    apply (rule exI[where x=NULL])
    apply (rule exI[where x="?generic_raw'"])
    apply (rule exI[where x="?event_raw'"])
    apply (rule exI[where x="?S'"])
    using stable fold ledger Nil by simp
next
  case (Cons f fs)
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and state:
      "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
        processed task f fs C branch S generic_raw event_raw K_G K_E managed
        termination external before t"
    using terminal Cons
    by (auto simp:
        cursor_general_due_prefix_managed_generated_terminal_post_def)
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  note state0 = state[
    unfolded CursorGeneralDueLoopManagedStrongTerminalFutureState_def Let_def]
  note state1 = conjunct2[OF state0]
  have stable:
    "CursorGeneralStrongDuePrefixLoopHeadRel D t
       (due_prefix_result_step_abs entry processed (Generic task))
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) []
       (Generic f # map Generic fs) FutureExit (Some (Generic f))
       (sd_tcb_ptr D f)"
    by (rule conjunct1[OF state1])
  have fold:
    "due_prefix_result_step_abs entry processed (Generic task) =
       due_prefix_fold_state entry all_due"
    using ledger by (simp add: due_prefix_result_step_abs_def)
  show ?thesis
    unfolding
      cursor_general_due_prefix_managed_generated_terminal_head_post_def
    apply (rule exI[where x="sd_tcb_ptr D f"])
    apply (rule exI[where x="?generic_raw'"])
    apply (rule exI[where x="?event_raw'"])
    apply (rule exI[where x="?S'"])
    using stable fold ledger Cons by simp
qed

end

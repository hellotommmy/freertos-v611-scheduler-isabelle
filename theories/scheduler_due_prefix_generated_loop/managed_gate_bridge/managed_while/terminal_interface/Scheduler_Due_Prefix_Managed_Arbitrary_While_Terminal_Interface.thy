theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Interface
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Index.Scheduler_Due_Prefix_Managed_Arbitrary_While_Index"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Zero.Scheduler_Due_Prefix_Managed_Arbitrary_While_Zero"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Arbitrary_While_Lift.Scheduler_Due_Prefix_Strong_Generated_Terminal_Contracts"
begin

text \<open>
  Terminal join expected by the managed arbitrary-list induction.  The post
  is intentionally the already checked strong endpoint contract: it contains
  no entry Gate-H relation.  Only the two last-due execution leaves still
  need managed-view versions before the induction can be closed.
\<close>

definition due_prefix_managed_strong_generated_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_managed_strong_generated_terminal_post D now entry all_due
       future managed termination external K_G K_E r t \<longleftrightarrow>
     due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"

lemma due_prefix_managed_strong_generated_terminal_post_controlD:
  assumes terminal:
    "due_prefix_managed_strong_generated_terminal_post D now entry all_due
       future managed termination external K_G K_E r t"
  shows
    "(future = [] \<and> r = Result NULL) \<or>
     (\<exists>f fs. future = f # fs \<and> r = Exn ())"
proof -
  have old:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
    using terminal
    by (simp add: due_prefix_managed_strong_generated_terminal_post_def)
  show ?thesis
    by (rule due_prefix_strong_generated_terminal_post_controlD[OF old])
qed

lemma due_prefix_managed_strong_generated_terminal_post_headD:
  assumes terminal:
    "due_prefix_managed_strong_generated_terminal_post D now entry all_due
       future managed termination external K_G K_E r t"
  shows
    "due_prefix_strong_generated_terminal_head_post D now entry all_due
       future managed termination external K_G K_E t"
proof -
  have old:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
    using terminal
    by (simp add: due_prefix_managed_strong_generated_terminal_post_def)
  show ?thesis
    by (rule due_prefix_strong_generated_terminal_post_headD[OF old])
qed

text \<open>
  Exact sibling obligations (schematic names shown deliberately, not admitted
  declarations):

    DueLoopStrongHeadRel_managed_gate_last_empty_bare_loop_full

      assumes DueLoopStrongHeadRel D c current managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task] [] phase next pxTCB
      and due_prefix_managed_gate_inv D R c now entry processed
        [Generic task] [] current managed C branch S generic_raw event_raw
      and odc_task C = task
      and R = generated_scheduler_roots
      shows due_prefix_generated_bare_loop (sd_tcb_ptr D task) on c with
        r = Result NULL and
        DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
          generic_raw event_raw K_G K_E managed termination external c t.

    DueLoopStrongHeadRel_managed_gate_last_future_bare_loop_full

      assumes the same shared Strong/managed-Gate package with remaining
        [Generic task] and future Generic f # map Generic fs
      and odc_task C = task
      and R = generated_scheduler_roots
      shows the bare loop returns Exn () and establishes both
        DueLoopStrongTerminalFutureState D now entry processed task f fs C
          branch S generic_raw event_raw K_G K_E managed termination external
          c t
      and due_prefix_generated_terminal_post D now entry
        (processed @ [Generic task]) (f # fs) (Exn ()) t.

  These are derived execution theorems, never successor-post premises.  Once supplied by
  the terminal sibling staircase, the Nil induction leaf can package either
  result directly into due_prefix_managed_strong_generated_terminal_post;
  the Cons leaf already uses
  due_prefix_managed_strong_generated_nonlast_index_step.
\<close>

end

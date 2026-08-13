theory Scheduler_Delayed_Cursor_General_Managed_While_Complete
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While.Scheduler_Delayed_Cursor_General_Managed_While"
begin

lemma cursor_general_due_prefix_managed_generated_zero_post_completeD:
  assumes zero:
    "cursor_general_due_prefix_managed_generated_zero_post D now entry future
       before managed termination external K_G K_E t"
  shows
    "cursor_general_due_prefix_managed_generated_complete_public_post D now
       entry [] future before managed termination external K_G K_E t"
proof -
  note facts = zero[
    unfolded cursor_general_due_prefix_managed_generated_zero_post_def]
  have state: "t = before"
    by (rule conjunct1[OF facts])
  note tail = conjunct2[OF facts]
  have weak_zero:
    "due_prefix_generated_zero_public_post D now entry future before t"
    by (rule conjunct1[OF tail])
  obtain terminal_pxTCB S generic_raw event_raw where head:
    "CursorGeneralStrongDuePrefixLoopHeadRel D t entry managed termination
       external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) terminal_pxTCB"
    using conjunct2[OF tail] by blast
  obtain q where zero_terminal:
    "due_prefix_generated_zero_terminal_post D now entry future before q t"
    using weak_zero
    by (auto simp: due_prefix_generated_zero_public_post_def)
  have weak_complete:
    "due_prefix_generated_complete_public_post D now entry [] future before t"
    unfolding due_prefix_generated_complete_public_post_def
    apply (rule exI[where x=q])
    using zero_terminal
    by (simp add: due_prefix_generated_complete_terminal_post_def)
  have fold: "due_prefix_fold_state entry [] = entry"
    by (simp add: due_prefix_fold_state_def remove_nodes_def)
  have stable_head:
    "cursor_general_due_prefix_managed_generated_terminal_head_post D now
       entry [] future managed termination external K_G K_E t"
    unfolding
      cursor_general_due_prefix_managed_generated_terminal_head_post_def
    apply (rule exI[where x=terminal_pxTCB])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=S])
    using head fold by simp
  show ?thesis
    using weak_complete stable_head
    by (simp add:
        cursor_general_due_prefix_managed_generated_complete_public_post_def)
qed

theorem CursorGeneralManagedDuePrefixGeneratedEntryRel_zero_finally_complete:
  assumes entry_rel:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry [] future c managed termination external K_G K_E t\<rbrace>"
proof -
  note zero =
    CursorGeneralManagedDuePrefixGeneratedEntryRel_zero_finally[OF entry_rel]
  show ?thesis
    apply (rule runs_to_weaken[OF zero])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       cursor_general_due_prefix_managed_generated_zero_post D now entry
         future c managed termination external K_G K_E t"
    have zero_post:
      "cursor_general_due_prefix_managed_generated_zero_post D now entry
        future c managed termination external K_G K_E t"
      using post by simp
    have complete_post:
      "cursor_general_due_prefix_managed_generated_complete_public_post D now
        entry [] future c managed termination external K_G K_E t"
      by (rule
        cursor_general_due_prefix_managed_generated_zero_post_completeD[OF
          zero_post])
    show
      "r = Result () \<and>
       cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry [] future c managed termination external K_G K_E t"
      apply (rule conjI)
      subgoal using post by simp
      by (rule complete_post)
  qed
    done
qed

text \<open>
  Public arbitrary-finite managed theorem.  Every task, priority, tick, queue
  length, family, cursor, heap address, and future suffix remains symbolic.
  The conclusion is derived solely from generated execution and the unified
  cursor-general entry relation.
\<close>

theorem CursorGeneralManagedDuePrefixGeneratedEntryRel_finally_complete_exact:
  assumes entry_rel:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry due_tasks
       future pxTCB managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry due_tasks future c managed termination external K_G K_E t\<rbrace>"
proof (cases due_tasks)
  case Nil
  have zero_entry:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
    using entry_rel Nil by simp
  note zero =
    CursorGeneralManagedDuePrefixGeneratedEntryRel_zero_finally_complete[
      OF zero_entry]
  show ?thesis using zero Nil by simp
next
  case (Cons task due_tail)
  have nonempty_entry:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry
       (task # due_tail) future pxTCB managed termination external K_G K_E"
    using entry_rel Cons by simp
  have index:
    "cursor_general_due_prefix_managed_generated_head_index D R now entry
       (map Generic (task # due_tail)) future [] task due_tail pxTCB c
       managed termination external K_G K_E"
    by (rule
      CursorGeneralManagedDuePrefixGeneratedEntryRel_nonempty_indexD[
        OF nonempty_entry])
  have exact_run:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<exists>q. cursor_general_due_prefix_managed_generated_terminal_post
         D now entry (map Generic (task # due_tail)) future managed termination
         external K_G K_E q t)\<rbrace>"
    by (rule
      cursor_general_due_prefix_managed_generated_finally_loop_nonempty[
        OF index roots])
  show ?thesis
    apply (rule runs_to_weaken[OF exact_run])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       (\<exists>q. cursor_general_due_prefix_managed_generated_terminal_post
         D now entry (map Generic (task # due_tail)) future managed termination
         external K_G K_E q t)"
    obtain q where terminal:
      "cursor_general_due_prefix_managed_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t"
      using post by blast
    have public:
      "cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry (task # due_tail) future c managed termination external
         K_G K_E t"
      by (rule
        cursor_general_due_prefix_managed_generated_terminal_post_publicD[
          OF _ _ terminal]) simp_all
    have public_due:
      "cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry due_tasks future c managed termination external K_G K_E t"
      using public Cons by simp
    have result0: "r = Result ()"
      by (rule conjunct1[OF post])
    show
      "r = Result () \<and>
       cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry due_tasks future c managed termination external K_G K_E t"
      by (rule conjI[OF result0 public_due])
  qed
    done
qed

end

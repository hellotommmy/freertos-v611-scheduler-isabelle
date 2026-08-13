theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Complete
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While.Scheduler_Due_Prefix_Managed_Arbitrary_While"
begin

text \<open>
  Zero-due adapter.  The checked managed zero theorem already supplies the
  unchanged strong endpoint and exact generated zero post.  This lemma only
  packages those facts into the same complete public contract used by the
  nonempty induction.
\<close>

lemma due_prefix_managed_generated_zero_strong_post_completeD:
  assumes zero:
    "due_prefix_managed_generated_zero_strong_post D now entry future before
       managed termination external K_G K_E t"
  shows
    "due_prefix_strong_generated_complete_public_post D now entry [] future
       before managed termination external K_G K_E t"
proof -
  note zero_facts =
    zero[unfolded due_prefix_managed_generated_zero_strong_post_def]
  have state: "t = before"
    by (rule conjunct1[OF zero_facts])
  note zero_tail = conjunct2[OF zero_facts]
  have weak_zero:
    "due_prefix_generated_zero_public_post D now entry future before t"
    by (rule conjunct1[OF zero_tail])
  obtain terminal_pxTCB S generic_raw event_raw where head:
    "StrongDuePrefixLoopHeadRel D t entry managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) terminal_pxTCB"
    using conjunct2[OF zero_tail] by blast
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
  have strong_head:
    "due_prefix_strong_generated_terminal_head_post D now entry [] future
       managed termination external K_G K_E t"
    unfolding due_prefix_strong_generated_terminal_head_post_def
    apply (rule exI[where x=terminal_pxTCB])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=S])
    using head fold by simp
  show ?thesis
    using weak_complete strong_head
    by (simp add: due_prefix_strong_generated_complete_public_post_def)
qed

theorem ManagedStrongDuePrefixGeneratedEntryRel_zero_finally_complete_exact:
  assumes entry_rel:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry [] future
         c managed termination external K_G K_E t\<rbrace>"
proof -
  note zero =
    ManagedStrongDuePrefixGeneratedEntryRel_zero_finally_strong[OF entry_rel]
  show ?thesis
    apply (rule runs_to_weaken[OF zero])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       due_prefix_managed_generated_zero_strong_post D now entry future c
         managed termination external K_G K_E t"
    have zero_post:
      "due_prefix_managed_generated_zero_strong_post D now entry future c
         managed termination external K_G K_E t"
      using post by simp
    have exact:
      "due_prefix_strong_generated_complete_public_post D now entry [] future
         c managed termination external K_G K_E t"
      by (rule due_prefix_managed_generated_zero_strong_post_completeD[
            OF zero_post])
    show
      "r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry [] future
         c managed termination external K_G K_E t"
      apply (rule conjI)
      subgoal using post by simp
      by (rule exact)
  qed
    done
qed

text \<open>
  Public arbitrary-finite managed theorem.  due_tasks and future are arbitrary,
  including the genuine zero-due path.  For a nonempty list, C, branch, S and
  both raw families are existential fields of ManagedStrongDuePrefixGenerated-
  EntryRel and remain hidden from the caller.  No task, priority, tick, wake
  time, list length, heap address or generated exit value is fixed.
\<close>

theorem ManagedStrongDuePrefixGeneratedEntryRel_finally_complete_exact:
  assumes entry_rel:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry due_tasks future
       pxTCB managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future c managed termination external K_G K_E t\<rbrace>"
proof (cases due_tasks)
  case Nil
  have zero_entry:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
    using entry_rel Nil by simp
  note zero =
    ManagedStrongDuePrefixGeneratedEntryRel_zero_finally_complete_exact[
      OF zero_entry]
  show ?thesis using zero Nil by simp
next
  case (Cons task due_tail)
  have nonempty_entry:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry
       (task # due_tail) future pxTCB managed termination external K_G K_E"
    using entry_rel Cons by simp
  have index:
    "due_prefix_managed_strong_generated_head_index D R now entry
       (map Generic (task # due_tail)) future [] task due_tail pxTCB c
       managed termination external K_G K_E"
    by (rule ManagedStrongDuePrefixGeneratedEntryRel_nonempty_indexD[
          OF nonempty_entry])
  have exact:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<exists>q. due_prefix_managed_strong_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t)\<rbrace>"
    by (rule due_prefix_managed_strong_generated_finally_loop_nonempty[
          OF index roots])
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       (\<exists>q. due_prefix_managed_strong_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t)"
    obtain q where terminal:
      "due_prefix_managed_strong_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t"
      using post by blast
    have public:
      "due_prefix_strong_generated_complete_public_post D now entry
         (task # due_tail) future c managed termination external K_G K_E t"
      by (rule due_prefix_managed_strong_generated_terminal_post_publicD[
            OF _ _ terminal]) simp_all
    have result: "r = Result ()"
      using post by simp
    have public_due:
      "due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future c managed termination external K_G K_E t"
      using public Cons by simp
    show
      "r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future c managed termination external K_G K_E t"
      by (rule conjI[OF result public_due])
  qed
    done
qed

end

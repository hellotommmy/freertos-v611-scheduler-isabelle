theory Scheduler_Due_Prefix_Strong_Generated_Complete
  imports Scheduler_Due_Prefix_Strong_Generated_While
begin

text \<open>
  The zero-due branch is state preserving.  This adapter reuses the exact
  entry families and the fixed payload observations after finally normalises
  either the false guard or the future-head exception.  It is kept separate
  from the nonempty induction because zero due tasks have no Gate-H context.
\<close>

theorem StrongDuePrefixGeneratedEntryRel_zero_finally_exact:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry [] future
         c managed termination external K_G K_E t\<rbrace>"
proof -
  obtain phase nxt where head:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (map Generic future) phase nxt pxTCB"
    using rel
    by (auto simp: StrongDuePrefixGeneratedEntryRel_def)
  have weak:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       strong_due_prefix_generated_complete_public_post D now entry
         [] future c managed termination external t\<rbrace>"
    by (rule StrongDuePrefixGeneratedEntryRel_zero_finally_strong[
          OF rel roots])
  show ?thesis
    apply (rule runs_to_weaken[OF weak])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       strong_due_prefix_generated_complete_public_post D now entry
         [] future c managed termination external t"
    have result: "r = Result ()"
      using post by simp
    have weak_public:
      "due_prefix_generated_complete_public_post D now entry [] future c t"
      using post
      by (simp add: strong_due_prefix_generated_complete_public_post_def)
    have state: "t = c"
      using weak_public
      by (auto simp: due_prefix_generated_complete_public_post_def
          due_prefix_generated_complete_terminal_post_def
          due_prefix_generated_zero_public_post_def
          due_prefix_generated_zero_terminal_post_def)
    note snapshot = StrongDuePrefixLoopHeadRel_snapshotD[OF head]
    have families:
      "generic_abs = ods_generic_family S \<and>
       event_abs = ods_event_family S"
      using StrongSchedulerSnapshotRel_snapshot_pinsD[OF snapshot]
      by blast
    note exit = StrongDuePrefixLoopHeadRel_exitD[OF head]
    have phase_eq:
      "phase = due_prefix_exit_phase_of [] (map Generic future)"
      by (rule due_prefix_exit_inv_phaseD[OF exit])
    have next_eq:
      "nxt = due_prefix_next_node_of [] (map Generic future)"
      by (rule due_prefix_exit_inv_nextD[OF exit])
    have fold: "due_prefix_fold_state entry [] = entry"
      by (simp add: due_prefix_fold_state_def remove_nodes_def)
    have strong_head:
      "due_prefix_strong_generated_terminal_head_post D now entry [] future
        managed termination external K_G K_E t"
      unfolding due_prefix_strong_generated_terminal_head_post_def
      apply (rule exI[where x=pxTCB])
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=event_raw])
      apply (rule exI[where x=S])
      using head state families phase_eq next_eq fold
      by simp
    have exact_public:
      "due_prefix_strong_generated_complete_public_post D now entry [] future
        c managed termination external K_G K_E t"
      using weak_public strong_head
      by (simp add: due_prefix_strong_generated_complete_public_post_def)
    show
      "r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry [] future
         c managed termination external K_G K_E t"
      by (rule conjI[OF result exact_public])
  qed
    done
qed

text \<open>
  Public arbitrary-finite strong theorem.  Both due_tasks and future are
  universally quantified, including the zero-length due prefix.  In the
  nonempty case the exact all_due ledger is map Generic due_tasks; the
  terminal head therefore denotes precisely
  due_prefix_fold_state entry (map Generic due_tasks).  No task identity,
  priority, tick, key, cursor, branch, heap address or list length is fixed.
\<close>

theorem StrongDuePrefixGeneratedEntryRel_finally_complete_exact:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry due_tasks future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future c managed termination external K_G K_E t\<rbrace>"
proof (cases due_tasks)
  case Nil
  have rel_zero:
    "StrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    using rel Nil by simp
  note zero = StrongDuePrefixGeneratedEntryRel_zero_finally_exact[
    OF rel_zero roots]
  show ?thesis using zero Nil by simp
next
  case (Cons task due_tail)
  have rel_nonempty:
    "StrongDuePrefixGeneratedEntryRel D R c now entry (task # due_tail) future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    using rel Cons by simp
  have index:
    "due_prefix_strong_generated_head_index D R now entry
       (map Generic (task # due_tail)) future [] task due_tail pxTCB c
       managed termination external K_G K_E"
    by (rule StrongDuePrefixGeneratedEntryRel_nonempty_head_indexD[
          OF rel_nonempty])
  have exact:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<exists>q. due_prefix_strong_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t)\<rbrace>"
    by (rule due_prefix_strong_generated_finally_loop_nonempty[
          OF index roots])
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       (\<exists>q. due_prefix_strong_generated_terminal_post D now entry
         (map Generic (task # due_tail)) future managed termination external
         K_G K_E q t)"
    obtain q where terminal:
      "due_prefix_strong_generated_terminal_post D now entry
        (map Generic (task # due_tail)) future managed termination external
        K_G K_E q t"
      using post by blast
    have public:
      "due_prefix_strong_generated_complete_public_post D now entry
        (task # due_tail) future c managed termination external K_G K_E t"
      by (rule due_prefix_strong_generated_terminal_post_publicD[
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

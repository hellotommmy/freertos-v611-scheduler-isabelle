theory Scheduler_Delayed_Cursor_General_Managed_While_Zero
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Index.Scheduler_Delayed_Cursor_General_Managed_While_Index"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready.Scheduler_Delayed_Cursor_General_Terminal_Future_Ready"
begin

lemma CursorGeneralStrongDuePrefixLoopHeadRel_managed_generated_zero_entryI:
  assumes strong:
    "CursorGeneralStrongDuePrefixLoopHeadRel D c entry managed termination
       external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future) phase next pxTCB"
  shows
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
proof -
  have exit:
    "due_prefix_exit_inv now entry [] [] (map Generic future) entry phase next"
    using strong
    by (simp add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
  have phase_eq:
    "phase = due_prefix_exit_phase_of [] (map Generic future)"
    by (rule due_prefix_exit_inv_phaseD[OF exit])
  have next_eq:
    "next = due_prefix_next_node_of [] (map Generic future)"
    by (rule due_prefix_exit_inv_nextD[OF exit])
  show ?thesis
    unfolding CursorGeneralManagedDuePrefixGeneratedEntryRel_def
    apply (simp only: list.case)
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using strong phase_eq next_eq by simp
qed

theorem CursorGeneralManagedDuePrefixGeneratedEntryRel_zero_finally:
  assumes entry_rel:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       cursor_general_due_prefix_managed_generated_zero_post D now entry
         future c managed termination external K_G K_E t\<rbrace>"
proof -
  obtain S generic_raw event_raw where head:
    "CursorGeneralStrongDuePrefixLoopHeadRel D c entry managed termination
       external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using entry_rel
    by (auto simp: CursorGeneralManagedDuePrefixGeneratedEntryRel_def)
  have exit:
    "due_prefix_exit_inv now entry [] [] (map Generic future) entry
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future))"
    and ptr:
      "strong_due_next_ptr_rel D
        (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using head
    by (simp_all add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
  have empty:
    "future = [] \<Longrightarrow>
       pxTCB = NULL \<and>
       due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
  proof -
    assume future_empty: "future = []"
    have exit_empty:
      "due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
      using exit future_empty by simp
    have ptr_empty: "pxTCB = NULL"
      using ptr future_empty
      by (auto simp: strong_due_next_ptr_rel_def)
    show ?thesis using ptr_empty exit_empty by simp
  qed
  have nonempty:
    "\<And>f fs. future = f # fs \<Longrightarrow>
      \<exists>k. pxTCB = sd_tcb_ptr D f \<and>
        due_prefix_exit_inv now entry [] []
          (Generic f # map Generic fs) entry
          FutureExit (Some (Generic f)) \<and>
        due_prefix_future_source_ready D c now entry f k"
  proof -
    fix f fs
    assume future_cons: "future = f # fs"
    have head_future:
      "CursorGeneralStrongDuePrefixLoopHeadRel D c entry managed termination
        external generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry [] [] (Generic f # map Generic fs)
        FutureExit (Some (Generic f)) pxTCB"
      using head future_cons by simp
    have exit_future:
      "due_prefix_exit_inv now entry [] []
        (Generic f # map Generic fs) entry
        FutureExit (Some (Generic f))"
      using exit future_cons by simp
    have ptr_future: "pxTCB = sd_tcb_ptr D f"
      using ptr future_cons
      by (auto simp: strong_due_next_ptr_rel_def)
    have ready: "due_prefix_future_source_ready D c now entry f (K_G f)"
      by (rule
        CursorGeneralStrongDuePrefixLoopHeadRel_managed_terminal_future_ready[
          OF head_future])
    show
      "\<exists>k. pxTCB = sd_tcb_ptr D f \<and>
        due_prefix_exit_inv now entry [] []
          (Generic f # map Generic fs) entry
          FutureExit (Some (Generic f)) \<and>
        due_prefix_future_source_ready D c now entry f k"
      apply (rule exI[where x="K_G f"])
      using ptr_future exit_future ready by simp
  qed
  have weak:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_zero_public_post D now entry future c t\<rbrace>"
    by (rule due_prefix_generated_zero_due_finally_loop[OF empty nonempty])
  show ?thesis
    apply (rule runs_to_weaken[OF weak])
    subgoal for r t
  proof -
    assume post:
      "r = Result () \<and>
       due_prefix_generated_zero_public_post D now entry future c t"
    have result0: "r = Result ()"
      by (rule conjunct1[OF post])
    have state: "t = c"
      using post
      by (auto simp: due_prefix_generated_zero_public_post_def
          due_prefix_generated_zero_terminal_post_def)
    have head_at_t:
      "CursorGeneralStrongDuePrefixLoopHeadRel D t entry managed termination
        external generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry [] [] (map Generic future)
        (due_prefix_exit_phase_of [] (map Generic future))
        (due_prefix_next_node_of [] (map Generic future)) pxTCB"
      using head state by simp
    have zero_post:
      "cursor_general_due_prefix_managed_generated_zero_post D now entry
        future c managed termination external K_G K_E t"
      unfolding cursor_general_due_prefix_managed_generated_zero_post_def
      apply (intro conjI)
      subgoal by (rule state)
      subgoal using post by simp
      apply (rule exI[where x=pxTCB])
      apply (rule exI[where x=S])
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=event_raw])
      by (rule head_at_t)
    show
      "r = Result () \<and>
       cursor_general_due_prefix_managed_generated_zero_post D now entry
         future c managed termination external K_G K_E t"
      by (rule conjI[OF result0 zero_post])
  qed
    done
qed

end

theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Zero
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs.Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs"
begin

text \<open>
  The zero-due constructor consumes only a stable Strong head.  There is no
  Gate-H relation in either its assumptions or conclusion, and no generated
  root equality is required because no due body mutates the state.
\<close>

lemma StrongDuePrefixLoopHeadRel_managed_generated_zero_entryI:
  assumes strong:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future) phase nxt pxTCB"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
proof -
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF strong]
  have phase_eq:
    "phase = due_prefix_exit_phase_of [] (map Generic future)"
    by (rule due_prefix_exit_inv_phaseD[OF exit])
  have next_eq:
    "nxt = due_prefix_next_node_of [] (map Generic future)"
    by (rule due_prefix_exit_inv_nextD[OF exit])
  show ?thesis
    unfolding ManagedStrongDuePrefixGeneratedEntryRel_def
    apply (simp only: list.case)
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using strong phase_eq next_eq by simp
qed

theorem ManagedStrongDuePrefixGeneratedEntryRel_zero_finally_strong:
  assumes entry_rel:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external K_G K_E"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_managed_generated_zero_strong_post D now entry future c
         managed termination external K_G K_E t\<rbrace>"
proof -
  obtain S generic_raw event_raw where head:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using entry_rel
    by (auto simp: ManagedStrongDuePrefixGeneratedEntryRel_def)
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF head]
  note ptr = StrongDuePrefixLoopHeadRel_ptrD[OF head]
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
      "StrongDuePrefixLoopHeadRel D c entry managed termination external
        generic_raw (ods_generic_family S)
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
    have ready:
      "due_prefix_future_source_ready D c now entry f (K_G f)"
      by (rule StrongDuePrefixLoopHeadRel_zero_future_ready[OF head_future])
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
    have result: "r = Result ()"
      using post by simp
    have weak_public:
      "due_prefix_generated_zero_public_post D now entry future c t"
      using post by simp
    have state: "t = c"
      using weak_public
      by (auto simp: due_prefix_generated_zero_public_post_def
          due_prefix_generated_zero_terminal_post_def)
    have strong_at_t:
      "StrongDuePrefixLoopHeadRel D t entry managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry [] [] (map Generic future)
        (due_prefix_exit_phase_of [] (map Generic future))
        (due_prefix_next_node_of [] (map Generic future)) pxTCB"
      using head state by simp
    have strong_post:
      "due_prefix_managed_generated_zero_strong_post D now entry future c
        managed termination external K_G K_E t"
      unfolding due_prefix_managed_generated_zero_strong_post_def
      apply (intro conjI)
      subgoal by (rule state)
      subgoal by (rule weak_public)
      apply (rule exI[where x=pxTCB])
      apply (rule exI[where x=S])
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=event_raw])
      by (rule strong_at_t)
    show
      "r = Result () \<and>
       due_prefix_managed_generated_zero_strong_post D now entry future c
         managed termination external K_G K_E t"
      by (rule conjI[OF result strong_post])
  qed
    done
qed

end

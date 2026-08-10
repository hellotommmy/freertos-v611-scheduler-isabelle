theory Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts.Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts"
begin

lemma cursor_general_due_prefix_managed_generated_terminal_post_publicD:
  assumes nonempty: "due_tasks \<noteq> []"
    and ledger: "all_due = map Generic due_tasks"
    and terminal:
      "cursor_general_due_prefix_managed_generated_terminal_post D now entry
         all_due future managed termination external K_G K_E r t"
  shows
    "cursor_general_due_prefix_managed_generated_complete_public_post D now
       entry due_tasks future before managed termination external K_G K_E t"
proof -
  have weak_terminal:
    "due_prefix_generated_terminal_post D now entry
       (map Generic due_tasks) future r t"
    using
      cursor_general_due_prefix_managed_generated_terminal_post_weakD[
        OF terminal] ledger
    by simp
  have weak_complete:
    "due_prefix_generated_complete_public_post D now entry due_tasks future
       before t"
  proof -
    obtain task due_tail where tasks: "due_tasks = task # due_tail"
      using nonempty by (cases due_tasks) auto
    show ?thesis
      unfolding due_prefix_generated_complete_public_post_def
      apply (rule exI[where x=r])
      using weak_terminal tasks
      by (simp add: due_prefix_generated_complete_terminal_post_def)
  qed
  have head:
    "cursor_general_due_prefix_managed_generated_terminal_head_post D now
       entry (map Generic due_tasks) future managed termination external
       K_G K_E t"
    using
      cursor_general_due_prefix_managed_generated_terminal_post_headD[
        OF terminal] ledger
    by simp
  show ?thesis
    using weak_complete head
    by (simp add:
        cursor_general_due_prefix_managed_generated_complete_public_post_def)
qed

end

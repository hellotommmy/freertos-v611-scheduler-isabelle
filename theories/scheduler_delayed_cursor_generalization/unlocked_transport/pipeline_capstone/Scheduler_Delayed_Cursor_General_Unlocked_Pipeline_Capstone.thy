theory Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone.Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Complete.Scheduler_Delayed_Cursor_General_Managed_While_Complete"
begin

definition CursorGeneralStrongUnlockedTickManagedFinallyPost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralStrongUnlockedTickManagedFinallyPost D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S t \<longleftrightarrow>
     (\<exists>entry_c entry now due_tasks future pxTCB.
       CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
         generated_scheduler_roots before a entry_c entry now due_tasks future
         pxTCB managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S \<and>
       cursor_general_due_prefix_managed_generated_complete_public_post D now
         entry due_tasks future entry_c managed termination external
         K_G K_E t)"

text \<open>
  End-to-end generated unlocked prefix followed by the arbitrary finite
  managed while/finally.  The due/future decomposition and returned pointer
  are existential products of source reads and the real snapshot; no desired
  endpoint appears in a premise.
\<close>

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongUnlockedTickManagedFinallyPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S t\<rbrace>"
proof -
  obtain due_tasks future where readable:
      "generated_current_delayed_readable
         (scheduler_tick_role_entry_state c)"
    and assembler:
      "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
         generated_scheduler_roots c a (scheduler_tick_role_entry_state c)
         (tick_role_entry_abs a) (sa_tick (tick_role_entry_abs a))
         due_tasks future
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c))
         managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S"
    by (rule
      CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_managed_entry[
        OF before unlocked arithmetic_defined])
  have managed_entry:
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D
       generated_scheduler_roots (scheduler_tick_role_entry_state c)
       (sa_tick (tick_role_entry_abs a)) (tick_role_entry_abs a)
       due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))
       managed termination external K_G K_E"
    by (rule
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_entryI[
        OF assembler])
  note source = generated_unlocked_tick_prefix_source_defined_exact[
    OF arithmetic_defined readable]
  note loop =
    CursorGeneralManagedDuePrefixGeneratedEntryRel_finally_complete_exact[
      OF managed_entry refl]
  show ?thesis
    unfolding one_due_tick_unlocked_source_factor
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF source])
     apply clarsimp
    apply (rule runs_to_weaken[OF loop])
    apply clarsimp
    unfolding CursorGeneralStrongUnlockedTickManagedFinallyPost_def
    apply (rule exI[where x="scheduler_tick_role_entry_state c"])
    apply (rule exI[where x="tick_role_entry_abs a"])
    apply (rule exI[where x="sa_tick (tick_role_entry_abs a)"])
    apply (rule exI[where x=due_tasks])
    apply (rule exI[where x=future])
    apply (rule exI[where x=
      "generated_current_delayed_result (scheduler_tick_role_entry_state c)"])
    using assembler
    by simp
qed

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix_all_arithmetic_inputs:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
  shows
    "if generated_unlocked_tick_arithmetic_defined c
     then generated_unlocked_tick_prefix_source \<bullet> c
       \<lbrace>CursorGeneralStrongUnlockedTickGeneratedPrefixPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S\<rbrace>
     else \<not> succeeds generated_unlocked_tick_prefix_source c"
proof (cases "generated_unlocked_tick_arithmetic_defined c")
  case True
  then show ?thesis
    using
      CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix[
        OF before unlocked True]
    by simp
next
  case False
  then show ?thesis
    using generated_unlocked_tick_prefix_source_undefined_has_no_run[OF False]
    by simp
qed

end

theory Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler.Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Exact.Scheduler_Unlocked_Tick_Prefix_Source_Exact"
begin

definition CursorGeneralStrongUnlockedTickGeneratedPrefixPost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) exception_or_result
     \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralStrongUnlockedTickGeneratedPrefixPost D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S r entry_c \<longleftrightarrow>
     (\<exists>entry now due_tasks future pxTCB.
       r = Result pxTCB \<and>
       CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
         generated_scheduler_roots before a entry_c entry now due_tasks future
         pxTCB managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S)"

lemma CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_managed_entry:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  obtains due_tasks future where
    "generated_current_delayed_readable
       (scheduler_tick_role_entry_state c)"
    and
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
       generated_scheduler_roots c a (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs a) (sa_tick (tick_role_entry_abs a))
       due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))
       managed termination external generic_raw generic_abs event_raw
       event_abs K_G K_E S"
proof -
  obtain due_tasks future where
      due: "tick_due_sequence_abs a = map Generic due_tasks"
    and future:
      "due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) = map Generic future"
    and snapshot:
      "case due_tasks of
         [] \<Rightarrow>
           CursorGeneralStrongSchedulerSnapshotRel D
             (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
             managed termination external generic_raw generic_abs event_raw
             event_abs K_G K_E S
       | task # due_tail \<Rightarrow>
           CursorGeneralDueLoopSchedulerSnapshotRel D
             (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
             managed termination external generic_raw generic_abs event_raw
             event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
             (map Generic (task # due_tail)) (map Generic future)"
    using
      CursorGeneralStrongVTaskIncrementTickEntryRel_canonical_task_snapshot_transport[
        OF before unlocked arithmetic_defined]
    by blast
  have stable:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using before
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have core: "cursor_general_core_wf a"
    using stable
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have loop0:
    "due_prefix_loop_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
    by (rule cursor_general_core_wf_tick_role_entry_loop_initial[OF core])
  have loop:
    "due_prefix_loop_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (map Generic due_tasks)
       (map Generic future) (tick_role_entry_abs a)"
    using loop0 due future by simp
  have exit:
    "due_prefix_exit_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (map Generic due_tasks)
       (map Generic future) (tick_role_entry_abs a)
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
    using loop by (simp add: due_prefix_exit_inv_def)
  have split:
    "ring (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic due_tasks @ map Generic future"
    by (rule due_prefix_loop_inv_ringD[OF loop])
  have physical:
    "generated_current_delayed_readable
       (scheduler_tick_role_entry_state c) \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))"
    by (rule cursor_general_unlocked_tick_entry_snapshot_pointer_bridge[
          OF snapshot split])
  have assembler:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
       generated_scheduler_roots c a (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs a) (sa_tick (tick_role_entry_abs a))
       due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))
       managed termination external generic_raw generic_abs event_raw
       event_abs K_G K_E S"
    unfolding CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def
    using before unlocked exit physical snapshot by simp
  show thesis
    by (rule that[OF conjunct1[OF physical] assembler])
qed

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix:
  assumes before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "generated_unlocked_tick_prefix_source \<bullet> c
     \<lbrace>CursorGeneralStrongUnlockedTickGeneratedPrefixPost D c a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S\<rbrace>"
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
  note source = generated_unlocked_tick_prefix_source_defined_exact[
    OF arithmetic_defined readable]
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr)
         exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume exact:
      "r = Result
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c)) \<and>
       t = scheduler_tick_role_entry_state c"
    show
      "CursorGeneralStrongUnlockedTickGeneratedPrefixPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S r t"
      unfolding CursorGeneralStrongUnlockedTickGeneratedPrefixPost_def
      apply (rule exI[where x="tick_role_entry_abs a"])
      apply (rule exI[where x="sa_tick (tick_role_entry_abs a)"])
      apply (rule exI[where x=due_tasks])
      apply (rule exI[where x=future])
      apply (rule exI[where x=
        "generated_current_delayed_result
          (scheduler_tick_role_entry_state c)"])
      using exact assembler by simp
  qed
qed

end

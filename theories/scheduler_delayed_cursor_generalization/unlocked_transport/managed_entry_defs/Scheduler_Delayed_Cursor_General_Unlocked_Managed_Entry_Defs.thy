theory Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw.Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Pointer_Bridge.Scheduler_Delayed_Cursor_General_Pointer_Bridge"
begin

text \<open>
  Exact prefix-to-loop package.  The same real raw and abstract families occur
  in the public entry relation and the branch snapshot.  The case split is a
  derived decomposition of the physical delayed ring; it is not a caller
  supplied desired post-state.
\<close>

definition CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   32 word \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     CursorGeneralStrongVTaskIncrementTickEntryRel D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S \<and>
     sa_suspend_depth a = 0 \<and>
     R = generated_scheduler_roots \<and>
     entry_c = scheduler_tick_role_entry_state before \<and>
     entry = tick_role_entry_abs a \<and>
     now = sa_tick entry \<and>
     due_prefix_exit_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future)) \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future pxTCB \<and>
     (case due_tasks of
        [] \<Rightarrow>
          CursorGeneralStrongSchedulerSnapshotRel D entry_c entry managed
            termination external generic_raw generic_abs event_raw event_abs
            K_G K_E S
      | task # due_tail \<Rightarrow>
          CursorGeneralDueLoopSchedulerSnapshotRel D entry_c entry managed
            termination external generic_raw generic_abs event_raw event_abs
            K_G K_E S now (map Generic (task # due_tail))
            (map Generic future))"

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_beforeD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongVTaskIncrementTickEntryRel D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S \<and>
     sa_suspend_depth a = 0"
  using rel
  by (simp add: CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def)

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "R = generated_scheduler_roots \<and>
     entry_c = scheduler_tick_role_entry_state before \<and>
     entry = tick_role_entry_abs a \<and>
     now = sa_tick entry"
  using rel
  by (simp add: CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def)

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exitD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "due_prefix_exit_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
  using rel
  unfolding CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def
  by (elim conjE) assumption

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_pointerD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "unlocked_tick_entry_pointer_rel D due_tasks future pxTCB"
  using rel
  by (simp add: CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def)

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_snapshotD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "case due_tasks of
       [] \<Rightarrow>
         CursorGeneralStrongSchedulerSnapshotRel D entry_c entry managed
           termination external generic_raw generic_abs event_raw event_abs
           K_G K_E S
     | task # due_tail \<Rightarrow>
         CursorGeneralDueLoopSchedulerSnapshotRel D entry_c entry managed
           termination external generic_raw generic_abs event_raw event_abs
           K_G K_E S now (map Generic (task # due_tail))
           (map Generic future)"
  using rel
  by (simp add: CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_def)

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "sa_suspend_depth entry = 0 \<and> ring (sa_pending entry) = []"
proof -
  have before:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_beforeD[
      OF rel] by blast+
  have pending_wf: "tick_entry_pending_wf a"
    using before
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have pending: "ring (sa_pending a) = []"
    by (rule tick_entry_pending_wfD[OF pending_wf unlocked])
  have entry_eq: "entry = tick_role_entry_abs a"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[
      OF rel] by simp
  show ?thesis
    using entry_eq unlocked pending
    by (simp add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)
qed

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_domainD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "CursorGeneralStrongManagedDomainRel entry termination managed"
  using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_snapshotD[
      OF rel]
  by (cases due_tasks)
     (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def
        CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_due_sequenceD:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "map Generic due_tasks = tick_due_sequence_abs a"
proof -
  note exit =
    CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel]
  have loop:
    "due_prefix_loop_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have due:
    "due_nodes now (current_delayed_ring entry) = map Generic due_tasks"
    using due_prefix_loop_inv_due_splitD[OF loop] by simp
  have exact: "entry = tick_role_entry_abs a \<and> now = sa_tick entry"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[
        OF rel]
    by simp
  show ?thesis
    using due exact
    by (simp add: tick_due_sequence_abs_def due_tick_sequence_abs_def Let_def)
qed

end

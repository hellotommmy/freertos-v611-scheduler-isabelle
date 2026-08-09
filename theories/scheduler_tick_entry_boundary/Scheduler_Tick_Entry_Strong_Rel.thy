theory Scheduler_Tick_Entry_Strong_Rel
  imports
    Scheduler_Tick_Entry_Pending_Boundary
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Core.Scheduler_Due_Prefix_Strong_Snapshot_Core"
begin

text \<open>
  The strong tick-entry relation is the existing complete scheduler snapshot
  plus the control-flow boundary fact proved independently above.  In
  particular, this definition does not weaken root coverage or manufacture a
  desired concrete post-state.
\<close>

definition StrongVTaskIncrementTickEntryRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     tick_entry_pending_wf a"

lemma StrongVTaskIncrementTickEntryRelI:
  assumes strong:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and entry: "tick_entry_pending_wf a"
  shows
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using strong entry
  by (simp add: StrongVTaskIncrementTickEntryRel_def)

lemma StrongVTaskIncrementTickEntryRel_snapshotD:
  assumes entry:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using entry
  by (simp add: StrongVTaskIncrementTickEntryRel_def)

lemma StrongVTaskIncrementTickEntryRel_pending_wfD:
  assumes entry:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "tick_entry_pending_wf a"
  using entry
  by (simp add: StrongVTaskIncrementTickEntryRel_def)

lemma StrongVTaskIncrementTickEntryRel_unlocked_pending_emptyD:
  assumes entry:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
  shows "ring (sa_pending a) = []"
  using StrongVTaskIncrementTickEntryRel_pending_wfD[OF entry] unlocked
  by (rule tick_entry_pending_wfD)

lemma StrongVTaskIncrementTickEntryRel_from_settled:
  assumes strong:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and settled: "settled_wf a"
  shows
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  by (rule StrongVTaskIncrementTickEntryRelI[OF strong
        settled_wf_establishes_tick_entry_pending_wf[OF settled]])

lemma StrongVTaskIncrementTickEntryRel_from_yield_pending:
  assumes strong:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "yield_pending_wf a"
  shows
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  by (rule StrongVTaskIncrementTickEntryRelI[OF strong
        yield_pending_wf_establishes_tick_entry_pending_wf[OF pending]])

lemma StrongVTaskIncrementTickEntryRel_from_suspended:
  assumes strong:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  by (rule StrongVTaskIncrementTickEntryRelI[OF strong
        suspended_establishes_tick_entry_pending_wf[OF suspended]])

end

theory Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs.Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero.Scheduler_Delayed_Cursor_General_Managed_While_Zero"
begin

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_nonempty_headI:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now (task # due_tail) future pxTCB managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralDueLoopStrongHeadRel D entry_c entry managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
proof -
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S now (map Generic (task # due_tail)) (map Generic future)"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_snapshotD[
      OF rel] by simp
  have exit:
    "due_prefix_exit_inv now entry [] (map Generic (task # due_tail))
       (map Generic future) entry DueGate (Some (Generic task))"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel]
    by simp
  have tick: "sa_tick entry = now"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[
        OF rel]
    by simp
  have quiet: "sa_suspend_depth entry = 0"
    and pending: "ring (sa_pending entry) = []"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[
        OF rel]
    by blast+
  have ptr:
    "strong_due_next_ptr_rel D (Some (Generic task)) pxTCB"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_pointerD[
      OF rel]
    by (simp add: unlocked_tick_entry_pointer_rel_def)
  show ?thesis
    using snapshot exit tick quiet pending ptr
    by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
qed

theorem CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_nonempty_entryI:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now (task # due_tail) future pxTCB managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R entry_c now entry
       (task # due_tail) future pxTCB managed termination external K_G K_E"
proof -
  have head:
    "CursorGeneralDueLoopStrongHeadRel D entry_c entry managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
    by (rule
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_nonempty_headI[
        OF rel])
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S now (map Generic (task # due_tail)) (map Generic future)"
    by (rule CursorGeneralDueLoopStrongHeadRel_snapshotD[OF head])
  have families:
    "generic_abs = ods_generic_family S \<and>
     event_abs = ods_event_family S"
    using snapshot
    by (simp add: CursorGeneralDueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have head_pinned:
    "CursorGeneralDueLoopStrongHeadRel D entry_c entry managed termination
       external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
    using head families by simp
  have roots: "R = generated_scheduler_roots"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[
        OF rel]
    by simp
  have head_cons:
    "CursorGeneralDueLoopStrongHeadRel D entry_c entry managed termination
       external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] (Generic task # map Generic due_tail)
       (map Generic future) DueGate (Some (Generic task)) pxTCB"
    using head_pinned by simp
  obtain C branch where selector: "odc_task C = task"
    and gate_cons:
      "due_prefix_managed_gate_inv D R entry_c now entry []
        (Generic task # map Generic due_tail) (map Generic future)
        entry managed C branch S generic_raw event_raw"
    using CursorGeneralDueLoopStrongHeadRel_managed_gate_witness[
      OF head_cons roots]
    by blast
  have gate:
    "due_prefix_managed_gate_inv D R entry_c now entry []
       (map Generic (task # due_tail)) (map Generic future)
       entry managed C branch S generic_raw event_raw"
    using gate_cons by simp
  show ?thesis
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_generated_entryI[
          OF head_pinned gate selector])
qed

lemma CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_zero_headI:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now [] future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongDuePrefixLoopHeadRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
proof -
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_snapshotD[
      OF rel] by simp
  have exit:
    "due_prefix_exit_inv now entry [] [] (map Generic future) entry
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future))"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel]
    by simp
  have tick: "sa_tick entry = now"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[
        OF rel]
    by simp
  have quiet: "sa_suspend_depth entry = 0"
    and pending: "ring (sa_pending entry) = []"
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[
        OF rel]
    by blast+
  have ptr:
    "strong_due_next_ptr_rel D
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_pointerD[
      OF rel]
    by (simp add: unlocked_tick_entry_pointer_rel_def)
  show ?thesis
    using snapshot exit tick quiet pending ptr
    by (simp add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
qed

theorem CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_zero_entryI:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now [] future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R entry_c now entry []
       future pxTCB managed termination external K_G K_E"
proof -
  have head:
    "CursorGeneralStrongDuePrefixLoopHeadRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    by (rule
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_zero_headI[
        OF rel])
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D entry_c entry managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_snapshotD[
      OF rel] by simp
  have families:
    "generic_abs = ods_generic_family S \<and>
     event_abs = ods_event_family S"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have head_pinned:
    "CursorGeneralStrongDuePrefixLoopHeadRel D entry_c entry managed
       termination external generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using head families by simp
  show ?thesis
    by (rule
      CursorGeneralStrongDuePrefixLoopHeadRel_managed_generated_zero_entryI[
        OF head_pinned])
qed

theorem CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_entryI:
  assumes rel:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now due_tasks future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralManagedDuePrefixGeneratedEntryRel D R entry_c now entry
       due_tasks future pxTCB managed termination external K_G K_E"
proof (cases due_tasks)
  case Nil
  have zero:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now [] future pxTCB managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using rel Nil by simp
  show ?thesis
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_zero_entryI[
        OF zero]
      Nil by simp
next
  case (Cons task due_tail)
  have nonempty:
    "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D R before a
       entry_c entry now (task # due_tail) future pxTCB managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using rel Cons by simp
  show ?thesis
    using
      CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_nonempty_entryI[
        OF nonempty]
      Cons by simp
qed

end

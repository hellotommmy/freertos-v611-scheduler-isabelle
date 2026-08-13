theory Scheduler_Delayed_Cursor_General_Outer_Tick_Connector
  imports "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone.Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone"
begin
section \<open>Cursor-general public endpoint\<close>
definition CursorGeneralStrongSchedulerEndpointRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongSchedulerEndpointRel D c a managed termination external \<longleftrightarrow>
     (\<exists>generic_raw generic_abs event_raw event_abs K_G K_E S.
       CursorGeneralStrongSchedulerSnapshotRel D c a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S)"
definition CursorGeneralStrongVTaskIncrementTickSourcePost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickSourcePost D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S r t
       \<longleftrightarrow>
     (if sa_suspend_depth a = 0
      then r = Result () \<and> CursorGeneralStrongUnlockedTickManagedFinallyPost D c a managed
          termination external generic_raw generic_abs event_raw event_abs
          K_G K_E S t
      else StrongSuspendedTickWordPost c r t)"
definition CursorGeneralStrongVTaskIncrementTickCompletePost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S r t
       \<longleftrightarrow>
     CursorGeneralStrongVTaskIncrementTickSourcePost D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S r t \<and>
     CursorGeneralStrongSchedulerEndpointRel D t
       (task_increment_tick_modular_abs a) managed termination external"
section \<open>Unlocked endpoint extraction\<close>
lemma CursorGeneralStrongUnlockedTickManagedFinallyPost_endpointD:
  assumes post: "CursorGeneralStrongUnlockedTickManagedFinallyPost D before a managed
    termination external generic_raw generic_abs event_raw event_abs K_G K_E S t"
  shows "CursorGeneralStrongSchedulerEndpointRel D t (tick_unlocked_abs a)
    managed termination external"
proof -
  obtain entry_c entry now due_tasks future pxTCB where
    assembler: "CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel D
      generated_scheduler_roots before a entry_c entry now due_tasks future pxTCB
      managed termination external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and complete: "cursor_general_due_prefix_managed_generated_complete_public_post D now
      entry due_tasks future entry_c managed termination external K_G K_E t"
    using post by (auto simp: CursorGeneralStrongUnlockedTickManagedFinallyPost_def)
  have terminal_head:
    "cursor_general_due_prefix_managed_generated_terminal_head_post D now
      entry (map Generic due_tasks) future managed termination external K_G K_E t"
    using complete by (simp add:
      cursor_general_due_prefix_managed_generated_complete_public_post_def)
  obtain terminal_pxTCB terminal_generic_raw terminal_event_raw terminal_S
    where head:
    "CursorGeneralStrongDuePrefixLoopHeadRel D t
      (due_prefix_fold_state entry (map Generic due_tasks)) managed termination external
      terminal_generic_raw (ods_generic_family terminal_S) terminal_event_raw
      (ods_event_family terminal_S) K_G K_E terminal_S now entry
      (map Generic due_tasks) [] (map Generic future)
      (due_prefix_exit_phase_of [] (map Generic future))
      (due_prefix_next_node_of [] (map Generic future)) terminal_pxTCB"
    using terminal_head by (auto simp:
      cursor_general_due_prefix_managed_generated_terminal_head_post_def)
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D t
      (due_prefix_fold_state entry (map Generic due_tasks)) managed termination external
      terminal_generic_raw (ods_generic_family terminal_S) terminal_event_raw
      (ods_event_family terminal_S) K_G K_E terminal_S"
    using head by (simp add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
  have due: "map Generic due_tasks = tick_due_sequence_abs a"
    by (rule CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_due_sequenceD[OF assembler])
  have entry_eq: "entry = due_tick_entry_abs a"
    using CursorGeneralStrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF assembler]
    by simp
  have current_eq:
    "due_prefix_fold_state entry (map Generic due_tasks) = tick_unlocked_abs a"
    using tick_unlocked_abs_is_due_prefix_fold[of a] entry_eq due by simp
  show ?thesis
    unfolding CursorGeneralStrongSchedulerEndpointRel_def
    apply (rule exI[where x=terminal_generic_raw])
    apply (rule exI[where x="ods_generic_family terminal_S"])
    apply (rule exI[where x=terminal_event_raw])
    apply (rule exI[where x="ods_event_family terminal_S"])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=terminal_S])
    using snapshot current_eq by simp
qed
section \<open>Suspended modular preservation\<close>
lemma canonicalize_scheduler_cursors_missed_tick_update [simp]:
  "canonicalize_scheduler_cursors (a\<lparr>sa_missed_ticks := n\<rparr>) =
     (canonicalize_scheduler_cursors a)\<lparr>sa_missed_ticks := n\<rparr>"
  by (cases a)
     (simp add: canonicalize_scheduler_cursors_def clear_delayed_cursors_def)
lemma cursor_general_core_wf_missed_tick_update [simp]:
  "cursor_general_core_wf (a\<lparr>sa_missed_ticks := n\<rparr>) =
     cursor_general_core_wf a"
  by (simp add: cursor_general_core_wf_def ring_shape_wf_def)
lemma CursorGeneralStrongSchedulerSnapshotRel_increment_missed_tick_modular:
  assumes rel: "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
    generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "CursorGeneralStrongSchedulerSnapshotRel D (scheduler_missed_tick_source_step c)
    (a\<lparr>sa_missed_ticks := missed_tick_mod_suc (sa_missed_ticks a)\<rparr>) managed
    termination external generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using rel by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have missed: "sa_missed_ticks a =
    unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c)"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
  have canonical: "Scheduler_V611_Parse.globals.uxMissedTicks_' c = of_nat (sa_missed_ticks a)"
    using missed by simp
  show ?thesis
    using rel canonical
    unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
    apply (simp only: scheduler_current_rel_missed_tick_update)
    by (simp add:
      scheduler_missed_tick_source_step_def CursorGeneralStrongManagedDomainRel_def
      strong_generic_role_projection_def strong_event_role_projection_def
      strong_wake_payload_projection_def strong_one_due_snapshot_projection_def scheduler_role_rel_def
      scheduler_managed_scalar_rel_def managed_scheduler_view_def
      scheduler_scalar_rel_def scheduler_boundary_rel_def
      TaskObservationRel_def scheduler_managed_task_observation_rel_def
      missed_tick_mod_suc_def)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_source_suspension_zeroD:
  assumes rel:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and quiet: "sa_suspend_depth a = 0"
  shows "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using rel
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have suspended_unat:
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
  show ?thesis
    using suspended_unat quiet by (simp add: unat_eq_0)
qed

section \<open>Sequential generated outer call\<close>
theorem CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete:
  assumes entry: "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
    external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked_defined: "sa_suspend_depth a = 0 \<Longrightarrow>
      generated_unlocked_tick_arithmetic_defined c"
  shows "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
    \<lbrace>CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed termination
      external generic_raw generic_abs event_raw event_abs K_G K_E S\<rbrace>"
proof (cases "sa_suspend_depth a = 0")
  case unlocked: True
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using entry by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have source_zero: "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_source_suspension_zeroD[
          OF snapshot unlocked])
  have arithmetic_defined: "generated_unlocked_tick_arithmetic_defined c"
    by (rule unlocked_defined[OF unlocked])
  have unlocked_source:
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongUnlockedTickManagedFinallyPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S t\<rbrace>"
    by (rule CursorGeneralStrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally[
      OF entry unlocked arithmetic_defined])
  have outer:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       CursorGeneralStrongUnlockedTickManagedFinallyPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S t\<rbrace>"
    unfolding one_due_vTaskIncrementTick_named_outer_source
    apply (simp only: runs_to_condition_iff)
    apply (simp add: source_zero)
    apply (rule runs_to_weaken[OF unlocked_source])
    by simp
  show ?thesis
  proof (rule runs_to_weaken[OF outer])
    fix r :: "(unit, unit) exception_or_result" and t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result () \<and>
       CursorGeneralStrongUnlockedTickManagedFinallyPost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S t"
    have endpoint:
      "CursorGeneralStrongSchedulerEndpointRel D t (tick_unlocked_abs a)
         managed termination external"
      by (rule CursorGeneralStrongUnlockedTickManagedFinallyPost_endpointD)
         (use post in simp)
    show "CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
        termination external generic_raw generic_abs event_raw event_abs
        K_G K_E S r t"
      using post endpoint unlocked
      by (simp add: CursorGeneralStrongVTaskIncrementTickCompletePost_def
          CursorGeneralStrongVTaskIncrementTickSourcePost_def
          task_increment_tick_modular_abs_def)
  qed
next
  case suspended: False
  have snapshot: "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
    generic_raw generic_abs event_raw event_abs K_G K_E S"
    using entry by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have managed_scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have source_suspended:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 0"
    using managed_scalar suspended
    by (auto simp: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
  have exact:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c
     \<rbrace>"
    unfolding one_due_vTaskIncrementTick_named_outer_source
      scheduler_missed_tick_source_step_def
    apply runs_to_vcg
    using source_suspended
    apply simp
    done
  show ?thesis
  proof (rule runs_to_weaken[OF exact])
    fix r :: "(unit, unit) exception_or_result" and t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result () \<and>
       t = scheduler_missed_tick_source_step c"
    have snapshot_step: "CursorGeneralStrongSchedulerSnapshotRel D
      (scheduler_missed_tick_source_step c)
      (a\<lparr>sa_missed_ticks := missed_tick_mod_suc (sa_missed_ticks a)\<rparr>) managed
      termination external generic_raw generic_abs event_raw event_abs K_G K_E S"
      by (rule CursorGeneralStrongSchedulerSnapshotRel_increment_missed_tick_modular[OF snapshot])
    have abstract: "task_increment_tick_modular_abs a =
      a\<lparr>sa_missed_ticks := missed_tick_mod_suc (sa_missed_ticks a)\<rparr>"
      by (rule task_increment_tick_modular_abs_suspended[OF suspended])
    have endpoint:
      "CursorGeneralStrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) managed termination external"
      unfolding CursorGeneralStrongSchedulerEndpointRel_def
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=generic_abs])
      apply (rule exI[where x=event_raw])
      apply (rule exI[where x=event_abs])
      apply (rule exI[where x=K_G])
      apply (rule exI[where x=K_E])
      apply (rule exI[where x=S])
      using snapshot_step abstract post by simp
    have word_post: "StrongSuspendedTickWordPost c r t"
      using post
      by (simp add: StrongSuspendedTickWordPost_def
          scheduler_missed_tick_source_step_def
          scheduler_increment_tick_suspended_frame_def)
    show "CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
        termination external generic_raw generic_abs event_raw event_abs
        K_G K_E S r t"
      using word_post endpoint suspended
      by (simp add: CursorGeneralStrongVTaskIncrementTickCompletePost_def
          CursorGeneralStrongVTaskIncrementTickSourcePost_def)
  qed
qed

lemma CursorGeneralStrongVTaskIncrementTickEntryRel_unlocked_arithmetic_undefined_no_run:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
  shows
    "\<not> succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c"
proof -
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using entry
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have source_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_source_suspension_zeroD[
          OF snapshot unlocked])
  have wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
    and overflow_undefined: "\<not> tick_overflow_increment_defined c"
    using undefined
    by (simp_all add: generated_unlocked_tick_arithmetic_undefined_iff)
  have no_unlocked: "\<not> succeeds one_due_tick_unlocked_source c"
    by (rule one_due_tick_unlocked_source_signed_overflow_has_no_run[
          OF wrap overflow_undefined])
  show ?thesis
    unfolding one_due_vTaskIncrementTick_named_outer_source
    using source_zero no_unlocked by simp
qed

theorem CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_all_arithmetic_inputs:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "if sa_suspend_depth a = 0 \<and>
          classify_generated_tick_arithmetic c = TickWrapSignedOverflow
     then \<not> succeeds
       Scheduler_V611_Delay_Translation.vTaskIncrementTick' c
     else Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
       \<lbrace>CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S\<rbrace>"
proof (cases "sa_suspend_depth a = 0")
  case unlocked: True
  show ?thesis
  proof (cases
      "classify_generated_tick_arithmetic c = TickWrapSignedOverflow")
    case True
    have undefined: "\<not> generated_unlocked_tick_arithmetic_defined c"
      using True generated_unlocked_tick_arithmetic_class_iff by blast
    have no_run:
      "\<not> succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c"
      by (rule
        CursorGeneralStrongVTaskIncrementTickEntryRel_unlocked_arithmetic_undefined_no_run[
          OF entry unlocked undefined])
    show ?thesis using unlocked True no_run by simp
  next
    case False
    have defined: "generated_unlocked_tick_arithmetic_defined c"
      using False generated_unlocked_tick_arithmetic_class_iff by blast
    have complete:
      "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
       \<lbrace>CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S\<rbrace>"
      by (rule
        CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete[
          OF entry]) (use defined in simp)
    show ?thesis using unlocked False complete by simp
  qed
next
  case suspended: False
  have complete:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S\<rbrace>"
    by (rule
      CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete[
        OF entry]) (use suspended in simp)
  show ?thesis using suspended complete by simp
qed

text \<open>
  This theorem is for bare sequential spec_monad semantics.  It neither inserts
  interrupt interference nor proves that every cursor-general relational state
  is boot-reachable.  The only non-success case classified here is the emitted
  signed-overflow guard on the unlocked tick-wrap branch; the suspended unsigned
  missed-tick update remains total, including MAX_WORD to zero.
\<close>

end

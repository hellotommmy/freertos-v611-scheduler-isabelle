theory Scheduler_Delayed_Cursor_General_Snapshots
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Invariants.Scheduler_Delayed_Cursor_General_Invariants"
    "EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary.Scheduler_Tick_Entry_Strong_Rel"
begin

text \<open>
  Cursor-general snapshot adapters.  Only the scheduler well-formedness
  conjunct is changed.  GenericRootFamilyCoverage and xlist_relabel still
  observe the real raw and abstract cursor exactly; in particular, these
  predicates do not clear, existentially hide, or otherwise normalise pxIndex.
\<close>

definition CursorGeneralStrongManagedDomainRel ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring \<Rightarrow>
   'tid set \<Rightarrow> bool"
where
  "CursorGeneralStrongManagedDomainRel a termination managed \<longleftrightarrow>
     finite managed \<and>
     sa_live a \<subseteq> managed \<and>
     xlist_wf termination \<and>
     generic_ring termination \<and>
     generic_task_set termination = managed - sa_live a"

lemma strong_managed_domain_rel_imp_cursor_general:
  assumes old: "strong_managed_domain_rel a termination managed"
  shows "CursorGeneralStrongManagedDomainRel a termination managed"
  using old
  by (simp add: strong_managed_domain_rel_def
      CursorGeneralStrongManagedDomainRel_def)

lemma CursorGeneralStrongManagedDomainRel_with_tail_imp_old:
  assumes general:
    "CursorGeneralStrongManagedDomainRel a termination managed"
    and tail: "tail_cursor_wf termination"
  shows "strong_managed_domain_rel a termination managed"
  using general tail
  by (simp add: strong_managed_domain_rel_def
      CursorGeneralStrongManagedDomainRel_def)

definition CursorGeneralStrongSchedulerSnapshotRel ::
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
  "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in cursor_general_core_wf a \<and>
         CursorGeneralStrongManagedDomainRel a termination managed \<and>
         GenericRootFamilyCoverage D h GenericRootUniverse
           generic_raw generic_abs managed K_G \<and>
         EventRootFamilyCoverage external D h event_raw event_abs
           managed K_E \<and>
         strong_generic_role_projection a termination generic_abs \<and>
         strong_event_role_projection a managed external event_abs \<and>
         strong_wake_payload_projection a K_G \<and>
         scheduler_managed_task_observation_rel D h a managed \<and>
         strong_one_due_snapshot_projection a generic_abs event_abs
           K_G K_E S \<and>
         scheduler_role_rel generated_scheduler_roots c a \<and>
         scheduler_managed_scalar_rel c a managed \<and>
         scheduler_current_rel D c a \<and>
         scheduler_boundary_rel c \<and>
         (\<forall>g\<in>GenericRootUniverse.
          \<forall>e\<in>EventRootUniverse external.
            raw_xlist_storage g (generic_raw g) \<inter>
              raw_xlist_storage e (event_raw e) = {}))"

definition CursorGeneralStrongVTaskIncrementTickEntryRel ::
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
  "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       \<longleftrightarrow>
     CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     tick_entry_pending_wf a"

definition CursorGeneralDueLoopSchedulerSnapshotRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> 32 word \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow> bool"
where
  "CursorGeneralDueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in cursor_general_due_loop_core_wf a \<and>
         due_loop_time_wf now remaining future a \<and>
         CursorGeneralStrongManagedDomainRel a termination managed \<and>
         GenericRootFamilyCoverage D h GenericRootUniverse
           generic_raw generic_abs managed K_G \<and>
         EventRootFamilyCoverage external D h event_raw event_abs
           managed K_E \<and>
         strong_generic_role_projection a termination generic_abs \<and>
         strong_event_role_projection a managed external event_abs \<and>
         strong_wake_payload_projection a K_G \<and>
         scheduler_managed_task_observation_rel D h a managed \<and>
         strong_one_due_snapshot_projection a generic_abs event_abs
           K_G K_E S \<and>
         scheduler_role_rel generated_scheduler_roots c a \<and>
         scheduler_managed_scalar_rel c a managed \<and>
         scheduler_current_rel D c a \<and>
         scheduler_boundary_rel c \<and>
         (\<forall>g\<in>GenericRootUniverse.
          \<forall>e\<in>EventRootUniverse external.
            raw_xlist_storage g (generic_raw g) \<inter>
              raw_xlist_storage e (event_raw e) = {}))"

definition CursorGeneralDueLoopStrongHeadRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> due_prefix_exit_phase \<Rightarrow>
   'tid node_kind option \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB \<longleftrightarrow>
     CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future \<and>
     due_prefix_exit_inv now entry processed remaining future current
       phase next \<and>
     sa_tick current = now \<and>
     sa_suspend_depth current = 0 \<and>
     ring (sa_pending current) = [] \<and>
     strong_due_next_ptr_rel D next pxTCB"

definition CursorGeneralStrongDuePrefixLoopHeadRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> due_prefix_exit_phase \<Rightarrow>
   'tid node_kind option \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "CursorGeneralStrongDuePrefixLoopHeadRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB \<longleftrightarrow>
     CursorGeneralStrongSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     due_prefix_exit_inv now entry processed remaining future current
       phase next \<and>
     sa_tick current = now \<and>
     sa_suspend_depth current = 0 \<and>
     ring (sa_pending current) = [] \<and>
     strong_due_next_ptr_rel D next pxTCB"

text \<open>Conservative adapters from every old, sentinel-cursor relation.\<close>

lemma StrongSchedulerSnapshotRel_imp_cursor_general:
  assumes old:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have core: "core_wf a"
    and domain: "strong_managed_domain_rel a termination managed"
    using old by (simp_all add: StrongSchedulerSnapshotRel_def Let_def)
  have general: "cursor_general_core_wf a"
    by (rule core_wf_imp_cursor_general_core_wf[OF core])
  have general_domain:
    "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule strong_managed_domain_rel_imp_cursor_general[OF domain])
  show ?thesis
    using old general general_domain
    unfolding StrongSchedulerSnapshotRel_def
      CursorGeneralStrongSchedulerSnapshotRel_def Let_def
    by blast
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_with_old_policy_imp_old:
  assumes general:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
    and termination_tail: "tail_cursor_wf termination"
  shows
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have core: "cursor_general_core_wf a"
    and domain:
      "CursorGeneralStrongManagedDomainRel a termination managed"
    using general
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have old_core: "core_wf a"
    by (rule cursor_general_core_wf_with_old_policy_imp_core_wf[
          OF core delayed_a delayed_b pending suspended])
  have old_domain: "strong_managed_domain_rel a termination managed"
    by (rule CursorGeneralStrongManagedDomainRel_with_tail_imp_old[
          OF domain termination_tail])
  show ?thesis
    using general old_core old_domain
    unfolding StrongSchedulerSnapshotRel_def
      CursorGeneralStrongSchedulerSnapshotRel_def Let_def
    by blast
qed

lemma StrongVTaskIncrementTickEntryRel_imp_cursor_general:
  assumes old:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have snapshot:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF old])
  have pending: "tick_entry_pending_wf a"
    by (rule StrongVTaskIncrementTickEntryRel_pending_wfD[OF old])
  show ?thesis
    using StrongSchedulerSnapshotRel_imp_cursor_general[OF snapshot] pending
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
qed

lemma CursorGeneralStrongVTaskIncrementTickEntryRel_with_old_policy_imp_old:
  assumes general:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending_tail: "tail_cursor_wf (sa_pending a)"
    and suspended_tail: "tail_cursor_wf (sa_suspended a)"
    and termination_tail: "tail_cursor_wf termination"
  shows
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "tick_entry_pending_wf a"
    using general
    by (simp_all add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have old_snapshot:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_with_old_policy_imp_old[
          OF snapshot delayed_a delayed_b pending_tail suspended_tail
            termination_tail])
  show ?thesis
    by (rule StrongVTaskIncrementTickEntryRelI[OF old_snapshot pending])
qed

lemma DueLoopSchedulerSnapshotRel_imp_cursor_general:
  assumes old:
    "DueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
  shows
    "CursorGeneralDueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
proof -
  have core: "due_loop_core_wf a"
    and domain: "strong_managed_domain_rel a termination managed"
    using old by (simp_all add: DueLoopSchedulerSnapshotRel_def Let_def)
  have general: "cursor_general_due_loop_core_wf a"
    by (rule due_loop_core_wf_imp_cursor_general[OF core])
  have general_domain:
    "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule strong_managed_domain_rel_imp_cursor_general[OF domain])
  show ?thesis
    using old general general_domain
    unfolding DueLoopSchedulerSnapshotRel_def
      CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def
    by blast
qed

lemma CursorGeneralDueLoopSchedulerSnapshotRel_with_old_policy_imp_old:
  assumes general:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
    and delayed_a: "cursor (sa_delayed_a a) = None"
    and delayed_b: "cursor (sa_delayed_b a) = None"
    and pending: "tail_cursor_wf (sa_pending a)"
    and suspended: "tail_cursor_wf (sa_suspended a)"
    and termination_tail: "tail_cursor_wf termination"
  shows
    "DueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
proof -
  have core: "cursor_general_due_loop_core_wf a"
    and domain:
      "CursorGeneralStrongManagedDomainRel a termination managed"
    using general
    by (simp_all add: CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def)
  have old_core: "due_loop_core_wf a"
    by (rule cursor_general_due_loop_core_wf_with_old_policy_imp_old[
          OF core delayed_a delayed_b pending suspended])
  have old_domain: "strong_managed_domain_rel a termination managed"
    by (rule CursorGeneralStrongManagedDomainRel_with_tail_imp_old[
          OF domain termination_tail])
  show ?thesis
    using general old_core old_domain
    unfolding DueLoopSchedulerSnapshotRel_def
      CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def
    by blast
qed

lemma DueLoopStrongHeadRel_imp_cursor_general:
  assumes old:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
proof -
  have snapshot:
    "DueLoopSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
    by (rule DueLoopStrongHeadRel_snapshotD[OF old])
  show ?thesis
    using old DueLoopSchedulerSnapshotRel_imp_cursor_general[OF snapshot]
    by (simp add: DueLoopStrongHeadRel_def
        CursorGeneralDueLoopStrongHeadRel_def)
qed

lemma CursorGeneralDueLoopStrongHeadRel_snapshotD:
  assumes rel:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
  using rel by (simp add: CursorGeneralDueLoopStrongHeadRel_def)

lemma CursorGeneralDueLoopSchedulerSnapshotRel_terminal_strong:
  assumes rel:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now [] future"
    and tick: "sa_tick a = now"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have loop_core: "cursor_general_due_loop_core_wf a"
    and loop_time: "due_loop_time_wf now [] future a"
    and rest:
      "CursorGeneralStrongManagedDomainRel a termination managed \<and>
       GenericRootFamilyCoverage D ?h GenericRootUniverse
         generic_raw generic_abs managed K_G \<and>
       EventRootFamilyCoverage external D ?h event_raw event_abs
         managed K_E \<and>
       strong_generic_role_projection a termination generic_abs \<and>
       strong_event_role_projection a managed external event_abs \<and>
       strong_wake_payload_projection a K_G \<and>
       scheduler_managed_task_observation_rel D ?h a managed \<and>
       strong_one_due_snapshot_projection a generic_abs event_abs
         K_G K_E S \<and>
       scheduler_role_rel generated_scheduler_roots c a \<and>
       scheduler_managed_scalar_rel c a managed \<and>
       scheduler_current_rel D c a \<and>
       scheduler_boundary_rel c \<and>
       (\<forall>g\<in>GenericRootUniverse.
        \<forall>e\<in>EventRootUniverse external.
          raw_xlist_storage g (generic_raw g) \<inter>
            raw_xlist_storage e (event_raw e) = {})"
    using rel
    unfolding CursorGeneralDueLoopSchedulerSnapshotRel_def Let_def
    by blast+
  have core: "cursor_general_core_wf a"
    by (rule cursor_general_due_loop_terminal_core_wf[
          OF loop_core loop_time tick])
  show ?thesis
    unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
    using core rest by blast
qed

theorem CursorGeneralDueLoopStrongHeadRel_terminal_strong:
  assumes rel:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] future phase next pxTCB"
  shows
    "CursorGeneralStrongDuePrefixLoopHeadRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] future phase next pxTCB"
proof -
  have snapshot:
    "CursorGeneralDueLoopSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S
       now [] future"
    and tick: "sa_tick current = now"
    using rel by (simp_all add: CursorGeneralDueLoopStrongHeadRel_def)
  have stable:
    "CursorGeneralStrongSchedulerSnapshotRel D c current managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralDueLoopSchedulerSnapshotRel_terminal_strong[
          OF snapshot tick])
  show ?thesis
    using rel stable
    by (simp add: CursorGeneralDueLoopStrongHeadRel_def
        CursorGeneralStrongDuePrefixLoopHeadRel_def)
qed

end

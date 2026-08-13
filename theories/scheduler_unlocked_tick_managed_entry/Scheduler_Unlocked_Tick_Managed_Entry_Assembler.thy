theory Scheduler_Unlocked_Tick_Managed_Entry_Assembler
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary.Scheduler_Tick_Entry_Strong_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold.Scheduler_Unlocked_Tick_Scaffold"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_ML_Public_Wrapper.Scheduler_Due_Prefix_ML_Public_Wrapper"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Index.Scheduler_Due_Prefix_Managed_Arbitrary_While_Index"
begin

section \<open>Canonical generated-loop pointer\<close>

text \<open>
  The generated prefix returns the first due task when the due prefix is
  nonempty.  If there is no due task, it returns the first future task, or
  NULL when the current delayed ring is empty.  This is a three-way symbolic
  classification over arbitrary finite task lists, not three fixed test
  executions.
\<close>

definition unlocked_tick_entry_pointer_rel ::
  "'tid scheduler_decode \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "unlocked_tick_entry_pointer_rel D due_tasks future pxTCB \<longleftrightarrow>
     strong_due_next_ptr_rel D
       (due_prefix_next_node_of (map Generic due_tasks)
          (map Generic future)) pxTCB"

lemma unlocked_tick_entry_pointer_dueD:
  assumes ptr:
    "unlocked_tick_entry_pointer_rel D (task # due_tail) future pxTCB"
  shows "pxTCB = sd_tcb_ptr D task"
  using ptr
  by (auto simp: unlocked_tick_entry_pointer_rel_def
      strong_due_next_ptr_rel_def)

lemma unlocked_tick_entry_pointer_futureD:
  assumes ptr:
    "unlocked_tick_entry_pointer_rel D [] (task # future_tail) pxTCB"
  shows "pxTCB = sd_tcb_ptr D task"
  using ptr
  by (auto simp: unlocked_tick_entry_pointer_rel_def
      strong_due_next_ptr_rel_def)

lemma unlocked_tick_entry_pointer_emptyD:
  assumes ptr: "unlocked_tick_entry_pointer_rel D [] [] pxTCB"
  shows "pxTCB = NULL"
  using ptr
  by (auto simp: unlocked_tick_entry_pointer_rel_def
      strong_due_next_ptr_rel_def)

theorem unlocked_tick_entry_pointer_trichotomy:
  assumes ptr:
    "unlocked_tick_entry_pointer_rel D due_tasks future pxTCB"
  shows
    "(\<exists>task due_tail.
        due_tasks = task # due_tail \<and>
        pxTCB = sd_tcb_ptr D task) \<or>
     (due_tasks = [] \<and>
       (\<exists>task future_tail.
          future = task # future_tail \<and>
          pxTCB = sd_tcb_ptr D task)) \<or>
     (due_tasks = [] \<and> future = [] \<and> pxTCB = NULL)"
  using ptr
  by (cases due_tasks; cases future)
     (auto simp: unlocked_tick_entry_pointer_rel_def
        strong_due_next_ptr_rel_def)

section \<open>Prefix-to-managed-entry assembly package\<close>

text \<open>
  The pre-state is the strong public tick-entry relation.  For the unlocked
  branch, the generated prefix reaches exactly scheduler_tick_role_entry_state
  and tick_role_entry_abs.  The canonical exit invariant fixes due_tasks and
  future to the complete due/future split of the current delayed ring.

  A nonempty due prefix is deliberately represented by
  DueLoopSchedulerSnapshotRel: stable time_wf is false while a due head
  remains.  With no due task, the state is already terminal and the ordinary
  stable StrongSchedulerSnapshotRel is required.  In both branches managed is
  the decoder/geometry carrier M; it is never replaced by sa_live entry.
\<close>

definition StrongUnlockedTickManagedEntryAssemblerRel ::
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
  "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     StrongVTaskIncrementTickEntryRel D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
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
          StrongSchedulerSnapshotRel D entry_c entry M termination external
            generic_raw generic_abs event_raw event_abs K_G K_E S
      | task # due_tail \<Rightarrow>
          DueLoopSchedulerSnapshotRel D entry_c entry M termination external
            generic_raw generic_abs event_raw event_abs K_G K_E S
            now (map Generic (task # due_tail)) (map Generic future))"

lemma StrongUnlockedTickManagedEntryAssemblerRel_beforeD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "StrongVTaskIncrementTickEntryRel D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     sa_suspend_depth a = 0"
  using rel
  unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
  by blast

lemma StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "R = generated_scheduler_roots \<and>
     entry_c = scheduler_tick_role_entry_state before \<and>
     entry = tick_role_entry_abs a \<and>
     now = sa_tick entry"
  using rel
  unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
  by blast

lemma StrongUnlockedTickManagedEntryAssemblerRel_exitD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "due_prefix_exit_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
  using rel
  unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
  by blast

lemma StrongUnlockedTickManagedEntryAssemblerRel_pointerD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows "unlocked_tick_entry_pointer_rel D due_tasks future pxTCB"
  using rel
  unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
  by blast

lemma StrongUnlockedTickManagedEntryAssemblerRel_snapshotD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "case due_tasks of
       [] \<Rightarrow>
         StrongSchedulerSnapshotRel D entry_c entry M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         DueLoopSchedulerSnapshotRel D entry_c entry M termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S
           now (map Generic (task # due_tail)) (map Generic future)"
  using rel
  unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
  by blast

corollary StrongUnlockedTickManagedEntryAssemblerRel_pointer_trichotomyD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "(\<exists>task due_tail.
        due_tasks = task # due_tail \<and>
        pxTCB = sd_tcb_ptr D task) \<or>
     (due_tasks = [] \<and>
       (\<exists>task future_tail.
          future = task # future_tail \<and>
          pxTCB = sd_tcb_ptr D task)) \<or>
     (due_tasks = [] \<and> future = [] \<and> pxTCB = NULL)"
  by (rule unlocked_tick_entry_pointer_trichotomy[
        OF StrongUnlockedTickManagedEntryAssemblerRel_pointerD[OF rel]])

lemma StrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "sa_suspend_depth entry = 0 \<and>
     ring (sa_pending entry) = []"
proof -
  note before_facts =
    StrongUnlockedTickManagedEntryAssemblerRel_beforeD[OF rel]
  have before:
    "StrongVTaskIncrementTickEntryRel D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using before_facts by simp
  have unlocked: "sa_suspend_depth a = 0"
    using before_facts by simp
  have pending: "ring (sa_pending a) = []"
    by (rule StrongVTaskIncrementTickEntryRel_unlocked_pending_emptyD[
          OF before unlocked])
  have entry_eq: "entry = tick_role_entry_abs a"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  show ?thesis
    using entry_eq unlocked pending
    by (simp add: tick_role_entry_abs_def swap_delayed_roles_def Let_def)
qed

lemma StrongUnlockedTickManagedEntryAssemblerRel_domainD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "strong_managed_domain_rel entry termination M"
proof (cases due_tasks)
  case Nil
  have strong:
    "StrongSchedulerSnapshotRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel] Nil
    by simp
  show ?thesis
    by (rule StrongSchedulerSnapshotRel_domainD[OF strong])
next
  case (Cons task due_tail)
  have snapshot:
    "DueLoopSchedulerSnapshotRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now (map Generic (task # due_tail)) (map Generic future)"
    using StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel] Cons
    by simp
  show ?thesis
    by (rule DueLoopSchedulerSnapshotRel_domainD[OF snapshot])
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_ML_domainD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "finite M \<and>
     sa_live entry \<subseteq> M \<and>
     generic_task_set termination = M - sa_live entry"
  using StrongUnlockedTickManagedEntryAssemblerRel_domainD[OF rel]
  by (simp add: strong_managed_domain_rel_def)

section \<open>Managed entry constructors\<close>

lemma StrongUnlockedTickManagedEntryAssemblerRel_nonempty_headI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now (task # due_tail) future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "DueLoopStrongHeadRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
proof -
  have snapshot:
    "DueLoopSchedulerSnapshotRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now (map Generic (task # due_tail)) (map Generic future)"
    using StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel]
    by simp
  have exit:
    "due_prefix_exit_inv now entry [] (map Generic (task # due_tail))
       (map Generic future) entry DueGate (Some (Generic task))"
    using StrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel]
    by simp
  have tick: "sa_tick entry = now"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  have quiet: "sa_suspend_depth entry = 0"
    using StrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[OF rel]
    by simp
  have pending: "ring (sa_pending entry) = []"
    using StrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[OF rel]
    by simp
  have ptr:
    "strong_due_next_ptr_rel D (Some (Generic task)) pxTCB"
    using StrongUnlockedTickManagedEntryAssemblerRel_pointerD[OF rel]
    by (simp add: unlocked_tick_entry_pointer_rel_def)
  show ?thesis
    using snapshot exit tick quiet pending ptr
    by (simp add: DueLoopStrongHeadRel_def)
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_nonempty_ML_gateD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now (task # due_tail) future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "\<exists>C branch.
       odc_task C = task \<and>
       due_prefix_ML_gate_inv D R entry_c now entry []
         (map Generic (task # due_tail)) (map Generic future)
         entry M (sa_live entry) C branch S generic_raw event_raw"
proof -
  have head:
    "DueLoopStrongHeadRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] (Generic task # map Generic due_tail)
       (map Generic future) DueGate (Some (Generic task)) pxTCB"
    using StrongUnlockedTickManagedEntryAssemblerRel_nonempty_headI[OF rel]
    by simp
  have roots: "R = generated_scheduler_roots"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  show ?thesis
    using DueLoopStrongHeadRel_ML_gate_witness[OF head roots]
    by simp
qed

corollary StrongUnlockedTickManagedEntryAssemblerRel_nonempty_ML_pinsD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now (task # due_tail) future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "\<exists>C branch.
       due_prefix_ML_gate_inv D R entry_c now entry []
         (map Generic (task # due_tail)) (map Generic future)
         entry M (sa_live entry) C branch S generic_raw event_raw \<and>
       odc_live C = M \<and>
       odc_task C = task \<and>
       task \<in> sa_live entry \<and>
       sa_live entry \<subseteq> M"
proof -
  obtain C branch where
      selector: "odc_task C = task"
    and gate:
      "due_prefix_ML_gate_inv D R entry_c now entry []
        (map Generic (task # due_tail)) (map Generic future)
        entry M (sa_live entry) C branch S generic_raw event_raw"
    using StrongUnlockedTickManagedEntryAssemblerRel_nonempty_ML_gateD[
        OF rel]
    by blast
  have carrier: "odc_live C = M"
    by (rule due_prefix_ML_gate_decoder_carrierD[OF gate])
  have selected_live: "odc_task C \<in> sa_live entry"
    using due_prefix_ML_gate_selected_liveD[OF gate]
      due_prefix_ML_gate_live_eqD[OF gate]
    by simp
  have live_subset: "sa_live entry \<subseteq> M"
    using due_prefix_ML_gate_domainD[OF gate]
      due_prefix_ML_gate_live_eqD[OF gate]
    by simp
  show ?thesis
    apply (rule exI[where x=C])
    apply (rule exI[where x=branch])
    using gate carrier selector selected_live live_subset by simp
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_nonempty_entryI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now (task # due_tail) future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R entry_c now entry
       (task # due_tail) future pxTCB M termination external K_G K_E"
proof -
  have head:
    "DueLoopStrongHeadRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_nonempty_headI[
          OF rel])
  have before:
    "StrongVTaskIncrementTickEntryRel D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using StrongUnlockedTickManagedEntryAssemblerRel_beforeD[OF rel]
    by simp
  have stable_before:
    "StrongSchedulerSnapshotRel D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF before])
  have families:
    "generic_abs = ods_generic_family S \<and>
     event_abs = ods_event_family S"
    using StrongSchedulerSnapshotRel_snapshot_pinsD[OF stable_before]
    by simp
  have roots: "R = generated_scheduler_roots"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  have head_pinned:
    "DueLoopStrongHeadRel D entry_c entry M termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] (map Generic (task # due_tail)) (map Generic future)
       DueGate (Some (Generic task)) pxTCB"
    using head families by simp
  show ?thesis
    by (rule DueLoopStrongHeadRel_managed_generated_entryI[
          OF head_pinned roots])
qed

lemma StrongUnlockedTickManagedEntryAssemblerRel_zero_headI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now [] future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "StrongDuePrefixLoopHeadRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
proof -
  have snapshot:
    "StrongSchedulerSnapshotRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel]
    by simp
  have exit:
    "due_prefix_exit_inv now entry [] [] (map Generic future) entry
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future))"
    using StrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel]
    by simp
  have tick: "sa_tick entry = now"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  have quiet: "sa_suspend_depth entry = 0"
    using StrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[OF rel]
    by simp
  have pending: "ring (sa_pending entry) = []"
    using StrongUnlockedTickManagedEntryAssemblerRel_quiet_pendingD[OF rel]
    by simp
  have ptr:
    "strong_due_next_ptr_rel D
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using StrongUnlockedTickManagedEntryAssemblerRel_pointerD[OF rel]
    by (simp add: unlocked_tick_entry_pointer_rel_def)
  show ?thesis
    using snapshot exit tick quiet pending ptr
    by (simp add: StrongDuePrefixLoopHeadRel_def)
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_zero_entryI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now [] future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R entry_c now entry [] future
       pxTCB M termination external K_G K_E"
proof -
  have head:
    "StrongDuePrefixLoopHeadRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_zero_headI[OF rel])
  have snapshot:
    "StrongSchedulerSnapshotRel D entry_c entry M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using StrongUnlockedTickManagedEntryAssemblerRel_snapshotD[OF rel]
    by simp
  have families:
    "generic_abs = ods_generic_family S \<and>
     event_abs = ods_event_family S"
    using StrongSchedulerSnapshotRel_snapshot_pinsD[OF snapshot]
    by simp
  show ?thesis
    unfolding ManagedStrongDuePrefixGeneratedEntryRel_def
    apply (simp only: list.case)
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using head families by simp
qed

theorem StrongUnlockedTickManagedEntryAssemblerRel_entryI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R entry_c now entry due_tasks
       future pxTCB M termination external K_G K_E"
proof (cases due_tasks)
  case Nil
  have zero:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now [] future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
    using rel Nil by simp
  show ?thesis
    using StrongUnlockedTickManagedEntryAssemblerRel_zero_entryI[OF zero]
      Nil by simp
next
  case (Cons task due_tail)
  have nonempty:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now (task # due_tail) future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
    using rel Cons by simp
  show ?thesis
    using StrongUnlockedTickManagedEntryAssemblerRel_nonempty_entryI[
        OF nonempty]
      Cons by simp
qed

corollary StrongUnlockedTickManagedEntryAssemblerRel_full_entryI:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R entry_c now entry due_tasks
       future pxTCB M termination external K_G K_E \<and>
     finite M \<and>
     sa_live entry \<subseteq> M \<and>
     ((\<exists>task due_tail.
         due_tasks = task # due_tail \<and>
         pxTCB = sd_tcb_ptr D task) \<or>
      (due_tasks = [] \<and>
        (\<exists>task future_tail.
           future = task # future_tail \<and>
           pxTCB = sd_tcb_ptr D task)) \<or>
      (due_tasks = [] \<and> future = [] \<and> pxTCB = NULL))"
  using StrongUnlockedTickManagedEntryAssemblerRel_entryI[OF rel]
    StrongUnlockedTickManagedEntryAssemblerRel_ML_domainD[OF rel]
    StrongUnlockedTickManagedEntryAssemblerRel_pointer_trichotomyD[OF rel]
  by blast

end

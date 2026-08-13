theory Scheduler_Due_Prefix_Strong_While_Connector
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat.Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally.Scheduler_Due_Prefix_Generated_While_Finally"
begin

text \<open>
  Connector between the whole-scheduler strong snapshot and the already
  checked arbitrary-finite generated while theorem.  No field is added to
  one_due_context: the historical Gate-H relation remains the local runnable
  transformation, while the phase-accurate DueLoopStrongHeadRel below carries
  the independently framed managed/termination/external state during DueGate.

  The only extra witness needed at a nonempty initial due prefix is the local
  Gate-H package.  Making that package explicit is important: the present
  the strong family layer covers the managed domain, whereas Gate-H still
  uses odc_live both as its physical allocation domain and as sa_live.  The
  connector must not silently identify those domains when the termination
  root is nonempty.
\<close>

lemma scheduler_managed_task_observation_live_projection:
  assumes observation:
    "scheduler_managed_task_observation_rel D h a managed"
    and domain: "strong_managed_domain_rel a termination managed"
  shows "TaskObservationRel D h a"
proof -
  have managed_observation:
    "TaskObservationRel D h (managed_scheduler_view a managed)"
    using observation
    by (simp add: scheduler_managed_task_observation_rel_def)
  have finite_managed: "finite managed"
    and live_subset: "sa_live a \<subseteq> managed"
    using domain
    by (simp_all add: strong_managed_domain_rel_def)
  have finite_live: "finite (sa_live a)"
    by (rule finite_subset[OF live_subset finite_managed])
  show ?thesis
    unfolding TaskObservationRel_def
  proof (rule conjI)
    show "finite (sa_live a)" by (rule finite_live)
  next
    show "\<forall>t\<in>sa_live a.
      c_guard (sd_tcb_ptr D t) \<and>
      c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
      c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
      sa_priority a t < 4 \<and>
      unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
      Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
        (h_val h (sd_tcb_ptr D t)) < 4 \<and>
      Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
        (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
          PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
            (sd_tcb_ptr D t) \<and>
      Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
        (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
          PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
            (sd_tcb_ptr D t)"
    proof (intro ballI)
      fix t
      assume live: "t \<in> sa_live a"
    have managed: "t \<in> managed"
      by (rule subsetD[OF live_subset live])
    have managed_live:
      "t \<in> sa_live (managed_scheduler_view a managed)"
      using managed by (simp add: managed_scheduler_view_def)
    note observed = TaskObservationRel_liveD[
      OF managed_observation managed_live]
    have observed':
      "c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority a t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t)"
      using observed
      by (simp add: managed_scheduler_view_def)
    show
      "c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority a t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t))) = sa_priority a t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t)"
      by (rule observed')
    qed
  qed
qed

lemma core_wf_current_delayed_member_live:
  assumes core: "core_wf a"
    and member:
      "Generic t \<in> set (ring (current_delayed_ring a))"
  shows "t \<in> sa_live a"
proof -
  have membership: "membership_wf a"
    using core by (simp add: core_wf_def)
  have delayed_member:
    "t \<in> generic_task_set (sa_delayed_a a) \<union>
       generic_task_set (sa_delayed_b a)"
    using member
    by (cases "sa_current_role_a a")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  show ?thesis
    using membership delayed_member
    by (auto simp: membership_wf_def Let_def)
qed

lemma core_wf_current_delayed_key:
  assumes core: "core_wf a"
    and member:
      "Generic t \<in> set (ring (current_delayed_ring a))"
  shows
    "sa_wake a t =
       Some (item_key (current_delayed_ring a) (Generic t))"
proof -
  have time: "time_wf a"
    using core by (simp add: core_wf_def)
  show ?thesis
    using time member
    by (cases "sa_current_role_a a")
       (auto simp: time_wf_def delayed_key_agrees_def
          current_delayed_ring_def generic_task_set_def)
qed

lemma StrongDuePrefixLoopHeadRel_snapshotD:
  assumes rel:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "StrongSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using rel by (simp add: StrongDuePrefixLoopHeadRel_def)

lemma StrongDuePrefixLoopHeadRel_exitD:
  assumes rel:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  using rel by (simp add: StrongDuePrefixLoopHeadRel_def)

lemma StrongDuePrefixLoopHeadRel_ptrD:
  assumes rel:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows "strong_due_next_ptr_rel D next pxTCB"
  using rel by (simp add: StrongDuePrefixLoopHeadRel_def)

lemma StrongDuePrefixLoopHeadRel_tickD:
  assumes rel:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows "sa_tick current = now"
  using rel by (simp add: StrongDuePrefixLoopHeadRel_def)

text \<open>
  A zero-due future head is not an additional source assumption.  Its
  liveness, concrete key read and strict future comparison follow from the
  strong snapshot and the exit ledger.  The concrete task/key remain
  arbitrary.
\<close>

lemma StrongDuePrefixLoopHeadRel_zero_future_ready:
  assumes head:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (Generic f # map Generic fs)
       phase next pxTCB"
  shows "due_prefix_future_source_ready D c now entry f (K_G f)"
proof -
  note strong = StrongDuePrefixLoopHeadRel_snapshotD[OF head]
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF head]
  have base:
    "due_prefix_loop_inv now entry [] []
       (Generic f # map Generic fs) entry"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have ring:
    "ring (current_delayed_ring entry) =
       Generic f # map Generic fs"
    using due_prefix_loop_inv_ringD[OF base] by simp
  have member:
    "Generic f \<in> set (ring (current_delayed_ring entry))"
    using ring by simp
  have core: "core_wf entry"
    by (rule StrongSchedulerSnapshotRel_coreD[OF strong])
  have live: "f \<in> sa_live entry"
    by (rule core_wf_current_delayed_member_live[OF core member])
  have domain:
    "strong_managed_domain_rel entry termination managed"
    by (rule StrongSchedulerSnapshotRel_domainD[OF strong])
  have live_subset: "sa_live entry \<subseteq> managed"
    using domain by (simp add: strong_managed_domain_rel_def)
  have managed_task: "f \<in> managed"
    by (rule subsetD[OF live_subset live])
  have managed_observation:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       entry managed"
    by (rule StrongSchedulerSnapshotRel_managed_observationD[OF strong])
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) entry"
    by (rule scheduler_managed_task_observation_live_projection[
          OF managed_observation domain])
  have scalar_pins:
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick entry \<and>
     unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth entry \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks entry \<and>
     Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield entry then 1 else 0) \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready entry \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows entry) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card managed \<and>
     unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) =
       sa_yield_count entry"
    by (rule StrongSchedulerSnapshotRel_scalar_pinsD[OF strong])
  have abstract_tick: "sa_tick entry = now"
    by (rule StrongDuePrefixLoopHeadRel_tickD[OF head])
  have tick: "Scheduler_V611_Parse.globals.xTickCount_' c = now"
    using scalar_pins abstract_tick by simp
  have physical_key:
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = K_G f"
    using StrongSchedulerSnapshotRel_generic_payloadD[
      OF strong managed_task]
    by (simp add: one_due_generic_raw_ptr_def generic_item_raw_ptr_def)
  have wake_from_ring:
    "sa_wake entry f =
       Some (item_key (current_delayed_ring entry) (Generic f))"
    by (rule core_wf_current_delayed_key[OF core member])
  have delayed_member:
    "f \<in> generic_task_set (sa_delayed_a entry) \<union>
       generic_task_set (sa_delayed_b entry)"
    using member
    by (cases "sa_current_role_a entry")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have wake_from_payload: "sa_wake entry f = Some (K_G f)"
    using StrongSchedulerSnapshotRel_wakeD[OF strong live]
      delayed_member by simp
  have key_eq:
    "item_key (current_delayed_ring entry) (Generic f) = K_G f"
    using wake_from_ring wake_from_payload by simp
  have future_key:
    "now < item_key (current_delayed_ring entry) (Generic f)"
    using due_prefix_future_head_exception_exit[OF base] by simp
  have future: "now < K_G f"
    using future_key key_eq by simp
  show ?thesis
    using observation live tick physical_key future
    by (simp add: due_prefix_future_source_ready_def)
qed

text \<open>
  The stable strong snapshot cannot itself be the invariant at a nonempty due
  loop head.  core_wf/time_wf says every current-delayed task has a wake key
  strictly greater than the current tick, whereas a DueGate head has key at
  most that tick.  The following phase predicates replace only this transient
  time clause; every spatial family and concrete pin remains strong.
\<close>

lemma StrongDuePrefixLoopHeadRel_nonempty_remaining_false:
  assumes rel:
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (n # remaining) future phase next pxTCB"
  shows False
proof -
  note snapshot = StrongDuePrefixLoopHeadRel_snapshotD[OF rel]
  have core: "core_wf current"
    by (rule StrongSchedulerSnapshotRel_coreD[OF snapshot])
  have time: "time_wf current"
    using core by (simp add: core_wf_def)
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF rel]
  have loop:
    "due_prefix_loop_inv now entry processed (n # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have current_ring:
    "ring (current_delayed_ring current) = n # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have node_member:
    "n \<in> set (ring (current_delayed_ring current))"
    using current_ring by simp
  obtain task where node: "n = Generic task"
    using due_prefix_loop_inv_result_head[OF loop] by blast
  have task_member:
    "task \<in> generic_task_set (current_delayed_ring current)"
    using node_member node by (simp add: generic_task_set_def)
  have agree_a: "delayed_key_agrees current (sa_delayed_a current)"
    and agree_b: "delayed_key_agrees current (sa_delayed_b current)"
    and current_future:
      "\<forall>t\<in>generic_task_set (current_delayed_ring current).
        case sa_wake current t of
          None \<Rightarrow> False
        | Some k \<Rightarrow> sa_tick current < k"
    using time by (simp_all add: time_wf_def)
  have agree_current:
    "delayed_key_agrees current (current_delayed_ring current)"
    using agree_a agree_b
    by (cases "sa_current_role_a current")
       (simp_all add: current_delayed_ring_def)
  have wake:
    "sa_wake current task =
       Some (item_key (current_delayed_ring current) (Generic task))"
    using agree_current task_member
    by (simp add: delayed_key_agrees_def)
  have greater:
    "sa_tick current < item_key (current_delayed_ring current) n"
    using bspec[OF current_future task_member] wake node by simp
  have due:
    "item_key (current_delayed_ring entry) n \<le> now"
    using due_prefix_loop_inv_result_head[OF loop] by blast
  have current_eq:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have key_eq:
    "item_key (current_delayed_ring current) n =
       item_key (current_delayed_ring entry) n"
    using current_eq by simp
  have tick: "sa_tick current = now"
    by (rule StrongDuePrefixLoopHeadRel_tickD[OF rel])
  show False using greater due key_eq tick by simp
qed

definition due_loop_core_wf :: "'tid scheduler_abs \<Rightarrow> bool"
where
  "due_loop_core_wf a \<longleftrightarrow>
     finite (sa_live a) \<and>
     (\<forall>t\<in>sa_live a. sa_priority a t < 4) \<and>
     ring_shape_wf a \<and>
     role_wf a \<and>
     membership_wf a \<and>
     ready_cache_wf a \<and>
     current_wf a"

definition due_loop_time_wf ::
  "32 word \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "due_loop_time_wf now remaining future a \<longleftrightarrow>
     delayed_key_agrees a (sa_delayed_a a) \<and>
     delayed_key_agrees a (sa_delayed_b a) \<and>
     sorted (map (item_key (sa_delayed_a a)) (ring (sa_delayed_a a))) \<and>
     sorted (map (item_key (sa_delayed_b a)) (ring (sa_delayed_b a))) \<and>
     (\<forall>t\<in>ready_task_set a \<union>
                 generic_task_set (sa_suspended a).
        sa_wake a t = None) \<and>
     ring (current_delayed_ring a) = remaining @ future \<and>
     (\<forall>n\<in>set remaining.
        (\<exists>t. n = Generic t) \<and>
        item_key (current_delayed_ring a) n \<le> now) \<and>
     (\<forall>n\<in>set future.
        (\<exists>t. n = Generic t) \<and>
        now < item_key (current_delayed_ring a) n) \<and>
     (\<forall>t\<in>generic_task_set (overflow_delayed_ring a).
        case sa_wake a t of
          None \<Rightarrow> False
        | Some k \<Rightarrow> k < now)"

definition DueLoopSchedulerSnapshotRel ::
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
  "DueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in due_loop_core_wf a \<and>
         due_loop_time_wf now remaining future a \<and>
         strong_managed_domain_rel a termination managed \<and>
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

definition DueLoopStrongHeadRel ::
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
  "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB \<longleftrightarrow>
     DueLoopSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future \<and>
     due_prefix_exit_inv now entry processed remaining future current
       phase next \<and>
     sa_tick current = now \<and>
     sa_suspend_depth current = 0 \<and>
     ring (sa_pending current) = [] \<and>
     strong_due_next_ptr_rel D next pxTCB"

lemma DueLoopStrongHeadRel_snapshotD:
  assumes rel:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "DueLoopSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
  using rel by (simp add: DueLoopStrongHeadRel_def)

lemma DueLoopStrongHeadRel_exitD:
  assumes rel:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  using rel by (simp add: DueLoopStrongHeadRel_def)

lemma DueLoopStrongHeadRel_ptrD:
  assumes rel:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB"
  shows "strong_due_next_ptr_rel D next pxTCB"
  using rel by (simp add: DueLoopStrongHeadRel_def)

lemma DueLoopSchedulerSnapshotRel_domainD:
  assumes rel:
    "DueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now remaining future"
  shows "strong_managed_domain_rel a termination managed"
  using rel by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)

lemma due_loop_time_wf_terminal_time_wf:
  assumes phase: "due_loop_time_wf now [] future a"
    and tick: "sa_tick a = now"
  shows "time_wf a"
proof -
  have agree_a: "delayed_key_agrees a (sa_delayed_a a)"
    and agree_b: "delayed_key_agrees a (sa_delayed_b a)"
    and sorted_a:
      "sorted (map (item_key (sa_delayed_a a)) (ring (sa_delayed_a a)))"
    and sorted_b:
      "sorted (map (item_key (sa_delayed_b a)) (ring (sa_delayed_b a)))"
    and inactive:
      "\<forall>t\<in>ready_task_set a \<union>
          generic_task_set (sa_suspended a). sa_wake a t = None"
    and current_ring: "ring (current_delayed_ring a) = future"
    and future_keys:
      "\<forall>n\<in>set future.
        (\<exists>t. n = Generic t) \<and>
        now < item_key (current_delayed_ring a) n"
    and overflow:
      "\<forall>t\<in>generic_task_set (overflow_delayed_ring a).
        case sa_wake a t of None \<Rightarrow> False | Some k \<Rightarrow> k < now"
    using phase
    by (simp_all add: due_loop_time_wf_def)
  have agree_current:
    "delayed_key_agrees a (current_delayed_ring a)"
    using agree_a agree_b
    by (cases "sa_current_role_a a")
       (simp_all add: current_delayed_ring_def)
  have current_future:
    "\<forall>t\<in>generic_task_set (current_delayed_ring a).
       case sa_wake a t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> sa_tick a < k"
  proof (intro ballI)
    fix t
    assume member: "t \<in> generic_task_set (current_delayed_ring a)"
    have node:
      "Generic t \<in> set (ring (current_delayed_ring a))"
      using member by (simp add: generic_task_set_def)
    have in_future: "Generic t \<in> set future"
      using node current_ring by simp
    have greater:
      "now < item_key (current_delayed_ring a) (Generic t)"
      using future_keys in_future by blast
    have wake:
      "sa_wake a t =
       Some (item_key (current_delayed_ring a) (Generic t))"
      using agree_current member
      by (simp add: delayed_key_agrees_def)
    show
      "case sa_wake a t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> sa_tick a < k"
      using wake greater tick by simp
  qed
  have overflow':
    "\<forall>t\<in>generic_task_set (overflow_delayed_ring a).
       case sa_wake a t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < sa_tick a"
  proof (intro ballI)
    fix t
    assume member:
      "t \<in> generic_task_set (overflow_delayed_ring a)"
    have old:
      "case sa_wake a t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < now"
      by (rule bspec[OF overflow member])
    show
      "case sa_wake a t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < sa_tick a"
      using old tick by (cases "sa_wake a t") simp_all
  qed
  show ?thesis
    using agree_a agree_b sorted_a sorted_b inactive
      current_future overflow'
    by (simp add: time_wf_def)
qed

lemma due_loop_core_terminal_core_wf:
  assumes core: "due_loop_core_wf a"
    and time: "due_loop_time_wf now [] future a"
    and tick: "sa_tick a = now"
  shows "core_wf a"
  using core due_loop_time_wf_terminal_time_wf[OF time tick]
  by (simp add: due_loop_core_wf_def core_wf_def)

theorem DueLoopSchedulerSnapshotRel_terminal_strong:
  assumes rel:
    "DueLoopSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now [] future"
    and tick: "sa_tick a = now"
  shows
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have loop_core: "due_loop_core_wf a"
    and loop_time: "due_loop_time_wf now [] future a"
    and rest:
      "strong_managed_domain_rel a termination managed \<and>
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
    unfolding DueLoopSchedulerSnapshotRel_def Let_def
    by blast+
  have core: "core_wf a"
    by (rule due_loop_core_terminal_core_wf[
          OF loop_core loop_time tick])
  show ?thesis
    unfolding StrongSchedulerSnapshotRel_def Let_def
    using core rest by blast
qed

theorem DueLoopStrongHeadRel_terminal_strong:
  assumes rel:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] future phase next pxTCB"
  shows
    "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [] future phase next pxTCB"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF rel]
  have tick: "sa_tick current = now"
    and exit:
      "due_prefix_exit_inv now entry processed [] future current phase next"
    and quiet: "sa_suspend_depth current = 0"
    and pending: "ring (sa_pending current) = []"
    and ptr: "strong_due_next_ptr_rel D next pxTCB"
    using rel by (simp_all add: DueLoopStrongHeadRel_def)
  have stable:
    "StrongSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule DueLoopSchedulerSnapshotRel_terminal_strong[OF snapshot tick])
  show ?thesis
    unfolding StrongDuePrefixLoopHeadRel_def
    using stable exit tick quiet pending ptr by blast
qed

definition StrongDuePrefixGeneratedEntryRel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "StrongDuePrefixGeneratedEntryRel D R c now entry due_tasks future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S \<longleftrightarrow>
     (case due_tasks of
        [] \<Rightarrow>
          (\<exists>phase next.
            StrongDuePrefixLoopHeadRel D c entry managed termination external
              generic_raw generic_abs event_raw event_abs K_G K_E S
              now entry [] [] (map Generic future) phase next pxTCB)
      | task # due_tail \<Rightarrow>
          (\<exists>phase next C branch.
            DueLoopStrongHeadRel D c entry managed termination external
              generic_raw generic_abs event_raw event_abs K_G K_E S
              now entry [] (Generic task # map Generic due_tail)
              (map Generic future) phase next pxTCB \<and>
            odc_task C = task \<and>
            due_prefix_gate_inv D R c now entry []
              (Generic task # map Generic due_tail)
              (map Generic future) entry C branch S
              generic_raw event_raw))"

text \<open>
  This is the smallest entry bridge that does not refactor the old context.
  In the zero-due branch the local Gate-H witness disappears entirely.  In
  the nonempty branch it is exactly the old local runnable proof object; the
  phase-accurate relation beside it retains managed tasks and all protected
  roots without imposing stable time_wf on a due head.
\<close>

theorem StrongDuePrefixGeneratedEntryRel_startD:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry due_tasks future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
  shows
    "due_prefix_generated_start_inv D R now entry due_tasks future
       pxTCB c"
proof (cases due_tasks)
  case Nil
  note due_nil = Nil
  obtain phase next_node where head:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (map Generic future) phase next_node pxTCB"
    using rel Nil
    by (auto simp: StrongDuePrefixGeneratedEntryRel_def)
  note exit = StrongDuePrefixLoopHeadRel_exitD[OF head]
  note ptr = StrongDuePrefixLoopHeadRel_ptrD[OF head]
  show ?thesis
  proof (cases future)
    case Nil
    have exit_empty:
      "due_prefix_exit_inv now entry [] [] [] entry EmptyExit None"
      using exit Nil
      by (simp add: due_prefix_exit_inv_def)
    have ptr_null: "pxTCB = NULL"
      using ptr exit Nil
      by (auto simp: due_prefix_exit_inv_def strong_due_next_ptr_rel_def)
    show ?thesis
      using due_nil Nil exit_empty ptr_null
      by (simp add: due_prefix_generated_start_inv_def)
  next
    case (Cons f fs)
    have head_future:
      "StrongDuePrefixLoopHeadRel D c entry managed termination external
        generic_raw generic_abs event_raw event_abs K_G K_E S
        now entry [] [] (Generic f # map Generic fs)
        phase next_node pxTCB"
      using head Cons by simp
    have exit_future:
      "due_prefix_exit_inv now entry [] []
         (Generic f # map Generic fs) entry
         FutureExit (Some (Generic f))"
      using exit Cons
      by (simp add: due_prefix_exit_inv_def)
    have ptr_future: "pxTCB = sd_tcb_ptr D f"
      using ptr exit Cons
      by (auto simp: due_prefix_exit_inv_def strong_due_next_ptr_rel_def)
    have ready:
      "due_prefix_future_source_ready D c now entry f (K_G f)"
      by (rule StrongDuePrefixLoopHeadRel_zero_future_ready[OF head_future])
    have branch:
      "\<exists>k. pxTCB = sd_tcb_ptr D f \<and>
        due_prefix_exit_inv now entry [] []
          (Generic f # map Generic fs) entry
          FutureExit (Some (Generic f)) \<and>
        due_prefix_future_source_ready D c now entry f k"
      apply (rule exI[where x="K_G f"])
      using exit_future ptr_future ready by simp
    show ?thesis
      using branch
      by (simp add: due_prefix_generated_start_inv_def due_nil Cons)
  qed
next
  case (Cons task due_tail)
  obtain phase next_node C branch where
      head:
        "DueLoopStrongHeadRel D c entry managed termination external
          generic_raw generic_abs event_raw event_abs K_G K_E S
          now entry [] (Generic task # map Generic due_tail)
          (map Generic future)
          phase next_node pxTCB"
    and task: "odc_task C = task"
    and gate:
      "due_prefix_gate_inv D R c now entry []
          (Generic task # map Generic due_tail)
          (map Generic future) entry C branch S generic_raw event_raw"
    using rel Cons
    by (auto simp: StrongDuePrefixGeneratedEntryRel_def)
  note exit = DueLoopStrongHeadRel_exitD[OF head]
  note ptr = DueLoopStrongHeadRel_ptrD[OF head]
  have next_eq: "next_node = Some (Generic task)"
    using exit Cons by (simp add: due_prefix_exit_inv_def)
  have ptr_task: "pxTCB = sd_tcb_ptr D task"
    using ptr next_eq
    by (auto simp: strong_due_next_ptr_rel_def)
  have index:
    "due_prefix_generated_index_inv D R now entry
       (map Generic due_tasks) future due_tail pxTCB c"
    unfolding due_prefix_generated_index_inv_def
    apply (rule exI[where x="[]"])
    apply (rule exI[where x=entry])
    apply (rule exI[where x=C])
    apply (rule exI[where x=branch])
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using Cons task gate ptr_task
    by simp
  show ?thesis
    using Cons index
    by (simp add: due_prefix_generated_start_inv_def)
qed

theorem StrongDuePrefixGeneratedEntryRel_finally_complete:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry due_tasks future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_complete_public_post D now entry
         due_tasks future c t\<rbrace>"
  by (rule due_prefix_generated_finally_loop_complete[
        OF StrongDuePrefixGeneratedEntryRel_startD[OF rel] roots])

text \<open>
  Exact stable terminal-post target that remains to be established.  It is
  used below only with remaining = []; the checked contradiction lemma above
  forbids using it as a nonempty loop invariant.  It existentially quantifies
  only post-execution ghost families and the terminal pointer; managed,
  termination and external are the same arbitrary entry parameters.
\<close>

definition StrongDuePrefixGeneratedLoopHeadPost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "StrongDuePrefixGeneratedLoopHeadPost D c current managed termination
       external now entry processed remaining future pxTCB \<longleftrightarrow>
     (\<exists>phase next generic_raw generic_abs event_raw event_abs K_G K_E S.
       StrongDuePrefixLoopHeadRel D c current managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S
         now entry processed remaining future phase next pxTCB)"

definition strong_due_prefix_generated_complete_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "strong_due_prefix_generated_complete_public_post D now entry
       due_tasks future before managed termination external t \<longleftrightarrow>
     due_prefix_generated_complete_public_post D now entry
       due_tasks future before t \<and>
     (\<exists>endpoint pxTCB.
       StrongDuePrefixGeneratedLoopHeadPost D t endpoint managed termination
         external now entry (map Generic due_tasks) [] (map Generic future)
         pxTCB)"

text \<open>
  The zero-due strong closure is already derivable for every future suffix and
  every legal managed/termination/external population.  Both terminal controls
  are state preserving: NULL fails the while guard, while a future head throws
  before its first write.
\<close>

theorem StrongDuePrefixGeneratedEntryRel_zero_finally_strong:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry [] future
       pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       strong_due_prefix_generated_complete_public_post D now entry
         [] future c managed termination external t\<rbrace>"
proof -
  obtain phase next_node where head:
    "StrongDuePrefixLoopHeadRel D c entry managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry [] [] (map Generic future) phase next_node pxTCB"
    using rel
    by (auto simp: StrongDuePrefixGeneratedEntryRel_def)
  have weak:
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       due_prefix_generated_complete_public_post D now entry
         [] future c t\<rbrace>"
    by (rule StrongDuePrefixGeneratedEntryRel_finally_complete[OF rel roots])
  show ?thesis
  proof (rule runs_to_weaken[OF weak])
    fix r t
    assume post:
      "r = Result () \<and>
       due_prefix_generated_complete_public_post D now entry
         [] future c t"
    have result: "r = Result ()"
      using post by simp
    have public:
      "due_prefix_generated_complete_public_post D now entry
         [] future c t"
      using post by simp
    have state: "t = c"
      using public
      by (auto simp: due_prefix_generated_complete_public_post_def
          due_prefix_generated_complete_terminal_post_def
          due_prefix_generated_zero_public_post_def
          due_prefix_generated_zero_terminal_post_def)
    have loop_head:
      "StrongDuePrefixGeneratedLoopHeadPost D t entry managed termination
        external now entry [] [] (map Generic future) pxTCB"
      unfolding StrongDuePrefixGeneratedLoopHeadPost_def
      apply (rule exI[where x=phase])
      apply (rule exI[where x=next_node])
      apply (rule exI[where x=generic_raw])
      apply (rule exI[where x=generic_abs])
      apply (rule exI[where x=event_raw])
      apply (rule exI[where x=event_abs])
      apply (rule exI[where x=K_G])
      apply (rule exI[where x=K_E])
      apply (rule exI[where x=S])
      using head state by simp
    have strong_public:
      "strong_due_prefix_generated_complete_public_post D now entry
         [] future c managed termination external t"
      unfolding strong_due_prefix_generated_complete_public_post_def
      apply (rule conjI[OF public])
      apply (rule exI[where x=entry])
      apply (rule exI[where x=pxTCB])
      using loop_head by simp
    show
      "r = Result () \<and>
       strong_due_prefix_generated_complete_public_post D now entry
         [] future c managed termination external t"
      using result strong_public by simp
  qed
qed

text \<open>
  The next checker theorem must strengthen
  StrongDuePrefixGeneratedEntryRel_finally_complete by replacing its weak
  public post with strong_due_prefix_generated_complete_public_post.  The
  missing preservation facts are exactly:

    * every non-last Result body step reconstructs DueLoopStrongHeadRel at the
      successor DueGate head, with managed, termination and external unchanged;
    * the last-due Result/Exn split first closes the relaxed time partition and
      then reconstructs stable StrongDuePrefixLoopHeadRel at EmptyExit or
      FutureExit before finally normalises the control result;
    * xTasksWaitingTermination raw topology, count, cursor, container and
      payload are framed by the local Generic remove/ready insert footprint;
    * every external Event root other than the optional current task owner is
      framed, and the owner root is reconstructed after optional removal;
    * managed TaskObservation, current TCB pointer, delayed-role pair, task
      count, tick/suspend/missed/yield/top/overflow scalars, boundary globals
      and Generic/Event cross-storage separation are re-established;
    * strong_managed_domain_rel now carries tail_cursor_wf termination.
      The nonempty-step frame must preserve it explicitly: xlist_wf plus
      generic_ring alone would not imply the vListInsertEnd cursor policy
      required by ConcurrentTaskDomainWF.

  A suitable one-step theorem has the following schematic, fully universal
  shape (the primed families are existential outputs):

    DueLoopStrongHeadRel ... processed
      (Generic task # Generic u # remaining) future ...
    + local due_prefix_gate_inv for task
    + R = generated_scheduler_roots
    ---------------------------------------------------------------
    one_due_tick_loop_body_source (sd_tcb_ptr D task) produces
      Result (sd_tcb_ptr D u) and some primed families satisfying
      DueLoopStrongHeadRel ... (processed @ [Generic task])
        (Generic u # remaining) future ... .

  No post relation, branch, root, cursor, key or concrete state is allowed as
  a premise of that theorem.  The proof must obtain the primed families from
  the exact generated heap transformer and the primitive footprint frames.
\<close>

end

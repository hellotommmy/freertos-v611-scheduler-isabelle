theory Scheduler_Due_Prefix_Managed_Gate_Defs_Context
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Diagnostic.Scheduler_Due_Prefix_Managed_Gate_Diagnostic"
begin

text \<open>
  The repaired invariant supplies Gate-H with the managed scheduler view.  Its
  loop equation, time partition and public abstract state remain the real
  current scheduler state.  Thus no retired TCB is made runnable; it is merely
  retained in the allocation/decoder domain used by the local heap proof.
\<close>

definition due_prefix_managed_gate_inv ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "due_prefix_managed_gate_inv D R c now entry processed remaining future
       current managed C branch S generic_raw event_raw \<longleftrightarrow>
     one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed) C branch S
       generic_raw event_raw \<and>
     due_prefix_loop_inv now entry processed remaining future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"

definition due_prefix_canonical_managed_context ::
  "scheduler_roots \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid \<Rightarrow> ('tid, xLIST_C ptr) one_due_context"
where
  "due_prefix_canonical_managed_context R c current managed external K_E task =
     \<lparr>odc_live = managed,
      odc_task = task,
      odc_generic_roots = GenericRootUniverse,
      odc_event_roots = EventRootUniverse external,
      odc_delayed_root =
        abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c),
      odc_ready_root = (\<lambda>p. abi_list_ptr (sr_ready R p)),
      odc_pending_root = abi_list_ptr (sr_pending R),
      odc_priority = sa_priority current,
      odc_tick = sa_tick current,
      odc_entry_top = sa_top_ready current,
      odc_K_E = K_E\<rparr>"

lemma due_prefix_canonical_managed_context_components [simp]:
  "odc_live
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     managed"
  "odc_task
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     task"
  "odc_generic_roots
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     GenericRootUniverse"
  "odc_event_roots
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     EventRootUniverse external"
  "odc_delayed_root
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
  "odc_ready_root
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     (\<lambda>p. abi_list_ptr (sr_ready R p))"
  "odc_pending_root
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     abi_list_ptr (sr_pending R)"
  "odc_priority
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     sa_priority a"
  "odc_tick
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     sa_tick a"
  "odc_entry_top
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     sa_top_ready a"
  "odc_K_E
     (due_prefix_canonical_managed_context R c a managed external K_E task) =
     K_E"
  by (simp_all add: due_prefix_canonical_managed_context_def)

definition one_due_canonical_event_branch ::
  "('tid, 'root) one_due_context \<Rightarrow>
   ('tid, 'root) one_due_snapshot \<Rightarrow>
   'root one_due_event_branch"
where
  "one_due_canonical_event_branch C S =
     (if \<exists>owner\<in>one_due_external_roots C.
          Event (odc_task C) \<in>
            set (ring (ods_event_family S owner))
      then DueEventLinked
        (SOME owner. owner \<in> one_due_external_roots C \<and>
          Event (odc_task C) \<in>
            set (ring (ods_event_family S owner)))
      else DueEventNull)"

lemma one_due_canonical_event_branch_at:
  assumes pending_empty:
    "ring (ods_event_family S (odc_pending_root C)) = []"
  shows
    "one_due_event_branch_at C S
       (one_due_canonical_event_branch C S)"
proof (cases
    "\<exists>owner\<in>one_due_external_roots C.
       Event (odc_task C) \<in>
         set (ring (ods_event_family S owner))")
  case True
  let ?P = "\<lambda>owner. owner \<in> one_due_external_roots C \<and>
    Event (odc_task C) \<in> set (ring (ods_event_family S owner))"
  have witness: "?P (SOME owner. ?P owner)"
    by (rule someI_ex) (use True in blast)
  show ?thesis
    using True witness
    by (simp add: one_due_canonical_event_branch_def)
next
  case False
  note no_external = False
  have absent:
    "\<forall>r\<in>odc_event_roots C.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family S r))"
  proof (intro ballI)
    fix r
    assume root: "r \<in> odc_event_roots C"
    show
      "Event (odc_task C) \<notin>
         set (ring (ods_event_family S r))"
    proof (cases "r = odc_pending_root C")
      case True
      then show ?thesis using pending_empty by simp
    next
      case False
      have "r \<in> one_due_external_roots C"
        using root False
        by (simp add: one_due_external_roots_def)
      then show ?thesis using no_external by blast
    qed
  qed
  show ?thesis
    using False absent
    by (simp add: one_due_canonical_event_branch_def)
qed

lemma DueLoopStrongHeadRel_canonical_all_ready_destinations:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_all_ready_destinations
       (due_prefix_canonical_managed_context R c current managed
         external K_E task)"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have observation:
    "TaskObservationRel D ?h (managed_scheduler_view current managed)"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def Let_def)
  have role: "scheduler_role_rel generated_scheduler_roots c current"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  show ?thesis
    unfolding one_due_all_ready_destinations_def
  proof (intro ballI)
    fix t
    assume managed: "t \<in> odc_live ?C"
    have managed': "t \<in> managed"
      using managed by simp
    note observed = TaskObservationRel_liveD[OF observation]
    have priority_bound: "sa_priority current t < 4"
      using observed[of t] managed'
      by (simp add: managed_scheduler_view_def)
    have target:
      "abi_list_ptr (sr_ready R (sa_priority current t))
         \<in> GenericRootUniverse"
      using GenericRootUniverse_readyI[OF priority_bound] roots by simp
    have different:
      "abi_list_ptr
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c) \<noteq>
       abi_list_ptr (sr_ready R (sa_priority current t))"
      using role roots
        generated_ready_raw_root_neq_delayed_a[OF priority_bound]
        generated_ready_raw_root_neq_delayed_b[OF priority_bound]
      by (cases "sa_current_role_a current")
         (auto simp: scheduler_role_rel_def)
    show
      "odc_ready_root ?C (odc_priority ?C t)
          \<in> odc_generic_roots ?C \<and>
       odc_delayed_root ?C \<noteq>
          odc_ready_root ?C (odc_priority ?C t)"
      using target different by simp
  qed
qed

lemma DueLoopStrongHeadRel_canonical_context_wf:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_context_wf
       (due_prefix_canonical_managed_context R c current managed
         external K_E task)"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have domain:
    "strong_managed_domain_rel current termination managed"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have finite_managed: "finite managed"
    and live_subset: "sa_live current \<subseteq> managed"
    using domain by (simp_all add: strong_managed_domain_rel_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using current_ring
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have core: "due_loop_core_wf current"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have task_live: "task \<in> sa_live current"
    using core task_delayed
    by (auto simp: due_loop_core_wf_def membership_wf_def Let_def)
  have task_managed: "task \<in> managed"
    by (rule subsetD[OF live_subset task_live])
  have role: "scheduler_role_rel generated_scheduler_roots c current"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have delayed_root:
    "abi_list_ptr
       (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)
       \<in> GenericRootUniverse"
  proof (cases "sa_current_role_a current")
    case True
    have delayed_eq:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
         sr_delayed_a generated_scheduler_roots"
      using role True by (simp add: scheduler_role_rel_def)
    show ?thesis
      using GenericRootUniverse_delayed_aI
      by (simp only: delayed_eq)
  next
    case False
    have delayed_eq:
      "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
         sr_delayed_b generated_scheduler_roots"
      using role False by (simp add: scheduler_role_rel_def)
    show ?thesis
      using GenericRootUniverse_delayed_bI
      by (simp only: delayed_eq)
  qed
  have event_coverage:
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       event_raw event_abs managed K_E"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have external_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
  have finite_event: "finite (EventRootUniverse external)"
    by (rule EventRootUniverse_finite[OF external_wf])
  have destinations: "one_due_all_ready_destinations ?C"
    by (rule DueLoopStrongHeadRel_canonical_all_ready_destinations[
          OF strong roots])
  have task_destination:
    "odc_ready_root ?C (odc_priority ?C task)
        \<in> odc_generic_roots ?C \<and>
     odc_delayed_root ?C \<noteq>
        odc_ready_root ?C (odc_priority ?C task)"
    by (rule one_due_all_ready_destinationsD[OF destinations])
       (use task_managed in simp)
  have pending:
    "abi_list_ptr (sr_pending R) \<in> EventRootUniverse external"
  proof -
    have pending_eq:
      "abi_list_ptr (sr_pending R) = GeneratedPendingEventRoot"
      using roots by (simp add: GeneratedPendingEventRoot_def)
    show ?thesis
      using EventRootUniverse_pendingI pending_eq by simp
  qed
  show ?thesis
    unfolding one_due_context_wf_def
    using finite_managed task_managed delayed_root finite_event
      task_destination pending
    by (simp add: one_due_target_root_def)
qed

end

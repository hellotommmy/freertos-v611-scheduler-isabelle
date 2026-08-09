theory Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Projections.Scheduler_Due_Prefix_Strong_Snapshot_Projections"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exit_Aware_Invariant.Scheduler_Due_Prefix_Exit_Aware_Invariant"
begin

text \<open>
  Exit-aware loop-head packaging and compatibility with the historical
  eight-root scheduler relation.  The compatibility theorem is deliberately
  restricted to an empty termination root; the strong relation itself retains
  arbitrary legal managed/termination populations.
\<close>

definition StrongDuePrefixLoopHeadRel ::
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
  "StrongDuePrefixLoopHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase next pxTCB \<longleftrightarrow>
     StrongSchedulerSnapshotRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     due_prefix_exit_inv now entry processed remaining future current
       phase next \<and>
     sa_tick current = now \<and>
     sa_suspend_depth current = 0 \<and>
     ring (sa_pending current) = [] \<and>
     strong_due_next_ptr_rel D next pxTCB"

text \<open>
  The ordinary scheduler list relation can already be reconstructed from the
  strong families.  This does not collapse managed to runnable; the extra
  termination root simply remains outside scheduler_lists_rel's historical
  eight-root view.
\<close>

lemma GenericRootFamilyCoverage_sched_xlistD:
  assumes cov:
    "GenericRootFamilyCoverage D h roots raw_fam abs_fam managed K_G"
    and root: "lp \<in> roots"
  shows "sched_xlist_rel (sd_node_decode D) h lp (abs_fam lp)"
proof -
  have raw: "raw_xlist_rel h lp (raw_fam lp)"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF cov root])
  have relabel:
    "xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    by (rule GenericRootFamilyCoverage_relabelD[OF cov root])
  show ?thesis
    unfolding sched_xlist_rel_def
    by (rule exI[of _ "raw_fam lp"], rule conjI[OF raw relabel])
qed

theorem StrongSchedulerSnapshotRel_scheduler_listsD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "scheduler_lists_rel D generated_scheduler_roots c a"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  note gcov = StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
  note gproj = StrongSchedulerSnapshotRel_generic_projectionD[OF rel]
  note ecov = StrongSchedulerSnapshotRel_event_coverageD[OF rel]
  note eproj = StrongSchedulerSnapshotRel_event_projectionD[OF rel]
  have ready:
    "\<forall>p<4. sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_ready generated_scheduler_roots p))
       (sa_ready a p)"
  proof (intro allI impI)
    fix p :: nat
    assume priority: "p < 4"
    have root:
      "abi_list_ptr (sr_ready generated_scheduler_roots p)
         \<in> GenericRootUniverse"
      by (rule GenericRootUniverse_readyI[OF priority])
    have list:
      "sched_xlist_rel (sd_node_decode D) ?h
        (abi_list_ptr (sr_ready generated_scheduler_roots p))
        (generic_abs
          (abi_list_ptr (sr_ready generated_scheduler_roots p)))"
      by (rule GenericRootFamilyCoverage_sched_xlistD[OF gcov root])
    have projection:
      "generic_abs
         (abi_list_ptr (sr_ready generated_scheduler_roots p)) =
       sa_ready a p"
      by (rule strong_generic_role_readyD[OF gproj priority])
    show
      "sched_xlist_rel (sd_node_decode D) ?h
        (abi_list_ptr (sr_ready generated_scheduler_roots p))
        (sa_ready a p)"
      using list projection by simp
  qed
  have delayed_a:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_a generated_scheduler_roots))
       (sa_delayed_a a)"
  proof -
    have list:
      "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_a generated_scheduler_roots))
       (generic_abs
         (abi_list_ptr (sr_delayed_a generated_scheduler_roots)))"
      by (rule GenericRootFamilyCoverage_sched_xlistD[
            OF gcov GenericRootUniverse_delayed_aI])
    show ?thesis
      using list strong_generic_role_delayed_aD[OF gproj] by simp
  qed
  have delayed_b:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_b generated_scheduler_roots))
       (sa_delayed_b a)"
  proof -
    have list:
      "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_delayed_b generated_scheduler_roots))
       (generic_abs
         (abi_list_ptr (sr_delayed_b generated_scheduler_roots)))"
      by (rule GenericRootFamilyCoverage_sched_xlistD[
            OF gcov GenericRootUniverse_delayed_bI])
    show ?thesis
      using list strong_generic_role_delayed_bD[OF gproj] by simp
  qed
  have suspended:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_suspended generated_scheduler_roots))
       (sa_suspended a)"
  proof -
    have list:
      "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_suspended generated_scheduler_roots))
       (generic_abs
         (abi_list_ptr (sr_suspended generated_scheduler_roots)))"
      by (rule GenericRootFamilyCoverage_sched_xlistD[
            OF gcov GenericRootUniverse_suspendedI])
    show ?thesis
      using list strong_generic_role_suspendedD[OF gproj] by simp
  qed
  have event_family:
    "scheduler_event_root_family_rel D ?h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF ecov])
  have pending_raw:
    "sched_xlist_rel (sd_node_decode D) ?h GeneratedPendingEventRoot
       (event_abs GeneratedPendingEventRoot)"
    by (rule scheduler_event_root_family_sched_xlistD[
          OF event_family EventRootUniverse_pendingI])
  have pending_projection:
    "event_abs GeneratedPendingEventRoot = sa_pending a"
    by (rule strong_event_role_pendingD[OF eproj])
  have pending:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_pending generated_scheduler_roots))
       (sa_pending a)"
    using pending_raw pending_projection
    by (simp add: GeneratedPendingEventRoot_def)
  show ?thesis
    using ready delayed_a delayed_b suspended pending
    by (simp add: scheduler_lists_rel_def Let_def)
qed

text \<open>
  Compatibility with raw_scheduler_rel is intentionally conditional on an
  empty termination root.  This theorem is useful for regression, but it is
  not the final universal tick theorem: using it as the main route would
  discard legal states with tasks awaiting reclamation.
\<close>

theorem StrongSchedulerSnapshotRel_legacy_raw_scheduler_if_no_retired:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and no_retired: "ring termination = []"
  shows "raw_scheduler_rel D generated_scheduler_roots c a"
proof -
  have domain: "strong_managed_domain_rel a termination managed"
    by (rule StrongSchedulerSnapshotRel_domainD[OF rel])
  have managed_iff:
    "managed = sa_live a \<longleftrightarrow> ring termination = []"
    by (rule strong_managed_domain_no_retired_iff[OF domain])
  have managed_eq: "managed = sa_live a"
    by (rule iffD2[OF managed_iff no_retired])
  have gcov:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs managed K_G"
    by (rule StrongSchedulerSnapshotRel_generic_coverageD[OF rel])
  have pre:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF gcov])
  have geometry: "universal_tcb_geometry managed D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF gcov])
  have decode: "scheduler_decode_rel D a"
  proof (rule universal_geometry_scheduler_decode_rel)
    show "universal_scheduler_geometry managed D"
      using geometry laws by (simp add: universal_scheduler_geometry_def)
    show "sa_live a = managed" using managed_eq by simp
  qed
  have lists: "scheduler_lists_rel D generated_scheduler_roots c a"
    by (rule StrongSchedulerSnapshotRel_scheduler_listsD[OF rel])
  have controls:
    "scheduler_role_rel generated_scheduler_roots c a \<and>
     scheduler_managed_scalar_rel c a managed \<and>
     scheduler_current_rel D c a \<and>
     scheduler_boundary_rel c"
    by (rule StrongSchedulerSnapshotRel_role_scalar_currentD[OF rel])
  have role: "scheduler_role_rel generated_scheduler_roots c a"
    using controls by simp
  have managed_scalar: "scheduler_managed_scalar_rel c a managed"
    using controls by simp
  have scalar_iff:
    "scheduler_managed_scalar_rel c a managed \<longleftrightarrow>
       scheduler_scalar_rel c a"
    by (rule scheduler_managed_scalar_rel_no_retired[OF managed_eq])
  have scalar: "scheduler_scalar_rel c a"
    by (rule iffD1[OF scalar_iff managed_scalar])
  have current: "scheduler_current_rel D c a"
    using controls by simp
  have boundary: "scheduler_boundary_rel c"
    using controls by simp
  have core: "core_wf a"
    by (rule StrongSchedulerSnapshotRel_coreD[OF rel])
  show ?thesis
    using core decode lists role scalar current boundary
    by (simp add: raw_scheduler_rel_def)
qed

text \<open>
  Exact remaining ledger for a universal generated-while lifting.

  (1) one_due_context and one_due_gateH_entry_rel currently have only
      odc_live.  Their family/decoder/geometry clauses use it as the managed
      allocation domain, while TaskObservationRel and the abstract fold use it
      as sa_live.  They need a distinct odc_managed field (or an equivalent
      extra parameter), with odc_task and every delayed/ready head proved in
      sa_live and all raw-family nodes proved in odc_managed.

  (2) one_due_gateH_reentry must then be replayed over GenericRootUniverse,
      including an explicit frame for xTasksWaitingTermination and its raw
      count/cursor/payload/container facts.  The current re-entry theorem can
      preserve only roots whose nodes are drawn from its single odc_live set.

  (3) the generated Result-step theorem must preserve
      StrongSchedulerSnapshotRel, not only due_prefix_gate_inv.  The missing
      conjunctions are the termination root, external Event-root union,
      managed task observations, managed task count, current pointer, delayed
      role pair, untouched scalars, boundary globals and cross-family storage.

  (4) at tick wrap, xNumOfOverflows is a signed generated C scalar whereas
      scheduler_abs stores nat.  A universal contract needs either a proved
      reachable non-overflow invariant for that signed counter or a modular/
      event abstraction; silently fixing a non-wrap value is invalid.

  (5) the suspended branch increments the unsigned uxMissedTicks word, while
      task_increment_tick_abs uses Suc on nat.  Full all-input correctness
      therefore needs a word/modular observation or a public precondition that
      genuinely excludes the max-word state.  This does not block the unlocked
      due-prefix loop, where the field is framed, but it blocks the final
      branch-complete task_increment_tick theorem.

  (6) after (1)--(3), compose the real generated while using the existing
      Result step and the two distinct terminal controls: non-NULL future head
      gives state-preserving Exn (), while NULL gives state-preserving normal
      NULL.  Only the enclosing finally maps both to the public Result ().

  No clause above fixes a task identity, priority, tick, key, ring length,
  cursor, root address, delayed role, Event owner or terminal branch.
\<close>

end

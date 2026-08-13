theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Index
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs.Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs"
begin

text \<open>
  A nonempty Strong entry generates its managed-view package canonically.
  Thus callers do not supply a Gate-H premise.  The context and Event branch
  below are witnesses obtained from the checked Strong state and generated
  roots, not fixed constants.
\<close>

lemma DueLoopStrongHeadRel_managed_generated_entryI:
  assumes strong:
    "DueLoopStrongHeadRel D c entry managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] (map Generic (task # due_tail))
       (map Generic future) phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry
       (task # due_tail) future pxTCB managed termination external K_G K_E"
proof -
  have strong_head:
    "DueLoopStrongHeadRel D c entry managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry [] (Generic task # map Generic due_tail)
       (map Generic future) phase nxt pxTCB"
    using strong by simp
  let ?C =
    "due_prefix_canonical_managed_context R c entry managed
       external K_E task"
  let ?branch = "one_due_canonical_event_branch ?C S"
  have selector: "odc_task ?C = task"
    by simp
  have gate:
    "due_prefix_managed_gate_inv D R c now entry []
      (map Generic (task # due_tail)) (map Generic future)
      entry managed ?C ?branch S generic_raw event_raw"
    using DueLoopStrongHeadRel_canonical_managed_gate[OF strong_head roots]
    by simp
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have phase_eq: "phase = DueGate"
    and next_eq: "nxt = Some (Generic task)"
    using exit by (simp_all add: due_prefix_exit_inv_def)
  have ptr: "pxTCB = sd_tcb_ptr D task"
    using DueLoopStrongHeadRel_ptrD[OF strong] next_eq
    by (auto simp: strong_due_next_ptr_rel_def)
  show ?thesis
    unfolding ManagedStrongDuePrefixGeneratedEntryRel_def
    apply (simp only: list.case)
    apply (rule exI[where x = ?C])
    apply (rule exI[where x = ?branch])
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using selector ptr strong gate phase_eq next_eq by simp
qed

lemma ManagedStrongDuePrefixGeneratedEntryRel_nonempty_indexD:
  assumes entry_rel:
    "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry
       (task # due_tail) future pxTCB managed termination external K_G K_E"
  shows
    "due_prefix_managed_strong_generated_head_index D R now entry
       (map Generic (task # due_tail)) future [] task due_tail pxTCB c
       managed termination external K_G K_E"
proof -
  obtain C branch S generic_raw event_raw where
      selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and strong:
      "DueLoopStrongHeadRel D c entry managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry [] (map Generic (task # due_tail))
        (map Generic future) DueGate (Some (Generic task)) pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry []
        (map Generic (task # due_tail)) (map Generic future)
        entry managed C branch S generic_raw event_raw"
    using entry_rel
    by (auto simp: ManagedStrongDuePrefixGeneratedEntryRel_def)
  have entry_fold: "due_prefix_fold_state entry [] = entry"
    by (simp add: due_prefix_fold_state_def remove_nodes_def)
  show ?thesis
    unfolding due_prefix_managed_strong_generated_head_index_def
    apply (intro conjI)
    subgoal by simp
    apply (rule exI[where x=C])
    apply (rule exI[where x=branch])
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using selector ptr strong gate entry_fold by simp
qed

lemma due_prefix_managed_strong_generated_head_index_nonnull:
  assumes index:
    "due_prefix_managed_strong_generated_head_index D R now entry all_due
       future processed task due_tail pxTCB c managed termination external
       K_G K_E"
  shows "pxTCB \<noteq> NULL"
proof -
  obtain C branch S generic_raw event_raw where
      selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
        (map Generic (task # due_tail)) (map Generic future)
        (due_prefix_fold_state entry processed) managed
        C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_managed_strong_generated_head_index_def)
  have gateH:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view (due_prefix_fold_state entry processed)
         managed)
       C branch S generic_raw event_raw"
    using gate by (simp add: due_prefix_managed_gate_inv_def)
  have context_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF gateH])
  have abstract_live:
    "odc_task C \<in>
       sa_live (managed_scheduler_view
         (due_prefix_fold_state entry processed) managed)"
    using context_live one_due_gateH_live_absD[OF gateH] by simp
  have observation:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (managed_scheduler_view (due_prefix_fold_state entry processed)
         managed)"
    by (rule one_due_gateH_task_observationD[OF gateH])
  have guard: "c_guard (sd_tcb_ptr D (odc_task C))"
    using TaskObservationRel_liveD[OF observation abstract_live] by blast
  have nonnull: "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
    by (rule c_guard_NULL[OF guard])
  show ?thesis using nonnull selector ptr by simp
qed

text \<open>
  The checked managed non-last capstone advances the exact symbolic index.
  Its output context, branch, snapshot and raw families replace the old
  package together; none is re-existentialised independently.
\<close>

theorem due_prefix_managed_strong_generated_nonlast_index_step:
  assumes index:
    "due_prefix_managed_strong_generated_head_index D R now entry all_due
       future processed task (u # due_tail) pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_managed_strong_generated_head_index D R now entry all_due
         future (processed @ [Generic task]) u due_tail
         (sd_tcb_ptr D u) t managed termination external K_G K_E\<rbrace>"
proof -
  obtain C branch S generic_raw event_raw where
      ledger:
        "all_due = processed @ map Generic (task # u # due_tail)"
    and selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and strong:
      "DueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed (map Generic (task # u # due_tail))
        (map Generic future) DueGate (Some (Generic task)) pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
        (map Generic (task # u # due_tail)) (map Generic future)
        (due_prefix_fold_state entry processed) managed
        C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_managed_strong_generated_head_index_def)
  have strong':
    "DueLoopStrongHeadRel D c
       (due_prefix_fold_state entry processed)
       managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed
       (Generic task # Generic u # map Generic due_tail)
       (map Generic future) DueGate (Some (Generic task)) pxTCB"
    using strong by simp
  have gate':
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # Generic u # map Generic due_tail)
       (map Generic future) (due_prefix_fold_state entry processed) managed
       C branch S generic_raw event_raw"
    using gate by simp
  note step = DueLoopStrongHeadRel_managed_gate_nonlast_result_full[
    OF strong' gate' selector roots]
  show ?thesis
    unfolding ptr
  proof (rule runs_to_weaken[OF step])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "DueLoopManagedSharedResultPost D R now entry processed task u
        (map Generic due_tail) (map Generic future)
        (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw K_G K_E
        managed termination external c r t"
    let ?after =
      "due_prefix_result_step_abs entry processed (Generic task)"
    let ?h0 =
      "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
    let ?hg = "one_due_generic_remove_heap D C ?h0"
    let ?he = "one_due_event_remove_heap D C branch ?hg"
    let ?generic_raw' =
      "one_due_reentry_generic_raw D C ?he generic_raw"
    let ?event_raw' =
      "one_due_event_raw_after_remove D C branch event_raw"
    let ?S' = "one_due_reentry_snapshot C branch S"
    note post_facts =
      post[unfolded DueLoopManagedSharedResultPost_def Let_def]
    have result: "r = Result (sd_tcb_ptr D u)"
      by (rule conjunct1[OF post_facts])
    note post_tail1 = conjunct2[OF post_facts]
    note post_tail2 = conjunct2[OF post_tail1]
    note gate_exists = conjunct1[OF post_tail2]
    note strong_after = conjunct2[OF post_tail2]
    obtain branch' where gate_after:
      "due_prefix_managed_gate_inv D R t now entry
        (processed @ [Generic task])
        (Generic u # map Generic due_tail) (map Generic future)
        ?after managed (one_due_reentry_context C u) branch'
        ?S' ?generic_raw' ?event_raw'"
      using gate_exists by blast
    have after_fold:
      "?after = due_prefix_fold_state entry
        (processed @ [Generic task])"
      by (simp add: due_prefix_result_step_abs_def)
    have ledger_after:
      "all_due = (processed @ [Generic task]) @
        map Generic (u # due_tail)"
      using ledger by simp
    have index_after:
      "due_prefix_managed_strong_generated_head_index D R now entry all_due
        future (processed @ [Generic task]) u due_tail
        (sd_tcb_ptr D u) t managed termination external K_G K_E"
      unfolding due_prefix_managed_strong_generated_head_index_def
      apply (intro conjI)
      subgoal by (rule ledger_after)
      apply (rule exI[where x="one_due_reentry_context C u"])
      apply (rule exI[where x=branch'])
      apply (rule exI[where x="?S'"])
      apply (rule exI[where x="?generic_raw'"])
      apply (rule exI[where x="?event_raw'"])
      using gate_after strong_after after_fold
      by (simp add: one_due_reentry_context_components)
    show
      "r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_managed_strong_generated_head_index D R now entry all_due
         future (processed @ [Generic task]) u due_tail
         (sd_tcb_ptr D u) t managed termination external K_G K_E"
      using result index_after by simp
  qed
qed

end

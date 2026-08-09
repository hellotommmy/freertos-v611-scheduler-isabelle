theory Scheduler_Due_Prefix_Strong_Generated_Index
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone.Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone"
begin

text \<open>
  Exact induction index for the strong generated due loop.  The total due
  ledger and the processed prefix are explicit parameters; consequently a
  normal body result has only one possible successor index.  The local Gate-H
  context, raw root families and phase snapshot form one existential package.
  In particular the strong scheduler relation and Gate-H cannot select
  different representations of the successor heap.

  The managed domain, termination ring, protected external Event roots and
  both total payload observations are parameters rather than existential
  witnesses.  They therefore remain literally the same across every finite
  number of generated body executions.
\<close>

definition due_prefix_strong_generated_head_index ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "due_prefix_strong_generated_head_index D R now entry all_due future
       processed task due_tail pxTCB c managed termination external K_G K_E
       \<longleftrightarrow>
     all_due = processed @ map Generic (task # due_tail) \<and>
     (\<exists>C branch S generic_raw event_raw.
       odc_task C = task \<and>
       pxTCB = sd_tcb_ptr D task \<and>
       DueLoopStrongHeadRel D c
         (due_prefix_fold_state entry processed)
         managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry processed (map Generic (task # due_tail))
         (map Generic future) DueGate (Some (Generic task)) pxTCB \<and>
       due_prefix_gate_inv D R c now entry processed
         (map Generic (task # due_tail)) (map Generic future)
         (due_prefix_fold_state entry processed)
         C branch S generic_raw event_raw)"

lemma due_prefix_strong_generated_head_index_nonnull:
  assumes index:
    "due_prefix_strong_generated_head_index D R now entry all_due future
       processed task due_tail pxTCB c managed termination external K_G K_E"
  shows "pxTCB \<noteq> NULL"
proof -
  obtain C branch S generic_raw event_raw where
      selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
        (map Generic (task # due_tail)) (map Generic future)
        (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_strong_generated_head_index_def)
  have gate_task:
    "due_prefix_gate_inv D R c now entry processed
       (Generic (odc_task C) # map Generic due_tail)
       (map Generic future) (due_prefix_fold_state entry processed)
       C branch S generic_raw event_raw"
    using gate selector by simp
  have nonnull: "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
    by (rule due_prefix_gate_inv_head_nonnull[OF gate_task])
  show ?thesis using nonnull selector ptr by simp
qed

text \<open>
  A non-last source result advances the explicit processed index by exactly
  the current Generic node.  The successor Gate-H branch obtained from
  DueLoopSharedResultPost is installed in the same existential package as the
  computed raw families and snapshot used by DueLoopStrongHeadRel.  There is
  no second existential successor-family witness.
\<close>

theorem due_prefix_strong_generated_nonlast_index_step:
  assumes index:
    "due_prefix_strong_generated_head_index D R now entry all_due future
       processed task (u # due_tail) pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_strong_generated_head_index D R now entry all_due future
         (processed @ [Generic task]) u due_tail
         (sd_tcb_ptr D u) t managed termination external K_G K_E\<rbrace>"
proof -
  obtain C branch S generic_raw event_raw where
      ledger:
        "all_due = processed @
          map Generic (task # u # due_tail)"
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
      "due_prefix_gate_inv D R c now entry processed
        (map Generic (task # u # due_tail)) (map Generic future)
        (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_strong_generated_head_index_def)
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
    "due_prefix_gate_inv D R c now entry processed
       (Generic task # Generic u # map Generic due_tail)
       (map Generic future) (due_prefix_fold_state entry processed)
       C branch S generic_raw event_raw"
    using gate by simp
  note step = DueLoopStrongHeadRel_nonlast_result_full[
    OF strong' gate' selector roots]
  show ?thesis
    unfolding ptr
  proof (rule runs_to_weaken[OF step])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "DueLoopSharedResultPost D R now entry processed task u
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
      post[unfolded DueLoopSharedResultPost_def Let_def]
    have result: "r = Result (sd_tcb_ptr D u)"
      by (rule conjunct1[OF post_facts])
    note post_tail1 = conjunct2[OF post_facts]
    note state_eq = conjunct1[OF post_tail1]
    note post_tail2 = conjunct2[OF post_tail1]
    note gate_exists = conjunct1[OF post_tail2]
    note strong_after = conjunct2[OF post_tail2]
    obtain branch' where
        gate_after:
          "due_prefix_gate_inv D R t now entry
            (processed @ [Generic task])
            (Generic u # map Generic due_tail) (map Generic future)
            ?after (one_due_reentry_context C u) branch'
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
      "due_prefix_strong_generated_head_index D R now entry all_due future
        (processed @ [Generic task]) u due_tail
        (sd_tcb_ptr D u) t managed termination external K_G K_E"
      unfolding due_prefix_strong_generated_head_index_def
      apply (intro conjI)
      subgoal by (rule ledger_after)
      apply (rule exI[where x="one_due_reentry_context C u"])
      apply (rule exI[where x=branch'])
      apply (rule exI[where x = "?S'"])
      apply (rule exI[where x = "?generic_raw'"])
      apply (rule exI[where x = "?event_raw'"])
      using gate_after strong_after after_fold
      by (simp add: one_due_reentry_context_components)
    show
      "r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_strong_generated_head_index D R now entry all_due future
         (processed @ [Generic task]) u due_tail
         (sd_tcb_ptr D u) t managed termination external K_G K_E"
      using result index_after by simp
  qed
qed

text \<open>
  Entry adapter for a nonempty universally quantified due list.  The phase,
  next-node and current abstract state are not new assumptions: the existing
  exit invariant inside DueLoopStrongHeadRel fixes them from the nonempty
  remaining list.
\<close>

lemma StrongDuePrefixGeneratedEntryRel_nonempty_head_indexD:
  assumes rel:
    "StrongDuePrefixGeneratedEntryRel D R c now entry (task # due_tail)
       future pxTCB managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
  shows
    "due_prefix_strong_generated_head_index D R now entry
       (map Generic (task # due_tail)) future [] task due_tail pxTCB c
       managed termination external K_G K_E"
proof -
  obtain phase nxt ctx branch where
      strong:
        "DueLoopStrongHeadRel D c entry managed termination external
          generic_raw generic_abs event_raw event_abs K_G K_E S
          now entry [] (map Generic (task # due_tail))
          (map Generic future) phase nxt pxTCB"
    and selector: "odc_task ctx = task"
    and gate:
      "due_prefix_gate_inv D R c now entry []
        (map Generic (task # due_tail)) (map Generic future)
        entry ctx branch S generic_raw event_raw"
    using rel
    by (auto simp: StrongDuePrefixGeneratedEntryRel_def)
  have phase_eq: "phase = DueGate"
    and next_eq: "nxt = Some (Generic task)"
    using DueLoopStrongHeadRel_exitD[OF strong]
    by (simp_all add: due_prefix_exit_inv_def)
  have ptr: "pxTCB = sd_tcb_ptr D task"
    using DueLoopStrongHeadRel_ptrD[OF strong] next_eq
    by (auto simp: strong_due_next_ptr_rel_def)
  have families:
      "generic_abs = ods_generic_family S \<and>
       event_abs = ods_event_family S"
    using DueLoopStrongHeadRel_shared_snapshot_projectionD[OF strong]
    by blast
  have entry_fold: "due_prefix_fold_state entry [] = entry"
    by (simp add: due_prefix_fold_state_def remove_nodes_def)
  show ?thesis
    unfolding due_prefix_strong_generated_head_index_def
    apply (intro conjI)
    subgoal by simp
    apply (rule exI[where x=ctx])
    apply (rule exI[where x=branch])
    apply (rule exI[where x=S])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=event_raw])
    using strong selector gate phase_eq next_eq ptr families entry_fold
    by simp
qed

end

theory Scheduler_Due_Prefix_Generated_While_Index
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Core.Scheduler_Due_Prefix_Generated_While_Core"
begin

text \<open>
  The induction index is the arbitrary list of due tasks after the current
  head.  All concrete Gate-H witnesses are existential because each generated
  body execution changes the heap, raw families, list cursors, Event branch,
  and current task context.  The fixed ledger @{term all_due} prevents this
  existential packaging from weakening the functional claim: at every head it
  is exactly the processed prefix followed by the current task and the indexed
  suffix.
\<close>

definition due_prefix_generated_index_inv ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_index_inv D R now entry all_due future due_tail
       pxTCB c \<longleftrightarrow>
     (\<exists>processed current C branch S generic_raw event_raw.
        all_due = processed @
          (Generic (odc_task C) # map Generic due_tail) \<and>
        pxTCB = sd_tcb_ptr D (odc_task C) \<and>
        due_prefix_gate_inv D R c now entry processed
          (Generic (odc_task C) # map Generic due_tail)
          (map Generic future)
          current C branch S generic_raw event_raw)"

lemma due_prefix_generated_index_inv_nonnull:
  assumes index:
    "due_prefix_generated_index_inv D R now entry all_due future
       due_tail pxTCB c"
  shows "pxTCB \<noteq> NULL"
proof -
  obtain processed current C branch S generic_raw event_raw where
      ptr: "pxTCB = sd_tcb_ptr D (odc_task C)"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
        (Generic (odc_task C) # map Generic due_tail)
        (map Generic future) current C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_generated_index_inv_def)
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
      generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have live_abs: "odc_task C \<in> sa_live current"
    using live one_due_gateH_live_absD[OF rel] by simp
  have obs:
    "TaskObservationRel D
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) current"
    by (rule one_due_gateH_task_observationD[OF rel])
  have guard: "c_guard (sd_tcb_ptr D (odc_task C))"
    using TaskObservationRel_liveD[OF obs live_abs] by blast
  show ?thesis
    using c_guard_NULL[OF guard] ptr by simp
qed

text \<open>
  One exact generated body result shortens the arbitrary due index.  The
  selector bridge for @{const one_due_reentry_context} is stated explicitly:
  the proof never relies on blind search discovering that the next context's
  task selector is the arbitrary next task @{term u}.
\<close>

theorem due_prefix_generated_index_result_step:
  assumes index:
    "due_prefix_generated_index_inv D R now entry all_due future
       (u # due_tail) pxTCB c"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       (\<forall>q. r = Result q \<longrightarrow>
          due_prefix_generated_index_inv D R now entry all_due future
            due_tail q t) \<and>
       (\<forall>e. r = Exn e \<longrightarrow> False)\<rbrace>"
proof -
  obtain processed current C branch S generic_raw event_raw where
      ledger:
        "all_due = processed @
          (Generic (odc_task C) # map Generic (u # due_tail))"
    and ptr: "pxTCB = sd_tcb_ptr D (odc_task C)"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
        (Generic (odc_task C) # map Generic (u # due_tail))
        (map Generic future) current C branch S generic_raw event_raw"
    using index
    by (auto simp: due_prefix_generated_index_inv_def)
  have gate':
    "due_prefix_gate_inv D R c now entry processed
       (Generic (odc_task C) # Generic u # map Generic due_tail)
       (map Generic future) current C branch S generic_raw event_raw"
    using gate by simp
  note step = due_prefix_generated_source_result_step[OF gate' roots]
  show ?thesis
    unfolding ptr
  proof (rule runs_to_weaken[OF step])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "\<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # map Generic due_tail) (map Generic future)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
    obtain branch' where
        result: "r = Result (sd_tcb_ptr D u)"
      and gate_post:
        "due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # map Generic due_tail) (map Generic future)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
      using post by blast
    have ledger_post:
      "all_due =
        (processed @ [Generic (odc_task C)]) @
          (Generic u # map Generic due_tail)"
      using ledger by simp
    have index_post:
      "due_prefix_generated_index_inv D R now entry all_due future
        due_tail (sd_tcb_ptr D u) t"
      unfolding due_prefix_generated_index_inv_def
      apply (rule exI[where x =
        "processed @ [Generic (odc_task C)]"])
      apply (rule exI[where x =
        "due_prefix_result_step_abs entry processed
          (Generic (odc_task C))"])
      apply (rule exI[where x = "one_due_reentry_context C u"])
      apply (rule exI[where x = branch'])
      apply (rule exI[where x = "one_due_reentry_snapshot C branch S"])
      apply (rule exI[where x =
        "one_due_reentry_generic_raw D C
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem
                (Scheduler_V611_Parse.globals.t_hrs_' c))))
          generic_raw"])
      apply (rule exI[where x =
        "one_due_event_raw_after_remove D C branch event_raw"])
      using ledger_post gate_post
      by (simp add: one_due_reentry_context_components)
    show
      "(\<forall>q. r = Result q \<longrightarrow>
         due_prefix_generated_index_inv D R now entry all_due future
           due_tail q t) \<and>
       (\<forall>e. r = Exn e \<longrightarrow> False)"
      using result index_post by auto
  qed
qed

end

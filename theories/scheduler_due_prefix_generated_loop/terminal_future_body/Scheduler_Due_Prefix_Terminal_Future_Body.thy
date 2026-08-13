theory Scheduler_Due_Prefix_Terminal_Future_Body
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Empty_Body.Scheduler_Due_Prefix_Terminal_Empty_Body"
begin

text \<open>
  Nonempty suffix: the returned pointer, observation, live-domain membership,
  unchanged tick and physical Generic key are all derived.  These are exactly
  the premises of the generated future-head throw theorem and are deliberately
  weaker than Gate-H.
\<close>

theorem due_prefix_generated_last_due_future_body:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
        r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D (Generic f # fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) FutureExit (Some (Generic f))
          (sd_tcb_ptr D f) \<and>
        (\<exists>k. due_prefix_future_source_ready D t now
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) f k)\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] (Generic f # fs) current"
    by (rule due_prefix_gate_inv_loopD[OF inv])
  have current_def: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF prefix])
  note future_facts = due_prefix_gate_inv_last_due_future_semantics[OF inv]
  have f_live: "f \<in> odc_live C"
    by (rule conjunct1[OF future_facts])
  have future_key: "now < ods_generic_payload S f"
    by (rule conjunct2[OF conjunct2[OF future_facts]])
  note owner_facts = due_prefix_gate_inv_last_due_head_owner[OF inv]
  have raw_nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    by (rule conjunct1[OF conjunct2[OF owner_facts]])
  have owner_f:
    "PTR_COERCE(unit \<rightarrow>
        Scheduler_V611_Parse.tskTaskControlBlock_C)
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          (hd (ring (list_remove_abs
            (one_due_generic_raw_ptr D (odc_task C))
            (generic_raw (odc_delayed_root C))))))) =
      sd_tcb_ptr D f"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF owner_facts]]])
  have exit:
    "due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) FutureExit (Some (Generic f))"
    using due_prefix_gate_inv_last_due_exit[OF inv] by simp
  have terminal:
    "due_prefix_terminal_source_rel D (Generic f # fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) FutureExit (Some (Generic f))
       (sd_tcb_ptr D f)"
    by (simp add: due_prefix_terminal_source_rel_def
        due_prefix_bare_terminal_rel_def)
  show ?thesis
  proof (rule runs_to_weaken[OF one_due_tick_body_exact[OF rel roots]])
    fix r t
    assume exact:
      "\<exists>v. r = Result v \<and>
         one_due_tick_body_post D C branch generic_raw c (Result v) t"
    obtain v where result: "r = Result v"
      and body:
        "one_due_tick_body_post D C branch generic_raw c (Result v) t"
      using exact by (elim exE conjE)
    note body_facts = one_due_tick_body_post_def[THEN iffD1, OF body]
    note hrs_t = conjunct1[OF body_facts]
    note body_rest1 = conjunct2[OF body_facts]
    note body_rest2 = conjunct2[OF body_rest1]
    note body_rest3 = conjunct2[OF body_rest2]
    note tick_t = conjunct1[OF body_rest3]
    note result_pin = conjunct2[OF body_rest3]
    have v_f: "v = sd_tcb_ptr D f"
    proof -
      have selected:
        "(if ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))) = []
          then NULL
          else PTR_COERCE(unit \<rightarrow>
              Scheduler_V611_Parse.tskTaskControlBlock_C)
            (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
              (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
                (hd (ring (list_remove_abs
                  (one_due_generic_raw_ptr D (odc_task C))
                  (generic_raw (odc_delayed_root C)))))))) =
          sd_tcb_ptr D f"
        using raw_nonempty owner_f by simp
      have result_eq: "Result v = Result (sd_tcb_ptr D f)"
        using result_pin selected by simp
      show ?thesis using result_eq by simp
    qed
    have body_f:
      "one_due_tick_body_post D C branch generic_raw c
        (Result (sd_tcb_ptr D f)) t"
      using body v_f by simp

    let ?post = "due_prefix_result_step_abs entry processed
      (Generic (odc_task C))"
    have obs_heap:
      "TaskObservationRel D
        (one_due_ready_insert_heap D C generic_raw
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
        current"
      by (rule one_due_reentry_task_observation[OF rel])
    have obs_current:
      "TaskObservationRel D
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) current"
      using obs_heap hrs_t by simp
    have post_live: "sa_live ?post = sa_live current"
      using current_def by simp
    have post_priority: "sa_priority ?post = sa_priority current"
      using current_def by simp
    have obs_post:
      "TaskObservationRel D
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) ?post"
    proof -
      have obs_iff:
        "TaskObservationRel D
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) current
         \<longleftrightarrow>
         TaskObservationRel D
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) entry"
        using current_def by (simp add: TaskObservationRel_def)
      have obs_entry:
        "TaskObservationRel D
          (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) entry"
        by (rule iffD1[OF obs_iff obs_current])
      show ?thesis
        by (rule due_prefix_result_step_task_observation_iff[THEN iffD2,
              OF obs_entry])
    qed
    have context_live: "odc_live C = sa_live current"
      by (rule one_due_gateH_live_absD[OF rel])
    have f_post_live: "f \<in> sa_live ?post"
      using f_live context_live post_live by simp
    have context_tick: "odc_tick C = now"
      by (rule due_prefix_gate_inv_context_tickD[OF inv])
    have entry_tick:
      "odc_tick C = Scheduler_V611_Parse.globals.xTickCount_' c"
      by (rule one_due_gateH_tick_wordD[OF rel])
    have post_tick:
      "Scheduler_V611_Parse.globals.xTickCount_' t = now"
      using tick_t entry_tick context_tick by simp
    have heap_key:
      "raw_key_at
        (one_due_ready_insert_heap D C generic_raw
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))))
        (one_due_generic_raw_ptr D f) =
       ods_generic_payload (one_due_reentry_snapshot C branch S) f"
      by (rule one_due_reentry_generic_keys[OF rel f_live])
    have post_key:
      "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t))
         (one_due_generic_raw_ptr D f) = ods_generic_payload S f"
      using heap_key hrs_t
      by (simp add: one_due_reentry_snapshot_payloads)
    have ready:
      "due_prefix_future_source_ready D t now ?post f
         (ods_generic_payload S f)"
      apply (rule due_prefix_future_source_ready_def[THEN iffD2])
      apply (intro conjI)
      subgoal by (rule obs_post)
      subgoal by (rule f_post_live)
      subgoal by (rule post_tick)
      subgoal by (rule post_key)
      subgoal by (rule future_key)
      done
    show
      "r = Result (sd_tcb_ptr D f) \<and>
       one_due_tick_body_post D C branch generic_raw c
         (Result (sd_tcb_ptr D f)) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
         ?post FutureExit (Some (Generic f)) \<and>
       due_prefix_terminal_source_rel D (Generic f # fs) ?post
         FutureExit (Some (Generic f)) (sd_tcb_ptr D f) \<and>
       (\<exists>k. due_prefix_future_source_ready D t now ?post f k)"
    proof (intro conjI)
      show "r = Result (sd_tcb_ptr D f)" using result v_f by simp
    next
      show "one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t"
        by (rule body_f)
    next
      show "due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
          ?post FutureExit (Some (Generic f))"
        by (rule exit)
    next
      show "due_prefix_terminal_source_rel D (Generic f # fs) ?post
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
        by (rule terminal)
    next
      show "\<exists>k. due_prefix_future_source_ready D t now ?post f k"
        by (rule exI[where x = "ods_generic_payload S f"], rule ready)
    qed
  qed
qed

end

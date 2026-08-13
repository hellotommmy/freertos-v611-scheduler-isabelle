theory Scheduler_Due_Prefix_Managed_Gate_Terminal_Bodies
  imports Scheduler_Due_Prefix_Managed_Gate_Terminal_State_Core
begin

text \<open>
  Generated last-due control facts for the managed decoder domain.  These
  theorems reuse the checked one-due body and derive the returned pointer from
  the represented residual Generic ring.  They never coerce managed into the
  real runnable domain.
\<close>

lemma due_prefix_managed_gate_inv_head_nonnull:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed remaining future
       current managed C branch S generic_raw event_raw"
  shows "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have live_abs:
    "odc_task C \<in> sa_live (managed_scheduler_view current managed)"
    using live one_due_gateH_live_absD[OF rel] by simp
  have obs:
    "TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (managed_scheduler_view current managed)"
    by (rule one_due_gateH_task_observationD[OF rel])
  have guard: "c_guard (sd_tcb_ptr D (odc_task C))"
    using TaskObservationRel_liveD[OF obs live_abs] by blast
  show ?thesis by (rule c_guard_NULL[OF guard])
qed

lemma due_prefix_managed_gate_last_due_exit:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current managed
       C branch S generic_raw event_raw"
  shows
    "due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) [] future
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))
       (due_prefix_exit_phase_of [] future)
       (due_prefix_next_node_of [] future)"
proof -
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] future current"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have post:
    "due_prefix_loop_inv now entry
       (processed @ [Generic (odc_task C)]) [] future
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
    by (rule due_prefix_result_step_preserves_inv[OF prefix])
  show ?thesis using post by (simp add: due_prefix_exit_inv_def)
qed

lemma due_prefix_managed_gate_last_due_empty_raw:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] [] current managed
       C branch S generic_raw event_raw"
  shows
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) = []"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] [] current"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have current_ring:
    "ring (current_delayed_ring current) = [Generic (odc_task C)]"
    using due_prefix_loop_inv_ringD[OF prefix] by simp
  have abstract_empty:
    "ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = []"
    using delayed current_ring by (simp add: list_remove_abs_def)
  show ?thesis
    using one_due_gateH_removed_empty_iff[OF rel] abstract_empty by simp
qed

lemma due_prefix_managed_gate_last_due_future_raw_owner:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs) current managed
       C branch S generic_raw event_raw"
  shows
    "f \<in> odc_live C \<and>
     ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> [] \<and>
     hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D f \<and>
     PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (hd (ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))))))) =
       sd_tcb_ptr D f"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs) current"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # Generic f # map Generic fs"
    using due_prefix_loop_inv_ringD[OF prefix] by simp
  have snapshot_ring:
    "ring (ods_generic_family S (odc_delayed_root C)) =
       Generic (odc_task C) # Generic f # map Generic fs"
    using delayed current_ring by simp
  have head_shape:
    "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = Generic f # rest"
    using snapshot_ring by (auto simp: list_remove_abs_def)
  note bridge = one_due_gateH_removed_head_bridge[OF rel head_shape]
  have f_live: "f \<in> odc_live C" using bridge by blast
  have nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    using bridge by blast
  have hd_f:
    "hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D f"
    using bridge by blast
  obtain u where u_live: "u \<in> odc_live C"
    and hd_u:
      "hd (ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C)))) =
        one_due_generic_raw_ptr D u"
    and owner_u:
      "PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (hd (ring (list_remove_abs
              (one_due_generic_raw_ptr D (odc_task C))
              (generic_raw (odc_delayed_root C))))))) =
        sd_tcb_ptr D u"
    using one_due_next_head_owner_decode[OF rel nonempty] by blast
  have ptr_eq:
    "one_due_generic_raw_ptr D f = one_due_generic_raw_ptr D u"
    using hd_f hd_u by simp
  have decode_f:
    "sd_node_decode D (one_due_generic_raw_ptr D f) = Some (Generic f)"
    by (rule one_due_gateH_generic_ptr_decode[OF rel f_live])
  have decode_u:
    "sd_node_decode D (one_due_generic_raw_ptr D u) = Some (Generic u)"
    by (rule one_due_gateH_generic_ptr_decode[OF rel u_live])
  have eq1:
    "Some (Generic u) =
       sd_node_decode D (one_due_generic_raw_ptr D u)"
    by (rule sym[OF decode_u])
  have eq2:
    "sd_node_decode D (one_due_generic_raw_ptr D u) =
       sd_node_decode D (one_due_generic_raw_ptr D f)"
    by (rule arg_cong[OF sym[OF ptr_eq]])
  have eq12:
    "Some (Generic u) =
       sd_node_decode D (one_due_generic_raw_ptr D f)"
    by (rule trans[OF eq1 eq2])
  have some_eq: "Some (Generic u) = Some (Generic f)"
    by (rule trans[OF eq12 decode_f])
  have node_eq: "Generic u = Generic f"
    using some_eq by (simp only: option.inject)
  have u_eq: "u = f"
    using node_eq by (simp only: node_kind.inject)
  have owner_f:
    "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (hd (ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))))))) =
       sd_tcb_ptr D f"
    using owner_u u_eq by simp
  show ?thesis using f_live nonempty hd_f owner_f by blast
qed

theorem due_prefix_managed_generated_last_due_empty_body_full_state:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] [] current managed
       C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result NULL \<and>
        one_due_tick_body_post D C branch generic_raw c (Result NULL) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None \<and>
        due_prefix_terminal_source_rel D []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None NULL) \<and>
       t = one_due_tick_ready_inserted_state
         D C branch generic_raw c\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  have raw_empty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) = []"
    by (rule due_prefix_managed_gate_last_due_empty_raw[OF inv])
  have exit:
    "due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) [] []
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) EmptyExit None"
    using due_prefix_managed_gate_last_due_exit[OF inv] by simp
  have terminal:
    "due_prefix_terminal_source_rel D []
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) EmptyExit None NULL"
    by (simp add: due_prefix_terminal_source_rel_def
        due_prefix_bare_terminal_rel_def)
  have control:
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result NULL \<and>
       one_due_tick_body_post D C branch generic_raw c (Result NULL) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) [] []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None \<and>
       due_prefix_terminal_source_rel D []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None NULL\<rbrace>"
  proof (rule runs_to_weaken[OF one_due_tick_body_exact[OF rel roots]])
    fix r t
    assume exact:
      "\<exists>v. r = Result v \<and>
         one_due_tick_body_post D C branch generic_raw c (Result v) t"
    obtain v where result: "r = Result v"
      and body:
        "one_due_tick_body_post D C branch generic_raw c (Result v) t"
      using exact by (elim exE conjE)
    note facts = one_due_tick_body_post_def[THEN iffD1, OF body]
    note rest1 = conjunct2[OF facts]
    note rest2 = conjunct2[OF rest1]
    note rest3 = conjunct2[OF rest2]
    note result_pin = conjunct2[OF rest3]
    have v_null: "v = NULL" using result_pin raw_empty by simp
    show
      "r = Result NULL \<and>
       one_due_tick_body_post D C branch generic_raw c (Result NULL) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) [] []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None \<and>
       due_prefix_terminal_source_rel D []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None NULL"
      using result body v_null exit terminal by simp
  qed
  note state = one_due_tick_body_state_exact[OF rel roots]
  show ?thesis using control state by (simp only: runs_to_conj)
qed

theorem due_prefix_managed_generated_last_due_future_body_full_state:
  assumes inv:
    "due_prefix_managed_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # map Generic fs) current managed
       C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result (sd_tcb_ptr D f) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (sd_tcb_ptr D f)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) []
          (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D (Generic f # map Generic fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          FutureExit (Some (Generic f)) (sd_tcb_ptr D f)) \<and>
       t = one_due_tick_ready_inserted_state
         D C branch generic_raw c\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed)
       C branch S generic_raw event_raw"
    using inv by (simp add: due_prefix_managed_gate_inv_def)
  note raw = due_prefix_managed_gate_last_due_future_raw_owner[OF inv]
  have nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    using raw by blast
  have owner_f:
    "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (hd (ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))))))) =
       sd_tcb_ptr D f"
    using raw by blast
  have exit:
    "due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) []
       (Generic f # map Generic fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))
       FutureExit (Some (Generic f))"
    using due_prefix_managed_gate_last_due_exit[OF inv] by simp
  have terminal:
    "due_prefix_terminal_source_rel D (Generic f # map Generic fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))
       FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
    by (simp add: due_prefix_terminal_source_rel_def
        due_prefix_bare_terminal_rel_def)
  have control:
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result (sd_tcb_ptr D f) \<and>
       one_due_tick_body_post D C branch generic_raw c
         (Result (sd_tcb_ptr D f)) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) []
         (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C)))
         FutureExit (Some (Generic f)) \<and>
       due_prefix_terminal_source_rel D (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C)))
         FutureExit (Some (Generic f)) (sd_tcb_ptr D f)\<rbrace>"
  proof (rule runs_to_weaken[OF one_due_tick_body_exact[OF rel roots]])
    fix r t
    assume exact:
      "\<exists>v. r = Result v \<and>
         one_due_tick_body_post D C branch generic_raw c (Result v) t"
    obtain v where result: "r = Result v"
      and body:
        "one_due_tick_body_post D C branch generic_raw c (Result v) t"
      using exact by (elim exE conjE)
    note facts = one_due_tick_body_post_def[THEN iffD1, OF body]
    note rest1 = conjunct2[OF facts]
    note rest2 = conjunct2[OF rest1]
    note rest3 = conjunct2[OF rest2]
    note result_pin = conjunct2[OF rest3]
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
      using nonempty owner_f by simp
    have v_f: "v = sd_tcb_ptr D f"
      using result_pin selected by simp
    show
      "r = Result (sd_tcb_ptr D f) \<and>
       one_due_tick_body_post D C branch generic_raw c
         (Result (sd_tcb_ptr D f)) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) []
         (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) FutureExit (Some (Generic f)) \<and>
       due_prefix_terminal_source_rel D (Generic f # map Generic fs)
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) FutureExit (Some (Generic f))
         (sd_tcb_ptr D f)"
      using result body v_f exit terminal by simp
  qed
  note state = one_due_tick_body_state_exact[OF rel roots]
  show ?thesis using control state by (simp only: runs_to_conj)
qed

end

theory Scheduler_Due_Prefix_Terminal_Empty_Body
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Bridge.Scheduler_Due_Prefix_Terminal_Bridge"
begin

text \<open>
  Empty suffix: the last due body returns NULL.  The concrete poststate is the
  exact generated heap/global postcondition, while the abstract endpoint is
  projected to EmptyExit and the false next-loop guard.
\<close>

theorem due_prefix_generated_last_due_empty_body:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] [] current C branch S
       generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
        r = Result NULL \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result NULL) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None \<and>
        due_prefix_terminal_source_rel D []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None NULL\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
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
    have raw_empty:
      "ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))) = []"
      using due_prefix_gate_inv_last_due_raw_empty_iff[OF inv] by simp
    have v_null: "v = NULL"
    proof -
      note body_facts = one_due_tick_body_post_def[THEN iffD1, OF body]
      note body_rest1 = conjunct2[OF body_facts]
      note body_rest2 = conjunct2[OF body_rest1]
      note body_rest3 = conjunct2[OF body_rest2]
      note result_pin = conjunct2[OF body_rest3]
      show ?thesis using result_pin raw_empty by simp
    qed
    have exit:
      "due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) [] []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None"
      using due_prefix_gate_inv_last_due_exit[OF inv] by simp
    have terminal:
      "due_prefix_terminal_source_rel D []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None NULL"
      by (simp add: due_prefix_terminal_source_rel_def
          due_prefix_bare_terminal_rel_def)
    show
      "r = Result NULL \<and>
       one_due_tick_body_post D C branch generic_raw c
         (Result NULL) t \<and>
       due_prefix_exit_inv now entry
         (processed @ [Generic (odc_task C)]) [] []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None \<and>
       due_prefix_terminal_source_rel D []
         (due_prefix_result_step_abs entry processed
           (Generic (odc_task C))) EmptyExit None NULL"
    proof (intro conjI)
      show "r = Result NULL" using result v_null by simp
    next
      show "one_due_tick_body_post D C branch generic_raw c
          (Result NULL) t"
        using body v_null by simp
    next
      show "due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None"
        by (rule exit)
    next
      show "due_prefix_terminal_source_rel D []
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) EmptyExit None NULL"
        by (rule terminal)
    qed
  qed
qed

end

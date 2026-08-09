theory Scheduler_Due_Prefix_Terminal_Followup
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Body.Scheduler_Due_Prefix_Terminal_Future_Body"
begin

corollary due_prefix_generated_last_due_future_followup_throws:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
        r = Result (sd_tcb_ptr D f) \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) FutureExit (Some (Generic f)) \<and>
        due_prefix_terminal_source_rel D (Generic f # fs)
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) FutureExit (Some (Generic f))
          (sd_tcb_ptr D f) \<and>
        runs_to (one_due_tick_loop_body_source (sd_tcb_ptr D f)) t
          (\<lambda>q u. q = Exn () \<and> u = t)\<rbrace>"
proof (rule runs_to_weaken[OF
    due_prefix_generated_last_due_future_body[OF inv roots]])
  fix r t
  assume post:
    "r = Result (sd_tcb_ptr D f) \<and>
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
         (Generic (odc_task C))) f k)"
  note post_rest1 = conjunct2[OF post]
  note post_rest2 = conjunct2[OF post_rest1]
  note post_rest3 = conjunct2[OF post_rest2]
  note ready_exists = conjunct2[OF post_rest3]
  obtain k where ready:
    "due_prefix_future_source_ready D t now
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) f k"
    using ready_exists by (elim exE)
  have throws:
    "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
       \<lbrace>\<lambda>q u. q = Exn () \<and> u = t\<rbrace>"
    by (rule due_prefix_future_source_ready_throws[OF ready])
  show
    "r = Result (sd_tcb_ptr D f) \<and>
     due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) FutureExit (Some (Generic f)) \<and>
     due_prefix_terminal_source_rel D (Generic f # fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C))) FutureExit (Some (Generic f))
       (sd_tcb_ptr D f) \<and>
     runs_to (one_due_tick_loop_body_source (sd_tcb_ptr D f)) t
       (\<lambda>q u. q = Exn () \<and> u = t)"
  proof (intro conjI)
    show "r = Result (sd_tcb_ptr D f)" by (rule conjunct1[OF post])
  next
    show "due_prefix_exit_inv now entry
        (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
        (due_prefix_result_step_abs entry processed
          (Generic (odc_task C))) FutureExit (Some (Generic f))"
      by (rule conjunct1[OF post_rest2])
  next
    show "due_prefix_terminal_source_rel D (Generic f # fs)
        (due_prefix_result_step_abs entry processed
          (Generic (odc_task C))) FutureExit (Some (Generic f))
        (sd_tcb_ptr D f)"
      by (rule conjunct1[OF post_rest3])
  next
    show "runs_to (one_due_tick_loop_body_source (sd_tcb_ptr D f)) t
        (\<lambda>q u. q = Exn () \<and> u = t)"
      by (rule throws)
  qed
qed

end

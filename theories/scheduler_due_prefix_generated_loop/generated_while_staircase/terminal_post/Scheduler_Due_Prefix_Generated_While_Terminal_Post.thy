theory Scheduler_Due_Prefix_Generated_While_Terminal_Post
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Index.Scheduler_Due_Prefix_Generated_While_Index"
begin

text \<open>
  Exact control post for the generated bare loop.  Empty suffixes leave the
  loop by the false pointer guard and therefore expose @{term "Result NULL"}.
  Nonempty future suffixes execute their first not-yet-due body once; that
  generated body throws and the while exposes @{term "Exn ()"}.  Both cases
  retain the concrete last-due body post and the abstract exit relation.
\<close>

definition due_prefix_generated_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid list \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_generated_terminal_post D now entry all_due future r t
       \<longleftrightarrow>
     (\<exists>endpoint phase next v C branch generic_raw before.
        due_prefix_exit_inv now entry all_due [] (map Generic future)
          endpoint phase next \<and>
        due_prefix_terminal_source_rel D (map Generic future)
          endpoint phase next v \<and>
        one_due_tick_body_post D C branch generic_raw before
          (Result v) t \<and>
        ((future = [] \<and> r = Result NULL) \<or>
         (future \<noteq> [] \<and> r = Exn ())))"

lemma due_prefix_gate_inv_head_nonnull:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "sd_tcb_ptr D (odc_task C) \<noteq> NULL"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
      generic_raw event_raw"
    using inv by (simp add: due_prefix_gate_inv_def)
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
    by (rule c_guard_NULL[OF guard])
qed

lemma due_prefix_future_source_ready_nonnull:
  assumes ready: "due_prefix_future_source_ready D c now a f k"
  shows "sd_tcb_ptr D f \<noteq> NULL"
proof -
  have obs:
    "TaskObservationRel D
      (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a"
    and live: "f \<in> sa_live a"
    using ready
    by (auto simp: due_prefix_future_source_ready_def)
  have guard: "c_guard (sd_tcb_ptr D f)"
    using TaskObservationRel_liveD[OF obs live] by blast
  show ?thesis
    by (rule c_guard_NULL[OF guard])
qed

end

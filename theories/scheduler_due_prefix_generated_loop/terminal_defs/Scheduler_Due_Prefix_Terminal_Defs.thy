theory Scheduler_Due_Prefix_Terminal_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Source_Step.Scheduler_Due_Prefix_Source_Step"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exit_Aware_Invariant.Scheduler_Due_Prefix_Exit_Aware_Invariant"
begin

definition due_prefix_terminal_source_rel ::
  "'tid scheduler_decode \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> due_prefix_exit_phase \<Rightarrow>
   'tid node_kind option \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "due_prefix_terminal_source_rel D future endpoint phase next v \<longleftrightarrow>
     phase = due_prefix_exit_phase_of [] future \<and>
     next = due_prefix_next_node_of [] future \<and>
     phase \<noteq> DueGate \<and>
     due_prefix_terminal_of_phase phase =
       Some (due_prefix_terminal_for_future future) \<and>
     due_prefix_bare_terminal_rel phase endpoint
       (due_prefix_terminal_for_future future) endpoint \<and>
     due_prefix_finally_of_phase phase = Some DuePublicResultUnit \<and>
     ((future = [] \<and> phase = EmptyExit \<and> next = None \<and>
        v = NULL \<and> \<not> due_prefix_phase_guard phase \<and>
        due_prefix_control_of_exit_phase phase = DueLoopGuardNormal) \<or>
      (\<exists>f fs. future = Generic f # fs \<and>
        phase = FutureExit \<and> next = Some (Generic f) \<and>
        v = sd_tcb_ptr D f \<and> due_prefix_phase_guard phase \<and>
        due_prefix_control_of_exit_phase phase = DueLoopFutureHeadExn))"

definition due_prefix_future_source_ready ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid \<Rightarrow>
   32 word \<Rightarrow> bool"
where
  "due_prefix_future_source_ready D c now a f k \<longleftrightarrow>
     TaskObservationRel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a \<and>
     f \<in> sa_live a \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = now \<and>
     raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (one_due_generic_raw_ptr D f) = k \<and>
     now < k"

end

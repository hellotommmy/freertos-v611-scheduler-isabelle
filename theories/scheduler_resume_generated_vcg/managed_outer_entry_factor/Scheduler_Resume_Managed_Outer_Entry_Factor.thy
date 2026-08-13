theory Scheduler_Resume_Managed_Outer_Entry_Factor
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry.Scheduler_Resume_Managed_Outer_Entry"
begin

definition resume_outer_generated_entry_suffix ::
  "(int, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_outer_generated_entry_suffix = do {
     xAlreadyYielded \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.globals.uxSchedulerSuspended_' s = 0)
       (condition
         (\<lambda>s. 0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' s)
         (do {
            guard (\<lambda>s. c_guard Scheduler_V611_Parse.xPendingReadyList_');
            ret \<leftarrow> resume_pending_generated_head_read;
            (pxTCB, xYieldRequired) \<leftarrow>
              whileLoop resume_pending_generated_cond
                resume_pending_generated_body
                (PTR_COERCE(unit \<rightarrow>
                   Scheduler_V611_Parse.tskTaskControlBlock_C) ret, 0);
            resume_after_drain_continuation xYieldRequired
          })
         (return 0))
       (return 0);
     ret \<leftarrow>
       Scheduler_V611_Tick_Translation.eal6_port_exit_critical';
     return xAlreadyYielded
   }"

lemma xTaskResumeAll_generated_entry_prefix_factor:
  "Scheduler_V611_Delay_Translation.xTaskResumeAll' =
     bind resume_outer_generated_entry_prefix
       (\<lambda>_. resume_outer_generated_entry_suffix)"
  unfolding xTaskResumeAll_program_eq resume_outer_program_def
    resume_outer_generated_entry_prefix_def
    resume_outer_generated_entry_suffix_def
  by (simp add: bind_assoc)

ML \<open>
  val factor = @{thm xTaskResumeAll_generated_entry_prefix_factor}
  val _ =
    if null (Thm.hyps_of factor) then ()
    else error "outer generated source factor has hidden hypotheses"
  val _ =
    if length (Thm.prems_of factor) = 0 then ()
    else error "outer generated source factor gained a premise"
\<close>

end

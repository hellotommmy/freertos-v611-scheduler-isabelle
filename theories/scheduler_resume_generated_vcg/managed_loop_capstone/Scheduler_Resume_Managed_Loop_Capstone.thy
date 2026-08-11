theory Scheduler_Resume_Managed_Loop_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Pure.Scheduler_Resume_Managed_Loop_Pure"
begin

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_pure:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s.
        \<exists>generic_raw' generic_abs' event_raw' event_abs'
           S' C' P' yw.
          r = Result (NULL, yw) \<and>
          CursorGeneralStrongResumePendingManagedPhaseRel
            D s (drain_pending_abs a)
            managed termination external
            generic_raw' generic_abs' event_raw' event_abs'
            K_G K_E S' C' P' \<and>
          rpc_tasks C' = [] \<and>
          rpc_live C' = rpc_live C \<and>
          rpc_current_priority C' = rpc_current_priority C \<and>
          rpc_priority C' = rpc_priority C \<and>
          yw =
            (if resume_pending_requires_yield a
             then (1 :: int) else y) \<and>
          ring (sa_pending (drain_pending_abs a)) = [] \<and>
          CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
            D (1 :: 32 word) (1 :: 32 word) s
            (drain_pending_abs a) managed termination external \<and>
          Scheduler_V611_Parse.globals.eal6_port_critical_depth_' s = 1 \<and>
          Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' s = 1 \<and>
          Scheduler_V611_Parse.globals.xSchedulerRunning_' s = 1 \<and>
          resume_pending_control_frame c s
     \<rbrace>"
proof -
  note loop =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains[
      where y=y, OF phase]
  note drain =
    CursorGeneralStrongResumePendingManagedPhaseRel_drain_pending_absD[
      OF phase]
  note trigger =
    CursorGeneralStrongResumePendingManagedPhaseRel_requires_yieldD[
      OF phase]
  show ?thesis
  proof (rule runs_to_weaken[OF loop])
  fix r s
  assume old:
    "\<exists>post_generic_raw post_generic_abs post_event_raw post_event_abs
        post_S post_C post_P yw.
       r = Result (NULL, yw) \<and>
       CursorGeneralStrongResumePendingManagedPhaseRel
         D s (drain_pending_nodes_abs (map Event (rpc_tasks C)) a)
         managed termination external
         post_generic_raw post_generic_abs post_event_raw post_event_abs
         K_G K_E post_S post_C post_P \<and>
       rpc_tasks post_C = [] \<and>
       rpc_live post_C = rpc_live C \<and>
       rpc_current_priority post_C = rpc_current_priority C \<and>
       rpc_priority post_C = rpc_priority C \<and>
       yw =
         (if \<exists>u\<in>set (rpc_tasks C).
                rpc_current_priority C \<le> rpc_priority C u
          then (1 :: int) else y)"
  obtain post_generic_raw post_generic_abs post_event_raw post_event_abs
      post_S post_C post_P yw where
      result: "r = Result (NULL, yw)"
    and final_phase0:
      "CursorGeneralStrongResumePendingManagedPhaseRel
         D s (drain_pending_nodes_abs (map Event (rpc_tasks C)) a)
         managed termination external
         post_generic_raw post_generic_abs post_event_raw post_event_abs
         K_G K_E post_S post_C post_P"
    and tasks_empty: "rpc_tasks post_C = []"
    and live_frame: "rpc_live post_C = rpc_live C"
    and current_frame:
      "rpc_current_priority post_C = rpc_current_priority C"
    and priority_frame: "rpc_priority post_C = rpc_priority C"
    and word:
      "yw =
        (if \<exists>u\<in>set (rpc_tasks C).
               rpc_current_priority C \<le> rpc_priority C u
         then (1 :: int) else y)"
    using old by blast
  have final_phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D s (drain_pending_abs a)
       managed termination external
       post_generic_raw post_generic_abs post_event_raw post_event_abs
       K_G K_E post_S post_C post_P"
    using final_phase0 by (simp only: drain)
  have exact_word:
    "yw =
      (if resume_pending_requires_yield a
       then (1 :: int) else y)"
    using word by (simp only: trigger)
  note tick =
    CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD[
      OF final_phase tasks_empty]
  note control =
    CursorGeneralStrongResumePendingManagedPhaseRel_control_frame[
      OF phase final_phase]
  show
    "\<exists>generic_raw' generic_abs' event_raw' event_abs'
        S' C' P' yw.
       r = Result (NULL, yw) \<and>
       CursorGeneralStrongResumePendingManagedPhaseRel
         D s (drain_pending_abs a)
         managed termination external
         generic_raw' generic_abs' event_raw' event_abs'
         K_G K_E S' C' P' \<and>
       rpc_tasks C' = [] \<and>
       rpc_live C' = rpc_live C \<and>
       rpc_current_priority C' = rpc_current_priority C \<and>
       rpc_priority C' = rpc_priority C \<and>
       yw =
         (if resume_pending_requires_yield a
          then (1 :: int) else y) \<and>
       ring (sa_pending (drain_pending_abs a)) = [] \<and>
       CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D (1 :: 32 word) (1 :: 32 word) s
         (drain_pending_abs a) managed termination external \<and>
       Scheduler_V611_Parse.globals.eal6_port_critical_depth_' s = 1 \<and>
       Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' s = 1 \<and>
       Scheduler_V611_Parse.globals.xSchedulerRunning_' s = 1 \<and>
       resume_pending_control_frame c s"
    apply (rule exI[where x=post_generic_raw])
    apply (rule exI[where x=post_generic_abs])
    apply (rule exI[where x=post_event_raw])
    apply (rule exI[where x=post_event_abs])
    apply (rule exI[where x=post_S])
    apply (rule exI[where x=post_C])
    apply (rule exI[where x=post_P])
    apply (rule exI[where x=yw])
    using result final_phase tasks_empty live_frame current_frame
      priority_frame exact_word tick control
    by blast
  qed
qed

ML \<open>
  val managed_loop_pure =
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_pure}
  val _ =
    if null (Thm.hyps_of managed_loop_pure) then ()
    else error "managed loop pure capstone has hidden hypotheses"
  val _ =
    if length (Thm.prems_of managed_loop_pure) = 1 then ()
    else error "managed loop pure capstone premise ledger changed"
\<close>

end

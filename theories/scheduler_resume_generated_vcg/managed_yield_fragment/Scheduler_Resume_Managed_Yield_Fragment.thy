theory Scheduler_Resume_Managed_Yield_Fragment
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Ready_Insert_Relational.Scheduler_Resume_Managed_Ready_Insert_Relational"
begin

text \<open>
  Exact generated current-task guard and yield comparison at the managed
  ready-inserted cutpoint.  These source operations do not mutate the state;
  the abstract yield-phase transition remains a separate relational rung.
\<close>

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_yield_fragment_exact:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_yield_join D t y \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (if rpc_current_priority C \<le> rpc_priority C t then 1 else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?hR = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?cR)"

  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])

  have tasks_canonical:
    "rpc_tasks C = resume_pending_managed_tasks a"
    using alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have pending_ring:
    "ring (sa_pending a) = map Event (resume_pending_managed_tasks a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD[
        OF gate])
  have pending_nonempty: "ring (sa_pending a) \<noteq> []"
    using pending_ring tasks_canonical tasks by auto
  obtain current where current:
      "sa_current a = Some current"
    and current_live: "current \<in> sa_live a"
    using CursorGeneralStrongResumePendingManagedGateRel_current_liveD[
        OF gate pending_nonempty]
    by blast
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_domainD[
        OF gate])
  have current_managed: "current \<in> managed"
    using domain current_live
    by (auto simp: CursorGeneralStrongManagedDomainRel_def)

  have t_context: "t \<in> rpc_live C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)

  obtain c0 where overlay:
      "c = scheduler_port_overlay
         (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c0 a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have current_rel: "scheduler_current_rel D c0 a"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have current_shadow:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' c0 =
       sd_tcb_ptr D current"
    using current_rel current
    by (simp add: scheduler_current_rel_def)
  have current_entry:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' c =
       sd_tcb_ptr D current"
    using overlay current_shadow
    by (simp add: scheduler_port_overlay_def)
  have current_post:
    "Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cR =
       sd_tcb_ptr D current"
    using current_entry
    by (simp add: resume_pending_ready_inserted_pxCurrentTCB)

  have observation0:
    "scheduler_managed_task_observation_rel D ?hR a managed"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD[
        OF phase tasks])
  have observation:
    "TaskObservationRel D ?hR (managed_scheduler_view a managed)"
    using observation0
    by (simp add: scheduler_managed_task_observation_rel_def)
  have current_view:
    "current \<in> sa_live (managed_scheduler_view a managed)"
    using current_managed by (simp add: managed_scheduler_view_def)
  have t_view:
    "t \<in> sa_live (managed_scheduler_view a managed)"
    using t_managed by (simp add: managed_scheduler_view_def)
  note current_fields = TaskObservationRel_liveD[
    OF observation current_view]
  note head_fields = TaskObservationRel_liveD[OF observation t_view]
  have current_tcb_guard:
    "c_guard (sd_tcb_ptr D current)"
    using current_fields by blast
  have current_guard:
    "c_guard (Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cR)"
    using current_tcb_guard current_post by simp
  have current_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hR
         (Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cR))) =
       rpc_current_priority C"
    using current_fields current_post current alignment
    by (simp add: managed_scheduler_view_def
        resume_pending_managed_current_priority_def
        resume_pending_managed_phase_alignment_def)
  have head_priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hR (sd_tcb_ptr D t))) = rpc_priority C t"
    using head_fields alignment
    by (simp add: managed_scheduler_view_def
        resume_pending_managed_phase_alignment_def)

  let ?current_word =
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hR
         (Scheduler_V611_Parse.globals.pxCurrentTCB_' ?cR))"
  let ?head_word =
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hR (sd_tcb_ptr D t))"
  have compare:
    "(?current_word \<le> ?head_word) =
       (rpc_current_priority C \<le> rpc_priority C t)"
    using current_priority head_priority
    by (simp add: word_le_nat_alt)

  show ?thesis
    unfolding resume_pending_generated_yield_join_def
    apply runs_to_vcg
    using current_guard compare
    by simp_all
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_yield_fragment_exact}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed yield-fragment theorem has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed yield-fragment premise ledger changed"
\<close>

end

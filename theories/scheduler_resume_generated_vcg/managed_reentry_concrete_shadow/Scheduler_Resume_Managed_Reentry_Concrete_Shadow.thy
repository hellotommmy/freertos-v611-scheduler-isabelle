theory Scheduler_Resume_Managed_Reentry_Concrete_Shadow
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Observation.Scheduler_Resume_Managed_Reentry_Observation"
begin

lemma scheduler_port_overlay_current_id [simp]:
  "scheduler_port_overlay
     (Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c)
     (Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c) c = c"
  by (cases c) (simp add: scheduler_port_overlay_def)

lemma CursorGeneralStrongResumePendingManagedGateRel_reentry_concrete_shadowD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "resume_pending_ready_inserted_state D C t generic_raw c =
       scheduler_port_overlay (1 :: 32 word) (1 :: 32 word)
         (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
           (resume_pending_ready_inserted_state D C t generic_raw c)) \<and>
     scheduler_boundary_rel
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c)) \<and>
     scheduler_role_rel generated_scheduler_roots
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) \<and>
     scheduler_current_rel D
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a)"
proof -
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?c0R =
    "scheduler_port_overlay (0 :: 32 word) (0 :: 32 word) ?cR"
  let ?after = "resume_one_pending_abs t a"
  obtain c0 where c:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have role0: "scheduler_role_rel generated_scheduler_roots c0 a"
    and current0: "scheduler_current_rel D c0 a"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have port:
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1 \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 1 \<and>
     Scheduler_V611_Parse.globals.xSchedulerRunning_' c = 1"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_port_runningD[OF gate])
  have control: "resume_pending_control_frame c ?cR"
    by (rule resume_pending_ready_inserted_control_frame)
  have depthR:
      "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' ?cR = 1"
    and irqR:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' ?cR = 1"
    and runningR:
      "Scheduler_V611_Parse.globals.xSchedulerRunning_' ?cR = 1"
    using port control
    by (simp_all add: resume_pending_control_frame_def)
  have selfR:
    "scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) ?cR = ?cR"
    using scheduler_port_overlay_current_id[of ?cR] depthR irqR
    by simp
  have recover:
    "?cR = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) ?c0R"
    using selfR by simp
  have boundary: "scheduler_boundary_rel ?c0R"
    using runningR by (simp add: scheduler_boundary_rel_def)
  note globals = resume_pending_ready_inserted_globals[of D C t generic_raw c]
  note abs = resume_one_pending_abs_components[of t a]
  have role_after:
    "scheduler_role_rel generated_scheduler_roots ?c0R ?after"
    using role0 c globals abs
    by (simp add: scheduler_role_rel_def)
  have current_after: "scheduler_current_rel D ?c0R ?after"
    using current0 c abs
    by (simp add: scheduler_current_rel_def
        resume_pending_ready_inserted_pxCurrentTCB split: option.splits)
  show ?thesis
    using recover boundary role_after current_after by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_scalar_shadowD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "scheduler_managed_scalar_rel
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) managed"
proof -
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?c0R =
    "scheduler_port_overlay (0 :: 32 word) (0 :: 32 word) ?cR"
  let ?after = "resume_one_pending_abs t a"
  let ?PR = "resume_pending_drained_snapshot C t P"
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  obtain c0 where c:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have scalar0: "scheduler_managed_scalar_rel c0 a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  note globals = resume_pending_ready_inserted_globals[of D C t generic_raw c]
  note abs = resume_one_pending_abs_components[of t a]
  have top:
    "unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' ?cR) =
       rps_top ?PR"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_topD[
        OF phase tasks])
  have alignment_after:
    "resume_pending_managed_phase_alignment
       ?after managed external
       (rps_generic_family ?PR) (rps_event_family ?PR)
       K_G K_E (resume_pending_drained_context C t rest) ?PR"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD[
        OF phase tasks])
  have top_after: "rps_top ?PR = sa_top_ready ?after"
    using alignment_after
    by (simp add: resume_pending_managed_phase_alignment_def)
  show ?thesis
    using scalar0 c globals abs top top_after
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def scheduler_port_overlay_def)
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_concrete_shadowD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_ready_inserted_state D C t generic_raw c =
       scheduler_port_overlay (1 :: 32 word) (1 :: 32 word)
         (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
           (resume_pending_ready_inserted_state D C t generic_raw c)) \<and>
     scheduler_boundary_rel
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c)) \<and>
     scheduler_role_rel generated_scheduler_roots
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) \<and>
     scheduler_current_rel D
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) \<and>
     scheduler_managed_scalar_rel
       (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
         (resume_pending_ready_inserted_state D C t generic_raw c))
       (resume_one_pending_abs t a) managed \<and>
     scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
           (resume_pending_ready_inserted_state D C t generic_raw c))))
       (resume_one_pending_abs t a) managed"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  note structural =
    CursorGeneralStrongResumePendingManagedGateRel_reentry_concrete_shadowD[
      OF gate, where C=C and t=t]
  note scalar =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_scalar_shadowD[
      OF phase tasks]
  note observation =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_observationD[
      OF phase tasks]
  have observation0:
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (scheduler_port_overlay (0 :: 32 word) (0 :: 32 word)
           (resume_pending_ready_inserted_state D C t generic_raw c))))
       (resume_one_pending_abs t a) managed"
    using observation by simp
  show ?thesis
    using structural scalar observation0 by blast
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "port overlay current id" 0
    @{thm scheduler_port_overlay_current_id}
  val _ = audit_exact "managed gate reentry concrete structural shadow" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_reentry_concrete_shadowD}
  val _ = audit_exact "managed reentry scalar shadow" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_scalar_shadowD}
  val _ = audit_exact "managed reentry concrete shadow" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_concrete_shadowD}
\<close>

end

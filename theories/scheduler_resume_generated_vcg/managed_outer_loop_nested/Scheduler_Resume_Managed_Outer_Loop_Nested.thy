theory Scheduler_Resume_Managed_Outer_Loop_Nested
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Loop_Unsafe.Scheduler_Resume_Managed_Outer_Loop_Unsafe"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Inner_Source.Scheduler_Resume_Inner_Source"
begin

text \<open>
  The nested resume branch is selected when the positive suspension depth
  remains nonzero after the generated decrement.  It returns before reading
  pending tasks, the current task, missed ticks, or any list root.  The only
  new work here is to lift the existing exact generated-source theorem from
  its control-field relation to the complete cursor-general modular endpoint.
\<close>

lemma scheduler_managed_scalar_rel_resume_outer_entry_positive:
  assumes scalar: "scheduler_managed_scalar_rel c a managed"
    and positive: "0 < sa_suspend_depth a"
  shows
    "scheduler_managed_scalar_rel
       (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed"
proof -
  let ?w = "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  have count: "unat ?w = sa_suspend_depth a"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  have nonzero: "?w \<noteq> 0"
    using count positive by auto
  have predecessor: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF nonzero])
  have reduced:
    "unat (?w - 1) = sa_suspend_depth a - 1"
    using count predecessor positive by arith
  show ?thesis
    using scalar reduced positive
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def
        resume_outer_generated_public_state_def resume_outer_entry_abs_def)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry_positive:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and positive: "0 < sa_suspend_depth a"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have core: "cursor_general_core_wf (resume_outer_entry_abs a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have domain:
    "CursorGeneralStrongManagedDomainRel
       (resume_outer_entry_abs a) termination managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        CursorGeneralStrongManagedDomainRel_def resume_outer_entry_abs_def
        Let_def)
  have generic_role:
    "strong_generic_role_projection
       (resume_outer_entry_abs a) termination generic_abs"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        strong_generic_role_projection_def resume_outer_entry_abs_def Let_def)
  have event_role:
    "strong_event_role_projection
       (resume_outer_entry_abs a) managed external event_abs"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        strong_event_role_projection_def resume_outer_entry_abs_def Let_def)
  have wake:
    "strong_wake_payload_projection (resume_outer_entry_abs a) K_G"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        strong_wake_payload_projection_def resume_outer_entry_abs_def Let_def)
  have observation:
    "scheduler_managed_task_observation_rel D ?h
       (resume_outer_entry_abs a) managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        scheduler_managed_task_observation_rel_def managed_scheduler_view_def
        TaskObservationRel_def resume_outer_entry_abs_def Let_def)
  have one_due:
    "strong_one_due_snapshot_projection
       (resume_outer_entry_abs a) generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def resume_outer_entry_abs_def
        Let_def)
  have role:
    "scheduler_role_rel generated_scheduler_roots
       (resume_outer_generated_public_state c) (resume_outer_entry_abs a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        scheduler_role_rel_def resume_outer_generated_public_state_def
        resume_outer_entry_abs_def Let_def)
  have scalar0: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have scalar:
    "scheduler_managed_scalar_rel
       (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed"
    by (rule scheduler_managed_scalar_rel_resume_outer_entry_positive[
        OF scalar0 positive])
  have current0: "scheduler_current_rel D c a"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have current:
    "scheduler_current_rel D
       (resume_outer_generated_public_state c) (resume_outer_entry_abs a)"
    using current0
    by (cases "sa_current a")
       (simp_all add: scheduler_current_rel_def
          resume_outer_generated_public_state_def resume_outer_entry_abs_def
          Let_def)
  have boundary:
    "scheduler_boundary_rel (resume_outer_generated_public_state c)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        scheduler_boundary_rel_def resume_outer_generated_public_state_def
        Let_def)
  show ?thesis
    using snapshot core domain generic_role event_role wake observation
      one_due role scalar current boundary
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        resume_outer_generated_public_state_def Let_def)
qed

lemma CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
  shows
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
proof -
  have exact:
    "CursorGeneralStrongSchedulerEndpointRel
       D c (normalize_yield_count_abs a) managed termination external"
    using endpoint
    by (simp add: CursorGeneralStrongSchedulerModularEndpointRel_def)
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c (normalize_yield_count_abs a) managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using exact
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  have scalar:
    "scheduler_managed_scalar_rel c (normalize_yield_count_abs a) managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def normalize_yield_count_abs_def)
qed

lemma CursorGeneralStrongSchedulerModularEndpointRel_boundaryD:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
  shows "scheduler_boundary_rel c"
proof -
  have exact:
    "CursorGeneralStrongSchedulerEndpointRel
       D c (normalize_yield_count_abs a) managed termination external"
    using endpoint
    by (simp add: CursorGeneralStrongSchedulerModularEndpointRel_def)
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c (normalize_yield_count_abs a) managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using exact
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  show ?thesis
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
qed

lemma CursorGeneralStrongSchedulerModularEndpointRel_resume_outer_entry_positive:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and positive: "0 < sa_suspend_depth a"
  shows
    "CursorGeneralStrongSchedulerModularEndpointRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external"
proof -
  have exact:
    "CursorGeneralStrongSchedulerEndpointRel
       D c (normalize_yield_count_abs a) managed termination external"
    and counter:
      "yield_count_mod_rel
        (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
        (sa_yield_count a)"
    using endpoint
    by (simp_all add: CursorGeneralStrongSchedulerModularEndpointRel_def)
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel
         D c (normalize_yield_count_abs a) managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using exact
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  have normalized_positive:
    "0 < sa_suspend_depth (normalize_yield_count_abs a)"
    using positive by (simp add: normalize_yield_count_abs_def)
  have snapshot_after:
    "CursorGeneralStrongSchedulerSnapshotRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs (normalize_yield_count_abs a))
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry_positive[
        OF snapshot normalized_positive])
  have exact_after:
    "CursorGeneralStrongSchedulerEndpointRel
       D (resume_outer_generated_public_state c)
       (normalize_yield_count_abs (resume_outer_entry_abs a))
       managed termination external"
    unfolding CursorGeneralStrongSchedulerEndpointRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    using snapshot_after
    by (simp only: normalize_yield_count_abs_resume_outer_entry)
  have counter_after:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_'
         (resume_outer_generated_public_state c))
       (sa_yield_count (resume_outer_entry_abs a))"
    using counter
    by (simp add: resume_outer_generated_public_state_def
        resume_outer_entry_abs_def)
  show ?thesis
    using exact_after counter_after
    by (simp add: CursorGeneralStrongSchedulerModularEndpointRel_def)
qed

theorem CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_nested:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and nested: "1 < sa_suspend_depth a"
  shows
    "Scheduler_V611_Delay_Translation.xTaskResumeAll' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result 0 \<and>
       t = resume_outer_generated_public_state c \<and>
       ResumeRel a False (resume_outer_entry_abs a) \<and>
       CursorGeneralStrongSchedulerModularEndpointRel
         D t (resume_outer_entry_abs a)
         managed termination external\<rbrace>"
proof -
  let ?w = "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  have count: "unat ?w = sa_suspend_depth a"
    by (rule CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD[
        OF endpoint])
  have nonzero: "?w \<noteq> 0"
    using count nested by auto
  have predecessor: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF nonzero])
  have branch: "?w - 1 \<noteq> 0"
    using count predecessor nested by auto
  have boundary: "scheduler_boundary_rel c"
    by (rule CursorGeneralStrongSchedulerModularEndpointRel_boundaryD[
        OF endpoint])
  have depth:
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 0"
    and interrupts:
      "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 0"
    using boundary
    by (simp_all add: scheduler_boundary_rel_def)
  note source = scheduler_xTaskResumeAll_inner_exact[
      OF branch depth interrupts]
  have resume: "ResumeRel a False (resume_outer_entry_abs a)"
    using ResumeRel_inner_constructor[OF nested]
    by (simp add: resume_inner_abs_def resume_outer_entry_abs_def)
  have endpoint_after:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external"
    by (rule
      CursorGeneralStrongSchedulerModularEndpointRel_resume_outer_entry_positive[
        OF endpoint])
       (use nested in auto)
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    using resume endpoint_after
    by (simp add: scheduler_resume_inner_state_def
        resume_outer_generated_public_state_def)
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
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "nested managed scalar transport" 2
    @{thm scheduler_managed_scalar_rel_resume_outer_entry_positive}
  val _ = audit_exact "nested exact snapshot transport" 2
    @{thm CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry_positive}
  val _ = audit_exact "modular suspension-depth projection" 1
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_suspend_depthD}
  val _ = audit_exact "modular boundary projection" 1
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_boundaryD}
  val _ = audit_exact "nested modular endpoint transport" 2
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_resume_outer_entry_positive}
  val _ = audit_exact "actual generated nested resume" 2
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_nested}
\<close>

end

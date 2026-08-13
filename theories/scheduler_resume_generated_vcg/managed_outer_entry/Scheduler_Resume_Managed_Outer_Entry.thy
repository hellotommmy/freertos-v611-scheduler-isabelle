theory Scheduler_Resume_Managed_Outer_Entry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_After_Drain_Continuation.Scheduler_Resume_Managed_After_Drain_Continuation"
begin

definition resume_outer_generated_entry_prefix ::
  "(unit, Scheduler_V611_Parse.globals) res_monad"
where
  "resume_outer_generated_entry_prefix = do {
     ret \<leftarrow>
       Scheduler_V611_Tick_Translation.eal6_port_enter_critical';
     modify
       (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
         (\<lambda>w. w - 1))
   }"

definition resume_outer_generated_public_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "resume_outer_generated_public_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>w. w - 1) c"

definition resume_outer_generated_gate_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "resume_outer_generated_gate_state c =
     Scheduler_V611_Parse.globals.uxSchedulerSuspended_'_update
       (\<lambda>w. w - 1)
       (scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c)"

lemma normalize_yield_count_abs_resume_outer_entry [simp]:
  "normalize_yield_count_abs (resume_outer_entry_abs a) =
   resume_outer_entry_abs (normalize_yield_count_abs a)"
  by (cases a)
     (simp add: normalize_yield_count_abs_def resume_outer_entry_abs_def)

lemma resume_outer_generated_gate_state_shadow:
  "resume_outer_generated_gate_state c =
   scheduler_port_overlay (1 :: 32 word) (1 :: 32 word)
     (resume_outer_generated_public_state c)"
  by (simp add: resume_outer_generated_gate_state_def
      resume_outer_generated_public_state_def scheduler_port_overlay_def)

lemma canonicalize_scheduler_cursors_resume_outer_entry [simp]:
  "canonicalize_scheduler_cursors (resume_outer_entry_abs a) =
   resume_outer_entry_abs (canonicalize_scheduler_cursors a)"
  by (cases a)
     (simp add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def resume_outer_entry_abs_def)

lemma core_wf_resume_outer_entry [simp]:
  "core_wf (resume_outer_entry_abs a) = core_wf a"
proof -
  let ?a' = "resume_outer_entry_abs a"
  have live_frame: "sa_live ?a' = sa_live a"
    by (simp add: resume_outer_entry_abs_def)
  have priority_frame: "sa_priority ?a' = sa_priority a"
    by (simp add: resume_outer_entry_abs_def)
  have ring_shape_frame: "ring_shape_wf ?a' = ring_shape_wf a"
    by (simp add: ring_shape_wf_def resume_outer_entry_abs_def)
  have role_frame: "role_wf ?a' = role_wf a"
    by (simp add: role_wf_def resume_outer_entry_abs_def)
  have membership_frame: "membership_wf ?a' = membership_wf a"
    by (simp add: membership_wf_def ready_task_set_def
        resume_outer_entry_abs_def Let_def)
  have tick_frame: "sa_tick ?a' = sa_tick a"
    by (simp add: resume_outer_entry_abs_def)
  have time_frame: "time_wf ?a' = time_wf a"
    unfolding time_wf_def ready_task_set_def current_delayed_ring_def
      overflow_delayed_ring_def delayed_key_agrees_def
    apply (simp only: tick_frame)
    by (simp add: resume_outer_entry_abs_def)
  have ready_cache_frame: "ready_cache_wf ?a' = ready_cache_wf a"
    by (simp add: ready_cache_wf_def resume_outer_entry_abs_def)
  have current_frame: "current_wf ?a' = current_wf a"
    unfolding current_wf_def
    apply (simp only: live_frame)
    by (simp add: resume_outer_entry_abs_def)
  show ?thesis
    using live_frame priority_frame ring_shape_frame role_frame membership_frame
      time_frame ready_cache_frame current_frame
    by (simp add: core_wf_def)
qed

lemma cursor_general_core_wf_resume_outer_entry [simp]:
  "cursor_general_core_wf (resume_outer_entry_abs a) =
   cursor_general_core_wf a"
  unfolding cursor_general_core_wf_def
  apply (simp only: canonicalize_scheduler_cursors_resume_outer_entry
      core_wf_resume_outer_entry)
  by (simp add: ring_shape_wf_def resume_outer_entry_abs_def)

lemma scheduler_managed_scalar_rel_resume_outer_entry:
  assumes scalar: "scheduler_managed_scalar_rel c a managed"
    and outermost: "sa_suspend_depth a = 1"
  shows
    "scheduler_managed_scalar_rel
       (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed"
proof -
  let ?w = "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  have count: "unat ?w = 1"
    using scalar outermost
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  have nonzero: "?w \<noteq> 0"
    using count by auto
  have predecessor: "Suc (unat (?w - 1)) = unat ?w"
    by (rule Suc_unat_minus_one[OF nonzero])
  have reduced: "unat (?w - 1) = 0"
    using count predecessor by arith
  show ?thesis
    using scalar reduced outermost
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def
        resume_outer_generated_public_state_def resume_outer_entry_abs_def)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and outermost: "sa_suspend_depth a = 1"
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
    by (rule scheduler_managed_scalar_rel_resume_outer_entry[
        OF scalar0 outermost])
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

lemma CursorGeneralStrongSchedulerSnapshotRel_managed_count_positive:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c"
proof -
  have canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        cursor_general_core_wf_def Let_def)
  have shadow_live: "sa_live (canonicalize_scheduler_cursors a) \<noteq> {}"
    by (rule tick_entry_core_wf_live_nonempty[OF canonical_core])
  have live: "sa_live a \<noteq> {}"
    using shadow_live by simp
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    and scalar: "scheduler_managed_scalar_rel c a managed"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have finite: "finite managed"
    and subset: "sa_live a \<subseteq> managed"
    using domain
    by (simp_all add: CursorGeneralStrongManagedDomainRel_def)
  have managed_nonempty: "managed \<noteq> {}"
    using live subset by blast
  have card_nonzero: "card managed \<noteq> 0"
    using finite managed_nonempty by auto
  have count:
    "unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card managed"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  have word_nonzero:
    "Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c \<noteq> 0"
    using count card_nonzero by (metis unat_eq_zero)
  show ?thesis using word_nonzero by (simp add: word_gt_0)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_pending_guard:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have coverage:
    "EventRootFamilyCoverage external D ?h event_raw event_abs managed K_E"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have raw:
    "raw_xlist_rel ?h GeneratedPendingEventRoot
       (event_raw GeneratedPendingEventRoot)"
    by (rule scheduler_event_root_family_raw_rootD[
        OF EventRootFamilyCoverage_relD[OF coverage]
           EventRootUniverse_pendingI])
  have raw_guard: "c_guard GeneratedPendingEventRoot"
    using raw by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
  have abi_guard:
    "c_guard (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')"
    using raw_guard by (simp add: GeneratedPendingEventRoot_def)
  show ?thesis using abi_guard by (simp only: abi_list_ptr_c_guard)
qed

lemma CursorGeneralStrongSchedulerSnapshotRel_outer_entry_phase:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and outermost: "sa_suspend_depth a = 1"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
  shows
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D (resume_outer_generated_gate_state c)
       (resume_outer_entry_abs a) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       (resume_pending_canonical_managed_context
         (resume_outer_entry_abs a) managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  have public:
    "CursorGeneralStrongSchedulerSnapshotRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs a) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry[
        OF snapshot outermost])
  have protected:
    "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D (1 :: 32 word) (1 :: 32 word)
       (resume_outer_generated_gate_state c)
       (resume_outer_entry_abs a) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    apply (rule CursorGeneralStrongProtectedSchedulerSnapshotRelI[
        OF resume_outer_generated_gate_state_shadow public])
    done
  have quiet: "sa_suspend_depth (resume_outer_entry_abs a) = 0"
    using outermost by (simp add: resume_outer_entry_abs_def)
  have safe_after:
    "ring (sa_pending (resume_outer_entry_abs a)) \<noteq> [] \<longrightarrow>
     sa_current (resume_outer_entry_abs a) \<noteq> None"
    using current_safe by (simp add: resume_outer_entry_abs_def)
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D (resume_outer_generated_gate_state c)
       (resume_outer_entry_abs a) managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedGateRelI[
        OF protected quiet safe_after])
  show ?thesis
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_phaseD[OF gate])
qed

theorem resume_outer_generated_entry_prefix_exact:
  assumes boundary: "scheduler_boundary_rel c"
  shows
    "resume_outer_generated_entry_prefix \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = resume_outer_generated_gate_state c\<rbrace>"
  unfolding resume_outer_generated_entry_prefix_def
    resume_outer_generated_gate_state_def scheduler_port_overlay_def
    Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
  apply runs_to_vcg
  using boundary
  by (simp_all add: scheduler_boundary_rel_def)

theorem
  CursorGeneralStrongSchedulerModularEndpointRel_generated_outer_entry_phase:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and outermost: "sa_suspend_depth a = 1"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
  shows
    "let entry = resume_outer_entry_abs a;
         normalized_entry = normalize_yield_count_abs entry
     in resume_outer_generated_entry_prefix \<bullet> c
        \<lbrace>\<lambda>r t.
          r = Result () \<and>
          t = resume_outer_generated_gate_state c \<and>
          Scheduler_V611_Parse.globals.uxSchedulerSuspended_' t = 0 \<and>
          0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' t \<and>
          c_guard Scheduler_V611_Parse.xPendingReadyList_' \<and>
          yield_count_mod_rel
            (Scheduler_V611_Parse.globals.eal6_port_yield_count_' t)
            (sa_yield_count entry) \<and>
          (\<exists>generic_raw generic_abs event_raw event_abs K_G K_E S.
            CursorGeneralStrongResumePendingManagedPhaseRel
              D t normalized_entry managed termination external
              generic_raw generic_abs event_raw event_abs K_G K_E S
              (resume_pending_canonical_managed_context
                normalized_entry managed external K_G K_E)
              (resume_pending_snapshot_of_one_due S))\<rbrace>"
proof -
  let ?normalized = "normalize_yield_count_abs a"
  let ?entry = "resume_outer_entry_abs a"
  let ?normalized_entry = "normalize_yield_count_abs ?entry"
  have endpoint0:
    "CursorGeneralStrongSchedulerEndpointRel
       D c ?normalized managed termination external"
    and counter:
      "yield_count_mod_rel
        (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
        (sa_yield_count a)"
    using endpoint
    by (simp_all add: CursorGeneralStrongSchedulerModularEndpointRel_def)
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
      snapshot:
        "CursorGeneralStrongSchedulerSnapshotRel
           D c ?normalized managed termination external
           generic_raw generic_abs event_raw event_abs K_G K_E S"
    using endpoint0
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  have normalized_outermost: "sa_suspend_depth ?normalized = 1"
    using outermost by (simp add: normalize_yield_count_abs_def)
  have normalized_safe:
    "ring (sa_pending ?normalized) \<noteq> [] \<longrightarrow>
     sa_current ?normalized \<noteq> None"
    using current_safe by (simp add: normalize_yield_count_abs_def)
  have phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D (resume_outer_generated_gate_state c)
       (resume_outer_entry_abs ?normalized)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       (resume_pending_canonical_managed_context
         (resume_outer_entry_abs ?normalized)
         managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_outer_entry_phase[
        OF snapshot normalized_outermost normalized_safe])
  have boundary: "scheduler_boundary_rel c"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  note source = resume_outer_generated_entry_prefix_exact[OF boundary]
  have public_after:
    "CursorGeneralStrongSchedulerSnapshotRel
       D (resume_outer_generated_public_state c)
       (resume_outer_entry_abs ?normalized)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry[
        OF snapshot normalized_outermost])
  have count:
    "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_'
       (resume_outer_generated_gate_state c)"
    using CursorGeneralStrongSchedulerSnapshotRel_managed_count_positive[
      OF public_after]
    by (simp add: resume_outer_generated_gate_state_shadow
        scheduler_port_overlay_def)
  have guard: "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_pending_guard[
        OF public_after])
  have suspended:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
       (resume_outer_generated_gate_state c) = 0"
  proof -
    have scalar:
      "scheduler_managed_scalar_rel
        (resume_outer_generated_public_state c)
        (resume_outer_entry_abs ?normalized) managed"
      using public_after
      by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
    have zero:
      "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
        (resume_outer_generated_public_state c)) = 0"
      using scalar normalized_outermost
      by (simp add: scheduler_managed_scalar_rel_def
          managed_scheduler_view_def scheduler_scalar_rel_def
          resume_outer_entry_abs_def)
    show ?thesis
      using zero by (simp add: resume_outer_generated_gate_state_shadow
          unat_eq_zero)
  qed
  have modular_after:
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_'
         (resume_outer_generated_gate_state c))
       (sa_yield_count ?entry)"
    using counter
    by (simp add: resume_outer_generated_gate_state_def
        resume_outer_entry_abs_def)
  have phase_target:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D (resume_outer_generated_gate_state c) ?normalized_entry
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       (resume_pending_canonical_managed_context
         ?normalized_entry managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    using phase
    by (simp only: normalize_yield_count_abs_resume_outer_entry)
  show ?thesis
    unfolding Let_def
    apply (rule runs_to_weaken[OF source])
    using phase_target count guard suspended modular_after
    by blast
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

  val _ = audit_exact "outer yield normalization commute" 0
    @{thm normalize_yield_count_abs_resume_outer_entry}
  val _ = audit_exact "outer generated gate shadow" 0
    @{thm resume_outer_generated_gate_state_shadow}
  val _ = audit_exact "outer canonical cursor commute" 0
    @{thm canonicalize_scheduler_cursors_resume_outer_entry}
  val _ = audit_exact "outer core frame" 0
    @{thm core_wf_resume_outer_entry}
  val _ = audit_exact "outer cursor-general core frame" 0
    @{thm cursor_general_core_wf_resume_outer_entry}
  val _ = audit_exact "outer managed scalar frame" 2
    @{thm scheduler_managed_scalar_rel_resume_outer_entry}
  val _ = audit_exact "outer exact snapshot frame" 2
    @{thm CursorGeneralStrongSchedulerSnapshotRel_resume_outer_entry}
  val _ = audit_exact "outer managed count positive" 1
    @{thm CursorGeneralStrongSchedulerSnapshotRel_managed_count_positive}
  val _ = audit_exact "outer pending root guard" 1
    @{thm CursorGeneralStrongSchedulerSnapshotRel_pending_guard}
  val _ = audit_exact "outer exact managed phase" 3
    @{thm CursorGeneralStrongSchedulerSnapshotRel_outer_entry_phase}
  val _ = audit_exact "outer generated entry source" 1
    @{thm resume_outer_generated_entry_prefix_exact}
  val _ = audit_exact "outer modular managed phase" 3
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_generated_outer_entry_phase}
\<close>

end

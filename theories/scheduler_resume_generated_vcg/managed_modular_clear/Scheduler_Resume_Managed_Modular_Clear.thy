theory Scheduler_Resume_Managed_Modular_Clear
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Modular_Endpoint.Scheduler_Resume_Managed_Modular_Endpoint"
begin

definition resume_clear_missed_yield_state ::
  "Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "resume_clear_missed_yield_state c =
     Scheduler_V611_Parse.globals.xMissedYield_'_update (\<lambda>_. 0) c"

lemma normalize_yield_count_abs_missed_yield_update [simp]:
  "normalize_yield_count_abs (a\<lparr>sa_missed_yield := b\<rparr>) =
   (normalize_yield_count_abs a)\<lparr>sa_missed_yield := b\<rparr>"
  by (cases a) (simp add: normalize_yield_count_abs_def)

lemma resume_clear_missed_yield_state_yield_count [simp]:
  "Scheduler_V611_Parse.globals.eal6_port_yield_count_'
      (resume_clear_missed_yield_state c) =
   Scheduler_V611_Parse.globals.eal6_port_yield_count_' c"
  by (simp add: resume_clear_missed_yield_state_def)

lemma resume_clear_missed_yield_state_port_overlay [simp]:
  "resume_clear_missed_yield_state
      (scheduler_port_overlay depth irq_mask c) =
   scheduler_port_overlay depth irq_mask
      (resume_clear_missed_yield_state c)"
  by (simp add: resume_clear_missed_yield_state_def
      scheduler_port_overlay_def)

lemma core_wf_missed_yield_update [simp]:
  "core_wf (a\<lparr>sa_missed_yield := b\<rparr>) = core_wf a"
  by (simp add: core_wf_def ring_shape_wf_def role_wf_def
      membership_wf_def time_wf_def ready_cache_wf_def current_wf_def
      delayed_key_agrees_def ready_task_set_def current_delayed_ring_def
      overflow_delayed_ring_def Let_def split: option.splits)

lemma canonicalize_scheduler_cursors_missed_yield_update [simp]:
  "canonicalize_scheduler_cursors (a\<lparr>sa_missed_yield := b\<rparr>) =
   (canonicalize_scheduler_cursors a)\<lparr>sa_missed_yield := b\<rparr>"
  by (cases a)
     (simp add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def)

lemma cursor_general_core_wf_missed_yield_update [simp]:
  "cursor_general_core_wf (a\<lparr>sa_missed_yield := b\<rparr>) =
   cursor_general_core_wf a"
  by (simp add: cursor_general_core_wf_def ring_shape_wf_def)

lemma scheduler_current_rel_clear_missed_yield [simp]:
  "scheduler_current_rel D (resume_clear_missed_yield_state c)
      (a\<lparr>sa_missed_yield := False\<rparr>) =
   scheduler_current_rel D c a"
  by (simp add: resume_clear_missed_yield_state_def
      scheduler_current_rel_def split: option.splits)

lemma CursorGeneralStrongSchedulerSnapshotRel_clear_missed_yieldI:
  assumes snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongSchedulerSnapshotRel D
       (resume_clear_missed_yield_state c)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using snapshot
  unfolding CursorGeneralStrongSchedulerSnapshotRel_def Let_def
  apply (simp only: scheduler_current_rel_clear_missed_yield)
  by (simp add:
      resume_clear_missed_yield_state_def
      CursorGeneralStrongManagedDomainRel_def
      strong_generic_role_projection_def strong_event_role_projection_def
      strong_wake_payload_projection_def strong_one_due_snapshot_projection_def
      scheduler_role_rel_def scheduler_managed_scalar_rel_def
      managed_scheduler_view_def scheduler_scalar_rel_def
      scheduler_boundary_rel_def
      TaskObservationRel_def scheduler_managed_task_observation_rel_def)

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_clear_missed_yieldI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (resume_clear_missed_yield_state c)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external"
proof -
  obtain c0 where overlay:
      "c = scheduler_port_overlay depth irq_mask c0"
    and public:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
    full:
      "CursorGeneralStrongVTaskIncrementTickEntryRel
         D c0 a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF public] .
  have snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "tick_entry_pending_wf a"
    using full
    by (simp_all add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have snapshot':
    "CursorGeneralStrongSchedulerSnapshotRel D
       (resume_clear_missed_yield_state c0)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongSchedulerSnapshotRel_clear_missed_yieldI[
          OF snapshot])
  have pending':
    "tick_entry_pending_wf (a\<lparr>sa_missed_yield := False\<rparr>)"
    using pending by (simp add: tick_entry_pending_wf_def)
  have full':
    "CursorGeneralStrongVTaskIncrementTickEntryRel D
       (resume_clear_missed_yield_state c0)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using snapshot' pending'
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have public':
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D
       (resume_clear_missed_yield_state c0)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external"
    unfolding CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    by (rule full')
  show ?thesis
    unfolding CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def
    apply (rule exI[where x="resume_clear_missed_yield_state c0"])
    using overlay public' by simp
qed

lemma CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_clear_missed_yieldI:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask (resume_clear_missed_yield_state c)
       (a\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external"
proof -
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask c (normalize_yield_count_abs a)
       managed termination external"
    and counter:
      "yield_count_mod_rel
         (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c)
         (sa_yield_count a)"
    using entry
    by (simp_all add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
  have protected':
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (resume_clear_missed_yield_state c)
       ((normalize_yield_count_abs a)\<lparr>sa_missed_yield := False\<rparr>)
       managed termination external"
    by (rule
      CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_clear_missed_yieldI[
        OF protected])
  have normalized:
    "normalize_yield_count_abs
       (a\<lparr>sa_missed_yield := False\<rparr>) =
     (normalize_yield_count_abs a)\<lparr>sa_missed_yield := False\<rparr>"
    by simp
  have protected_normalized:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth irq_mask (resume_clear_missed_yield_state c)
       (normalize_yield_count_abs
         (a\<lparr>sa_missed_yield := False\<rparr>))
       managed termination external"
    using protected' normalized by simp
  have counter':
    "yield_count_mod_rel
       (Scheduler_V611_Parse.globals.eal6_port_yield_count_'
         (resume_clear_missed_yield_state c))
       (sa_yield_count (a\<lparr>sa_missed_yield := False\<rparr>))"
    using counter by simp
  show ?thesis
    using protected_normalized counter'
    by (simp add:
        CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_def)
qed

theorem CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_clear_missed_yield:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
       D depth irq_mask c a managed termination external"
  shows
    "modify (Scheduler_V611_Parse.globals.xMissedYield_'_update (\<lambda>_. 0))
       \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = resume_clear_missed_yield_state c \<and>
       CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel
         D depth irq_mask t
         (a\<lparr>sa_missed_yield := False\<rparr>)
         managed termination external\<rbrace>"
proof -
  note preserved =
    CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_clear_missed_yieldI[
      OF entry]
  show ?thesis
  apply runs_to_vcg
   apply (simp add: resume_clear_missed_yield_state_def)
  by (rule preserved[unfolded resume_clear_missed_yield_state_def])
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ = if null (Thm.hyps_of th) then ()
              else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ = if actual = expected then ()
              else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "normalization frames missed-yield update" 0
    @{thm normalize_yield_count_abs_missed_yield_update}
  val _ = audit_exact "missed-yield clear frames yield count" 0
    @{thm resume_clear_missed_yield_state_yield_count}
  val _ = audit_exact "missed-yield clear commutes with port overlay" 0
    @{thm resume_clear_missed_yield_state_port_overlay}
  val _ = audit_exact "core wf frames missed-yield update" 0
    @{thm core_wf_missed_yield_update}
  val _ = audit_exact "cursor canonicalization frames missed-yield update" 0
    @{thm canonicalize_scheduler_cursors_missed_yield_update}
  val _ = audit_exact "cursor-general core frames missed-yield update" 0
    @{thm cursor_general_core_wf_missed_yield_update}
  val _ = audit_exact "current relation frames missed-yield clear" 0
    @{thm scheduler_current_rel_clear_missed_yield}
  val _ = audit_exact "snapshot missed-yield clear" 1
    @{thm CursorGeneralStrongSchedulerSnapshotRel_clear_missed_yieldI}
  val _ = audit_exact "protected entry missed-yield clear" 1
    @{thm CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_clear_missed_yieldI}
  val _ = audit_exact "modular protected entry missed-yield clear" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_clear_missed_yieldI}
  val _ = audit_exact "generated missed-yield clear" 1
    @{thm CursorGeneralStrongVTaskIncrementTickModularProtectedEntryRel_generated_clear_missed_yield}
\<close>

end

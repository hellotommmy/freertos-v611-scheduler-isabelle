theory Scheduler_Resume_Managed_Reentry_Event_Role
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Generic_Role.Scheduler_Resume_Managed_Reentry_Generic_Role"
begin

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_event_roleD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "strong_event_role_projection
       (resume_one_pending_abs t a) managed external
       (rps_event_family (resume_pending_drained_snapshot C t P))"
proof -
  let ?after = "resume_one_pending_abs t a"
  let ?PR = "resume_pending_drained_snapshot C t P"

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
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast

  have core: "cursor_general_core_wf a"
    and event_coverage:
      "EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0))
         event_raw event_abs managed K_E"
    and role0:
      "strong_event_role_projection a managed external event_abs"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)

  have event_family_eq: "rps_event_family P = event_abs"
    and pending_eq:
      "rpc_pending_root C = GeneratedPendingEventRoot"
    using alignment
    by (simp_all add: resume_pending_managed_phase_alignment_def)
  have role:
    "strong_event_role_projection
       a managed external (rps_event_family P)"
    using role0 event_family_eq by simp

  have external_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
  have pending_not_external:
    "GeneratedPendingEventRoot \<notin> external"
    using external_wf
    by (simp add: EventExternalRootInputWF_def)

  have pending_before:
    "rps_event_family P GeneratedPendingEventRoot = sa_pending a"
    using role
    by (simp add: strong_event_role_projection_def)
  have pending_ring:
    "ring (rps_event_family P GeneratedPendingEventRoot) =
       Event t # map Event rest"
    using pure tasks pending_eq
    by (simp add: resume_pending_entry_rel_def)
  have t_pending: "t \<in> event_task_set (sa_pending a)"
    using pending_ring pending_before
    by (simp add: event_task_set_def)

  have canonical_core:
    "core_wf (canonicalize_scheduler_cursors a)"
    using core
    by (simp add: cursor_general_core_wf_def)
  have canonical_pending_wait_disjoint:
    "event_task_set
       (sa_pending (canonicalize_scheduler_cursors a)) \<inter>
       sa_event_waiting (canonicalize_scheduler_cursors a) = {}"
    using canonical_core
    by (simp add: core_wf_def membership_wf_def Let_def)
  have pending_wait_disjoint:
    "event_task_set (sa_pending a) \<inter> sa_event_waiting a = {}"
    using canonical_pending_wait_disjoint
    by (simp add: event_task_set_def)
  have t_not_waiting: "t \<notin> sa_event_waiting a"
    using t_pending pending_wait_disjoint by blast

  have live_after: "sa_live ?after = sa_live a"
    and waiting_remove:
      "sa_event_waiting ?after = sa_event_waiting a - {t}"
    and pending_after_abs:
      "sa_pending ?after =
         list_remove_abs (Event t) (sa_pending a)"
    using resume_one_pending_abs_components[of t a]
    by simp_all
  have waiting_after:
    "sa_event_waiting ?after = sa_event_waiting a"
    using waiting_remove t_not_waiting by auto

  have pending_after_family:
    "rps_event_family ?PR GeneratedPendingEventRoot =
       list_remove_abs (Event t)
         (rps_event_family P GeneratedPendingEventRoot)"
    using resume_pending_drained_event_at[
        of C t P GeneratedPendingEventRoot]
      pending_eq
    by simp
  have pending_match:
    "rps_event_family ?PR GeneratedPendingEventRoot =
       sa_pending ?after"
    using pending_after_family pending_before pending_after_abs
    by simp

  have external_frame:
    "\<And>lp. lp \<in> external \<Longrightarrow>
       rps_event_family ?PR lp = rps_event_family P lp"
  proof -
    fix lp
    assume lp_external: "lp \<in> external"
    have lp_ne: "lp \<noteq> rpc_pending_root C"
      using lp_external pending_not_external pending_eq by auto
    show "rps_event_family ?PR lp = rps_event_family P lp"
      using resume_pending_drained_event_at[of C t P lp] lp_ne
      by simp
  qed

  have external_before:
    "{u. \<exists>lp\<in>external.
       Event u \<in> set (ring (rps_event_family P lp))} =
       sa_event_waiting a"
    using role
    by (simp add: strong_event_role_projection_def)
  have external_unchanged:
    "{u. \<exists>lp\<in>external.
       Event u \<in> set (ring (rps_event_family ?PR lp))} =
     {u. \<exists>lp\<in>external.
       Event u \<in> set (ring (rps_event_family P lp))}"
  proof (rule set_eqI)
    fix u
    show
      "u \<in> {u. \<exists>lp\<in>external.
          Event u \<in> set (ring (rps_event_family ?PR lp))} \<longleftrightarrow>
       u \<in> {u. \<exists>lp\<in>external.
          Event u \<in> set (ring (rps_event_family P lp))}"
      using external_frame by auto
  qed
  have external_match:
    "{u. \<exists>lp\<in>external.
       Event u \<in> set (ring (rps_event_family ?PR lp))} =
       sa_event_waiting ?after"
    using external_unchanged external_before waiting_after
    by simp

  have post_subset:
    "\<And>lp.
       set (ring (rps_event_family ?PR lp)) \<subseteq>
         set (ring (rps_event_family P lp))"
  proof -
    fix lp
    show
      "set (ring (rps_event_family ?PR lp)) \<subseteq>
         set (ring (rps_event_family P lp))"
      using resume_pending_drained_event_at[of C t P lp]
        set_remove1_subset[
          of "Event t" "ring (rps_event_family P lp)"]
      by (auto simp: list_remove_abs_def)
  qed

  have retired:
    "\<forall>u\<in>managed - sa_live ?after.
       \<forall>lp\<in>EventRootUniverse external.
         Event u \<notin> set (ring (rps_event_family ?PR lp))"
  proof (intro ballI)
    fix u lp
    assume u_retired: "u \<in> managed - sa_live ?after"
      and lp_root: "lp \<in> EventRootUniverse external"
    have old_retired: "u \<in> managed - sa_live a"
      using u_retired live_after by simp
    have old_absent:
      "Event u \<notin> set (ring (rps_event_family P lp))"
      using role old_retired lp_root
      by (simp add: strong_event_role_projection_def)
    show
      "Event u \<notin> set (ring (rps_event_family ?PR lp))"
      using post_subset[of lp] old_absent by blast
  qed

  show ?thesis
    unfolding strong_event_role_projection_def
    using pending_match external_match retired
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
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "managed reentry Event role" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_event_roleD}
\<close>

end

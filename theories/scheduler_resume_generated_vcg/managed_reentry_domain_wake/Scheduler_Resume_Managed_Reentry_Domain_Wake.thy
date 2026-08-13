theory Scheduler_Resume_Managed_Reentry_Domain_Wake
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Alignment.Scheduler_Resume_Managed_Reentry_Alignment"
begin

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domainD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "CursorGeneralStrongManagedDomainRel
       (resume_one_pending_abs t a) termination managed"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  have domain:
    "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_domainD[
        OF gate])
  have live: "sa_live (resume_one_pending_abs t a) = sa_live a"
    using resume_one_pending_abs_components[of t a] by simp
  show ?thesis
    using domain live
    by (simp add: CursorGeneralStrongManagedDomainRel_def)
qed

lemma cursor_general_strong_wake_payload_projection_resume_one_pending_abs:
  assumes core: "cursor_general_core_wf a"
    and wake: "strong_wake_payload_projection a K_G"
  shows
    "strong_wake_payload_projection (resume_one_pending_abs t a) K_G"
proof -
  have shape: "ring_shape_wf a"
    by (rule cursor_general_core_wf_ring_shapeD[OF core])
  have da_distinct: "distinct (ring (sa_delayed_a a))"
    and db_distinct: "distinct (ring (sa_delayed_b a))"
    using shape by (simp_all add: ring_shape_wf_def xlist_wf_def)
  have live: "sa_live (resume_one_pending_abs t a) = sa_live a"
    and wake_after:
      "sa_wake (resume_one_pending_abs t a) = (sa_wake a)(t := None)"
    by (simp_all add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have da_after:
    "generic_task_set (sa_delayed_a (resume_one_pending_abs t a)) =
       generic_task_set (sa_delayed_a a) - {t}"
    using generic_task_set_remove[where t=t, OF da_distinct]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have db_after:
    "generic_task_set (sa_delayed_b (resume_one_pending_abs t a)) =
       generic_task_set (sa_delayed_b a) - {t}"
    using generic_task_set_remove[where t=t, OF db_distinct]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  show ?thesis
    unfolding strong_wake_payload_projection_def
  proof (intro ballI)
    fix u
    assume post_live: "u \<in> sa_live (resume_one_pending_abs t a)"
    have old_live: "u \<in> sa_live a"
      using post_live live by simp
    have old:
      "sa_wake a u =
       (if u \<in> generic_task_set (sa_delayed_a a) \<union>
                   generic_task_set (sa_delayed_b a)
        then Some (K_G u) else None)"
      using wake old_live
      by (simp add: strong_wake_payload_projection_def)
    show
      "sa_wake (resume_one_pending_abs t a) u =
       (if u \<in>
            generic_task_set
              (sa_delayed_a (resume_one_pending_abs t a)) \<union>
            generic_task_set
              (sa_delayed_b (resume_one_pending_abs t a))
        then Some (K_G u) else None)"
      using old wake_after da_after db_after
      by (cases "u = t") auto
  qed
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_wakeD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "strong_wake_payload_projection (resume_one_pending_abs t a) K_G"
proof -
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
    and wake: "strong_wake_payload_projection a K_G"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    by (rule
      cursor_general_strong_wake_payload_projection_resume_one_pending_abs[
        OF core wake])
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domain_wakeD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "CursorGeneralStrongManagedDomainRel
       (resume_one_pending_abs t a) termination managed \<and>
     strong_wake_payload_projection (resume_one_pending_abs t a) K_G"
  by (rule conjI)
     (rule
        CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domainD[
          OF phase],
      rule CursorGeneralStrongResumePendingManagedPhaseRel_reentry_wakeD[
          OF phase])

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

  val _ = audit_exact "managed reentry domain" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domainD}
  val _ = audit_exact "generic wake preservation" 2
    @{thm cursor_general_strong_wake_payload_projection_resume_one_pending_abs}
  val _ = audit_exact "managed reentry wake" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_wakeD}
  val _ = audit_exact "managed reentry domain/wake" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_domain_wakeD}
\<close>

end

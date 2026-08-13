theory Scheduler_Resume_Managed_Reentry_Gate_Phase
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Snapshot.Scheduler_Resume_Managed_Reentry_Snapshot"
begin

lemma CursorGeneralStrongResumePendingManagedGateRel_reentry_side_conditionsD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "sa_suspend_depth (resume_one_pending_abs t a) = 0 \<and>
     (ring (sa_pending (resume_one_pending_abs t a)) \<noteq> [] \<longrightarrow>
        sa_current (resume_one_pending_abs t a) \<noteq> None)"
proof -
  have quiet: "sa_suspend_depth a = 0"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast+
  note abs = resume_one_pending_abs_components[of t a]
  have quiet_after:
    "sa_suspend_depth (resume_one_pending_abs t a) = 0"
    using quiet abs by simp
  have pending_nonempty_before:
    "ring (sa_pending (resume_one_pending_abs t a)) \<noteq> [] \<Longrightarrow>
       ring (sa_pending a) \<noteq> []"
    using abs by (auto simp: list_remove_abs_def)
  have current_after:
    "sa_current (resume_one_pending_abs t a) = sa_current a"
    using abs by simp
  have current_safe_after:
    "ring (sa_pending (resume_one_pending_abs t a)) \<noteq> [] \<longrightarrow>
       sa_current (resume_one_pending_abs t a) \<noteq> None"
  proof
    assume post_pending:
      "ring (sa_pending (resume_one_pending_abs t a)) \<noteq> []"
    have pre_pending: "ring (sa_pending a) \<noteq> []"
      by (rule pending_nonempty_before[OF post_pending])
    have pre_current: "sa_current a \<noteq> None"
      using current_safe pre_pending by simp
    show "sa_current (resume_one_pending_abs t a) \<noteq> None"
      using current_after pre_current by simp
  qed
  show ?thesis
    using quiet_after current_safe_after by blast
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_gateD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "CursorGeneralStrongResumePendingManagedGateRel D
       (resume_pending_ready_inserted_state D C t generic_raw c)
       (resume_one_pending_abs t a) managed termination external
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))"
proof -
  have entry_gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  note side =
    CursorGeneralStrongResumePendingManagedGateRel_reentry_side_conditionsD[
      OF entry_gate, where t=t]
  have quiet:
      "sa_suspend_depth (resume_one_pending_abs t a) = 0"
    and current_safe:
      "ring (sa_pending (resume_one_pending_abs t a)) \<noteq> [] \<longrightarrow>
         sa_current (resume_one_pending_abs t a) \<noteq> None"
    using side by blast+
  note protected =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_protected_snapshotD[
      OF phase tasks]
  show ?thesis
    by (rule CursorGeneralStrongResumePendingManagedGateRelI[
          OF protected quiet current_safe])
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_phaseD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "CursorGeneralStrongResumePendingManagedPhaseRel D
       (resume_pending_ready_inserted_state D C t generic_raw c)
       (resume_one_pending_abs t a) managed termination external
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t P)"
proof -
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_gateD[
      OF phase tasks]
  note pure =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_pureD[
      OF phase tasks]
  note tasks_live =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_tasks_liveD[
      OF phase tasks]
  note alignment =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD[
      OF phase tasks]
  show ?thesis
    by (rule CursorGeneralStrongResumePendingManagedPhaseRelI[
          OF gate pure tasks_live alignment])
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

  val _ = audit_exact "managed reentry gate side conditions" 1
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_reentry_side_conditionsD}
  val _ = audit_exact "managed reentry gate" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_gateD}
  val _ = audit_exact "managed reentry phase" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_phaseD}
\<close>

end

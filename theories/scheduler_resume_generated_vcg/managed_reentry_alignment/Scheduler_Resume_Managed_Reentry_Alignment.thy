theory Scheduler_Resume_Managed_Reentry_Alignment
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Reentry_Captured_Key.Scheduler_Resume_Managed_Reentry_Captured_Key"
begin

definition resume_pending_one_due_of_snapshot ::
  "('tid, xLIST_C ptr) resume_pending_snapshot \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot"
where
  "resume_pending_one_due_of_snapshot P =
     \<lparr>ods_generic_family = rps_generic_family P,
      ods_event_family = rps_event_family P,
      ods_generic_payload = rps_generic_payload P,
      ods_event_payload = rps_event_payload P,
      ods_top = rps_top P,
      ods_captured_generic_key = None,
      ods_checked_event = None\<rparr>"

lemma resume_pending_snapshot_of_one_due_inverse:
  assumes local: "\<not> rps_local_yield P"
  shows
    "resume_pending_snapshot_of_one_due
       (resume_pending_one_due_of_snapshot P) = P"
  using local
  by (cases P)
     (simp add: resume_pending_snapshot_of_one_due_def
        resume_pending_one_due_of_snapshot_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_managed_tasksD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_managed_tasks (resume_one_pending_abs t a) = rest"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have tasks_a: "resume_pending_managed_tasks a = t # rest"
    using alignment tasks
    by (simp add: resume_pending_managed_phase_alignment_def)
  have pending_ring:
    "ring (sa_pending a) = map Event (resume_pending_managed_tasks a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD[
        OF gate])
  have pending_after:
    "ring (sa_pending (resume_one_pending_abs t a)) = map Event rest"
    using pending_ring tasks_a
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        list_remove_abs_def Let_def)
  have owner_map: "map node_owner (map Event rest) = rest"
    by (induction rest) simp_all
  show ?thesis
    unfolding resume_pending_managed_tasks_def
    apply (subst pending_after)
    by (rule owner_map)
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_pureD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_entry_rel
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t P)"
  by (rule resume_pending_drained_entry_rel[
        OF CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase]
          tasks])

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_tasks_liveD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "set (rpc_tasks (resume_pending_drained_context C t rest))
       \<subseteq> sa_live (resume_one_pending_abs t a)"
proof -
  have old: "set (rpc_tasks C) \<subseteq> sa_live a"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD[OF phase])
  have live:
    "sa_live (resume_one_pending_abs t a) = sa_live a"
    using resume_one_pending_abs_components[of t a] by simp
  show ?thesis
    using old tasks live
    by (simp add: resume_pending_drained_context_components)
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_managed_phase_alignment
       (resume_one_pending_abs t a) managed external
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t P)"
proof -
  let ?after = "resume_one_pending_abs t a"
  let ?C' = "resume_pending_drained_context C t rest"
  let ?P' = "resume_pending_drained_snapshot C t P"
  have old:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have tasks_after: "resume_pending_managed_tasks ?after = rest"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_managed_tasksD[
        OF phase tasks])
  note ctx_fields = resume_pending_drained_context_components[of C t rest]
  note snap_fields = resume_pending_drained_snapshot_scalars[of C t P]
  note abs_fields = resume_one_pending_abs_components[of t a]
  show ?thesis
    using old tasks_after ctx_fields snap_fields abs_fields
    by (simp add: resume_pending_managed_phase_alignment_def
        resume_pending_managed_current_priority_def split: option.splits)
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_one_due_projectionD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "strong_one_due_snapshot_projection
       (resume_one_pending_abs t a)
       (rps_generic_family (resume_pending_drained_snapshot C t P))
       (rps_event_family (resume_pending_drained_snapshot C t P))
       K_G K_E
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P))"
proof -
  note alignment =
    CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD[
      OF phase tasks]
  show ?thesis
    using alignment
    by (simp add: strong_one_due_snapshot_projection_def
        resume_pending_one_due_of_snapshot_def
        resume_pending_managed_phase_alignment_def)
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_reentry_snapshot_roundtripD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_snapshot_of_one_due
       (resume_pending_one_due_of_snapshot
         (resume_pending_drained_snapshot C t P)) =
     resume_pending_drained_snapshot C t P"
proof -
  have pure:
    "resume_pending_entry_rel
       (resume_pending_drained_context C t rest)
       (resume_pending_drained_snapshot C t P)"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_reentry_pureD[
        OF phase tasks])
  have local:
    "\<not> rps_local_yield (resume_pending_drained_snapshot C t P)"
    using pure by (simp add: resume_pending_entry_rel_def)
  show ?thesis
    by (rule resume_pending_snapshot_of_one_due_inverse[OF local])
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

  val _ = audit_exact "resume snapshot reverse adapter" 1
    @{thm resume_pending_snapshot_of_one_due_inverse}
  val _ = audit_exact "managed reentry task tail" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_managed_tasksD}
  val _ = audit_exact "managed reentry pure" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_pureD}
  val _ = audit_exact "managed reentry tasks live" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_tasks_liveD}
  val _ = audit_exact "managed reentry alignment" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_alignmentD}
  val _ = audit_exact "managed reentry one-due projection" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_one_due_projectionD}
  val _ = audit_exact "managed reentry snapshot roundtrip" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_snapshot_roundtripD}
\<close>

end

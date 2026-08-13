theory Scheduler_Resume_Managed_Reentry_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body.Scheduler_Resume_Managed_Body"
begin

section \<open>Cursor algebra for one pending resume\<close>

lemma canonical_tail_cursor_remove:
  fixes q :: "'tid node_ring"
  assumes distinct: "distinct (ring q)"
  shows
    "list_remove_abs x (canonical_tail_cursor q) =
       canonical_tail_cursor (list_remove_abs x q)"
proof -
  have shadow_wf: "xlist_wf (canonical_tail_cursor q)"
    using distinct
    by (auto simp: xlist_wf_def canonical_tail_cursor_def
        split: if_splits)
  have canonical_same:
    "canonical_tail_cursor (list_remove_abs x q) =
       canonical_tail_cursor
         (list_remove_abs x (canonical_tail_cursor q))"
    by (cases q)
       (simp add: canonical_tail_cursor_def list_remove_abs_def)
  have tail:
    "tail_cursor_wf
       (list_remove_abs x (canonical_tail_cursor q))"
  proof (cases "x \<in> set (ring q)")
    case True
    show ?thesis
      apply (rule tail_cursor_wf_remove[OF shadow_wf
            canonical_tail_cursor_wf])
      using True by simp
  next
    case False
    have unchanged:
      "list_remove_abs x (canonical_tail_cursor q) =
         canonical_tail_cursor q"
      apply (rule list_remove_abs_nonmember[OF shadow_wf])
      using False by simp
    show ?thesis using unchanged by simp
  qed
  have fixed:
    "canonical_tail_cursor
       (list_remove_abs x (canonical_tail_cursor q)) =
     list_remove_abs x (canonical_tail_cursor q)"
    by (rule canonical_tail_cursor_id[OF tail])
  show ?thesis using canonical_same fixed by simp
qed

lemma pending_generic_key_abs_canonicalize_scheduler_cursors [simp]:
  "pending_generic_key_abs t (canonicalize_scheduler_cursors a) =
     pending_generic_key_abs t a"
  by (simp add: pending_generic_key_abs_def)

lemma canonicalize_scheduler_cursors_resume_one_pending_abs:
  assumes shape: "ring_shape_wf a"
  shows
    "canonicalize_scheduler_cursors (resume_one_pending_abs t a) =
       resume_one_pending_abs t (canonicalize_scheduler_cursors a)"
proof -
  have pending_distinct: "distinct (ring (sa_pending a))"
    and suspended_distinct: "distinct (ring (sa_suspended a))"
    using shape by (simp_all add: ring_shape_wf_def xlist_wf_def)
  show ?thesis
    by (simp add: canonicalize_scheduler_cursors_def
        clear_delayed_cursors_def resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        pending_generic_key_abs_def
        canonical_tail_cursor_remove[OF pending_distinct]
        canonical_tail_cursor_remove[OF suspended_distinct] Let_def)
qed

section \<open>Cursor-general core preservation\<close>

theorem cursor_general_core_wf_resume_one_pending_abs:
  assumes core: "cursor_general_core_wf a"
    and pending: "Event t \<in> set (ring (sa_pending a))"
  shows "cursor_general_core_wf (resume_one_pending_abs t a)"
proof -
  let ?after = "resume_one_pending_abs t a"
  have canonical_core:
      "core_wf (canonicalize_scheduler_cursors a)"
    and real_shape: "ring_shape_wf a"
    using core
    by (simp_all add: cursor_general_core_wf_def)
  have canonical_pending:
    "Event t \<in>
       set (ring (sa_pending (canonicalize_scheduler_cursors a)))"
    using pending by simp
  have canonical_step:
    "core_wf
       (resume_one_pending_abs t (canonicalize_scheduler_cursors a))"
    by (rule core_wf_resume_one_pending_abs[
          OF canonical_core canonical_pending])
  have commute:
    "canonicalize_scheduler_cursors ?after =
       resume_one_pending_abs t (canonicalize_scheduler_cursors a)"
    by (rule canonicalize_scheduler_cursors_resume_one_pending_abs[
          OF real_shape])
  have canonical_after:
    "core_wf (canonicalize_scheduler_cursors ?after)"
    using canonical_step commute by simp

  have ready_after:
    "\<forall>p<4. xlist_wf (sa_ready ?after p)"
    using canonical_after
    by (simp add: core_wf_def ring_shape_wf_def)
  have delayed_a: "xlist_wf (sa_delayed_a a)"
    and delayed_b: "xlist_wf (sa_delayed_b a)"
    and pending_wf: "xlist_wf (sa_pending a)"
    and suspended: "xlist_wf (sa_suspended a)"
    using real_shape by (simp_all add: ring_shape_wf_def)
  have delayed_a_after: "xlist_wf (sa_delayed_a ?after)"
    using xlist_wf_remove[OF delayed_a, of "Generic t"]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have delayed_b_after: "xlist_wf (sa_delayed_b ?after)"
    using xlist_wf_remove[OF delayed_b, of "Generic t"]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have pending_after: "xlist_wf (sa_pending ?after)"
    using xlist_wf_remove[OF pending_wf, of "Event t"]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have suspended_after: "xlist_wf (sa_suspended ?after)"
    using xlist_wf_remove[OF suspended, of "Generic t"]
    by (simp add: resume_one_pending_abs_def
        resume_remove_generic_abs_def resume_add_ready_with_key_abs_def
        Let_def)
  have real_after_shape: "ring_shape_wf ?after"
    using ready_after delayed_a_after delayed_b_after pending_after
      suspended_after
    by (simp add: ring_shape_wf_def)
  show ?thesis
    using canonical_after real_after_shape
    by (simp add: cursor_general_core_wf_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_reentry_coreD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> set (resume_pending_managed_tasks a)"
  shows "cursor_general_core_wf (resume_one_pending_abs t a)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel
       D c0 a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have core: "cursor_general_core_wf a"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have pending_ring:
    "ring (sa_pending a) = map Event (resume_pending_managed_tasks a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD[
        OF gate])
  have pending: "Event t \<in> set (ring (sa_pending a))"
    using pending_ring task by simp
  show ?thesis
    by (rule cursor_general_core_wf_resume_one_pending_abs[
          OF core pending])
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_reentry_coreD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows "cursor_general_core_wf (resume_one_pending_abs t a)"
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
  have task_C: "t \<in> set (rpc_tasks C)"
    using tasks by simp
  have task: "t \<in> set (resume_pending_managed_tasks a)"
    using task_C alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  show ?thesis
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_reentry_coreD[
        OF gate task])
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

  val _ = audit_exact "canonical tail remove" 1
    @{thm canonical_tail_cursor_remove}
  val _ = audit_exact "pending key canonicalization" 0
    @{thm pending_generic_key_abs_canonicalize_scheduler_cursors}
  val _ = audit_exact "resume canonicalization commute" 1
    @{thm canonicalize_scheduler_cursors_resume_one_pending_abs}
  val _ = audit_exact "cursor-general resume core" 2
    @{thm cursor_general_core_wf_resume_one_pending_abs}
  val _ = audit_exact "managed gate reentry core" 2
    @{thm CursorGeneralStrongResumePendingManagedGateRel_reentry_coreD}
  val _ = audit_exact "managed phase reentry core" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_reentry_coreD}
\<close>

end

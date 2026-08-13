theory Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Owner.Scheduler_Resume_Managed_Phase_Adapter_Owner"
begin

text \<open>
  The canonical pending entry is now a pure assembly: context, complete family
  shape, exact pending order, task-scoped owner clauses, top, and local-yield
  state.  The public and managed carriers remain distinct.
\<close>

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_pure_entryD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "resume_pending_entry_rel
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have event_role:
    "strong_event_role_projection a managed external event_abs"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have projection:
    "strong_one_due_snapshot_projection
       a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have snapshot_event: "ods_event_family S = event_abs"
    and snapshot_top: "ods_top S = sa_top_ready a"
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
  have context_wf:
    "resume_pending_context_wf
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_context_wf[
        OF gate])
  have family:
    "resume_pending_family_shape
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_family_shapeD[
        OF gate])
  have pending:
    "ring (ods_event_family S GeneratedPendingEventRoot) =
       map Event (resume_pending_managed_tasks a)"
    using event_role snapshot_event
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD[
        OF gate]
    by (simp add: strong_event_role_projection_def)
  have owners:
    "\<forall>t\<in>set (resume_pending_managed_tasks a).
       Generic t \<in> set (ring (ods_generic_family S
         (resume_pending_managed_owner a t))) \<and>
       (\<forall>g\<in>GenericRootUniverse.
          Generic t \<in> set (ring (ods_generic_family S g)) \<longleftrightarrow>
            g = resume_pending_managed_owner a t) \<and>
       item_key (ods_generic_family S
         (resume_pending_managed_owner a t)) (Generic t) = K_G t"
  proof (rule ballI)
    fix t
    assume task: "t \<in> set (resume_pending_managed_tasks a)"
    show
      "Generic t \<in> set (ring (ods_generic_family S
         (resume_pending_managed_owner a t))) \<and>
       (\<forall>g\<in>GenericRootUniverse.
          Generic t \<in> set (ring (ods_generic_family S g)) \<longleftrightarrow>
            g = resume_pending_managed_owner a t) \<and>
       item_key (ods_generic_family S
         (resume_pending_managed_owner a t)) (Generic t) = K_G t"
      by (rule
        CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD[
          OF gate task])
  qed
  show ?thesis
    unfolding resume_pending_entry_rel_def
    apply (intro conjI)
    subgoal by (rule context_wf)
    subgoal by (rule family)
    subgoal using pending
      by (simp add: resume_pending_canonical_managed_context_def
          resume_pending_snapshot_of_one_due_def)
    subgoal using owners
      by (simp add: resume_pending_canonical_managed_context_def
          resume_pending_snapshot_of_one_due_def)
    subgoal using snapshot_top
      by (simp add: resume_pending_canonical_managed_context_def
          resume_pending_snapshot_of_one_due_def)
    subgoal
      by (simp add: resume_pending_snapshot_of_one_due_def)
    done
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_pure_entryD}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "canonical managed pending pure entry has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 1 then ()
    else error "canonical managed pending pure-entry premise ledger changed"
\<close>

end

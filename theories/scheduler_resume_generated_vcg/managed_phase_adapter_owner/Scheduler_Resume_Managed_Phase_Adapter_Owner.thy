theory Scheduler_Resume_Managed_Phase_Adapter_Owner
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Family.Scheduler_Resume_Managed_Phase_Adapter_Family"
begin

text \<open>
  Pending owner reconstruction is task scoped.  The cursor-general core
  supplies only the cursor-insensitive membership partition; complete family
  coverage then supplies unique roots and abstract keys across the full
  managed universe.
\<close>

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> set (resume_pending_managed_tasks a)"
  shows
    "Generic t \<in>
       set (ring
         (ods_generic_family S (resume_pending_managed_owner a t))) \<and>
     (\<forall>g\<in>GenericRootUniverse.
        Generic t \<in> set (ring (ods_generic_family S g)) \<longleftrightarrow>
          g = resume_pending_managed_owner a t) \<and>
     item_key
       (ods_generic_family S (resume_pending_managed_owner a t))
       (Generic t) = K_G t"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have core: "cursor_general_core_wf a"
    and role:
      "strong_generic_role_projection a termination generic_abs"
    and projection:
      "strong_one_due_snapshot_projection
         a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using core by (simp add: cursor_general_core_wf_def)
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
  have task_managed: "t \<in> managed"
    using context_wf task
    by (auto simp: resume_pending_context_wf_def
        resume_pending_canonical_managed_context_def)
  have owner_root:
    "resume_pending_managed_owner a t \<in> GenericRootUniverse"
    using context_wf task
    by (auto simp: resume_pending_context_wf_def
        resume_pending_canonical_managed_context_def)
  have pending_task: "t \<in> event_task_set (sa_pending a)"
    using task
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_setD[
        OF gate]
    by blast
  have pending_event:
    "Event t \<in> set (ring (sa_pending a))"
    using pending_task by (simp add: event_task_set_def)
  have pending_shadow:
    "Event t \<in>
       set (ring (sa_pending (canonicalize_scheduler_cursors a)))"
    using pending_event by simp
  note located = core_wf_pending_generic_key_has_physical_source[
      OF canonical_core pending_shadow]
  have source:
    "Generic t \<in> set (ring (sa_delayed_a a)) \<or>
     Generic t \<in> set (ring (sa_delayed_b a)) \<or>
     Generic t \<in> set (ring (sa_suspended a))"
    using located by auto
  have owner_member0:
    "Generic t \<in>
       set (ring
         (generic_abs (resume_pending_managed_owner a t)))"
    using source role
    by (auto simp: resume_pending_managed_owner_def
        strong_generic_role_projection_def
        split: if_splits)
  have snapshot_family: "ods_generic_family S = generic_abs"
    using projection
    by (simp add: strong_one_due_snapshot_projection_def)
  have owner_member:
    "Generic t \<in>
       set (ring
         (ods_generic_family S (resume_pending_managed_owner a t)))"
    using owner_member0 snapshot_family by simp
  have pairwise:
    "\<forall>g\<in>GenericRootUniverse.
       \<forall>g'\<in>GenericRootUniverse.
         g \<noteq> g' \<longrightarrow>
         set (ring (ods_generic_family S g)) \<inter>
           set (ring (ods_generic_family S g')) = {}"
    using family
    by (simp add: resume_pending_family_shape_def
        resume_pending_canonical_managed_context_def
        resume_pending_snapshot_of_one_due_def)
  have key_ledger:
    "\<forall>g\<in>GenericRootUniverse. \<forall>u\<in>managed.
       Generic u \<in> set (ring (ods_generic_family S g)) \<longrightarrow>
       item_key (ods_generic_family S g) (Generic u) = K_G u"
    using family
    by (simp add: resume_pending_family_shape_def
        resume_pending_canonical_managed_context_def
        resume_pending_snapshot_of_one_due_def)
  have owner_unique:
    "\<forall>g\<in>GenericRootUniverse.
       Generic t \<in> set (ring (ods_generic_family S g)) \<longleftrightarrow>
         g = resume_pending_managed_owner a t"
  proof (intro ballI iffI)
    fix g
    assume g_root: "g \<in> GenericRootUniverse"
      and g_member:
        "Generic t \<in> set (ring (ods_generic_family S g))"
    show "g = resume_pending_managed_owner a t"
    proof (rule ccontr)
      assume different: "g \<noteq> resume_pending_managed_owner a t"
      have disjoint:
        "set (ring (ods_generic_family S g)) \<inter>
           set (ring (ods_generic_family S
             (resume_pending_managed_owner a t))) = {}"
        using pairwise g_root owner_root different by blast
      show False using disjoint g_member owner_member by blast
    qed
  next
    fix g
    assume "g \<in> GenericRootUniverse"
      and "g = resume_pending_managed_owner a t"
    then show "Generic t \<in> set (ring (ods_generic_family S g))"
      using owner_member by simp
  qed
  have key:
    "item_key
       (ods_generic_family S (resume_pending_managed_owner a t)) (Generic t) =
       K_G t"
    using key_ledger owner_root task_managed owner_member by blast
  show ?thesis
    using owner_member owner_unique key by blast
qed

ML \<open>
  val owner =
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD}
  val _ =
    if null (Thm.hyps_of owner) then ()
    else error "canonical managed pending owner has hidden hypotheses"
  val _ =
    if length (Thm.prems_of owner) = 2 then ()
    else error "canonical managed pending owner premise ledger changed"
\<close>

end

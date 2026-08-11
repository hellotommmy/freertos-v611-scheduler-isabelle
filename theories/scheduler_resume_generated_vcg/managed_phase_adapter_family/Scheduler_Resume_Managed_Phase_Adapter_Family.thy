theory Scheduler_Resume_Managed_Phase_Adapter_Family
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Context.Scheduler_Resume_Managed_Phase_Adapter_Context"
begin

text \<open>
  Complete Generic and Event coverage already supplies the cross-family shape
  required by the Resume pending phase.  Transfer that checked one-due result
  to the canonical Resume context and snapshot instead of duplicating its
  disjointness and key ledger.
\<close>

lemma full_family_coverage_resume_pending_family_shape:
  assumes generic:
    "GenericRootFamilyCoverage D h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    and event:
      "EventRootFamilyCoverage external D h event_raw
         (ods_event_family S) managed (ods_event_payload S)"
    and projection:
      "strong_one_due_snapshot_projection
         a generic_abs event_abs K_G K_E S"
  shows
    "resume_pending_family_shape
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  let ?C =
    "due_prefix_canonical_managed_context
       generated_scheduler_roots
       (undefined :: Scheduler_V611_Parse.globals)
       a managed external K_E undefined"
  have one_due: "one_due_family_shape ?C S"
    apply (rule full_family_coverage_one_due_family_shape[OF generic event])
    using projection
    by (simp_all add: strong_one_due_snapshot_projection_def)
  show ?thesis
    using one_due projection
    by (auto simp: one_due_family_shape_def
        resume_pending_family_shape_def
        due_prefix_canonical_managed_context_def
        resume_pending_canonical_managed_context_def
        resume_pending_snapshot_of_one_due_def
        strong_one_due_snapshot_projection_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_family_shapeD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "resume_pending_family_shape
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0)"
  have generic0:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse generic_raw
       generic_abs managed K_G"
    and event0:
      "EventRootFamilyCoverage external D ?h event_raw
         event_abs managed K_E"
    and projection:
      "strong_one_due_snapshot_projection
         a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have generic:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse generic_raw
       (ods_generic_family S) managed (ods_generic_payload S)"
    using generic0 projection
    by (simp add: strong_one_due_snapshot_projection_def)
  have event:
    "EventRootFamilyCoverage external D ?h event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    using event0 projection
    by (simp add: strong_one_due_snapshot_projection_def)
  show ?thesis
    by (rule full_family_coverage_resume_pending_family_shape[
        OF generic event projection])
qed

ML \<open>
  val generic = @{thm full_family_coverage_resume_pending_family_shape}
  val gate =
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_family_shapeD}
  val _ =
    if null (Thm.hyps_of generic) andalso null (Thm.hyps_of gate) then ()
    else error "canonical managed pending family shape has hidden hypotheses"
  val _ =
    if length (Thm.prems_of generic) = 3 andalso
       length (Thm.prems_of gate) = 1
    then ()
    else error "canonical managed pending family-shape premise ledger changed"
\<close>

end

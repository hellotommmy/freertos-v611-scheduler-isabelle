theory Scheduler_Resume_Managed_Phase_Adapter_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry.Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry"
begin

text \<open>
  The managed gate now has a canonical proof-only pending phase.  This final
  adapter step adds no execution claim: it combines the pure entry, public-live
  task subset, and field alignment already established from the gate.
\<close>

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_phaseD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
proof -
  have pure:
    "resume_pending_entry_rel
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_pure_entryD[
        OF gate])
  have tasks_live:
    "set (rpc_tasks
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)) \<subseteq> sa_live a"
    using
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_liveD[
        OF gate]
    by (simp add: resume_pending_canonical_managed_context_def)
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_alignmentD[
        OF gate])
  show ?thesis
    by (rule CursorGeneralStrongResumePendingManagedPhaseRelI[
        OF gate pure tasks_live alignment])
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_phase_exD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "\<exists>C P.
       CursorGeneralStrongResumePendingManagedPhaseRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  using
    CursorGeneralStrongResumePendingManagedGateRel_canonical_phaseD[OF gate]
  by blast

ML \<open>
  val canonical =
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_phaseD}
  val existential =
    @{thm CursorGeneralStrongResumePendingManagedGateRel_phase_exD}
  val _ =
    if null (Thm.hyps_of canonical) andalso
       null (Thm.hyps_of existential)
    then ()
    else error "canonical managed pending phase has hidden hypotheses"
  val _ =
    if length (Thm.prems_of canonical) = 1 andalso
       length (Thm.prems_of existential) = 1
    then ()
    else error "canonical managed pending phase premise ledger changed"
\<close>

end

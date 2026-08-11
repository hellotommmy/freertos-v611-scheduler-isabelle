theory Scheduler_Resume_Managed_Generic_Remove_After_Event
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Event_Remove_Relational.Scheduler_Resume_Managed_Event_Remove_Relational"
begin

text \<open>
  Owner alignment is deliberately task scoped: only the current pending head's
  proof-only owner is identified with its canonical blocked root.  Complete
  Generic coverage on the exact Event-removed heap then supplies the raw root
  and member.  The task-scoped equality exposes the concrete owner-list pointer
  used by the low-level generated vListRemove' interface.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_head_owner_eq:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "rpc_generic_owner C t = resume_pending_managed_owner a t"
proof -
  have gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase])
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have tasks_canonical:
    "rpc_tasks C = resume_pending_managed_tasks a"
    using alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have task: "t \<in> set (resume_pending_managed_tasks a)"
    using tasks tasks_canonical by simp
  have owner_info:
    "Generic t \<in>
       set (ring
         (ods_generic_family S (resume_pending_managed_owner a t))) \<and>
     (\<forall>g\<in>GenericRootUniverse.
        Generic t \<in> set (ring (ods_generic_family S g)) \<longleftrightarrow>
          g = resume_pending_managed_owner a t) \<and>
     item_key
       (ods_generic_family S (resume_pending_managed_owner a t))
       (Generic t) = K_G t"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_canonical_task_ownerD[
        OF gate task])
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have projection:
    "strong_one_due_snapshot_projection
       a generic_abs event_abs K_G K_E S"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have owner_root:
    "rpc_generic_owner C t \<in> rpc_generic_roots C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have owner_root_universe:
    "rpc_generic_owner C t \<in> GenericRootUniverse"
    using owner_root alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have owner_member:
    "Generic t \<in>
       set (ring (rps_generic_family P (rpc_generic_owner C t)))"
    using pure tasks
    by (simp add: resume_pending_entry_rel_def)
  have owner_member_snapshot:
    "Generic t \<in>
       set (ring (ods_generic_family S (rpc_generic_owner C t)))"
    using owner_member alignment projection
    by (simp add: resume_pending_managed_phase_alignment_def
        strong_one_due_snapshot_projection_def)
  show ?thesis
    using owner_info owner_root_universe owner_member_snapshot by blast
qed

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_generic_remove_after_event:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<bullet>
       (scheduler_mem_state (resume_pending_event_remove_heap D t c) c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c
     \<rbrace>"
proof -
  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have owner_eq:
    "rpc_generic_owner C t = resume_pending_managed_owner a t"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_head_owner_eq[
        OF phase tasks])
  have t_context: "t \<in> rpc_live C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have owner_root_context:
    "rpc_generic_owner C t \<in> rpc_generic_roots C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have owner_root:
    "rpc_generic_owner C t \<in> GenericRootUniverse"
    using owner_root_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have abstract_member0:
    "Generic t \<in>
       set (ring (rps_generic_family P (rpc_generic_owner C t)))"
    using pure tasks
    by (simp add: resume_pending_entry_rel_def)
  have abstract_member:
    "Generic t \<in>
       set (ring (generic_abs (rpc_generic_owner C t)))"
    using abstract_member0 alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have coverage:
    "GenericRootFamilyCoverage D
       (resume_pending_event_remove_heap D t c)
       GenericRootUniverse generic_raw generic_abs managed K_G"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_event_remove_generic_coverageD[
        OF phase tasks])
  have raw_owner:
    "raw_xlist_rel (resume_pending_event_remove_heap D t c)
       (rpc_generic_owner C t) (generic_raw (rpc_generic_owner C t))"
    by (rule GenericRootFamilyCoverage_raw_rootD[
        OF coverage owner_root])
  have raw_member:
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw (rpc_generic_owner C t)))"
    by (rule iffD2[OF GenericRootFamilyCoverage_member_iff[
        OF coverage t_managed owner_root] abstract_member])
  have member:
    "abi_item_ptr (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<in>
       set (ring (generic_raw (rpc_generic_owner C t)))"
    using raw_member
    by (simp add: generic_item_raw_ptr_def
        scheduler_generic_item_ptr_def abi_generic_list_item_ptr_def)
  have owner_choices:
    "rpc_generic_owner C t \<in>
       {abi_list_ptr (sr_delayed_a generated_scheduler_roots),
        abi_list_ptr (sr_delayed_b generated_scheduler_roots),
        abi_list_ptr (sr_suspended generated_scheduler_roots)}"
    using owner_eq
    by (auto simp: resume_pending_managed_owner_def)
  have owner_source:
    "abi_list_ptr
       (resume_pending_owner_list_ptr generated_scheduler_roots C t) =
     rpc_generic_owner C t"
    using owner_choices
    by (auto simp: resume_pending_owner_list_ptr_def)
  have raw_source:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
         (scheduler_mem_state (resume_pending_event_remove_heap D t c) c)))
       (abi_list_ptr
         (resume_pending_owner_list_ptr generated_scheduler_roots C t))
       (generic_raw (rpc_generic_owner C t))"
    using raw_owner owner_source by simp
  note source = resume_pending_generic_remove_generated_interface[
      OF raw_source member]
  show ?thesis
    apply (rule runs_to_weaken[OF source])
    by (simp add: resume_pending_generic_remove_heap_def
        resume_pending_generic_raw_ptr_def scheduler_generic_item_ptr_def
        abi_generic_list_item_ptr_def)
qed

ML \<open>
  fun audit_exact label th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length (Thm.prems_of th) = 2 then ()
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed pending-head owner equality"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_head_owner_eq}
  val _ = audit_exact "managed Generic remove after Event"
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_generic_remove_after_event}
\<close>

end

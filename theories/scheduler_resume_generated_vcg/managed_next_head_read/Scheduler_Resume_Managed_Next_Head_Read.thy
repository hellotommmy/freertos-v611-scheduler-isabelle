theory Scheduler_Resume_Managed_Next_Head_Read
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Yield_Relational.Scheduler_Resume_Managed_Yield_Relational"
begin

text \<open>
  Exact source read of the pending-list head after the current task has been
  removed and inserted into its ready list.  The empty and nonempty tail
  branches are established from the post-ready Event/Generic coverage and
  managed observation, not from an entry-state head-read theorem.
\<close>

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_next_head_read_exact:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_head_read \<bullet>
       (resume_pending_ready_inserted_state D C t generic_raw c)
     \<lbrace>\<lambda>r s.
       r = Result
         (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (resume_pending_next_head_tcb D rest)) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  let ?cR = "resume_pending_ready_inserted_state D C t generic_raw c"
  let ?hR = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?cR)"
  let ?PR = "resume_pending_drained_snapshot C t P"
  let ?PY = "resume_pending_yield_check_state C t ?PR"

  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have generic_coverage:
    "GenericRootFamilyCoverage D ?hR GenericRootUniverse
       (resume_pending_drained_generic_fam C D t c generic_raw)
       (rps_generic_family ?PR) managed K_G"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD[
        OF phase tasks])
  have event_coverage:
    "EventRootFamilyCoverage external D ?hR
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family ?PR) managed K_E"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD[
        OF phase tasks])
  have observation0:
    "scheduler_managed_task_observation_rel D ?hR a managed"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD[
        OF phase tasks])
  have observation:
    "TaskObservationRel D ?hR (managed_scheduler_view a managed)"
    using observation0
    by (simp add: scheduler_managed_task_observation_rel_def)
  have decode:
    "scheduler_decode_rel D (managed_scheduler_view a managed)"
    by (rule GenericRootFamilyCoverage_managed_view_decodeD[
        OF generic_coverage])
  have checked:
    "resume_pending_loop_phase_inv C P [] (t # rest)
       RP_YieldChecked ?PY"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_yield_checkedD[
        OF phase tasks])
  have pending_checked0:
    "ring (rps_event_family ?PY (rpc_pending_root C)) =
       map Event
         (resume_pending_visible_tasks RP_YieldChecked (t # rest))"
    using checked unfolding resume_pending_loop_phase_inv_def by blast
  have pending_checked:
    "ring (rps_event_family ?PY (rpc_pending_root C)) =
       map Event rest"
    using pending_checked0 by simp
  have pending_rpc:
    "ring (rps_event_family ?PR (rpc_pending_root C)) =
       map Event rest"
    using pending_checked
    by (simp add: resume_pending_yield_check_state_def)
  have pending:
    "ring (rps_event_family ?PR GeneratedPendingEventRoot) =
       map Event rest"
    using pending_rpc alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have event_rel:
    "scheduler_event_root_family_rel D ?hR
       (EventRootUniverse external) GeneratedPendingEventRoot
       (resume_pending_event_raw_after C D t event_raw)
       (rps_event_family ?PR) managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF event_coverage])
  have lists:
    "sched_xlist_rel (sd_node_decode D) ?hR
       GeneratedPendingEventRoot
       (rps_event_family ?PR GeneratedPendingEventRoot)"
    by (rule scheduler_event_root_family_sched_xlistD[
        OF event_rel EventRootUniverse_pendingI])
  have lists_source:
    "sched_xlist_rel (sd_node_decode D) ?hR
       (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')
       (rps_event_family ?PR GeneratedPendingEventRoot)"
    using lists by (simp add: GeneratedPendingEventRoot_def)
  note count_cursor = EventRootFamilyCoverage_count_cursorD[
      OF event_coverage EventRootUniverse_pendingI]

  show ?thesis
  proof (cases rest)
    case Nil
    have raw_zero:
      "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val ?hR GeneratedPendingEventRoot) = 0"
      using count_cursor pending Nil
      by (simp add: unat_eq_0)
    have pending_raw_zero:
      "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val ?hR
           (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) = 0"
      using raw_zero by (simp add: GeneratedPendingEventRoot_def)
    have count:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
         (h_val ?hR Scheduler_V611_Parse.xPendingReadyList_') = 0"
      using pending_raw_zero by (simp only: abi_list_count_h_val)
    show ?thesis
      unfolding resume_pending_generated_head_read_def
      apply runs_to_vcg
      using count Nil
      by (simp_all add: resume_pending_next_head_tcb_def)
  next
    case (Cons u us)
    have ring_cons:
      "ring (rps_event_family ?PR GeneratedPendingEventRoot) =
         Event u # map Event us"
      using pending Cons by simp
    note observed = represented_event_head_owner_priority[
        OF lists_source decode observation ring_cons]
    have u_context: "u \<in> rpc_live C"
      using pure tasks Cons
      by (auto simp: resume_pending_entry_rel_def
          resume_pending_context_wf_def)
    have u_managed: "u \<in> managed"
      using u_context alignment
      by (simp add: resume_pending_managed_phase_alignment_def)
    have u_view:
      "u \<in> sa_live (managed_scheduler_view a managed)"
      using u_managed by (simp add: managed_scheduler_view_def)
    note fields = TaskObservationRel_liveD[OF observation u_view]
    have event_guard:
      "c_guard (scheduler_event_item_ptr (sd_tcb_ptr D u))"
      using fields by blast
    have event_owner:
      "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val ?hR (scheduler_event_item_ptr (sd_tcb_ptr D u))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D u)"
      using fields by blast
    have head_ptr:
      "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
         (Scheduler_V611_Parse.xLIST_C.xListEnd_C
           (h_val ?hR Scheduler_V611_Parse.xPendingReadyList_')) =
       scheduler_event_item_ptr (sd_tcb_ptr D u)"
      using observed by (simp add: scheduler_list_head_item_def)
    have raw_nonzero:
      "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val ?hR GeneratedPendingEventRoot) \<noteq> 0"
      using count_cursor ring_cons
      by (auto simp: unat_eq_0)
    have pending_raw_nonzero:
      "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val ?hR
           (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) \<noteq> 0"
      using raw_nonzero by (simp add: GeneratedPendingEventRoot_def)
    have count_eq:
      "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
         (h_val ?hR
           (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) =
       Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
         (h_val ?hR Scheduler_V611_Parse.xPendingReadyList_')"
      by (rule abi_list_count_h_val)
    have count:
      "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
         (h_val ?hR Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0"
      using pending_raw_nonzero count_eq by simp
    show ?thesis
      unfolding resume_pending_generated_head_read_def
      apply runs_to_vcg
      using count head_ptr event_guard event_owner Cons
      by (simp_all add: resume_pending_next_head_tcb_def)
  qed
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_next_head_read_exact}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed next-head read has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed next-head read premise ledger changed"
\<close>

end

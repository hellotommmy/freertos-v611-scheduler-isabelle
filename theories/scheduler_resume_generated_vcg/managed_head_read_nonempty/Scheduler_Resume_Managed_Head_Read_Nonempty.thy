theory Scheduler_Resume_Managed_Head_Read_Nonempty
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Capstone.Scheduler_Resume_Managed_Phase_Adapter_Capstone"
begin

text \<open>
  The first managed operational theorem reads one nonempty pending head.  The
  represented head is interpreted over the total managed scheduler view; the
  public shadow and actual protected state share the same heap.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_nonempty:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result
         (PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t)) \<and>
       s = c
     \<rbrace>"
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
  obtain c0 where overlay:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0)"
  have heap_eq:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c) = ?h"
    using overlay by simp
  have generic_coverage:
    "GenericRootFamilyCoverage D ?h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D ?h
         event_raw event_abs managed K_E"
    and observation0:
      "scheduler_managed_task_observation_rel D ?h a managed"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have observation:
    "TaskObservationRel D ?h (managed_scheduler_view a managed)"
    using observation0
    by (simp add: scheduler_managed_task_observation_rel_def)
  have decode:
    "scheduler_decode_rel D (managed_scheduler_view a managed)"
    by (rule GenericRootFamilyCoverage_managed_view_decodeD[
        OF generic_coverage])
  have ring:
    "ring (event_abs GeneratedPendingEventRoot) =
       Event t # map Event rest"
    using pure alignment tasks
    by (simp add: resume_pending_entry_rel_def
        resume_pending_managed_phase_alignment_def)
  have event_rel:
    "scheduler_event_root_family_rel D ?h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF event_coverage])
  have lists:
    "sched_xlist_rel (sd_node_decode D) ?h
       GeneratedPendingEventRoot
       (event_abs GeneratedPendingEventRoot)"
    by (rule scheduler_event_root_family_sched_xlistD[
        OF event_rel EventRootUniverse_pendingI])
  have lists_source:
    "sched_xlist_rel (sd_node_decode D) ?h
       (abi_list_ptr (sr_pending generated_scheduler_roots))
       (event_abs GeneratedPendingEventRoot)"
    using lists by (simp add: GeneratedPendingEventRoot_def)
  note observed = represented_event_head_owner_priority[
      OF lists_source decode observation ring]
  have t_live: "t \<in> sa_live a"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_tasks_liveD[OF phase]
      tasks by auto
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_domainD[OF gate])
  have t_managed: "t \<in> managed"
    using domain t_live
    by (auto simp: CursorGeneralStrongManagedDomainRel_def)
  have t_view: "t \<in> sa_live (managed_scheduler_view a managed)"
    using t_managed by (simp add: managed_scheduler_view_def)
  note fields = TaskObservationRel_liveD[OF observation t_view]
  have event_guard:
    "c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t))"
    using fields by blast
  have head_ptr0:
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C
         (h_val ?h Scheduler_V611_Parse.xPendingReadyList_')) =
       scheduler_event_item_ptr (sd_tcb_ptr D t)"
    using observed
    by (simp add: scheduler_list_head_item_def)
  have head_ptr:
    "Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
       (Scheduler_V611_Parse.xLIST_C.xListEnd_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           Scheduler_V611_Parse.xPendingReadyList_')) =
       scheduler_event_item_ptr (sd_tcb_ptr D t)"
    using head_ptr0 heap_eq by simp
  have event_owner0:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val ?h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D t)"
    using fields by blast
  have event_owner:
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
       PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
         (sd_tcb_ptr D t)"
    using event_owner0 heap_eq by simp
  note count_cursor = EventRootFamilyCoverage_count_cursorD[
      OF event_coverage EventRootUniverse_pendingI]
  have raw_nonzero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h GeneratedPendingEventRoot) \<noteq> 0"
    using count_cursor ring by (auto simp: unat_eq_0)
  have pending_raw_nonzero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h
         (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) \<noteq> 0"
    using raw_nonzero
    by (simp add: GeneratedPendingEventRoot_def)
  have count_eq:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h
         (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) =
     Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?h Scheduler_V611_Parse.xPendingReadyList_')"
    by (rule abi_list_count_h_val)
  have count0:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?h Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0"
    using pending_raw_nonzero count_eq by simp
  have count:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         Scheduler_V611_Parse.xPendingReadyList_') \<noteq> 0"
    using count0 heap_eq by simp
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using count head_ptr event_guard event_owner
    by simp_all
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_nonempty}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed pending head read has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed pending head-read premise ledger changed"
\<close>

end

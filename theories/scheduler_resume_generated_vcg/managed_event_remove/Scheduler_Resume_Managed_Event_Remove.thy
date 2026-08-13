theory Scheduler_Resume_Managed_Event_Remove
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Uniform.Scheduler_Resume_Managed_Head_Read_Uniform"
begin

text \<open>
  The first destructive managed source step removes only the represented Event
  item of the pending head.  Complete Event coverage supplies the raw list and
  member required by the universal generated remove theorem.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generated_event_remove:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "Scheduler_V611_Delay_Translation.vListRemove'
       (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_event_remove_heap D t c) c
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
  have event_coverage:
    "EventRootFamilyCoverage external D ?h
       event_raw event_abs managed K_E"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have event_rel:
    "scheduler_event_root_family_rel D ?h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF event_coverage])
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
  have abstract_member:
    "Event t \<in> set (ring (event_abs GeneratedPendingEventRoot))"
    using pure alignment tasks
    by (simp add: resume_pending_entry_rel_def
        resume_pending_managed_phase_alignment_def)
  have raw_member:
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw GeneratedPendingEventRoot))"
    using scheduler_event_root_family_member_iff[
        OF event_rel t_managed EventRootUniverse_pendingI]
      abstract_member
    by blast
  have raw0:
    "raw_xlist_rel ?h GeneratedPendingEventRoot
       (event_raw GeneratedPendingEventRoot)"
    by (rule scheduler_event_root_family_raw_rootD[
        OF event_rel EventRootUniverse_pendingI])
  have raw_source:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')
       (event_raw GeneratedPendingEventRoot)"
    using raw0 heap_eq
    by (simp add: GeneratedPendingEventRoot_def)
  have member:
    "abi_item_ptr (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<in>
       set (ring (event_raw GeneratedPendingEventRoot))"
    using raw_member by (simp add: event_item_raw_ptr_def)
  note source = scheduler_vListRemove_general_exact_state[
      OF raw_source member]
  show ?thesis
    using source
    by (simp add: resume_pending_event_remove_heap_def
        event_item_raw_ptr_def)
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_event_remove}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed pending Event remove has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed pending Event-remove premise ledger changed"
\<close>

end

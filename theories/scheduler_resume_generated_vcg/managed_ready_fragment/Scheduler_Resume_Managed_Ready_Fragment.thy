theory Scheduler_Resume_Managed_Ready_Fragment
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Two_Unlinks.Scheduler_Resume_Managed_Two_Unlinks"
begin

text \<open>
  Exact execution of the generated ready fragment after both pending-head
  removals.  The fragment retains the source's top-priority conditional and
  guarded ready-array selection before the generated insert-end call.
\<close>

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_ready_fragment_exact:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "bind
       (resume_pending_generated_raise_top D t)
       (\<lambda>_. bind
         (resume_pending_generated_ready_select D t)
         (\<lambda>pxList.
           Scheduler_V611_Delay_Translation.vListInsertEnd'
             pxList (scheduler_generic_item_ptr (sd_tcb_ptr D t)))) \<bullet>
       (scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c)
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
proof -
  let ?hG = "resume_pending_generic_remove_heap D t c"
  let ?rawG = "resume_pending_generic_raw_after C D t generic_raw"
  let ?top = "resume_pending_top_raised_state D t c"
  let ?q = "rpc_priority C t"
  let ?ready = "sr_ready generated_scheduler_roots ?q"
  let ?item = "scheduler_generic_item_ptr (sd_tcb_ptr D t)"

  have pure: "resume_pending_entry_rel C P"
    by (rule CursorGeneralStrongResumePendingManagedPhaseRel_pureD[OF phase])
  have alignment:
    "resume_pending_managed_phase_alignment
       a managed external generic_abs event_abs K_G K_E C P"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase])
  have t_context: "t \<in> rpc_live C"
    using pure tasks
    by (auto simp: resume_pending_entry_rel_def
        resume_pending_context_wf_def)
  have t_managed: "t \<in> managed"
    using t_context alignment
    by (simp add: resume_pending_managed_phase_alignment_def)

  have coverage:
    "GenericRootFamilyCoverage D ?hG GenericRootUniverse
       ?rawG
       (rps_generic_family
         (resume_pending_generic_unlink_state C t
           (resume_pending_event_unlink_state C t P)))
       managed K_G"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_generic_coverageD[
        OF phase tasks])
  have observation0:
    "scheduler_managed_task_observation_rel D ?hG a managed"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_observationD[
        OF phase tasks])
  have observation:
    "TaskObservationRel D ?hG (managed_scheduler_view a managed)"
    using observation0
    by (simp add: scheduler_managed_task_observation_rel_def)
  have t_view:
    "t \<in> sa_live (managed_scheduler_view a managed)"
    using t_managed by (simp add: managed_scheduler_view_def)
  have observed:
    "sa_priority (managed_scheduler_view a managed) t < 4 \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t))) =
       sa_priority (managed_scheduler_view a managed) t \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t)) < 4"
    using TaskObservationRel_liveD[OF observation t_view]
    by blast
  have priority:
    "unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t))) = ?q \<and>
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?hG (sd_tcb_ptr D t)) < 4"
    using observed alignment
    by (simp add: managed_scheduler_view_def
        resume_pending_managed_phase_alignment_def)
  have q_bound: "?q < 4"
    using observed alignment
    by (simp add: managed_scheduler_view_def
        resume_pending_managed_phase_alignment_def)

  have top_heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?top) = ?hG"
    by (simp add: resume_pending_top_raised_state_def Let_def)
  have top_priority:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?top))
         (sd_tcb_ptr D t)) < 4 \<and>
     unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?top))
         (sd_tcb_ptr D t))) = ?q"
    using priority top_heap by simp
  have select:
    "resume_pending_generated_ready_select D t \<bullet> ?top
     \<lbrace>\<lambda>r s.
       r = Result ?ready \<and> s = ?top \<and> c_guard ?ready
     \<rbrace>"
  proof -
    have destination:
      "array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False
         (unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?top))
             (sd_tcb_ptr D t)))) = ?ready"
      using top_priority generated_ready_root_is_array_index by simp
    have array_guard:
      "c_guard Scheduler_V611_Parse.pxReadyTasksLists_'"
      by (rule generated_ready_array_guard)
    have ready_guard: "c_guard ?ready"
      by (rule generated_ready_root_guard[OF q_bound])
    show ?thesis
      unfolding resume_pending_generated_ready_select_def
      apply runs_to_vcg
      using top_priority destination array_guard ready_guard
      by simp_all
  qed

  have target_ptr:
    "rpc_ready_root C ?q = abi_list_ptr ?ready"
    using alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
  have item_ptr:
    "abi_item_ptr ?item = resume_pending_generic_raw_ptr D t"
    by (rule resume_pending_generic_item_is_raw_ptr)
  have raw_item_ptr:
    "generic_item_raw_ptr D t = resume_pending_generic_raw_ptr D t"
    by (simp add: generic_item_raw_ptr_def
        resume_pending_generic_raw_ptr_def)
  have ready_root: "abi_list_ptr ?ready \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_readyI[OF q_bound])
  have raw0:
    "raw_xlist_rel ?hG (abi_list_ptr ?ready) (?rawG (abi_list_ptr ?ready))"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage ready_root])
  have ring_rel:
    "raw_xlist_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?top))
       (abi_list_ptr ?ready) (?rawG (rpc_ready_root C ?q))"
    using raw0 top_heap target_ptr by simp

  have pre:
    "scheduler_family_pre_rel ?hG GenericRootUniverse ?rawG managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have family: "raw_family_rel ?hG GenericRootUniverse ?rawG"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have geometry:
    "raw_family_insert_geometry GenericRootUniverse ?rawG
       (generic_item_raw_ptr D t)"
    by (rule GenericRootFamilyCoverage_managed_view_insert_geometry[
        OF coverage observation t_managed])
  have unlinked0:
    "raw_family_globally_unlinked ?hG GenericRootUniverse ?rawG
       (resume_pending_generic_raw_ptr D t)"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_globally_unlinkedD[
        OF phase tasks])
  have unlinked:
    "raw_family_globally_unlinked ?hG GenericRootUniverse ?rawG
       (generic_item_raw_ptr D t)"
    using unlinked0 raw_item_ptr by simp
  have fresh0:
    "raw_fresh_for_insert (abi_list_ptr ?ready)
       (ring (?rawG (abi_list_ptr ?ready)))
       (generic_item_raw_ptr D t)"
    by (rule raw_family_globally_unlinked_fresh_for_target[
        OF family unlinked ready_root geometry])
  have fresh:
    "raw_fresh_for_insert (abi_list_ptr ?ready)
       (ring (?rawG (rpc_ready_root C ?q))) (abi_item_ptr ?item)"
    using fresh0 target_ptr item_ptr raw_item_ptr by simp
  have insert:
    "Scheduler_V611_Delay_Translation.vListInsertEnd' ?ready ?item \<bullet> ?top
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
  proof -
    note source = scheduler_vListInsertEnd_general_exact_state[
      OF ring_rel fresh]
    show ?thesis
      apply (rule runs_to_weaken[OF source])
      using target_ptr item_ptr
      by (simp add: resume_pending_ready_inserted_state_def)
  qed
  have insert_array:
    "Scheduler_V611_Delay_Translation.vListInsertEnd'
       (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_' False ?q)
       ?item \<bullet> ?top
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c
     \<rbrace>"
    using insert by simp

  note raise = resume_pending_generated_raise_top_exact[
    where D=D and t=t and c=c]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF raise])
     apply clarsimp
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF select])
     apply clarsimp
    apply (rule runs_to_weaken[OF insert_array])
    by simp
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_ready_fragment_exact}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed ready-fragment theorem has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed ready-fragment premise ledger changed"
\<close>

end

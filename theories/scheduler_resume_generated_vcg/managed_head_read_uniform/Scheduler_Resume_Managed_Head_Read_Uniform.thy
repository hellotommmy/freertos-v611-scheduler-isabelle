theory Scheduler_Resume_Managed_Head_Read_Uniform
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Nonempty.Scheduler_Resume_Managed_Head_Read_Nonempty"
begin

text \<open>
  The empty branch needs only the represented pending count.  Joining it with
  the checked nonempty branch yields a uniform source read without adding a
  task-list premise.
\<close>

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_empty:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = []"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s. r = Result NULL \<and> s = c\<rbrace>"
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
  have empty:
    "ring (event_abs GeneratedPendingEventRoot) = []"
    using pure alignment tasks
    by (simp add: resume_pending_entry_rel_def
        resume_pending_managed_phase_alignment_def)
  note count_cursor = EventRootFamilyCoverage_count_cursorD[
      OF event_coverage EventRootUniverse_pendingI]
  have raw_zero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h GeneratedPendingEventRoot) = 0"
    using count_cursor empty by (simp add: unat_eq_0)
  have pending_raw_zero:
    "List_V611_Raw_Skip_Translation.xLIST_C.uxNumberOfItems_C
       (h_val ?h
         (abi_list_ptr Scheduler_V611_Parse.xPendingReadyList_')) = 0"
    using raw_zero by (simp add: GeneratedPendingEventRoot_def)
  have count0:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val ?h Scheduler_V611_Parse.xPendingReadyList_') = 0"
    using pending_raw_zero by (simp only: abi_list_count_h_val)
  have count:
    "Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         Scheduler_V611_Parse.xPendingReadyList_') = 0"
    using count0 heap_eq by simp
  show ?thesis
    unfolding resume_pending_generated_head_read_def
    apply runs_to_vcg
    using count by simp_all
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_uniform:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "resume_pending_generated_head_read \<bullet> c
     \<lbrace>\<lambda>r s. \<exists>u. r = Result u \<and> s = c \<and>
        PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
          u = resume_pending_next_head_tcb D (rpc_tasks C)\<rbrace>"
proof (cases "rpc_tasks C")
  case Nil
  show ?thesis
    apply (rule runs_to_weaken[
        OF CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_empty[
          OF phase Nil]])
    by (simp add: Nil resume_pending_next_head_tcb_def)
next
  case (Cons t rest)
  show ?thesis
    apply (rule runs_to_weaken[
        OF CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_nonempty[
          OF phase Cons]])
    by (simp add: Cons resume_pending_next_head_tcb_def)
qed

ML \<open>
  val empty =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_empty}
  val uniform =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_uniform}
  val _ =
    if null (Thm.hyps_of empty) andalso null (Thm.hyps_of uniform) then ()
    else error "managed pending uniform head read has hidden hypotheses"
  val _ =
    if length (Thm.prems_of empty) = 2 andalso
       length (Thm.prems_of uniform) = 1
    then ()
    else error "managed pending uniform head-read premise ledger changed"
\<close>

end

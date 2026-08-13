theory Scheduler_Resume_Managed_Two_Unlinks
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_Relational.Scheduler_Resume_Managed_Generic_Remove_Relational"
begin

text \<open>
  Exact source composition of the pending head's Event and Generic removals.
  Both source calls and the intermediate Event-removed state were established
  independently; this child contributes only their bind composition.
\<close>

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_two_unlinks_exact:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_event_item_ptr (sd_tcb_ptr D t)))
       (\<lambda>_. Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr (sd_tcb_ptr D t))) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result () \<and>
       s = scheduler_mem_state
         (resume_pending_generic_remove_heap D t c) c
     \<rbrace>"
proof -
  note event =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_event_remove[
      OF phase tasks]
  note generic =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_generic_remove_after_event[
      OF phase tasks]
  show ?thesis
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF event])
     apply clarsimp
    apply (rule runs_to_weaken[OF generic])
    by simp
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_two_unlinks_exact}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "managed two-unlink source theorem has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 2 then ()
    else error "managed two-unlink source premise ledger changed"
\<close>

end

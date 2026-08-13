theory Scheduler_Resume_Managed_Body
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_TCB_Guard.Scheduler_Resume_Managed_Head_TCB_Guard"
begin

text \<open>
  Group the literal generated body into the five checker-green managed source
  programs, then compose them without introducing a legacy gate or a re-entry
  assumption.
\<close>

lemma resume_pending_generated_body_managed_factor:
  "resume_pending_generated_body (sd_tcb_ptr D t, y) =
     do {
       guard (\<lambda>_. c_guard (sd_tcb_ptr D t));
       (do {
          Scheduler_V611_Delay_Translation.vListRemove'
            (scheduler_event_item_ptr (sd_tcb_ptr D t));
          Scheduler_V611_Delay_Translation.vListRemove'
            (scheduler_generic_item_ptr (sd_tcb_ptr D t))
        });
       (do {
          resume_pending_generated_raise_top D t;
          pxList \<leftarrow> resume_pending_generated_ready_select D t;
          Scheduler_V611_Delay_Translation.vListInsertEnd'
            pxList (scheduler_generic_item_ptr (sd_tcb_ptr D t))
        });
       y' \<leftarrow> resume_pending_generated_yield_join D t y;
       next_owner \<leftarrow> resume_pending_generated_head_read;
       return
         (PTR_COERCE(unit \<rightarrow>
            Scheduler_V611_Parse.tskTaskControlBlock_C) next_owner,
          y')
     }"
  unfolding resume_pending_generated_body_def
    resume_pending_generated_raise_top_def
    resume_pending_generated_ready_select_def
    resume_pending_generated_yield_join_def
    scheduler_event_item_ptr_def
    scheduler_generic_item_ptr_def
  by (simp add: bind_assoc)

theorem CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_exact:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and tasks: "rpc_tasks C = t # rest"
  shows
    "resume_pending_generated_body (sd_tcb_ptr D t, y) \<bullet> c
     \<lbrace>\<lambda>r s.
       r = Result
         (resume_pending_next_head_tcb D rest,
          if rpc_current_priority C \<le> rpc_priority C t
          then (1 :: int) else y) \<and>
       s = resume_pending_ready_inserted_state D C t generic_raw c \<and>
       GenericRootFamilyCoverage D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         GenericRootUniverse
         (resume_pending_drained_generic_fam C D t c generic_raw)
         (rps_generic_family (resume_pending_drained_snapshot C t P))
         managed K_G \<and>
       EventRootFamilyCoverage external D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
         (resume_pending_event_raw_after C D t event_raw)
         (rps_event_family (resume_pending_drained_snapshot C t P))
         managed K_E \<and>
       scheduler_managed_task_observation_rel D
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s)) a managed \<and>
       (\<forall>g\<in>GenericRootUniverse.
          \<forall>e\<in>EventRootUniverse external.
            raw_xlist_storage g
                (resume_pending_drained_generic_fam
                  C D t c generic_raw g) \<inter>
              raw_xlist_storage e
                (resume_pending_event_raw_after C D t event_raw e) = {}) \<and>
       resume_pending_control_frame c s \<and>
       unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' s) =
         rps_top (resume_pending_drained_snapshot C t P) \<and>
       resume_pending_loop_phase_inv C P [t] rest RP_LoopHead
         (resume_pending_yield_check_state C t
           (resume_pending_drained_snapshot C t P)) \<and>
       (((if rpc_current_priority C \<le> rpc_priority C t
            then (1 :: int) else y) \<noteq> 0) =
         ((y \<noteq> 0) \<or>
          rps_local_yield
            (resume_pending_yield_check_state C t
              (resume_pending_drained_snapshot C t P))))
     \<rbrace>"
proof -
  note entry =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_tcb_guard[
      OF phase tasks]
  note unlinks =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_two_unlinks_exact[
      OF phase tasks]
  note ready =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_ready_fragment_exact[
      OF phase tasks]
  note yield =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_yield_fragment_exact[
      where y=y, OF phase tasks]
  note head =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_next_head_read_exact[
      OF phase tasks]
  note generic_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_generic_coverageD[
      OF phase tasks]
  note event_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_event_coverageD[
      OF phase tasks]
  note observation_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_observationD[
      OF phase tasks]
  note cross_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_cross_storageD[
      OF phase tasks]
  note top_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_ready_insert_topD[
      OF phase tasks]
  note loop_head =
    CursorGeneralStrongResumePendingManagedPhaseRel_loop_head_after_oneD[
      OF phase tasks]
  note word_rel =
    CursorGeneralStrongResumePendingManagedPhaseRel_yield_word_encodingD[
      where y=y, OF phase tasks]
  have control_rel:
    "resume_pending_control_frame c
       (resume_pending_ready_inserted_state D C t generic_raw c)"
    by (rule resume_pending_ready_inserted_control_frame)

  show ?thesis
    unfolding resume_pending_generated_body_managed_factor
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF entry])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF unlinks])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF ready])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF yield])
     apply (clarsimp split del: if_split)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF head])
     apply (clarsimp split del: if_split)
    apply runs_to_vcg
    using generic_rel event_rel observation_rel cross_rel control_rel
      top_rel loop_head word_rel
    by (simp_all split del: if_split)
qed

ML \<open>
  val factor = @{thm resume_pending_generated_body_managed_factor}
  val body =
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_exact}
  val _ =
    if null (Thm.hyps_of factor) andalso null (Thm.prems_of factor) then ()
    else error "managed body factorization ledger changed"
  val _ =
    if null (Thm.hyps_of body) then ()
    else error "managed body theorem has hidden hypotheses"
  val _ =
    if length (Thm.prems_of body) = 2 then ()
    else error "managed body premise ledger changed"
\<close>

end

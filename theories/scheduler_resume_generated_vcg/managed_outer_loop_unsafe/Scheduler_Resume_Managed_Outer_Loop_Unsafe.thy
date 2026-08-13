theory Scheduler_Resume_Managed_Outer_Loop_Unsafe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry_Factor.Scheduler_Resume_Managed_Outer_Entry_Factor"
begin

text \<open>
  The managed partial-correctness theorems below need actual reachable
  cutpoints before they can be used to refute source success.  The Spec
  monad's @{const always_progress} excludes only bottom, so these structural
  facts add neither a scheduler invariant nor a termination premise.
\<close>

lemma resume_pending_generated_head_read_always_progress:
  "always_progress resume_pending_generated_head_read"
  unfolding resume_pending_generated_head_read_def
  by (intro always_progress_intros)

lemma resume_pending_generated_body_always_progress:
  "always_progress (resume_pending_generated_body pair)"
  apply (cases pair)
  unfolding resume_pending_generated_body_def
  by (intro always_progress_intros
      vListRemove_always_progress
      vListInsertEnd_always_progress
      resume_pending_generated_head_read_always_progress)

lemma resume_pending_generated_loop_always_progress:
  "always_progress
     (whileLoop resume_pending_generated_cond
       resume_pending_generated_body initial)"
  by (intro always_progress_intros
      resume_pending_generated_body_always_progress)

lemma resume_outer_generated_entry_prefix_always_progress:
  "always_progress resume_outer_generated_entry_prefix"
  unfolding resume_outer_generated_entry_prefix_def
    Scheduler_V611_Tick_Translation.eal6_port_enter_critical'_def
  by (intro always_progress_intros)

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_unsafe_no_run:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    and count:
      "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c"
    and pending_guard: "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and unsafe:
      "let drained = drain_pending_abs a
       in \<not> resume_missed_replay_horizon_safe
            (sa_missed_ticks drained) drained"
  shows "\<not> succeeds resume_outer_generated_entry_suffix c"
proof -
  have unsafe0:
    "\<not> resume_missed_replay_horizon_safe
       (sa_missed_ticks (drain_pending_abs a)) (drain_pending_abs a)"
    using unsafe unfolding Let_def by assumption

  note head =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_head_read_uniform[
      OF phase]
  obtain r_h s_h where head_reach:
      "reaches resume_pending_generated_head_read c r_h s_h"
    using Ex_reaches[OF head
      resume_pending_generated_head_read_always_progress]
    by blast
  have head_post:
    "\<exists>u. r_h = Result u \<and> s_h = c \<and>
       PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
         u = resume_pending_next_head_tcb D (rpc_tasks C)"
    by (rule runs_toD2[OF head head_reach])
  obtain u where head_result: "r_h = Result u"
      and head_state: "s_h = c"
      and head_ptr:
        "PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
           u = resume_pending_next_head_tcb D (rpc_tasks C)"
    using head_post by blast
  have head_reach0:
    "reaches resume_pending_generated_head_read c (Result u) c"
    using head_reach head_result head_state by simp

  note loop =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_pure[
      where y=0, OF phase]
  obtain r_l t where loop_reach:
      "reaches
        (whileLoop resume_pending_generated_cond
          resume_pending_generated_body
          (resume_pending_next_head_tcb D (rpc_tasks C), (0 :: int)))
        c r_l t"
    using Ex_reaches[OF loop
      resume_pending_generated_loop_always_progress]
    by blast
  from runs_toD2[OF loop loop_reach]
  obtain generic_raw' generic_abs' event_raw' event_abs'
      S' C' P' yw where
      loop_result: "r_l = Result (NULL, yw)"
    and final_phase:
      "CursorGeneralStrongResumePendingManagedPhaseRel
         D t (drain_pending_abs a) managed termination external
         generic_raw' generic_abs' event_raw' event_abs'
         K_G K_E S' C' P'"
    and final_empty: "rpc_tasks C' = []"
    by blast
  have loop_reach0:
    "reaches
      (whileLoop resume_pending_generated_cond
        resume_pending_generated_body
        (resume_pending_next_head_tcb D (rpc_tasks C), (0 :: int)))
      c (Result (NULL, yw)) t"
    using loop_reach loop_result by simp
  have continuation_no_run:
    "\<not> succeeds (resume_after_drain_continuation yw) t"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_bare_continuation_horizon_unsafe_no_run[
        where y=yw, OF final_phase final_empty unsafe0])

  show ?thesis
  proof
    assume suffix_success:
      "succeeds resume_outer_generated_entry_suffix c"
    have branch_success:
      "succeeds
        (do {
           guard (\<lambda>s. c_guard Scheduler_V611_Parse.xPendingReadyList_');
           ret \<leftarrow> resume_pending_generated_head_read;
           (pxTCB, xYieldRequired) \<leftarrow>
             whileLoop resume_pending_generated_cond
               resume_pending_generated_body
               (PTR_COERCE(unit \<rightarrow>
                  Scheduler_V611_Parse.tskTaskControlBlock_C) ret, 0);
           resume_after_drain_continuation xYieldRequired
         }) c"
      using suffix_success suspended count
      unfolding resume_outer_generated_entry_suffix_def
      by (simp add: succeeds_bind succeeds_condition_iff)
    have guard_reach:
      "reaches
        (guard (\<lambda>s. c_guard Scheduler_V611_Parse.xPendingReadyList_'))
        c (Result ()) c"
      using pending_guard by simp
    have after_guard_success:
      "succeeds
        (do {
           ret \<leftarrow> resume_pending_generated_head_read;
           (pxTCB, xYieldRequired) \<leftarrow>
             whileLoop resume_pending_generated_cond
               resume_pending_generated_body
               (PTR_COERCE(unit \<rightarrow>
                  Scheduler_V611_Parse.tskTaskControlBlock_C) ret, 0);
           resume_after_drain_continuation xYieldRequired
         }) c"
      using branch_success guard_reach
      by (auto simp: succeeds_bind)
    have after_head_success:
      "succeeds
        (do {
           (pxTCB, xYieldRequired) \<leftarrow>
             whileLoop resume_pending_generated_cond
               resume_pending_generated_body
               (PTR_COERCE(unit \<rightarrow>
                  Scheduler_V611_Parse.tskTaskControlBlock_C) u, 0);
           resume_after_drain_continuation xYieldRequired
         }) c"
      using after_guard_success head_reach0
      by (auto simp: succeeds_bind)
    have after_head_success0:
      "succeeds
        (do {
           (pxTCB, xYieldRequired) \<leftarrow>
             whileLoop resume_pending_generated_cond
               resume_pending_generated_body
               (resume_pending_next_head_tcb D (rpc_tasks C), 0);
           resume_after_drain_continuation xYieldRequired
         }) c"
      using after_head_success head_ptr by simp
    have continuation_success:
      "succeeds (resume_after_drain_continuation yw) t"
      using after_head_success0 loop_reach0
      by (auto simp: succeeds_bind)
    show False using continuation_no_run continuation_success by blast
  qed
qed

theorem
  CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_unsafe_no_run:
  assumes endpoint:
    "CursorGeneralStrongSchedulerModularEndpointRel
       D c a managed termination external"
    and outermost: "sa_suspend_depth a = 1"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
    and unsafe:
      "let entry = resume_outer_entry_abs a;
           normalized_entry = normalize_yield_count_abs entry;
           drained = drain_pending_abs normalized_entry
       in \<not> resume_missed_replay_horizon_safe
            (sa_missed_ticks drained) drained"
  shows
    "\<not> succeeds Scheduler_V611_Delay_Translation.xTaskResumeAll' c"
proof -
  let ?entry = "resume_outer_entry_abs a"
  let ?normalized_entry = "normalize_yield_count_abs ?entry"
  have unsafe0:
    "\<not> resume_missed_replay_horizon_safe
       (sa_missed_ticks (drain_pending_abs ?normalized_entry))
       (drain_pending_abs ?normalized_entry)"
    using unsafe unfolding Let_def by assumption
  have unsafe_internal:
    "\<not> resume_missed_replay_horizon_safe
       (sa_missed_ticks
         (drain_pending_abs
           (resume_outer_entry_abs (normalize_yield_count_abs a))))
       (drain_pending_abs
         (resume_outer_entry_abs (normalize_yield_count_abs a)))"
    using unsafe0
    unfolding normalize_yield_count_abs_resume_outer_entry
    by assumption
  note prefix =
    CursorGeneralStrongSchedulerModularEndpointRel_generated_outer_entry_phase[
      OF endpoint outermost current_safe, unfolded Let_def]
  obtain r_p t where prefix_reach:
      "reaches resume_outer_generated_entry_prefix c r_p t"
    using Ex_reaches[OF prefix
      resume_outer_generated_entry_prefix_always_progress]
    by blast
  from runs_toD2[OF prefix prefix_reach]
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where
      prefix_result: "r_p = Result ()"
    and suspended:
      "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' t = 0"
    and count:
      "0 < Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' t"
    and pending_guard: "c_guard Scheduler_V611_Parse.xPendingReadyList_'"
    and phase0:
      "CursorGeneralStrongResumePendingManagedPhaseRel
         D t (normalize_yield_count_abs (resume_outer_entry_abs a))
         managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S
         (resume_pending_canonical_managed_context
           (normalize_yield_count_abs (resume_outer_entry_abs a))
           managed external K_G K_E)
         (resume_pending_snapshot_of_one_due S)"
    by blast
  have phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D t (resume_outer_entry_abs (normalize_yield_count_abs a))
       managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       (resume_pending_canonical_managed_context
         (resume_outer_entry_abs (normalize_yield_count_abs a))
         managed external K_G K_E)
       (resume_pending_snapshot_of_one_due S)"
    using phase0
    unfolding normalize_yield_count_abs_resume_outer_entry
    by assumption
  have prefix_reach0:
    "reaches resume_outer_generated_entry_prefix c (Result ()) t"
    using prefix_reach prefix_result by simp
  have suffix_no_run:
    "\<not> succeeds resume_outer_generated_entry_suffix t"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_unsafe_no_run[
        unfolded Let_def,
        OF phase suspended count pending_guard unsafe_internal])
  show ?thesis
  proof
    assume root_success:
      "succeeds Scheduler_V611_Delay_Translation.xTaskResumeAll' c"
    have factor_success:
      "succeeds
        (bind resume_outer_generated_entry_prefix
          (\<lambda>_. resume_outer_generated_entry_suffix)) c"
      using root_success
      by (simp only: xTaskResumeAll_generated_entry_prefix_factor)
    have suffix_success:
      "succeeds resume_outer_generated_entry_suffix t"
      using factor_success prefix_reach0
      by (auto simp: succeeds_bind)
    show False using suffix_no_run suffix_success by blast
  qed
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error (label ^ " premise ledger changed")
    in () end

  val _ = audit_exact "managed pending head-read progress" 0
    @{thm resume_pending_generated_head_read_always_progress}
  val _ = audit_exact "managed pending body progress" 0
    @{thm resume_pending_generated_body_always_progress}
  val _ = audit_exact "managed pending loop progress" 0
    @{thm resume_pending_generated_loop_always_progress}
  val _ = audit_exact "managed outer entry-prefix progress" 0
    @{thm resume_outer_generated_entry_prefix_always_progress}
  val _ = audit_exact "managed normalized outer suffix unsafe" 5
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_generated_outer_suffix_horizon_unsafe_no_run}
  val _ = audit_exact "managed normalized public outer unsafe" 4
    @{thm CursorGeneralStrongSchedulerModularEndpointRel_generated_xTaskResumeAll_outermost_horizon_unsafe_no_run}
\<close>

end

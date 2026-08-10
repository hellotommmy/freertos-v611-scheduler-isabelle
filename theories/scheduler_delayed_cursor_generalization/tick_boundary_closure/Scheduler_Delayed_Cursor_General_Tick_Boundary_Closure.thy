theory Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Outer_Tick_Connector.Scheduler_Delayed_Cursor_General_Outer_Tick_Connector"
begin

section \<open>Public cursor-general tick boundary\<close>

text \<open>
  The generated tick theorem carries concrete family witnesses because its
  proof needs them.  At a public API boundary those witnesses are internal:
  callers need only know that some complete cursor-general representation
  exists and that the pending-ready entry condition holds.
\<close>

definition CursorGeneralStrongSchedulerPublicBoundaryRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongSchedulerPublicBoundaryRel D c a managed termination
       external \<longleftrightarrow>
     CursorGeneralStrongSchedulerEndpointRel D c a managed termination external \<and>
     tick_entry_pending_wf a"

definition CursorGeneralStrongVTaskIncrementTickPublicEntryRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external \<longleftrightarrow>
     (\<exists>generic_raw generic_abs event_raw event_abs K_G K_E S.
       CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S)"

definition CursorGeneralStrongVTaskIncrementTickPublicCompletePost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickPublicCompletePost D before a managed
       termination external r after \<longleftrightarrow>
     (\<exists>generic_raw generic_abs event_raw event_abs K_G K_E S.
       CursorGeneralStrongVTaskIncrementTickCompletePost D before a managed
         termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S r after) \<and>
     CursorGeneralStrongVTaskIncrementTickPublicEntryRel D after
       (task_increment_tick_modular_abs a) managed termination external"

lemma CursorGeneralStrongVTaskIncrementTickPublicEntryRel_iff_boundary:
  "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external \<longleftrightarrow>
   CursorGeneralStrongSchedulerPublicBoundaryRel D c a managed termination
       external"
  by (auto simp: CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def
      CursorGeneralStrongSchedulerPublicBoundaryRel_def
      CursorGeneralStrongVTaskIncrementTickEntryRel_def
      CursorGeneralStrongSchedulerEndpointRel_def)

lemma CursorGeneralStrongVTaskIncrementTickPublicEntryRel_iff_endpoint_pending:
  "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external \<longleftrightarrow>
   CursorGeneralStrongSchedulerEndpointRel D c a managed termination external \<and>
   tick_entry_pending_wf a"
  using CursorGeneralStrongVTaskIncrementTickPublicEntryRel_iff_boundary
  by (simp add: CursorGeneralStrongSchedulerPublicBoundaryRel_def)

lemma CursorGeneralStrongVTaskIncrementTickPublicEntryRelD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
  obtains generic_raw generic_abs event_raw event_abs K_G K_E S where
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
  using entry
  by (auto simp: CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def)

lemma CursorGeneralStrongSchedulerEndpointRel_public_tick_entryI:
  assumes endpoint:
    "CursorGeneralStrongSchedulerEndpointRel D c a managed termination external"
    and pending: "tick_entry_pending_wf a"
  shows
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using endpoint
    by (auto simp: CursorGeneralStrongSchedulerEndpointRel_def)
  show ?thesis
    unfolding CursorGeneralStrongVTaskIncrementTickPublicEntryRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    using snapshot pending
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
qed

section \<open>Boundary invariant preservation\<close>

lemma task_increment_tick_modular_abs_preserves_tick_entry_pending_wf:
  assumes entry: "tick_entry_pending_wf a"
  shows "tick_entry_pending_wf (task_increment_tick_modular_abs a)"
  using entry
  by (cases "sa_suspend_depth a = 0")
     (simp_all add: task_increment_tick_modular_abs_def
        tick_entry_pending_wf_def)

lemma CursorGeneralStrongVTaskIncrementTickCompletePost_public_reentry:
  assumes complete:
    "CursorGeneralStrongVTaskIncrementTickCompletePost D before a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S r after"
    and pending: "tick_entry_pending_wf a"
  shows
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D after
       (task_increment_tick_modular_abs a) managed termination external"
proof -
  have endpoint:
    "CursorGeneralStrongSchedulerEndpointRel D after
       (task_increment_tick_modular_abs a) managed termination external"
    using complete
    by (simp add: CursorGeneralStrongVTaskIncrementTickCompletePost_def)
  have pending_after:
    "tick_entry_pending_wf (task_increment_tick_modular_abs a)"
    by (rule task_increment_tick_modular_abs_preserves_tick_entry_pending_wf[OF pending])
  show ?thesis
    by (rule CursorGeneralStrongSchedulerEndpointRel_public_tick_entryI[
          OF endpoint pending_after])
qed

lemma CursorGeneralStrongVTaskIncrementTickPublicCompletePost_result_reentryD:
  assumes post:
    "CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
       termination external r t"
  shows
    "r = Result () \<and>
     CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t
       (task_increment_tick_modular_abs a) managed termination external"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where complete:
    "CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S r t"
    using post
    by (auto simp: CursorGeneralStrongVTaskIncrementTickPublicCompletePost_def)
  have result: "r = Result ()"
    using complete
    by (cases "sa_suspend_depth a = 0")
       (simp_all add: CursorGeneralStrongVTaskIncrementTickCompletePost_def
          CursorGeneralStrongVTaskIncrementTickSourcePost_def
          StrongSuspendedTickWordPost_def)
  have reentry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t
       (task_increment_tick_modular_abs a) managed termination external"
    using post
    by (simp add: CursorGeneralStrongVTaskIncrementTickPublicCompletePost_def)
  show ?thesis using result reentry by simp
qed

theorem CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
    and unlocked_defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
       termination external\<rbrace>"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where witnessed:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF entry] .
  have pending: "tick_entry_pending_wf a"
    using witnessed
    by (simp add: CursorGeneralStrongVTaskIncrementTickEntryRel_def)
  have run:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
       termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S\<rbrace>"
    by (rule
      CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete[
        OF witnessed unlocked_defined])
  show ?thesis
  proof (rule runs_to_weaken[OF run])
    fix r :: "(unit, unit) exception_or_result"
      and after :: Scheduler_V611_Parse.globals
    assume complete:
      "CursorGeneralStrongVTaskIncrementTickCompletePost D c a managed
        termination external generic_raw generic_abs event_raw event_abs
        K_G K_E S r after"
    have reentry:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D after
        (task_increment_tick_modular_abs a) managed termination external"
      by (rule CursorGeneralStrongVTaskIncrementTickCompletePost_public_reentry[
            OF complete pending])
    show
      "CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
        termination external r after"
      unfolding CursorGeneralStrongVTaskIncrementTickPublicCompletePost_def
      apply (intro conjI)
       apply (rule exI[where x=generic_raw])
       apply (rule exI[where x=generic_abs])
       apply (rule exI[where x=event_raw])
       apply (rule exI[where x=event_abs])
       apply (rule exI[where x=K_G])
       apply (rule exI[where x=K_E])
       apply (rule exI[where x=S])
       apply (rule complete)
      by (rule reentry)
  qed
qed

theorem CursorGeneralStrongVTaskIncrementTickPublicEntryRel_all_arithmetic_inputs:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel D c a managed
       termination external"
  shows
    "if sa_suspend_depth a = 0 \<and>
          classify_generated_tick_arithmetic c = TickWrapSignedOverflow
     then \<not> succeeds Scheduler_V611_Delay_Translation.vTaskIncrementTick' c
     else Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
       \<lbrace>CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
         termination external\<rbrace>"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where witnessed:
    "CursorGeneralStrongVTaskIncrementTickEntryRel D c a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongVTaskIncrementTickPublicEntryRelD[OF entry] .
  note classified =
    CursorGeneralStrongVTaskIncrementTickEntryRel_vTaskIncrementTick_all_arithmetic_inputs[
      OF witnessed]
  show ?thesis
  proof (cases
      "sa_suspend_depth a = 0 \<and>
       classify_generated_tick_arithmetic c = TickWrapSignedOverflow")
    case True
    then show ?thesis using classified by simp
  next
    case False
    have defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
      using False generated_unlocked_tick_arithmetic_class_iff by blast
    have run:
      "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
       \<lbrace>CursorGeneralStrongVTaskIncrementTickPublicCompletePost D c a managed
         termination external\<rbrace>"
      by (rule
        CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete[
          OF entry defined])
    show ?thesis
      by (simp only: if_not_P[OF False]; rule run)
  qed
qed

text \<open>
  This is a one-root public-boundary closure theorem.  It supports repeated
  tick-call composition because every successful result re-establishes the
  same existential entry relation.  It is not yet the five-root dispatcher or
  an interrupt-interleaving theorem.
\<close>

end

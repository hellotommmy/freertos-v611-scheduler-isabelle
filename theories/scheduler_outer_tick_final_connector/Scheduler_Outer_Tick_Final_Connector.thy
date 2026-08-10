theory Scheduler_Outer_Tick_Final_Connector
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Capstone.Scheduler_Unlocked_Tick_Prefix_Capstone"
begin

section \<open>Sequential outer tick connector\<close>

text \<open>
  This is a relation-universal theorem for the sequential generated
  vTaskIncrementTick' call.  It is not a reachability theorem for every legal
  scheduler state: StrongVTaskIncrementTickEntryRel includes
  tick_entry_pending_wf and retains the legacy cursor restrictions of
  StrongSchedulerSnapshotRel.  The generated signed-overflow guards are
  assumed defined only when the source takes the unlocked branch.

  The post retains the existing branch-specific public source post and also
  exposes one common abstract endpoint.  In the unlocked branch the former is
  the relational StrongUnlockedTickSourcePost; in the suspended branch it is
  the exact modular uxMissedTicks word update and frame in
  StrongSuspendedTickWordPost.  No expected concrete post-state, chosen
  due-prefix branch, task, priority, ring, root or cursor is supplied as a
  premise.
\<close>

theorem StrongVTaskIncrementTickEntryRel_vTaskIncrementTick_sequential_branch_complete:
  assumes entry:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked_defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       StrongVTaskIncrementTickSourcePost
         D c a M termination external r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) M termination external\<rbrace>"
proof (cases "sa_suspend_depth a = 0")
  case unlocked: True
  have snapshot:
    "StrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF entry])
  have source_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    by (rule StrongSchedulerSnapshotRel_source_suspension_zeroD[
          OF snapshot unlocked])
  have arithmetic_defined:
    "generated_unlocked_tick_arithmetic_defined c"
    by (rule unlocked_defined[OF unlocked])
  have unlocked_source:
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>StrongUnlockedTickSourcePost D a M termination external\<rbrace>"
    by (rule StrongVTaskIncrementTickEntryRel_one_due_tick_unlocked_source[
          OF entry unlocked arithmetic_defined])
  have outer:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>StrongUnlockedTickSourcePost D a M termination external\<rbrace>"
    unfolding one_due_vTaskIncrementTick_named_outer_source
    apply (simp only: runs_to_condition_iff)
    apply (simp add: source_zero)
    apply (rule runs_to_weaken[OF unlocked_source])
    by simp
  show ?thesis
  proof (rule runs_to_weaken[OF outer])
    fix r :: "(unit, unit) exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "StrongUnlockedTickSourcePost D a M termination external r t"
    have source_post:
      "StrongVTaskIncrementTickSourcePost
         D c a M termination external r t"
      using post unlocked
      by (simp add: StrongVTaskIncrementTickSourcePost_def)
    have endpoint:
      "StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) M termination external"
      using post unlocked
      by (simp add: StrongUnlockedTickSourcePost_def
          task_increment_tick_modular_abs_def)
    show
      "StrongVTaskIncrementTickSourcePost
         D c a M termination external r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) M termination external"
      using source_post endpoint by simp
  qed
next
  case suspended: False
  have snapshot:
    "StrongSchedulerSnapshotRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF entry])
  note modular = StrongSchedulerSnapshotRel_suspended_modular_endpoint[
    OF snapshot suspended]
  show ?thesis
  proof (rule runs_to_weaken[OF modular])
    fix r :: "(unit, unit) exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "StrongSuspendedTickWordPost c r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) M termination external"
    have source_post:
      "StrongVTaskIncrementTickSourcePost
         D c a M termination external r t"
      using post suspended
      by (simp add: StrongVTaskIncrementTickSourcePost_def)
    show
      "StrongVTaskIncrementTickSourcePost
         D c a M termination external r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a) M termination external"
      using source_post post by simp
  qed
qed

text \<open>
  The theorem is about bare sequential spec_monad semantics.  It neither
  inserts an interrupt step nor establishes ConcurrentCutpointInterface, so it
  makes no interrupt-concurrency or linearisation claim.
\<close>

end

theory Scheduler_Unlocked_Tick_Prefix_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Snapshot_Transport.Scheduler_Unlocked_Tick_Snapshot_Transport"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pointer_Bridge.Scheduler_Unlocked_Tick_Pointer_Bridge"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Complete.Scheduler_Due_Prefix_Managed_Arbitrary_While_Complete"
begin

section \<open>Universal generated-prefix post\<close>

text \<open>
  The post hides the source-discovered due/future split and returned pointer.
  The caller supplies neither a branch nor an expected concrete post-state.
  Every task, priority, tick, delayed-ring length, heap address and cursor
  admitted by the strong entry relation remains quantified.
\<close>

definition StrongUnlockedTickGeneratedPrefixPost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) exception_or_result
     \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongUnlockedTickGeneratedPrefixPost D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S r entry_c
       \<longleftrightarrow>
     (\<exists>entry now due_tasks future pxTCB.
       r = Result pxTCB \<and>
       StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
         before a entry_c entry now due_tasks future pxTCB M termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S)"

text \<open>
  The final composition theorem is stated below after the two independent
  transport bridges.  Its proof is intentionally thin: exact generated source
  supplies the concrete state and return value; the snapshot transport and
  pointer bridge identify that value with the canonical managed loop entry.
\<close>

lemma StrongVTaskIncrementTickEntryRel_canonical_managed_entry:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  obtains due_tasks future where
    "generated_current_delayed_readable
       (scheduler_tick_role_entry_state c)"
    and
    "StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
         c a (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         (sa_tick (tick_role_entry_abs a)) due_tasks future
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c))
         M termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S"
proof -
  obtain due_tasks future where
      due: "tick_due_sequence_abs a = map Generic due_tasks"
    and future:
      "due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic future"
    and snapshot:
      "case due_tasks of
         [] \<Rightarrow>
           StrongSchedulerSnapshotRel D
             (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
             M termination external generic_raw generic_abs event_raw
             event_abs K_G K_E S
       | task # due_tail \<Rightarrow>
           DueLoopSchedulerSnapshotRel D
             (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
             M termination external generic_raw generic_abs event_raw
             event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
             (map Generic (task # due_tail)) (map Generic future)"
    using StrongVTaskIncrementTickEntryRel_canonical_task_snapshot_transport[
      OF before unlocked arithmetic_defined]
    by blast
  have stable:
    "StrongSchedulerSnapshotRel D c a M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF before])
  have core: "core_wf a"
    by (rule StrongSchedulerSnapshotRel_coreD[OF stable])
  have loop0:
    "due_prefix_loop_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
    using core_wf_due_tick_loop_initial[OF core]
    by simp
  have loop:
    "due_prefix_loop_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (map Generic due_tasks)
       (map Generic future) (tick_role_entry_abs a)"
    using loop0 due future by simp
  have exit:
    "due_prefix_exit_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (map Generic due_tasks)
       (map Generic future) (tick_role_entry_abs a)
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
    using loop by (simp add: due_prefix_exit_inv_def)
  have split:
    "ring (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic due_tasks @ map Generic future"
    by (rule due_prefix_loop_inv_ringD[OF loop])
  have physical:
    "generated_current_delayed_readable
       (scheduler_tick_role_entry_state c) \<and>
     unlocked_tick_entry_pointer_rel D due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))"
    by (rule unlocked_tick_entry_snapshot_pointer_bridge[
          OF snapshot split])
  have assembler:
    "StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
       c a (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
       (sa_tick (tick_role_entry_abs a)) due_tasks future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))
       M termination external generic_raw generic_abs event_raw event_abs
       K_G K_E S"
    unfolding StrongUnlockedTickManagedEntryAssemblerRel_def
    using before unlocked exit physical snapshot by simp
  show thesis
    by (rule that[OF conjunct1[OF physical] assembler])
qed

theorem StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "generated_unlocked_tick_prefix_source \<bullet> c
     \<lbrace>StrongUnlockedTickGeneratedPrefixPost D c a M termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S\<rbrace>"
proof -
  obtain due_tasks future where
      readable:
        "generated_current_delayed_readable
           (scheduler_tick_role_entry_state c)"
    and assembler:
      "StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
         c a (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         (sa_tick (tick_role_entry_abs a)) due_tasks future
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c))
         M termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_canonical_managed_entry[
          OF before unlocked arithmetic_defined])
  note source = generated_unlocked_tick_prefix_source_defined_exact[
    OF arithmetic_defined readable]
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr)
         exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume exact:
      "r = Result
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c)) \<and>
       t = scheduler_tick_role_entry_state c"
    show
      "StrongUnlockedTickGeneratedPrefixPost D c a M termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S r t"
      unfolding StrongUnlockedTickGeneratedPrefixPost_def
      apply (rule exI[where x="tick_role_entry_abs a"])
      apply (rule exI[where x="sa_tick (tick_role_entry_abs a)"])
      apply (rule exI[where x=due_tasks])
      apply (rule exI[where x=future])
      apply (rule exI[where x=
        "generated_current_delayed_result
          (scheduler_tick_role_entry_state c)"])
      using exact assembler by simp
  qed
qed

theorem StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix_arithmetic_undefined_no_run:
  assumes arithmetic_undefined:
    "\<not> generated_unlocked_tick_arithmetic_defined c"
  shows "\<not> succeeds generated_unlocked_tick_prefix_source c"
  by (rule generated_unlocked_tick_prefix_source_undefined_has_no_run[
        OF arithmetic_undefined])

theorem StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix_all_arithmetic_inputs:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
  shows
    "(if generated_unlocked_tick_arithmetic_defined c
      then generated_unlocked_tick_prefix_source \<bullet> c
        \<lbrace>StrongUnlockedTickGeneratedPrefixPost D c a M termination
          external generic_raw generic_abs event_raw event_abs K_G K_E S\<rbrace>
      else \<not> succeeds generated_unlocked_tick_prefix_source c)"
proof (cases "generated_unlocked_tick_arithmetic_defined c")
  case True
  then show ?thesis
    using StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_prefix[
      OF before unlocked True] by simp
next
  case False
  then show ?thesis
    using generated_unlocked_tick_prefix_source_undefined_has_no_run[
      OF False] by simp
qed

section \<open>Canonical due ledger and endpoint projection\<close>

lemma StrongUnlockedTickManagedEntryAssemblerRel_due_sequenceD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
  shows "map Generic due_tasks = tick_due_sequence_abs a"
proof -
  have exit:
    "due_prefix_exit_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry
       (due_prefix_exit_phase_of (map Generic due_tasks)
         (map Generic future))
       (due_prefix_next_node_of (map Generic due_tasks)
         (map Generic future))"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_exitD[OF rel])
  have loop:
    "due_prefix_loop_inv now entry [] (map Generic due_tasks)
       (map Generic future) entry"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have due:
    "due_nodes now (current_delayed_ring entry) = map Generic due_tasks"
    using due_prefix_loop_inv_due_splitD[OF loop] by simp
  have exact:
    "entry = tick_role_entry_abs a \<and> now = sa_tick entry"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  show ?thesis
    using due exact
    by (simp add: tick_due_sequence_abs_def due_tick_sequence_abs_def Let_def)
qed

lemma StrongUnlockedTickManagedEntryAssemblerRel_complete_endpointD:
  assumes rel:
    "StrongUnlockedTickManagedEntryAssemblerRel D R before a entry_c entry
       now due_tasks future pxTCB M termination external generic_raw
       generic_abs event_raw event_abs K_G K_E S"
    and complete:
      "due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future entry_c M termination external K_G K_E t"
  shows
    "StrongUnlockedTickSourcePost D a M termination external (Result ()) t"
proof -
  have terminal_head:
    "due_prefix_strong_generated_terminal_head_post D now entry
       (map Generic due_tasks) future M termination external K_G K_E t"
    using complete
    by (simp add: due_prefix_strong_generated_complete_public_post_def)
  obtain terminal_pxTCB terminal_generic_raw terminal_event_raw terminal_S
    where head:
      "StrongDuePrefixLoopHeadRel D t
         (due_prefix_fold_state entry (map Generic due_tasks))
         M termination external terminal_generic_raw
         (ods_generic_family terminal_S) terminal_event_raw
         (ods_event_family terminal_S) K_G K_E terminal_S now entry
         (map Generic due_tasks) [] (map Generic future)
         (due_prefix_exit_phase_of [] (map Generic future))
         (due_prefix_next_node_of [] (map Generic future)) terminal_pxTCB"
    using terminal_head
    by (auto simp: due_prefix_strong_generated_terminal_head_post_def)
  have snapshot:
    "StrongSchedulerSnapshotRel D t
       (due_prefix_fold_state entry (map Generic due_tasks))
       M termination external terminal_generic_raw
       (ods_generic_family terminal_S) terminal_event_raw
       (ods_event_family terminal_S) K_G K_E terminal_S"
    by (rule StrongDuePrefixLoopHeadRel_snapshotD[OF head])
  have due: "map Generic due_tasks = tick_due_sequence_abs a"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_due_sequenceD[OF rel])
  have entry_eq: "entry = due_tick_entry_abs a"
    using StrongUnlockedTickManagedEntryAssemblerRel_exact_entryD[OF rel]
    by simp
  have current_eq:
    "due_prefix_fold_state entry (map Generic due_tasks) =
       tick_unlocked_abs a"
    using tick_unlocked_abs_is_due_prefix_fold[of a] entry_eq due
    by simp
  have endpoint:
    "StrongSchedulerEndpointRel D t (tick_unlocked_abs a)
       M termination external"
    unfolding StrongSchedulerEndpointRel_def
    apply (rule exI[where x=terminal_generic_raw])
    apply (rule exI[where x="ods_generic_family terminal_S"])
    apply (rule exI[where x=terminal_event_raw])
    apply (rule exI[where x="ods_event_family terminal_S"])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=terminal_S])
    using snapshot current_eq by simp
  show ?thesis
    using endpoint
    by (simp add: StrongUnlockedTickSourcePost_def)
qed

section \<open>Managed arbitrary-prefix pipeline\<close>

definition StrongUnlockedTickManagedFinallyPost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongUnlockedTickManagedFinallyPost D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S t
       \<longleftrightarrow>
     (\<exists>entry_c entry now due_tasks future pxTCB.
       StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
         before a entry_c entry now due_tasks future pxTCB M termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
       due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future entry_c M termination external K_G K_E t)"

lemma StrongUnlockedTickManagedFinallyPost_endpointD:
  assumes post:
    "StrongUnlockedTickManagedFinallyPost D before a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S t"
  shows
    "StrongUnlockedTickSourcePost D a M termination external (Result ()) t"
proof -
  obtain entry_c entry now due_tasks future pxTCB where
      rel:
        "StrongUnlockedTickManagedEntryAssemblerRel D
           generated_scheduler_roots before a entry_c entry now due_tasks
           future pxTCB M termination external generic_raw generic_abs
           event_raw event_abs K_G K_E S"
    and complete:
      "due_prefix_strong_generated_complete_public_post D now entry due_tasks
         future entry_c M termination external K_G K_E t"
    using post
    by (auto simp: StrongUnlockedTickManagedFinallyPost_def)
  show ?thesis
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_complete_endpointD[
          OF rel complete])
qed

text \<open>
  Bind the exact prefix to the already proved arbitrary managed
  while/finally theorem.  The intermediate task lists and pointer remain
  existential; in particular this theorem does not turn the prefix result
  into a caller-selected branch.
\<close>

theorem StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       StrongUnlockedTickManagedFinallyPost D c a M termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S t\<rbrace>"
proof -
  obtain due_tasks future where
      readable:
        "generated_current_delayed_readable
           (scheduler_tick_role_entry_state c)"
    and assembler:
      "StrongUnlockedTickManagedEntryAssemblerRel D generated_scheduler_roots
         c a (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         (sa_tick (tick_role_entry_abs a)) due_tasks future
         (generated_current_delayed_result
           (scheduler_tick_role_entry_state c))
         M termination external generic_raw generic_abs event_raw event_abs
         K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_canonical_managed_entry[
          OF before unlocked arithmetic_defined])
  have managed_entry:
    "ManagedStrongDuePrefixGeneratedEntryRel D generated_scheduler_roots
       (scheduler_tick_role_entry_state c)
       (sa_tick (tick_role_entry_abs a)) (tick_role_entry_abs a) due_tasks
       future
       (generated_current_delayed_result
         (scheduler_tick_role_entry_state c))
       M termination external K_G K_E"
    by (rule StrongUnlockedTickManagedEntryAssemblerRel_entryI[OF assembler])
  note prefix = generated_unlocked_tick_prefix_source_defined_exact[
    OF arithmetic_defined readable]
  note loop =
    ManagedStrongDuePrefixGeneratedEntryRel_finally_complete_exact[
      OF managed_entry refl]
  show ?thesis
    unfolding one_due_tick_unlocked_source_factor
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF prefix])
     apply clarsimp
    apply (rule runs_to_weaken[OF loop])
    apply clarsimp
    unfolding StrongUnlockedTickManagedFinallyPost_def
    apply (rule exI[where x="scheduler_tick_role_entry_state c"])
    apply (rule exI[where x="tick_role_entry_abs a"])
    apply (rule exI[where x="sa_tick (tick_role_entry_abs a)"])
    apply (rule exI[where x=due_tasks])
    apply (rule exI[where x=future])
    apply (rule exI[where x=
      "generated_current_delayed_result (scheduler_tick_role_entry_state c)"])
    using assembler
    by simp
qed

text \<open>
  No endpoint relation is assumed.  It is projected from the terminal strong
  loop head and the canonical due ledger, so this is the actual unlocked
  source endpoint for every arithmetic-defined strong entry state.
\<close>

theorem StrongVTaskIncrementTickEntryRel_one_due_tick_unlocked_source:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>StrongUnlockedTickSourcePost D a M termination external\<rbrace>"
proof -
  note pipeline =
    StrongVTaskIncrementTickEntryRel_generated_unlocked_tick_managed_finally[
      OF before unlocked arithmetic_defined]
  show ?thesis
  proof (rule runs_to_weaken[OF pipeline])
    fix r :: "(unit, unit) exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result () \<and>
       StrongUnlockedTickManagedFinallyPost D c a M termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S t"
    have endpoint:
      "StrongUnlockedTickSourcePost D a M termination external (Result ()) t"
      by (rule StrongUnlockedTickManagedFinallyPost_endpointD[OF
            conjunct2[OF post]])
    show "StrongUnlockedTickSourcePost D a M termination external r t"
      using post endpoint by simp
  qed
qed

end

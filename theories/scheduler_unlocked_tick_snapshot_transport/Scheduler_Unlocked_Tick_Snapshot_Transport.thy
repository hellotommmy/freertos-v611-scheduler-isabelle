theory Scheduler_Unlocked_Tick_Snapshot_Transport
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pure_Entry_Phase.Scheduler_Unlocked_Tick_Pure_Entry_Phase"
    "EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary.Scheduler_Tick_Entry_Strong_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Contract.Scheduler_Outer_Tick_Contract"
begin

text \<open>
  Transport the complete stable tick-entry snapshot across the exact generated
  arithmetic/role prefix.  The concrete transformer changes only the tick,
  the two delayed-role pointers on wrap, and the overflow counter.  Its
  abstract counterpart changes the corresponding tick/role/overflow fields.

  Heap-backed Generic and Event families, the managed/termination split,
  task observations, the current task, the boundary pins and cross-storage
  separation are all retained.  Stable @{const time_wf} is not asserted while
  a due head remains: the postcondition is
  @{const DueLoopSchedulerSnapshotRel}.  Only the zero-due branch is converted
  back to @{const StrongSchedulerSnapshotRel}.

  The generated signed-overflow definedness premise is deliberately present
  on the public transport theorems.  It gates existence of the source prefix;
  the component frame lemmas themselves do not need it.
\<close>

section \<open>Concrete and abstract component frames\<close>

lemma scheduler_tick_role_entry_state_heap_frame [simp]:
  "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_'
      (scheduler_tick_role_entry_state c)) =
   hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  by (simp add: scheduler_tick_role_entry_state_def Let_def)

lemma tick_role_entry_abs_managed_scheduler_view:
  "tick_role_entry_abs (managed_scheduler_view a managed) =
   managed_scheduler_view (tick_role_entry_abs a) managed"
  by (cases a)
     (simp add: tick_role_entry_abs_def due_tick_entry_abs_def
        managed_scheduler_view_def
        swap_delayed_roles_def Let_def)

lemma due_tick_entry_abs_managed_scheduler_view:
  "due_tick_entry_abs (managed_scheduler_view a managed) =
   managed_scheduler_view (due_tick_entry_abs a) managed"
  using tick_role_entry_abs_managed_scheduler_view[of a managed]
  by (simp only: tick_role_entry_abs_eq_due_tick_entry_abs)

lemma strong_managed_domain_rel_tick_role_entry:
  assumes domain: "strong_managed_domain_rel a termination managed"
  shows
    "strong_managed_domain_rel
       (tick_role_entry_abs a) termination managed"
  using domain
  by (simp add: strong_managed_domain_rel_def tick_role_entry_abs_def
      swap_delayed_roles_def Let_def)

lemma strong_generic_role_projection_tick_role_entry:
  assumes projection:
    "strong_generic_role_projection a termination generic_abs"
  shows
    "strong_generic_role_projection
       (tick_role_entry_abs a) termination generic_abs"
  using projection
  by (simp add: strong_generic_role_projection_def tick_role_entry_abs_def
      swap_delayed_roles_def Let_def)

lemma strong_event_role_projection_tick_role_entry:
  assumes projection:
    "strong_event_role_projection a managed external event_abs"
  shows
    "strong_event_role_projection
       (tick_role_entry_abs a) managed external event_abs"
  using projection
  by (simp add: strong_event_role_projection_def tick_role_entry_abs_def
      swap_delayed_roles_def Let_def)

lemma strong_wake_payload_projection_tick_role_entry:
  assumes projection: "strong_wake_payload_projection a K_G"
  shows "strong_wake_payload_projection (tick_role_entry_abs a) K_G"
  using projection
  by (simp add: strong_wake_payload_projection_def tick_role_entry_abs_def
      swap_delayed_roles_def Let_def)

lemma strong_one_due_snapshot_projection_tick_role_entry:
  assumes projection:
    "strong_one_due_snapshot_projection a generic_abs event_abs K_G K_E S"
  shows
    "strong_one_due_snapshot_projection (tick_role_entry_abs a)
       generic_abs event_abs K_G K_E S"
  using projection
  by (simp add: strong_one_due_snapshot_projection_def
      tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma scheduler_managed_task_observation_rel_tick_role_entry:
  assumes observation:
    "scheduler_managed_task_observation_rel D h a managed"
  shows
    "scheduler_managed_task_observation_rel D h
       (tick_role_entry_abs a) managed"
  using observation
  by (simp add: scheduler_managed_task_observation_rel_def
      managed_scheduler_view_def TaskObservationRel_def
      tick_role_entry_abs_def swap_delayed_roles_def Let_def)

lemma scheduler_managed_scalar_rel_tick_role_entry:
  assumes scalar: "scheduler_managed_scalar_rel c a managed"
  shows
    "scheduler_managed_scalar_rel
       (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs a) managed"
proof -
  have old:
    "scheduler_scalar_rel c (managed_scheduler_view a managed)"
    using scalar by (simp add: scheduler_managed_scalar_rel_def)
  have new:
    "scheduler_scalar_rel
       (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs (managed_scheduler_view a managed))"
    by (rule scheduler_scalar_rel_tick_role_entry_modular[OF old])
  show ?thesis
    unfolding scheduler_managed_scalar_rel_def
    using new
    by (simp only: tick_role_entry_abs_eq_due_tick_entry_abs
        due_tick_entry_abs_managed_scheduler_view)
qed

lemma scheduler_current_rel_tick_role_entry:
  assumes current: "scheduler_current_rel D c a"
  shows
    "scheduler_current_rel D (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs a)"
  using current
  by (cases "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0";
      cases "sa_current a")
     (simp_all add: scheduler_current_rel_def
        scheduler_tick_role_entry_state_def tick_role_entry_abs_def
        due_tick_entry_abs_def swap_delayed_roles_def Let_def)

lemma scheduler_boundary_rel_tick_role_entry:
  assumes boundary: "scheduler_boundary_rel c"
  shows "scheduler_boundary_rel (scheduler_tick_role_entry_state c)"
  using boundary
  by (simp add: scheduler_boundary_rel_def scheduler_tick_role_entry_state_def
      Let_def)

section \<open>Canonical due-loop snapshot\<close>

theorem StrongVTaskIncrementTickEntryRel_canonical_due_loop_snapshot:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "DueLoopSchedulerSnapshotRel D
       (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
       managed termination external generic_raw generic_abs event_raw
       event_abs K_G K_E S
       (sa_tick (tick_role_entry_abs a)) (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))"
proof -
  let ?entry_c = "scheduler_tick_role_entry_state c"
  let ?entry = "tick_role_entry_abs a"
  let ?now = "sa_tick ?entry"
  let ?due = "tick_due_sequence_abs a"
  let ?future =
    "due_future_nodes ?now (current_delayed_ring ?entry)"
  let ?old_h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?new_h =
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?entry_c)"

  note arithmetic_gate = arithmetic_defined
  note unlocked_gate = unlocked
  have stable:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF before])
  have core: "core_wf a"
    by (rule StrongSchedulerSnapshotRel_coreD[OF stable])
  have canonical:
    "due_loop_core_wf ?entry \<and>
     ordered_generic_delayed_ring (current_delayed_ring ?entry) \<and>
     due_loop_time_wf ?now ?due ?future ?entry"
    using core_wf_due_tick_entry_canonical_phase[OF core]
    by simp
  then have loop_core: "due_loop_core_wf ?entry"
    and loop_time: "due_loop_time_wf ?now ?due ?future ?entry"
    by blast+

  have domain:
    "strong_managed_domain_rel ?entry termination managed"
    by (rule strong_managed_domain_rel_tick_role_entry[
          OF StrongSchedulerSnapshotRel_domainD[OF stable]])
  have generic_coverage:
    "GenericRootFamilyCoverage D ?new_h GenericRootUniverse
       generic_raw generic_abs managed K_G"
    using StrongSchedulerSnapshotRel_generic_coverageD[OF stable]
    by simp
  have event_coverage:
    "EventRootFamilyCoverage external D ?new_h event_raw event_abs
       managed K_E"
    using StrongSchedulerSnapshotRel_event_coverageD[OF stable]
    by simp
  have generic_projection:
    "strong_generic_role_projection ?entry termination generic_abs"
    by (rule strong_generic_role_projection_tick_role_entry[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF stable]])
  have event_projection:
    "strong_event_role_projection ?entry managed external event_abs"
    by (rule strong_event_role_projection_tick_role_entry[
          OF StrongSchedulerSnapshotRel_event_projectionD[OF stable]])
  have wake_projection:
    "strong_wake_payload_projection ?entry K_G"
    by (rule strong_wake_payload_projection_tick_role_entry[
          OF StrongSchedulerSnapshotRel_wake_projectionD[OF stable]])
  have observation:
    "scheduler_managed_task_observation_rel D ?new_h ?entry managed"
  proof -
    have old:
      "scheduler_managed_task_observation_rel D ?old_h a managed"
      by (rule StrongSchedulerSnapshotRel_managed_observationD[OF stable])
    have framed:
      "scheduler_managed_task_observation_rel D ?old_h ?entry managed"
      by (rule scheduler_managed_task_observation_rel_tick_role_entry[OF old])
    show ?thesis using framed by simp
  qed
  have snapshot_projection:
    "strong_one_due_snapshot_projection ?entry generic_abs event_abs
       K_G K_E S"
    by (rule strong_one_due_snapshot_projection_tick_role_entry[
          OF StrongSchedulerSnapshotRel_snapshot_projectionD[OF stable]])
  have old_role:
    "scheduler_role_rel generated_scheduler_roots c a"
    and old_scalar: "scheduler_managed_scalar_rel c a managed"
    and old_current: "scheduler_current_rel D c a"
    and old_boundary: "scheduler_boundary_rel c"
    using StrongSchedulerSnapshotRel_role_scalar_currentD[OF stable]
    by blast+
  have tick: "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a"
    using StrongSchedulerSnapshotRel_scalar_pinsD[OF stable] by simp
  have role:
    "scheduler_role_rel generated_scheduler_roots ?entry_c ?entry"
    by (rule scheduler_tick_role_entry_preserves_role_rel[OF old_role tick])
  have scalar: "scheduler_managed_scalar_rel ?entry_c ?entry managed"
    by (rule scheduler_managed_scalar_rel_tick_role_entry[OF old_scalar])
  have current: "scheduler_current_rel D ?entry_c ?entry"
    by (rule scheduler_current_rel_tick_role_entry[OF old_current])
  have boundary: "scheduler_boundary_rel ?entry_c"
    by (rule scheduler_boundary_rel_tick_role_entry[OF old_boundary])
  have cross_storage:
    "\<forall>g\<in>GenericRootUniverse.
      \<forall>e\<in>EventRootUniverse external.
        raw_xlist_storage g (generic_raw g) \<inter>
          raw_xlist_storage e (event_raw e) = {}"
  proof (intro ballI)
    fix g e
    assume generic_root: "g \<in> GenericRootUniverse"
      and event_root: "e \<in> EventRootUniverse external"
    show
      "raw_xlist_storage g (generic_raw g) \<inter>
         raw_xlist_storage e (event_raw e) = {}"
      by (rule StrongSchedulerSnapshotRel_cross_storageD[
            OF stable generic_root event_root])
  qed
  show ?thesis
    unfolding DueLoopSchedulerSnapshotRel_def Let_def
    using loop_core loop_time domain generic_coverage event_coverage
      generic_projection event_projection wake_projection observation
      snapshot_projection role scalar current boundary cross_storage
      arithmetic_gate unlocked_gate
    by blast
qed

theorem StrongVTaskIncrementTickEntryRel_canonical_snapshot_case:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "case tick_due_sequence_abs a of
       [] \<Rightarrow>
         StrongSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
     | n # ns \<Rightarrow>
         DueLoopSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
           (sa_tick (tick_role_entry_abs a)) (n # ns)
           (due_future_nodes (sa_tick (tick_role_entry_abs a))
             (current_delayed_ring (tick_role_entry_abs a)))"
proof -
  note loop = StrongVTaskIncrementTickEntryRel_canonical_due_loop_snapshot[
    OF before unlocked arithmetic_defined]
  show ?thesis
  proof (cases "tick_due_sequence_abs a")
    case Nil
    have terminal_loop:
      "DueLoopSchedulerSnapshotRel D
         (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S (sa_tick (tick_role_entry_abs a)) []
         (due_future_nodes (sa_tick (tick_role_entry_abs a))
           (current_delayed_ring (tick_role_entry_abs a)))"
      using loop Nil by simp
    have stable:
      "StrongSchedulerSnapshotRel D
         (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
         managed termination external generic_raw generic_abs event_raw
         event_abs K_G K_E S"
      by (rule DueLoopSchedulerSnapshotRel_terminal_strong[
            OF terminal_loop refl])
    show ?thesis using Nil stable by simp
  next
    case (Cons n ns)
    show ?thesis using Cons loop by simp
  qed
qed

section \<open>Canonical task-list view\<close>

lemma all_generic_nodes_map:
  assumes generic: "\<forall>n\<in>set xs. \<exists>t. n = Generic t"
  shows "\<exists>tasks. xs = map Generic tasks"
  using generic
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  obtain task where n: "n = Generic task"
    using Cons.prems by auto
  have tail_generic: "\<forall>x\<in>set ns. \<exists>t. x = Generic t"
    using Cons.prems by auto
  obtain tasks where ns: "ns = map Generic tasks"
    using Cons.IH[OF tail_generic] by blast
  show ?case
    apply (rule exI[where x="task # tasks"])
    using n ns by simp
qed

corollary StrongVTaskIncrementTickEntryRel_canonical_task_snapshot_case:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
    and due:
      "tick_due_sequence_abs a = map Generic due_tasks"
    and future:
      "due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic future"
  shows
    "case due_tasks of
       [] \<Rightarrow>
         StrongSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S
     | task # due_tail \<Rightarrow>
         DueLoopSchedulerSnapshotRel D
           (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
           managed termination external generic_raw generic_abs event_raw
           event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
           (map Generic (task # due_tail)) (map Generic future)"
  using StrongVTaskIncrementTickEntryRel_canonical_snapshot_case[
      OF before unlocked arithmetic_defined]
    due future
  by (cases due_tasks) simp_all

theorem StrongVTaskIncrementTickEntryRel_canonical_task_snapshot_transport:
  assumes before:
    "StrongVTaskIncrementTickEntryRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked: "sa_suspend_depth a = 0"
    and arithmetic_defined:
      "generated_unlocked_tick_arithmetic_defined c"
  shows
    "\<exists>due_tasks future.
       tick_due_sequence_abs a = map Generic due_tasks \<and>
       due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)) =
           map Generic future \<and>
       (case due_tasks of
          [] \<Rightarrow>
            StrongSchedulerSnapshotRel D
              (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
              managed termination external generic_raw generic_abs event_raw
              event_abs K_G K_E S
        | task # due_tail \<Rightarrow>
            DueLoopSchedulerSnapshotRel D
              (scheduler_tick_role_entry_state c) (tick_role_entry_abs a)
              managed termination external generic_raw generic_abs event_raw
              event_abs K_G K_E S (sa_tick (tick_role_entry_abs a))
              (map Generic (task # due_tail)) (map Generic future))"
proof -
  have stable:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    by (rule StrongVTaskIncrementTickEntryRel_snapshotD[OF before])
  have core: "core_wf a"
    by (rule StrongSchedulerSnapshotRel_coreD[OF stable])
  have phase:
    "due_loop_time_wf (sa_tick (tick_role_entry_abs a))
       (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
    using core_wf_due_tick_entry_canonical_phase[OF core]
    by simp
  have due_generic:
    "\<forall>n\<in>set (tick_due_sequence_abs a). \<exists>t. n = Generic t"
    using phase by (auto simp: due_loop_time_wf_def)
  have future_generic:
    "\<forall>n\<in>set
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a))).
       \<exists>t. n = Generic t"
    using phase by (auto simp: due_loop_time_wf_def)
  obtain due_tasks where due:
    "tick_due_sequence_abs a = map Generic due_tasks"
    using all_generic_nodes_map[OF due_generic] by blast
  obtain future where future:
    "due_future_nodes (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring (tick_role_entry_abs a)) =
       map Generic future"
    using all_generic_nodes_map[OF future_generic] by blast
  note snapshots =
    StrongVTaskIncrementTickEntryRel_canonical_task_snapshot_case[
      OF before unlocked arithmetic_defined due future]
  show ?thesis
    apply (rule exI[where x=due_tasks])
    apply (rule exI[where x=future])
    using due future snapshots by blast
qed

end

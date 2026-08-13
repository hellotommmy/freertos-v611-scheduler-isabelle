theory Scheduler_Tick_Wrap_Modular
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat.Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated.Scheduler_One_Due_Task_Phases_Generated"
begin

text \<open>
  Arithmetic contract for every generated vTaskIncrementTick input.

  The two counters have different C semantics and must not share a no-wrap
  premise.

    * uxMissedTicks is unsigned.  UINT_MAX + 1 is a legal source transition
      to zero.  The existing scheduler_abs nat field can represent the source
      counter canonically, provided its update is modulo 2^32 rather than Suc.

    * xNumOfOverflows is signed.  Its generated increment is preceded by
      CParser guards and has no legal generated execution at INT_MAX.  That
      condition is needed only on the tick-wrap branch; it is a generated-C
      definedness condition, not a global runtime no-wrap assumption.

  No task, priority, root, heap, tick, counter, ring length or delayed role is
  fixed below.
\<close>

subsection \<open>Unsigned missed ticks: canonical modulo-2^32 nat view\<close>

definition missed_tick_mod_suc :: "nat \<Rightarrow> nat"
where
  "missed_tick_mod_suc n =
     unat ((of_nat n :: 32 word) + 1)"

lemma missed_tick_mod_suc_word:
  "missed_tick_mod_suc (unat (w :: 32 word)) = unat (w + 1)"
  by (simp add: missed_tick_mod_suc_def)

lemma missed_tick_mod_suc_max [simp]:
  "missed_tick_mod_suc (unat (-1 :: 32 word)) = 0"
  by (simp add: missed_tick_mod_suc_def)

lemma missed_tick_mod_suc_range:
  "missed_tick_mod_suc n < 2 ^ 32"
proof -
  have bound:
    "unat ((of_nat n :: 32 word) + 1) < 2 ^ LENGTH(32)"
    by (rule unat_lt2p)
  show ?thesis
    using bound by (simp add: missed_tick_mod_suc_def)
qed

definition task_increment_tick_modular_abs ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs"
where
  "task_increment_tick_modular_abs a =
     (if sa_suspend_depth a = 0
      then tick_unlocked_abs a
      else a\<lparr>sa_missed_ticks :=
             missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)"

lemma task_increment_tick_modular_abs_suspended:
  assumes suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "task_increment_tick_modular_abs a =
       a\<lparr>sa_missed_ticks :=
         missed_tick_mod_suc (sa_missed_ticks a)\<rparr>"
  using suspended
  by (simp add: task_increment_tick_modular_abs_def)

lemma task_increment_tick_modular_abs_suspended_max:
  assumes suspended: "sa_suspend_depth a \<noteq> 0"
      and max_word:
        "sa_missed_ticks a = unat (-1 :: 32 word)"
  shows
    "sa_missed_ticks (task_increment_tick_modular_abs a) = 0"
  using suspended max_word
  by (simp add: task_increment_tick_modular_abs_def)

definition scheduler_missed_tick_source_step ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "scheduler_missed_tick_source_step c =
     Scheduler_V611_Parse.globals.uxMissedTicks_'_update
       (\<lambda>w. w + 1) c"

lemma scheduler_missed_tick_source_step_value [simp]:
  "Scheduler_V611_Parse.globals.uxMissedTicks_'
     (scheduler_missed_tick_source_step c) =
   Scheduler_V611_Parse.globals.uxMissedTicks_' c + 1"
  by (simp add: scheduler_missed_tick_source_step_def)

lemma scheduler_scalar_rel_increment_missed_tick_modular:
  assumes rel: "scheduler_scalar_rel c a"
  shows
    "scheduler_scalar_rel
       (scheduler_missed_tick_source_step c)
       (a\<lparr>sa_missed_ticks :=
          missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)"
proof -
  have missed:
    "sa_missed_ticks a =
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c)"
    using rel by (simp add: scheduler_scalar_rel_def)
  have canonical:
    "Scheduler_V611_Parse.globals.uxMissedTicks_' c =
       of_nat (sa_missed_ticks a)"
    using missed by simp
  show ?thesis
    using rel canonical
    by (simp add: scheduler_scalar_rel_def
        scheduler_missed_tick_source_step_def missed_tick_mod_suc_def)
qed

lemma scheduler_managed_scalar_rel_increment_missed_tick_modular:
  assumes rel: "scheduler_managed_scalar_rel c a managed"
  shows
    "scheduler_managed_scalar_rel
       (scheduler_missed_tick_source_step c)
       (a\<lparr>sa_missed_ticks :=
          missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)
       managed"
proof -
  have base:
    "scheduler_scalar_rel c (managed_scheduler_view a managed)"
    using rel by (simp add: scheduler_managed_scalar_rel_def)
  have step:
    "scheduler_scalar_rel
       (scheduler_missed_tick_source_step c)
       ((managed_scheduler_view a managed)
          \<lparr>sa_missed_ticks :=
             missed_tick_mod_suc
               (sa_missed_ticks (managed_scheduler_view a managed))\<rparr>)"
    by (rule scheduler_scalar_rel_increment_missed_tick_modular[OF base])
  show ?thesis
    using step
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
qed

text \<open>
  This is the branch-complete scalar theorem.  In particular, there is no
  premise excluding UINT_MAX.  At UINT_MAX the post-state debt is zero,
  exactly as in the unsigned generated source.  An independent unbounded
  ghost arrival ledger may still count the interrupt, but it must not drive
  xTaskResumeAll replay after the physical counter has wrapped.
\<close>

theorem vTaskIncrementTick_suspended_modular_refines:
  assumes rel: "scheduler_scalar_rel c a"
      and suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c \<and>
       scheduler_scalar_rel t (task_increment_tick_modular_abs a)
     \<rbrace>"
proof -
  have source_suspended:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 0"
    using rel suspended
    by (auto simp: scheduler_scalar_rel_def)
  have exact:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c
     \<rbrace>"
    unfolding one_due_vTaskIncrementTick_named_outer_source
      scheduler_missed_tick_source_step_def
    apply runs_to_vcg
    using source_suspended
    apply simp
    done
  have scalar:
    "scheduler_scalar_rel
       (scheduler_missed_tick_source_step c)
       (a\<lparr>sa_missed_ticks :=
          missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)"
    using scheduler_scalar_rel_increment_missed_tick_modular[OF rel] .
  have abstract:
    "task_increment_tick_modular_abs a =
       a\<lparr>sa_missed_ticks :=
         missed_tick_mod_suc (sa_missed_ticks a)\<rparr>"
    using task_increment_tick_modular_abs_suspended[OF suspended] .
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using scalar abstract
    apply clarsimp
    done
qed

subsection \<open>Signed overflow count: conditional generated definedness\<close>

definition tick_overflow_increment_defined ::
  "Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "tick_overflow_increment_defined c \<longleftrightarrow>
     0 \<le> 2147483649 +
       sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) \<and>
     sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) < INT_MAX"

definition tick_unlocked_signed_defined ::
  "Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "tick_unlocked_signed_defined c \<longleftrightarrow>
     Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0 \<or>
     tick_overflow_increment_defined c"

datatype generated_tick_arithmetic_class =
    TickNoWrap
  | TickWrapDefined
  | TickWrapSignedOverflow

definition classify_generated_tick_arithmetic ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   generated_tick_arithmetic_class"
where
  "classify_generated_tick_arithmetic c =
     (if Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0
      then TickNoWrap
      else if tick_overflow_increment_defined c
      then TickWrapDefined
      else TickWrapSignedOverflow)"

lemma generated_tick_arithmetic_cases:
  "classify_generated_tick_arithmetic c = TickNoWrap \<longleftrightarrow>
       Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0"
  "classify_generated_tick_arithmetic c = TickWrapDefined \<longleftrightarrow>
       Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0 \<and>
       tick_overflow_increment_defined c"
  "classify_generated_tick_arithmetic c = TickWrapSignedOverflow \<longleftrightarrow>
       Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0 \<and>
       \<not> tick_overflow_increment_defined c"
  by (auto simp: classify_generated_tick_arithmetic_def)

lemma tick_unlocked_signed_defined_no_wrap:
  assumes no_wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0"
  shows "tick_unlocked_signed_defined c"
  using no_wrap by (simp add: tick_unlocked_signed_defined_def)

lemma tick_unlocked_signed_defined_wrap_iff:
  assumes wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
  shows
    "tick_unlocked_signed_defined c \<longleftrightarrow>
       tick_overflow_increment_defined c"
  using wrap by (simp add: tick_unlocked_signed_defined_def)

lemma tick_overflow_INT_MAX_not_defined:
  assumes max:
    "sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) = INT_MAX"
  shows "\<not> tick_overflow_increment_defined c"
  using max by (simp add: tick_overflow_increment_defined_def)

text \<open>
  Exact guarded source subprogram emitted around xNumOfOverflows++.  It is
  deliberately separate from the unsigned counter: failure of either guard
  means no legal generated execution, whereas unsigned wrap remains normal.
\<close>

definition generated_overflow_increment_source ::
  "(unit, unit, Scheduler_V611_Parse.globals) spec_monad"
where
  "generated_overflow_increment_source = do {
     guard
       (\<lambda>s. 0 \<le> 2147483649 +
         sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' s));
     guard
       (\<lambda>s. sint
         (Scheduler_V611_Parse.globals.xNumOfOverflows_' s) < INT_MAX);
     modify
       (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
         (\<lambda>w. w + 1))
   }"

theorem generated_overflow_increment_source_defined_result:
  assumes defined: "tick_overflow_increment_defined c"
  shows
    "generated_overflow_increment_source \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
         (\<lambda>w. w + 1) c
     \<rbrace>"
proof -
  have guard_lower:
    "0 \<le> 2147483649 +
       sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c)"
    and guard_upper:
    "sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) < INT_MAX"
    using defined
    by (simp_all add: tick_overflow_increment_defined_def)
  show ?thesis
  unfolding generated_overflow_increment_source_def
  apply runs_to_vcg
  using guard_lower apply simp
  using guard_upper apply simp
  done
qed

lemma generated_overflow_increment_source_not_succeeds:
  assumes undefined: "\<not> tick_overflow_increment_defined c"
  shows "\<not> succeeds generated_overflow_increment_source c"
  using undefined
  by (auto simp: generated_overflow_increment_source_def
      tick_overflow_increment_defined_def succeeds_bind)

corollary generated_overflow_increment_source_INT_MAX_has_no_run:
  assumes max:
    "sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) = INT_MAX"
  shows "\<not> succeeds generated_overflow_increment_source c"
  using generated_overflow_increment_source_not_succeeds
    tick_overflow_INT_MAX_not_defined[OF max]
  by blast

text \<open>
  The existing scalar relation already observes xNumOfOverflows modulo its
  32-bit representation: xNumOfOverflows_' c = of_nat (sa_overflows a).
  Therefore the arithmetic post-relation itself needs no nat bound.  The only
  bound is the source-language definedness guard needed to obtain a generated
  execution on the wrap branch.
\<close>

lemma scheduler_scalar_rel_overflow_increment_modular:
  assumes rel: "scheduler_scalar_rel c a"
  shows
    "Scheduler_V611_Parse.globals.xNumOfOverflows_'
       (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
         (\<lambda>w. w + 1) c) =
     of_nat (Suc (sa_overflows a))"
  using rel
  by (simp add: scheduler_scalar_rel_def of_nat_Suc)

lemma scheduler_scalar_rel_tick_role_entry_modular:
  assumes rel: "scheduler_scalar_rel c a"
  shows
    "scheduler_scalar_rel
       (scheduler_tick_role_entry_state c)
       (tick_role_entry_abs a)"
  using rel
  by (auto simp: scheduler_scalar_rel_def
      scheduler_tick_role_entry_state_def tick_role_entry_abs_def
      swap_delayed_roles_def Let_def of_nat_Suc)

definition tick_role_entry_checked_abs ::
  "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid scheduler_abs option"
where
  "tick_role_entry_checked_abs c a =
     (if tick_unlocked_signed_defined c
      then Some (tick_role_entry_abs a)
      else None)"

lemma tick_role_entry_checked_abs_success_iff:
  "tick_role_entry_checked_abs c a = Some b \<longleftrightarrow>
     tick_unlocked_signed_defined c \<and> b = tick_role_entry_abs a"
  by (auto simp: tick_role_entry_checked_abs_def)

lemma tick_role_entry_checked_abs_signed_failure_iff:
  "tick_role_entry_checked_abs c a = None \<longleftrightarrow>
     Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0 \<and>
     \<not> tick_overflow_increment_defined c"
  by (auto simp: tick_role_entry_checked_abs_def
      tick_unlocked_signed_defined_def)

text \<open>
  Necessary generated-execution gate for the actual unlocked source.  The
  proof unfolds only far enough to reach the emitted signed guards; later
  pointer, heap and loop obligations cannot restore an execution killed by
  signed-overflow guarding.
\<close>

lemma one_due_tick_unlocked_source_signed_overflow_has_no_run:
  assumes wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
      and undefined: "\<not> tick_overflow_increment_defined c"
  shows "\<not> succeeds one_due_tick_unlocked_source c"
  using wrap undefined
  unfolding one_due_tick_unlocked_source_def
  by (auto simp: tick_overflow_increment_defined_def succeeds_bind)

theorem one_due_tick_unlocked_source_success_implies_signed_defined:
  assumes run: "succeeds one_due_tick_unlocked_source c"
  shows "tick_unlocked_signed_defined c"
proof (rule ccontr)
  assume not_defined: "\<not> tick_unlocked_signed_defined c"
  then have wrap:
    "Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0"
    and counter_undefined:
    "\<not> tick_overflow_increment_defined c"
    by (auto simp: tick_unlocked_signed_defined_def)
  have "\<not> succeeds one_due_tick_unlocked_source c"
    using one_due_tick_unlocked_source_signed_overflow_has_no_run[
      OF wrap counter_undefined] .
  then show False using run by contradiction
qed

subsection \<open>Strong-snapshot suspended frame\<close>

lemma sa_tick_missed_tick_update [simp]:
  "sa_tick (a\<lparr>sa_missed_ticks := n\<rparr>) = sa_tick a"
  by simp

lemma sa_live_missed_tick_update [simp]:
  "sa_live (a\<lparr>sa_missed_ticks := n\<rparr>) = sa_live a"
  by simp

lemma core_wf_missed_tick_update [simp]:
  "core_wf (a\<lparr>sa_missed_ticks := n\<rparr>) = core_wf a"
proof -
  let ?a' = "a\<lparr>sa_missed_ticks := n\<rparr>"
  have tick_frame: "sa_tick ?a' = sa_tick a"
    by (rule sa_tick_missed_tick_update)
  have live_frame: "sa_live ?a' = sa_live a"
    by (rule sa_live_missed_tick_update)
  have ring_shape_frame: "ring_shape_wf ?a' = ring_shape_wf a"
    by (simp add: ring_shape_wf_def)
  have role_frame: "role_wf ?a' = role_wf a"
    by (simp add: role_wf_def)
  have membership_frame: "membership_wf ?a' = membership_wf a"
    by (simp add: membership_wf_def ready_task_set_def Let_def)
  have time_frame: "time_wf ?a' = time_wf a"
    unfolding time_wf_def ready_task_set_def current_delayed_ring_def
      overflow_delayed_ring_def delayed_key_agrees_def
    apply (simp only: sa_tick_missed_tick_update)
    by simp
  have ready_cache_frame: "ready_cache_wf ?a' = ready_cache_wf a"
    by (simp add: ready_cache_wf_def)
  have current_frame: "current_wf ?a' = current_wf a"
    unfolding current_wf_def
    apply (simp only: sa_live_missed_tick_update)
    by simp
  show ?thesis
    using ring_shape_frame role_frame membership_frame time_frame
      ready_cache_frame current_frame live_frame
    by (simp add: core_wf_def)
qed

lemma scheduler_managed_task_observation_rel_missed_tick_update [simp]:
  "scheduler_managed_task_observation_rel D h
      (a\<lparr>sa_missed_ticks := n\<rparr>) managed =
   scheduler_managed_task_observation_rel D h a managed"
  by (simp add: scheduler_managed_task_observation_rel_def
      managed_scheduler_view_def TaskObservationRel_def
      scheduler_abs.update_convs)

lemma scheduler_globals_current_missed_tick_update [simp]:
  "Scheduler_V611_Parse.globals.pxCurrentTCB_'
      (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c) =
   Scheduler_V611_Parse.globals.pxCurrentTCB_' c"
  by simp

lemma scheduler_current_rel_missed_tick_update [simp]:
  "scheduler_current_rel D (scheduler_missed_tick_source_step c)
      (a\<lparr>sa_missed_ticks := n\<rparr>) =
   scheduler_current_rel D c a"
  unfolding scheduler_current_rel_def scheduler_missed_tick_source_step_def
  apply (simp only: scheduler_globals_current_missed_tick_update)
  by simp

lemma StrongSchedulerSnapshotRel_increment_missed_tick_modular:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "StrongSchedulerSnapshotRel D
       (scheduler_missed_tick_source_step c)
       (a\<lparr>sa_missed_ticks :=
          missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)
       managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using StrongSchedulerSnapshotRel_role_scalar_currentD[OF rel] by simp
  have missed:
    "sa_missed_ticks a =
       unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c)"
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def managed_scheduler_view_def
        scheduler_scalar_rel_def)
  have canonical:
    "Scheduler_V611_Parse.globals.uxMissedTicks_' c =
       of_nat (sa_missed_ticks a)"
    using missed by simp
  show ?thesis
    using rel canonical
    unfolding StrongSchedulerSnapshotRel_def Let_def
    apply (simp only: scheduler_current_rel_missed_tick_update)
    by (simp add:
      scheduler_missed_tick_source_step_def
      strong_managed_domain_rel_def strong_generic_role_projection_def
      strong_event_role_projection_def strong_wake_payload_projection_def
      strong_one_due_snapshot_projection_def scheduler_role_rel_def
      scheduler_managed_scalar_rel_def managed_scheduler_view_def
      scheduler_scalar_rel_def
      scheduler_boundary_rel_def TaskObservationRel_def
      scheduler_managed_task_observation_rel_def missed_tick_mod_suc_def)
qed

theorem vTaskIncrementTick_suspended_modular_refines_strong_snapshot:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
      and suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c \<and>
       StrongSchedulerSnapshotRel D t
         (task_increment_tick_modular_abs a)
         managed termination external generic_raw generic_abs
         event_raw event_abs K_G K_E S
     \<rbrace>"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using StrongSchedulerSnapshotRel_role_scalar_currentD[OF rel] by simp
  have source_suspended:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 0"
    using scalar suspended
    by (auto simp: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
  have exact:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c
     \<rbrace>"
    unfolding one_due_vTaskIncrementTick_named_outer_source
      scheduler_missed_tick_source_step_def
    apply runs_to_vcg
    using source_suspended
    apply simp
    done
  have snapshot:
    "StrongSchedulerSnapshotRel D
       (scheduler_missed_tick_source_step c)
       (a\<lparr>sa_missed_ticks :=
          missed_tick_mod_suc (sa_missed_ticks a)\<rparr>)
       managed termination external generic_raw generic_abs
       event_raw event_abs K_G K_E S"
    using StrongSchedulerSnapshotRel_increment_missed_tick_modular[OF rel] .
  have abstract:
    "task_increment_tick_modular_abs a =
       a\<lparr>sa_missed_ticks :=
         missed_tick_mod_suc (sa_missed_ticks a)\<rparr>"
    using task_increment_tick_modular_abs_suspended[OF suspended] .
  show ?thesis
    apply (rule runs_to_weaken[OF exact])
    using snapshot abstract
    apply clarsimp
    done
qed

text \<open>
  Quantifier/contract ledger.

    * uxMissedTicks: every 32-bit word is legal; no no-wrap premise remains.
      scheduler_abs.sa_missed_ticks is the canonical unat view and the new
      suspended step is modulo 2^32.

    * xNumOfOverflows: the existing of_nat relation is already modular, but a
      successful generated tick-wrap step additionally requires
      tick_overflow_increment_defined.  No-wrap ticks require no such bound.

    * The INT_MAX/wrap state is not silently removed: it is represented by
      TickWrapSignedOverflow and tick_role_entry_checked_abs = None, matching
      the generated guard failure.

    * A total theorem over all raw bit-patterns must therefore classify
      success versus signed-overflow guard failure.  A theorem promising a
      successful generated execution for the latter state is false unless the
      C source/configuration is changed to an unsigned overflow ledger.

    * The legacy task_increment_tick_abs suspended branch and the concurrent
      EnvTick rule still use Suc.  They agree with this theory away from
      UINT_MAX, but neither may appear in the final all-input acceptance
      theorem.  The replay loop itself may continue to use nat subtraction:
      after every source boundary sa_missed_ticks is the canonical unat of the
      physical word, so wrapped zero correctly drives zero replay iterations.
\<close>

end

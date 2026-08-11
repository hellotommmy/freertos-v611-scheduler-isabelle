theory Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated.Scheduler_One_Due_Task_Phases_Generated"
begin

text \<open>
  Unregistered, build-lane-exclusive probe for the semantic fact needed by
  missed-tick replay.  The C parser exports its generated
  <open>vTaskIncrementTick_modifies<close> fact, but a modifies theorem only preserves
  the two proof-port words along one
  run.  Transport from a public shadow state also needs read noninterference:
  running after a fixed overlay must be the overlay-image of the shadow run.
\<close>

definition tick_port_overlay ::
  "32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> Scheduler_V611_Parse.globals"
where
  "tick_port_overlay depth mask c =
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
       (\<lambda>_. mask)
       (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
         (\<lambda>_. depth) c)"

definition tick_port_overlay_rel ::
  "32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "tick_port_overlay_rel depth mask c c0 \<longleftrightarrow>
     c = tick_port_overlay depth mask c0"

lemma tick_port_overlay_selectors [simp]:
  "Scheduler_V611_Parse.globals.eal6_port_critical_depth_'
      (tick_port_overlay depth mask c) = depth"
  "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'
      (tick_port_overlay depth mask c) = mask"
  "Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
      (tick_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  "Scheduler_V611_Parse.globals.uxMissedTicks_'
      (tick_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.uxMissedTicks_' c"
  by (simp_all add: tick_port_overlay_def)

lemma tick_port_overlay_idempotent [simp]:
  "tick_port_overlay depth mask (tick_port_overlay d m c) =
   tick_port_overlay depth mask c"
  by (simp add: tick_port_overlay_def)

lemma tick_port_overlay_missed_tick_update:
  "tick_port_overlay depth mask
      (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c) =
   Scheduler_V611_Parse.globals.uxMissedTicks_'_update f
      (tick_port_overlay depth mask c)"
  by (simp add: tick_port_overlay_def)

lemma tick_port_overlay_rel_post_state_iff:
  "rel_post_state
      (rel_prod (=) (tick_port_overlay_rel depth mask)) X Y
   \<longleftrightarrow>
   X = map_post_state
     (\<lambda>(r, s). (r, tick_port_overlay depth mask s)) Y"
  by (cases X; cases Y)
     (auto simp: rel_set_def tick_port_overlay_rel_def)

lemma tick_port_overlay_rel_spec_iff_run:
  fixes p ::
    "('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad"
  shows
    "rel_spec p p (tick_port_overlay depth mask c) c
       (rel_prod (=) (tick_port_overlay_rel depth mask))
     \<longleftrightarrow>
     run p (tick_port_overlay depth mask c) =
       map_post_state
         (\<lambda>(r, s). (r, tick_port_overlay depth mask s))
         (run p c)"
  by (simp add: rel_spec_def tick_port_overlay_rel_post_state_iff)

definition tick_port_overlay_bisim ::
  "32 word \<Rightarrow> 32 word \<Rightarrow>
   ('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad \<Rightarrow> bool"
where
  "tick_port_overlay_bisim depth mask p \<longleftrightarrow>
     rel_spec_monad (tick_port_overlay_rel depth mask) (=) p p"

lemma tick_port_overlay_bisim_iff_run:
  "tick_port_overlay_bisim depth mask p
   \<longleftrightarrow>
   (\<forall>c. run p (tick_port_overlay depth mask c) =
      map_post_state
        (\<lambda>(r, s). (r, tick_port_overlay depth mask s))
        (run p c))"
  unfolding tick_port_overlay_bisim_def
    rel_spec_monad_iff_rel_spec tick_port_overlay_rel_def
  by (auto simp: tick_port_overlay_rel_spec_iff_run)

lemma tick_port_overlay_bisim_yield:
  "tick_port_overlay_bisim depth mask (yield x)"
  by (simp add: tick_port_overlay_bisim_iff_run)

lemma tick_port_overlay_bisim_gets:
  assumes invariant:
    "\<And>c. f (tick_port_overlay depth mask c) = f c"
  shows "tick_port_overlay_bisim depth mask (gets f)"
  using invariant
  by (simp add: tick_port_overlay_bisim_iff_run)

lemma tick_port_overlay_bisim_guard:
  assumes invariant:
    "\<And>c. P (tick_port_overlay depth mask c) = P c"
  shows "tick_port_overlay_bisim depth mask (guard P)"
  using invariant
  by (simp add: tick_port_overlay_bisim_iff_run run_guard)

lemma tick_port_overlay_bisim_modify:
  assumes commute:
    "\<And>c. f (tick_port_overlay depth mask c) =
       tick_port_overlay depth mask (f c)"
  shows "tick_port_overlay_bisim depth mask (modify f)"
  using commute
  by (simp add: tick_port_overlay_bisim_iff_run)

lemma tick_port_overlay_bisim_condition:
  assumes invariant:
      "\<And>c. P (tick_port_overlay depth mask c) = P c"
    and left: "tick_port_overlay_bisim depth mask p"
    and right: "tick_port_overlay_bisim depth mask q"
  shows
    "tick_port_overlay_bisim depth mask (condition P p q)"
  using invariant left right
  by (simp add: tick_port_overlay_bisim_iff_run run_condition)

lemma tick_port_overlay_bisim_bind:
  fixes p ::
    "('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad"
  assumes head: "tick_port_overlay_bisim depth mask p"
    and tail: "\<And>x. tick_port_overlay_bisim depth mask (k x)"
  shows "tick_port_overlay_bisim depth mask (p >>= k)"
proof -
  let ?R = "tick_port_overlay_rel depth mask"
  have head':
    "rel_spec_monad ?R (rel_exception_or_result (=) (=)) p p"
    using head
    by (simp add: tick_port_overlay_bisim_def
        rel_exception_or_result_eq_conv)
  have tail':
    "rel_fun (=)
       (rel_spec_monad ?R (rel_exception_or_result (=) (=))) k k"
    using tail
    by (auto simp: rel_fun_def tick_port_overlay_bisim_def
        rel_exception_or_result_eq_conv)
  have
    "rel_spec_monad ?R (rel_exception_or_result (=) (=))
       (p >>= k) (p >>= k)"
    by (rule rel_spec_monad_bind_rel_exception_or_result[OF head' tail'])
  then show ?thesis
    by (simp add: tick_port_overlay_bisim_def
        rel_exception_or_result_eq_conv)
qed

lemma tick_port_overlay_suspended_branch_bisim:
  "tick_port_overlay_bisim depth mask
     (modify
       (Scheduler_V611_Parse.globals.uxMissedTicks_'_update
         (\<lambda>a. a + 1)))"
  by (rule tick_port_overlay_bisim_modify)
     (simp add: tick_port_overlay_missed_tick_update)

text \<open>
  This theorem reduces whole-function noninterference to exactly the unlocked
  named generated factor.  The suspended source branch is discharged here;
  no final-state frame premise is used.
\<close>

theorem vTaskIncrementTick_tick_port_overlay_bisim_from_unlocked:
  assumes unlocked:
    "tick_port_overlay_bisim depth mask one_due_tick_unlocked_source"
  shows
    "rel_spec_monad (tick_port_overlay_rel depth mask) (=)
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
proof -
  have whole:
    "tick_port_overlay_bisim depth mask
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
    unfolding one_due_vTaskIncrementTick_named_outer_source
    apply (rule tick_port_overlay_bisim_condition)
    subgoal by simp
    subgoal by (rule unlocked)
    subgoal by (rule tick_port_overlay_suspended_branch_bisim)
    done
  show ?thesis
    using whole by (simp add: tick_port_overlay_bisim_def)
qed

text \<open>
  Exact remaining rule for the next checker lane:

  @{term "tick_port_overlay_bisim depth mask
     one_due_tick_unlocked_source"}.

  It can be proved compositionally from the rules above plus corresponding
  bisimulations for the generated vListRemove' and vListInsertEnd' callees,
  followed by the named delayed-task while rule.  That obligation is strictly
  stronger than the parser's vTaskIncrementTick_modifies fact.
\<close>

end

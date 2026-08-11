theory Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure.Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure"
begin

section \<open>Proof-port overlay\<close>

text \<open>
  A generated tick replay inside xTaskResumeAll runs after the proof port has
  entered a critical section.  The public tick relation cannot describe that
  cutpoint because it pins both proof-port words to zero.  We retain the
  checker-green public state as a shadow and overlay only the critical depth
  and interrupt mask on the concrete state that actually executes.
\<close>

definition scheduler_port_overlay ::
  "32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "scheduler_port_overlay depth mask c =
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'_update
       (\<lambda>_. mask)
       (Scheduler_V611_Parse.globals.eal6_port_critical_depth_'_update
         (\<lambda>_. depth) c)"

definition scheduler_port_overlay_rel ::
  "32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "scheduler_port_overlay_rel depth mask c c0 \<longleftrightarrow>
     c = scheduler_port_overlay depth mask c0"

lemma scheduler_port_overlay_relI:
  "c = scheduler_port_overlay depth mask c0 \<Longrightarrow>
   scheduler_port_overlay_rel depth mask c c0"
  by (simp add: scheduler_port_overlay_rel_def)

lemma scheduler_port_overlay_relD:
  "scheduler_port_overlay_rel depth mask c c0 \<Longrightarrow>
   c = scheduler_port_overlay depth mask c0"
  by (simp add: scheduler_port_overlay_rel_def)

lemma scheduler_port_overlay_selectors [simp]:
  "Scheduler_V611_Parse.globals.eal6_port_critical_depth_'
      (scheduler_port_overlay depth mask c) = depth"
  "Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_'
      (scheduler_port_overlay depth mask c) = mask"
  "Scheduler_V611_Parse.globals.t_hrs_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.t_hrs_' c"
  "Scheduler_V611_Parse.globals.pxCurrentTCB_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.pxCurrentTCB_' c"
  "Scheduler_V611_Parse.globals.pxDelayedTaskList_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
  "Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c"
  "Scheduler_V611_Parse.globals.xTickCount_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.xTickCount_' c"
  "Scheduler_V611_Parse.globals.uxSchedulerSuspended_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c"
  "Scheduler_V611_Parse.globals.uxMissedTicks_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.uxMissedTicks_' c"
  "Scheduler_V611_Parse.globals.xNumOfOverflows_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.xNumOfOverflows_' c"
  "Scheduler_V611_Parse.globals.xSchedulerRunning_'
      (scheduler_port_overlay depth mask c) =
    Scheduler_V611_Parse.globals.xSchedulerRunning_' c"
  by (simp_all add: scheduler_port_overlay_def)

lemma scheduler_port_overlay_idempotent [simp]:
  "scheduler_port_overlay depth mask
      (scheduler_port_overlay depth' mask' c) =
    scheduler_port_overlay depth mask c"
  by (simp add: scheduler_port_overlay_def)

lemma scheduler_port_overlay_missed_tick_update:
  "scheduler_port_overlay depth mask
      (Scheduler_V611_Parse.globals.uxMissedTicks_'_update f c) =
    Scheduler_V611_Parse.globals.uxMissedTicks_'_update f
      (scheduler_port_overlay depth mask c)"
  by (simp add: scheduler_port_overlay_def)

lemma generated_unlocked_tick_arithmetic_defined_port_overlay [simp]:
  "generated_unlocked_tick_arithmetic_defined
      (scheduler_port_overlay depth mask c) =
    generated_unlocked_tick_arithmetic_defined c"
  by (simp add: generated_unlocked_tick_arithmetic_defined_def)

lemma classify_generated_tick_arithmetic_port_overlay [simp]:
  "classify_generated_tick_arithmetic
      (scheduler_port_overlay depth mask c) =
    classify_generated_tick_arithmetic c"
  by (simp add: classify_generated_tick_arithmetic_def
      tick_overflow_increment_defined_def)

section \<open>Protected cursor-general entry relation\<close>

definition CursorGeneralStrongVTaskIncrementTickProtectedEntryRel ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow> bool"
where
  "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth mask c a managed termination external \<longleftrightarrow>
     (\<exists>c0.
        c = scheduler_port_overlay depth mask c0 \<and>
        CursorGeneralStrongVTaskIncrementTickPublicEntryRel
          D c0 a managed termination external)"

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth mask c a managed termination external"
  obtains c0 where
    "c = scheduler_port_overlay depth mask c0"
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
       D c0 a managed termination external"
  using entry
  by (auto simp: CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def)

lemma CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_portD:
  assumes entry:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D depth mask c a managed termination external"
  shows
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = depth \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = mask"
  using entry
  by (auto simp: CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def)

section \<open>Relational transfer\<close>

definition scheduler_port_overlay_tick_bisim ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "scheduler_port_overlay_tick_bisim depth mask \<longleftrightarrow>
     rel_spec_monad (scheduler_port_overlay_rel depth mask) (=)
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'
       Scheduler_V611_Delay_Translation.vTaskIncrementTick'"

text \<open>
  This generic rule is the exact bridge needed from a checked run on the
  public shadow to the corresponding run at the protected cutpoint.  Its
  premise is semantic noninterference, not merely a final-state frame.
\<close>

lemma scheduler_port_overlay_rel_runs_to_transfer:
  fixes p ::
    "('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad"
  assumes bisim:
    "rel_spec_monad (scheduler_port_overlay_rel depth mask) (=) p p"
    and shadow: "p \<bullet> c0 \<lbrace>Q\<rbrace>"
  shows
    "p \<bullet> scheduler_port_overlay depth mask c0
       \<lbrace>\<lambda>r t. \<exists>t0.
          t = scheduler_port_overlay depth mask t0 \<and> Q r t0\<rbrace>"
proof -
  have state_rel:
    "scheduler_port_overlay_rel depth mask
       (scheduler_port_overlay depth mask c0) c0"
    by (simp add: scheduler_port_overlay_rel_def)
  have related:
    "rel_spec p p (scheduler_port_overlay depth mask c0) c0
       (rel_prod (=) (scheduler_port_overlay_rel depth mask))"
    by (rule rel_spec_monadD[OF bisim state_rel])
  have refined:
    "refines p p (scheduler_port_overlay depth mask c0) c0
       (rel_prod (=) (scheduler_port_overlay_rel depth mask))"
    by (rule rel_specD_refines1[OF related])
  note run = refinesD_runs_to[OF refined shadow]
  show ?thesis
    apply (rule runs_to_weaken[OF run])
    by (auto simp: scheduler_port_overlay_rel_def)
qed

theorem
  CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_sequential_branch_complete:
  assumes bisim: "scheduler_port_overlay_tick_bisim depth mask"
    and entry:
      "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
         D depth mask c a managed termination external"
    and unlocked_defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
      \<lbrace>\<lambda>r t.
        r = Result () \<and>
        CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
          D depth mask t (task_increment_tick_modular_abs a)
          managed termination external\<rbrace>"
proof -
  obtain c0 where c:
      "c = scheduler_port_overlay depth mask c0"
    and shadow_entry:
      "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
         D c0 a managed termination external"
    using CursorGeneralStrongVTaskIncrementTickProtectedEntryRelD[OF entry] .
  have shadow_defined:
    "sa_suspend_depth a = 0 \<Longrightarrow>
     generated_unlocked_tick_arithmetic_defined c0"
  proof -
    assume unlocked: "sa_suspend_depth a = 0"
    have "generated_unlocked_tick_arithmetic_defined c"
      by (rule unlocked_defined[OF unlocked])
    then show ?thesis using c by simp
  qed
  have shadow_run:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c0
      \<lbrace>CursorGeneralStrongVTaskIncrementTickPublicCompletePost
        D c0 a managed termination external\<rbrace>"
    by (rule
      CursorGeneralStrongVTaskIncrementTickPublicEntryRel_sequential_branch_complete[
        OF shadow_entry shadow_defined])
  have shadow_reentry:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c0
      \<lbrace>\<lambda>r t.
        r = Result () \<and>
        CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t
          (task_increment_tick_modular_abs a) managed termination external\<rbrace>"
  proof (rule runs_to_weaken[OF shadow_run])
    fix r :: "(unit, unit) exception_or_result"
      and t :: Scheduler_V611_Parse.globals
    assume post:
      "CursorGeneralStrongVTaskIncrementTickPublicCompletePost
         D c0 a managed termination external r t"
    show
      "r = Result () \<and>
       CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t
         (task_increment_tick_modular_abs a) managed termination external"
      by (rule
        CursorGeneralStrongVTaskIncrementTickPublicCompletePost_result_reentryD[
          OF post])
  qed
  have transferred:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet>
       scheduler_port_overlay depth mask c0
      \<lbrace>\<lambda>r t. \<exists>t0.
        t = scheduler_port_overlay depth mask t0 \<and>
        (r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t0
           (task_increment_tick_modular_abs a) managed termination external)\<rbrace>"
  proof -
    have bisim_rel:
      "rel_spec_monad (scheduler_port_overlay_rel depth mask) (=)
        Scheduler_V611_Delay_Translation.vTaskIncrementTick'
        Scheduler_V611_Delay_Translation.vTaskIncrementTick'"
      using bisim
      by (simp add: scheduler_port_overlay_tick_bisim_def)
    show ?thesis
      by (rule scheduler_port_overlay_rel_runs_to_transfer[
            OF bisim_rel shadow_reentry])
  qed
  have transferred_c:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
      \<lbrace>\<lambda>r t. \<exists>t0.
        t = scheduler_port_overlay depth mask t0 \<and>
        (r = Result () \<and>
         CursorGeneralStrongVTaskIncrementTickPublicEntryRel D t0
           (task_increment_tick_modular_abs a) managed termination external)\<rbrace>"
    using transferred c
    by simp
  show ?thesis
    apply (rule runs_to_weaken[OF transferred_c])
    by (auto simp: CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def)
qed

text \<open>
  The only open premise in the protected tick theorem is
  scheduler_port_overlay_tick_bisim.  It must be discharged against the named
  generated source, including its delayed-task while and both generated list
  callees.  A final-state modifies theorem alone is not sufficient because it
  does not establish that the program never branches on the overlaid words.
\<close>

end

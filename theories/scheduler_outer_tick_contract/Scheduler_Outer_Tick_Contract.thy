theory Scheduler_Outer_Tick_Contract
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While.Scheduler_Due_Prefix_Generated_While"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat.Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat"
    "EAL6_FreeRTOS_V611_Scheduler_Increment_Tick_Suspended_Refinement.Scheduler_V611_Increment_Tick_Suspended_Refinement"
    "EAL6_FreeRTOS_V611_Scheduler_Tick_Wrap_Modular.Scheduler_Tick_Wrap_Modular"
    "EAL6_FreeRTOS_V611_Scheduler_Concurrent_Contract_Interface.Scheduler_Concurrent_Contract_Interface"
begin

section \<open>Exact generated outer-source factor\<close>

text \<open>
  This is the generated unlocked prefix before the already checked arbitrary
  due-prefix while/finally factor.  It increments the modular tick word, swaps
  only the two delayed-root pointer roles at tick wrap, checks the generated
  signed-overflow guards, and reads the first delayed-list owner (or NULL).
  No runtime value, list length, task, priority, root, pointer or branch is
  fixed.
\<close>

definition generated_unlocked_tick_prefix_source ::
  "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr,
     Scheduler_V611_Parse.globals) spec_monad"
where
  "generated_unlocked_tick_prefix_source = do {
     modify
       (Scheduler_V611_Parse.globals.xTickCount_'_update (\<lambda>a. a + 1));
     condition
       (\<lambda>s. Scheduler_V611_Parse.globals.xTickCount_' s = 0)
       (do {
         pxTemp \<leftarrow> gets
           Scheduler_V611_Parse.globals.pxDelayedTaskList_';
         modify
           (\<lambda>s. s\<lparr>Scheduler_V611_Parse.globals.pxDelayedTaskList_' :=
             Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' s\<rparr>);
         modify
           (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
             (\<lambda>_. pxTemp));
         guard
           (\<lambda>s. 0 \<le> 2147483649 +
             sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' s));
         guard
           (\<lambda>s. sint
             (Scheduler_V611_Parse.globals.xNumOfOverflows_' s) < INT_MAX);
         modify
           (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update
             (\<lambda>a. a + 1))
       })
       skip;
     guard
       (\<lambda>s. c_guard
         (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s));
     ret \<leftarrow> condition
       (\<lambda>s. Scheduler_V611_Parse.xLIST_C.uxNumberOfItems_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
            (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)) \<noteq> 0)
       (do {
         guard
           (\<lambda>s. c_guard
             (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
               (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                 (h_val
                   (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                   (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s)))));
         guard
           (\<lambda>s. c_guard
             (PTR(Scheduler_V611_Parse.xMINI_LIST_ITEM_C)
               &(Scheduler_V611_Parse.globals.pxDelayedTaskList_' s
                 \<rightarrow>[''xListEnd_C''])));
         gets
           (\<lambda>s. Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
             (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
               (Scheduler_V611_Parse.xMINI_LIST_ITEM_C.pxNext_C
                 (Scheduler_V611_Parse.xLIST_C.xListEnd_C
                   (h_val
                     (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' s))
                     (Scheduler_V611_Parse.globals.pxDelayedTaskList_' s))))))
       })
       (return NULL);
     return
       (PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C) ret)
   }"

lemma one_due_tick_unlocked_source_factor:
  "one_due_tick_unlocked_source = do {
     pxTCB \<leftarrow> generated_unlocked_tick_prefix_source;
     due_prefix_generated_finally_loop pxTCB
   }"
  unfolding one_due_tick_unlocked_source_def
    generated_unlocked_tick_prefix_source_def
    due_prefix_generated_finally_loop_def
    due_prefix_generated_bare_loop_def
  by (simp add: bind_assoc)

section \<open>Defined C arithmetic versus all 32-bit inputs\<close>

text \<open>
  The two conjuncts below are the literal generated guards, not a scheduler
  state invariant.  They are consulted only when xTickCount wraps.  If they
  fail, the AutoCorres spec_monad guard has no successor; a partial-correctness
  runs_to statement must not be advertised as defined C execution.
\<close>

definition generated_unlocked_tick_arithmetic_defined ::
  "Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "generated_unlocked_tick_arithmetic_defined c \<longleftrightarrow>
     (Scheduler_V611_Parse.globals.xTickCount_' c + 1 \<noteq> 0 \<or>
      (0 \<le> 2147483649 +
         sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) \<and>
       sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) < INT_MAX))"

lemma generated_unlocked_tick_arithmetic_classification:
  "generated_unlocked_tick_arithmetic_defined c \<or>
   (Scheduler_V611_Parse.globals.xTickCount_' c + 1 = 0 \<and>
    (\<not> 0 \<le> 2147483649 +
       sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) \<or>
     \<not> sint (Scheduler_V611_Parse.globals.xNumOfOverflows_' c) <
       INT_MAX))"
  by (auto simp: generated_unlocked_tick_arithmetic_defined_def)

section \<open>Strong public endpoints\<close>

definition StrongSchedulerEndpointRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> bool"
where
  "StrongSchedulerEndpointRel D c a managed termination external \<longleftrightarrow>
     (\<exists>generic_raw generic_abs event_raw event_abs K_G K_E S.
       StrongSchedulerSnapshotRel D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S)"

lemma StrongSchedulerEndpointRel_public_pinsD:
  assumes endpoint:
    "StrongSchedulerEndpointRel D c a managed termination external"
  shows
    "scheduler_role_rel generated_scheduler_roots c a \<and>
     scheduler_managed_scalar_rel c a managed \<and>
     scheduler_current_rel D c a \<and>
     scheduler_boundary_rel c \<and>
     Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card managed"
proof -
  obtain generic_raw generic_abs event_raw event_abs K_G K_E S where rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    using endpoint
    by (auto simp: StrongSchedulerEndpointRel_def)
  note controls = StrongSchedulerSnapshotRel_role_scalar_currentD[OF rel]
  note scalars = StrongSchedulerSnapshotRel_scalar_pinsD[OF rel]
  show ?thesis using controls scalars by simp
qed

definition StrongUnlockedTickSourcePost ::
  "'tid scheduler_decode \<Rightarrow> 'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongUnlockedTickSourcePost D a managed termination external r t
       \<longleftrightarrow>
     r = Result () \<and>
     StrongSchedulerEndpointRel D t (tick_unlocked_abs a)
       managed termination external"

lemma StrongUnlockedTickSourcePost_public_effectsD:
  assumes post:
    "StrongUnlockedTickSourcePost D a managed termination external r t"
  shows
    "r = Result () \<and>
     scheduler_role_rel generated_scheduler_roots t (tick_unlocked_abs a) \<and>
     scheduler_managed_scalar_rel t (tick_unlocked_abs a) managed \<and>
     scheduler_current_rel D t (tick_unlocked_abs a) \<and>
     scheduler_boundary_rel t \<and>
     Scheduler_V611_Parse.globals.xTickCount_' t = sa_tick a + 1 \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' t) =
       sa_top_ready (tick_unlocked_abs a) \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' t =
       of_nat (sa_overflows (tick_unlocked_abs a)) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' t) =
       card managed"
proof -
  have result: "r = Result ()"
    using post by (simp add: StrongUnlockedTickSourcePost_def)
  have endpoint:
    "StrongSchedulerEndpointRel D t (tick_unlocked_abs a)
       managed termination external"
    using post by (simp add: StrongUnlockedTickSourcePost_def)
  note pins = StrongSchedulerEndpointRel_public_pinsD[OF endpoint]
  have tick: "sa_tick (tick_unlocked_abs a) = sa_tick a + 1"
    by (simp add: tick_unlocked_abs_def swap_delayed_roles_def Let_def)
  show ?thesis using result pins tick by simp
qed

text \<open>
  The suspended source branch is total for every uxMissedTicks word.  In
  particular, MAX_WORD is updated to zero.  This word-exact post deliberately
  does not claim the old nat-Suc abstraction at wrap; the modular abstract
  connector is a separate theorem.
\<close>

definition StrongSuspendedTickWordPost ::
  "Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongSuspendedTickWordPost c r t \<longleftrightarrow>
     r = Result () \<and>
     t = Scheduler_V611_Parse.globals.uxMissedTicks_'_update
       (\<lambda>n. n + 1) c \<and>
     Scheduler_V611_Parse.globals.uxMissedTicks_' t =
       Scheduler_V611_Parse.globals.uxMissedTicks_' c + 1 \<and>
     scheduler_increment_tick_suspended_frame c t"

lemma StrongSuspendedTickWordPost_max_word_wrapD:
  assumes post: "StrongSuspendedTickWordPost c r t"
    and max_word:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' c = (-1 :: 32 word)"
  shows "Scheduler_V611_Parse.globals.uxMissedTicks_' t = 0"
  using post max_word
  by (simp add: StrongSuspendedTickWordPost_def)

theorem StrongSchedulerSnapshotRel_suspended_modular_endpoint:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and suspended: "sa_suspend_depth a \<noteq> 0"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>r t.
       StrongSuspendedTickWordPost c r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a)
         managed termination external\<rbrace>"
proof -
  have source:
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>\<lambda>(r :: (unit, unit) exception_or_result) t.
       r = Result () \<and>
       t = scheduler_missed_tick_source_step c \<and>
       StrongSchedulerSnapshotRel D t
         (task_increment_tick_modular_abs a)
         managed termination external generic_raw generic_abs
         event_raw event_abs K_G K_E S\<rbrace>"
    by (rule vTaskIncrementTick_suspended_modular_refines_strong_snapshot[
          OF rel suspended])
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r :: "(unit, unit) exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result () \<and>
       t = scheduler_missed_tick_source_step c \<and>
       StrongSchedulerSnapshotRel D t
         (task_increment_tick_modular_abs a)
         managed termination external generic_raw generic_abs
         event_raw event_abs K_G K_E S"
    have word_post: "StrongSuspendedTickWordPost c r t"
      using post
      by (simp add: StrongSuspendedTickWordPost_def
          scheduler_missed_tick_source_step_def
          scheduler_increment_tick_suspended_frame_def)
    have endpoint:
      "StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a)
         managed termination external"
      unfolding StrongSchedulerEndpointRel_def
      apply (rule exI[where x = generic_raw])
      apply (rule exI[where x = generic_abs])
      apply (rule exI[where x = event_raw])
      apply (rule exI[where x = event_abs])
      apply (rule exI[where x = K_G])
      apply (rule exI[where x = K_E])
      apply (rule exI[where x = S])
      using post by blast
    show
      "StrongSuspendedTickWordPost c r t \<and>
       StrongSchedulerEndpointRel D t
         (task_increment_tick_modular_abs a)
         managed termination external"
      using word_post endpoint by simp
  qed
qed

definition StrongVTaskIncrementTickSourcePost ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> (unit, unit) exception_or_result \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongVTaskIncrementTickSourcePost D c a managed termination external r t
       \<longleftrightarrow>
     (if sa_suspend_depth a = 0
      then StrongUnlockedTickSourcePost D a managed termination external r t
      else StrongSuspendedTickWordPost c r t)"

lemma StrongSchedulerSnapshotRel_source_suspension_zeroD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and quiet: "sa_suspend_depth a = 0"
  shows "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
proof -
  have suspended_unat:
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
    using StrongSchedulerSnapshotRel_scalar_pinsD[OF rel] by simp
  have suspended_nat:
    "sa_suspend_depth a =
       unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c)"
    using suspended_unat by simp
  have canonical:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c =
       of_nat (sa_suspend_depth a)"
    using suspended_nat by simp
  show ?thesis using canonical quiet by simp
qed

lemma StrongSchedulerSnapshotRel_source_suspension_nonzeroD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and suspended: "sa_suspend_depth a \<noteq> 0"
  shows "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 0"
proof -
  have
    "unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a"
    using StrongSchedulerSnapshotRel_scalar_pinsD[OF rel] by simp
  then show ?thesis using suspended by auto
qed

theorem StrongSchedulerSnapshotRel_vTaskIncrementTick_branch_complete_reduction:
  assumes entry:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and unlocked_defined:
      "sa_suspend_depth a = 0 \<Longrightarrow>
       generated_unlocked_tick_arithmetic_defined c"
    and unlocked_source:
      "\<lbrakk>sa_suspend_depth a = 0;
         generated_unlocked_tick_arithmetic_defined c\<rbrakk> \<Longrightarrow>
       one_due_tick_unlocked_source \<bullet> c
       \<lbrace>StrongUnlockedTickSourcePost D a managed termination external\<rbrace>"
  shows
    "Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
     \<lbrace>StrongVTaskIncrementTickSourcePost
       D c a managed termination external\<rbrace>"
proof (cases "sa_suspend_depth a = 0")
  case True
  have source_zero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c = 0"
    by (rule StrongSchedulerSnapshotRel_source_suspension_zeroD[OF entry True])
  have defined: "generated_unlocked_tick_arithmetic_defined c"
    by (rule unlocked_defined[OF True])
  have unlocked:
    "one_due_tick_unlocked_source \<bullet> c
     \<lbrace>StrongUnlockedTickSourcePost D a managed termination external\<rbrace>"
    by (rule unlocked_source[OF True defined])
  show ?thesis
    unfolding one_due_vTaskIncrementTick_named_outer_source
    apply (simp only: runs_to_condition_iff)
    apply (simp add: source_zero)
    apply (rule runs_to_weaken[OF unlocked])
    using True by (simp add: StrongVTaskIncrementTickSourcePost_def)
next
  case False
  have source_nonzero:
    "Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c \<noteq> 0"
    by (rule StrongSchedulerSnapshotRel_source_suspension_nonzeroD[
          OF entry False])
  note exact = vTaskIncrementTick_suspended_result[OF source_nonzero]
  show ?thesis
  proof (rule runs_to_weaken[OF exact])
    fix r :: "(unit, unit) exception_or_result"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "r = Result () \<and>
       t = Scheduler_V611_Parse.globals.uxMissedTicks_'_update
         (\<lambda>n. n + 1) c"
    have frame: "scheduler_increment_tick_suspended_frame c t"
      using post by (simp add: scheduler_increment_tick_suspended_frame_def)
    have word:
      "Scheduler_V611_Parse.globals.uxMissedTicks_' t =
       Scheduler_V611_Parse.globals.uxMissedTicks_' c + 1"
      using post by simp
    have suspended_post: "StrongSuspendedTickWordPost c r t"
      using post frame word
      by (simp add: StrongSuspendedTickWordPost_def)
    show
      "StrongVTaskIncrementTickSourcePost
         D c a managed termination external r t"
      using False suspended_post
      by (simp add: StrongVTaskIncrementTickSourcePost_def)
  qed
qed

section \<open>Sequential call versus interrupt concurrency\<close>

text \<open>
  The runs_to theorem above is sequential generated-source semantics: there is
  no implicit ISR step between its source commands.  An interrupt-concurrent
  theorem needs an explicit linearisation transition and re-establishment of
  ConcurrentCutpointInterface.  The relation below states that separate
  abstract transition; it is intentionally not equated with runs_to.
\<close>

definition SequentialQuiescentTickContract ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow> bool"
where
  "SequentialQuiescentTickContract D c a managed termination external
       \<longleftrightarrow>
     StrongSchedulerEndpointRel D c a managed termination external \<and>
     sa_suspend_depth a = 0 \<and>
     generated_unlocked_tick_arithmetic_defined c \<and>
     (Scheduler_V611_Delay_Translation.vTaskIncrementTick' \<bullet> c
       \<lbrace>StrongUnlockedTickSourcePost
         D a managed termination external\<rbrace>)"

definition ConcurrentQuiescentTickLinearisation ::
  "'tid concurrent_scheduler_state \<Rightarrow>
   'tid concurrent_scheduler_state \<Rightarrow> bool"
where
  "ConcurrentQuiescentTickLinearisation before after \<longleftrightarrow>
     environment_window_open before \<and>
     cs_phase before = ConcurrentQuiescent \<and>
     sa_suspend_depth (cs_abs before) = 0 \<and>
     after = before\<lparr>cs_abs := tick_unlocked_abs (cs_abs before)\<rparr>"

lemma ConcurrentQuiescentTickLinearisation_frames_control_domain:
  assumes step: "ConcurrentQuiescentTickLinearisation before after"
  shows
    "cs_allocated after = cs_allocated before \<and>
     cs_termination after = cs_termination before \<and>
     cs_critical_depth after = cs_critical_depth before \<and>
     cs_interrupt_masked after = cs_interrupt_masked before \<and>
     cs_saved_masks after = cs_saved_masks before \<and>
     cs_phase after = cs_phase before \<and>
     cs_resume_yielded after = cs_resume_yielded before"
  using step
  by (simp add: ConcurrentQuiescentTickLinearisation_def)

text \<open>
  Remaining generated-source connectors are deliberately visible:

    * prove generated_unlocked_tick_prefix_source from a strong entry snapshot
      reaches the canonical due/future split and a strong generated-loop entry;
    * strengthen the arbitrary generated while post from its current terminal
      ledger to StrongSchedulerEndpointRel at tick_unlocked_abs;
    * discharge the literal signed guards for the claimed defined-execution
      domain, while retaining the guard-failure class for all other 32-bit
      states;
    * replace the suspended word post by the modular missed-tick abstraction,
      including MAX_WORD to zero, without reviving the old no-wrap premise;
    * for interrupt concurrency, prove the source call implements
      ConcurrentQuiescentTickLinearisation at one explicit linearisation point
      and restores ConcurrentCutpointInterface.  The sequential runs_to theorem
      alone does not establish that claim.
\<close>

end

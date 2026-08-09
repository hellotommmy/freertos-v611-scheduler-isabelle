theory Scheduler_Due_Prefix_Strong_Role_Wake_Ledgers
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector.Scheduler_Due_Prefix_Strong_Result_Components"
begin

text \<open>
  Pure semantic ledgers for one generated due-loop Result step.  Every task,
  priority, tick, ring, cursor, payload and delayed-role choice remains
  symbolic.  The only finite case split below is over the four configured
  ready-array slots of this frozen build.

  The first group records the exact scheduler_abs effect.  The second group
  proves that the independently staged one_due_reentry_snapshot denotes the
  same complete Generic-root family, including the unchanged suspended and
  termination roots.  No desired post-relation is assumed.
\<close>

section \<open>Exact abstract Generic-role and wake ledgers\<close>

lemma due_prefix_result_step_ready_at:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "sa_ready
       (due_prefix_result_step_abs entry processed (Generic task)) p =
     (if p = sa_priority current task
      then list_insert_end_abs (Generic task)
             (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w)
             (sa_ready current p)
      else sa_ready current p)"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: Let_def)

lemma due_prefix_result_step_delayed_a:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "sa_delayed_a
       (due_prefix_result_step_abs entry processed (Generic task)) =
     (if sa_current_role_a current
      then list_remove_abs (Generic task) (sa_delayed_a current)
      else sa_delayed_a current)"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: current_delayed_ring_def Let_def)

lemma due_prefix_result_step_delayed_b:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "sa_delayed_b
       (due_prefix_result_step_abs entry processed (Generic task)) =
     (if sa_current_role_a current
      then sa_delayed_b current
      else list_remove_abs (Generic task) (sa_delayed_b current))"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: current_delayed_ring_def Let_def)

lemma due_prefix_result_step_current_delayed:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "current_delayed_ring
       (due_prefix_result_step_abs entry processed (Generic task)) =
     list_remove_abs (Generic task) (current_delayed_ring current)"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: current_delayed_ring_def Let_def)

lemma due_prefix_result_step_overflow_delayed:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "overflow_delayed_ring
       (due_prefix_result_step_abs entry processed (Generic task)) =
     overflow_delayed_ring current"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: current_delayed_ring_def overflow_delayed_ring_def
        Let_def)

lemma due_prefix_result_step_suspended:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "sa_suspended
       (due_prefix_result_step_abs entry processed (Generic task)) =
     sa_suspended current"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: Let_def)

lemma due_prefix_result_step_wake_task:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "sa_wake
       (due_prefix_result_step_abs entry processed (Generic task)) task =
     None"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
  by (cases "sa_current_role_a current")
     (simp_all add: Let_def)

lemma due_prefix_result_step_wake_other:
  assumes current: "current = due_prefix_fold_state entry processed"
    and different: "u \<noteq> task"
  shows
    "sa_wake
       (due_prefix_result_step_abs entry processed (Generic task)) u =
     sa_wake current u"
  using due_prefix_result_step_generic_state_eq[OF current, where task=task]
    different
  by (cases "sa_current_role_a current")
     (simp_all add: Let_def)

theorem due_prefix_result_step_generic_role_wake_ledger:
  assumes current: "current = due_prefix_fold_state entry processed"
  shows
    "(\<forall>p.
       sa_ready
         (due_prefix_result_step_abs entry processed (Generic task)) p =
       (if p = sa_priority current task
        then list_insert_end_abs (Generic task)
               (case sa_wake current task of
                  None \<Rightarrow> 0
                | Some w \<Rightarrow> w)
               (sa_ready current p)
        else sa_ready current p)) \<and>
     current_delayed_ring
       (due_prefix_result_step_abs entry processed (Generic task)) =
       list_remove_abs (Generic task) (current_delayed_ring current) \<and>
     overflow_delayed_ring
       (due_prefix_result_step_abs entry processed (Generic task)) =
       overflow_delayed_ring current \<and>
     sa_suspended
       (due_prefix_result_step_abs entry processed (Generic task)) =
       sa_suspended current \<and>
     sa_wake
       (due_prefix_result_step_abs entry processed (Generic task)) task =
       None \<and>
     (\<forall>u. u \<noteq> task \<longrightarrow>
       sa_wake
         (due_prefix_result_step_abs entry processed (Generic task)) u =
       sa_wake current u)"
  using due_prefix_result_step_ready_at[OF current]
    due_prefix_result_step_current_delayed[OF current]
    due_prefix_result_step_overflow_delayed[OF current]
    due_prefix_result_step_suspended[OF current]
    due_prefix_result_step_wake_task[OF current]
    due_prefix_result_step_wake_other[OF current]
  by blast

corollary DueLoopStrongHeadRel_result_step_wake_exact:
  assumes strong:
      "DueLoopStrongHeadRel D c current managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S
         now entry processed (Generic task # remaining) future
         phase next pxTCB"
  shows
    "sa_wake
       (due_prefix_result_step_abs entry processed (Generic task)) task =
       None \<and>
     (\<forall>u. u \<noteq> task \<longrightarrow>
       sa_wake
         (due_prefix_result_step_abs entry processed (Generic task)) u =
       sa_wake current u)"
proof -
  have exit:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    by (rule DueLoopStrongHeadRel_exitD[OF strong])
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have current:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  show ?thesis
    using due_prefix_result_step_wake_task[OF current]
      due_prefix_result_step_wake_other[OF current]
    by blast
qed

section \<open>Frozen Generic-root role injectivity\<close>

lemma GeneratedGenericRootRoles_readyI:
  assumes bound: "p < 4"
  shows "GenericReadyRoot p \<in> GeneratedGenericRootRoles"
  using generated_ready_role_cases[OF bound]
  by (auto simp: GeneratedGenericRootRoles_def)

lemma generated_generic_role_raw_root_injD:
  assumes left: "r \<in> GeneratedGenericRootRoles"
    and right: "s \<in> GeneratedGenericRootRoles"
    and equal:
      "abi_list_ptr (generated_generic_role_source_root r) =
       abi_list_ptr (generated_generic_role_source_root s)"
  shows "r = s"
proof -
  have composed:
    "(abi_list_ptr \<circ> generated_generic_role_source_root) r =
     (abi_list_ptr \<circ> generated_generic_role_source_root) s"
    using equal by simp
  show ?thesis
    by (rule inj_onD[OF generated_generic_role_raw_root_inj
          composed left right])
qed

lemma generated_ready_raw_root_inj:
  assumes p_bound: "p < 4"
    and q_bound: "q < 4"
    and equal:
      "abi_list_ptr (sr_ready generated_scheduler_roots p) =
       abi_list_ptr (sr_ready generated_scheduler_roots q)"
  shows "p = q"
proof -
  have roles:
    "GenericReadyRoot p = GenericReadyRoot q"
    by (rule generated_generic_role_raw_root_injD[
          OF GeneratedGenericRootRoles_readyI[OF p_bound]
             GeneratedGenericRootRoles_readyI[OF q_bound]])
       (use equal in simp)
  show ?thesis using roles by simp
qed

lemma generated_ready_raw_root_neq_delayed_a:
  assumes bound: "p < 4"
  shows
    "abi_list_ptr (sr_ready generated_scheduler_roots p) \<noteq>
     abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
proof
  assume equal:
    "abi_list_ptr (sr_ready generated_scheduler_roots p) =
     abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
  have delayed: "GenericDelayedARoot \<in> GeneratedGenericRootRoles"
    by (simp add: GeneratedGenericRootRoles_def)
  have roots_equal:
      "abi_list_ptr
         (generated_generic_role_source_root (GenericReadyRoot p)) =
       abi_list_ptr
         (generated_generic_role_source_root GenericDelayedARoot)"
    using equal by simp
  have
    "GenericReadyRoot p = GenericDelayedARoot"
    by (rule generated_generic_role_raw_root_injD[
          OF GeneratedGenericRootRoles_readyI[OF bound]
             delayed roots_equal])
  then show False by simp
qed

lemma generated_ready_raw_root_neq_delayed_b:
  assumes bound: "p < 4"
  shows
    "abi_list_ptr (sr_ready generated_scheduler_roots p) \<noteq>
     abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
proof
  assume equal:
    "abi_list_ptr (sr_ready generated_scheduler_roots p) =
     abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
  have delayed: "GenericDelayedBRoot \<in> GeneratedGenericRootRoles"
    by (simp add: GeneratedGenericRootRoles_def)
  have roots_equal:
      "abi_list_ptr
         (generated_generic_role_source_root (GenericReadyRoot p)) =
       abi_list_ptr
         (generated_generic_role_source_root GenericDelayedBRoot)"
    using equal by simp
  have
    "GenericReadyRoot p = GenericDelayedBRoot"
    by (rule generated_generic_role_raw_root_injD[
          OF GeneratedGenericRootRoles_readyI[OF bound]
             delayed roots_equal])
  then show False by simp
qed

lemma generated_ready_raw_root_neq_suspended:
  assumes bound: "p < 4"
  shows
    "abi_list_ptr (sr_ready generated_scheduler_roots p) \<noteq>
     abi_list_ptr (sr_suspended generated_scheduler_roots)"
proof
  assume equal:
    "abi_list_ptr (sr_ready generated_scheduler_roots p) =
     abi_list_ptr (sr_suspended generated_scheduler_roots)"
  have suspended: "GenericSuspendedRoot \<in> GeneratedGenericRootRoles"
    by (simp add: GeneratedGenericRootRoles_def)
  have roots_equal:
      "abi_list_ptr
         (generated_generic_role_source_root (GenericReadyRoot p)) =
       abi_list_ptr
         (generated_generic_role_source_root GenericSuspendedRoot)"
    using equal by simp
  have
    "GenericReadyRoot p = GenericSuspendedRoot"
    by (rule generated_generic_role_raw_root_injD[
          OF GeneratedGenericRootRoles_readyI[OF bound]
             suspended roots_equal])
  then show False by simp
qed

lemma generated_ready_raw_root_neq_termination:
  assumes bound: "p < 4"
  shows
    "abi_list_ptr (sr_ready generated_scheduler_roots p) \<noteq>
     abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
proof
  assume equal:
    "abi_list_ptr (sr_ready generated_scheduler_roots p) =
     abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
  have termination_role:
      "GenericTerminationRoot \<in> GeneratedGenericRootRoles"
    by (simp add: GeneratedGenericRootRoles_def)
  have roots_equal:
      "abi_list_ptr
         (generated_generic_role_source_root (GenericReadyRoot p)) =
       abi_list_ptr
         (generated_generic_role_source_root GenericTerminationRoot)"
    using equal by simp
  have
    "GenericReadyRoot p = GenericTerminationRoot"
    by (rule generated_generic_role_raw_root_injD[
          OF GeneratedGenericRootRoles_readyI[OF bound]
             termination_role roots_equal])
  then show False by simp
qed

lemma generated_nonready_raw_roots_distinct:
  "abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<noteq>
       abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<and>
   abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<noteq>
       abi_list_ptr (sr_suspended generated_scheduler_roots) \<and>
   abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<noteq>
       abi_list_ptr (sr_suspended generated_scheduler_roots) \<and>
   abi_list_ptr (sr_delayed_a generated_scheduler_roots) \<noteq>
       abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_' \<and>
   abi_list_ptr (sr_delayed_b generated_scheduler_roots) \<noteq>
       abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_' \<and>
   abi_list_ptr (sr_suspended generated_scheduler_roots) \<noteq>
       abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
  using frozen_generated_named_roots_distinct
  by (auto simp only: abi_list_ptr_eq_iff distinct.simps set_simps)

section \<open>One re-entry snapshot is the due Result Generic family\<close>

theorem strong_generic_role_projection_one_due_reentry:
  assumes current: "current = due_prefix_fold_state entry processed"
    and role:
      "strong_generic_role_projection current termination
         (ods_generic_family S)"
    and priority_bound: "sa_priority current task < 4"
    and selector: "odc_task C = task"
    and source:
      "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
    and target:
      "one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority current task))"
    and key:
      "ods_generic_payload S task =
       (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w)"
  shows
    "strong_generic_role_projection
       (due_prefix_result_step_abs entry processed (Generic task))
       termination
       (ods_generic_family (one_due_reentry_snapshot C branch S))"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?family =
    "ods_generic_family (one_due_reentry_snapshot C branch S)"
  let ?old = "ods_generic_family S"
  let ?pri = "sa_priority current task"
  let ?ready =
    "\<lambda>p. abi_list_ptr (sr_ready generated_scheduler_roots p)"
  let ?da = "abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
  let ?db = "abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
  let ?sus = "abi_list_ptr (sr_suspended generated_scheduler_roots)"
  let ?term =
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
  let ?source = "odc_delayed_root C"
  let ?target = "one_due_target_root C"
  let ?insert =
    "\<lambda>q. list_insert_end_abs (Generic task)
       (ods_generic_payload S task) q"
  let ?remove = "\<lambda>q. list_remove_abs (Generic task) q"

  have ready_before:
    "\<And>p. p < 4 \<Longrightarrow> ?old (?ready p) = sa_ready current p"
    using role by (simp add: strong_generic_role_projection_def)
  have da_before: "?old ?da = sa_delayed_a current"
    and db_before: "?old ?db = sa_delayed_b current"
    and sus_before: "?old ?sus = sa_suspended current"
    and term_before: "?old ?term = termination"
    using role by (simp_all add: strong_generic_role_projection_def)

  have source_target_ne: "?source \<noteq> ?target"
    using source target priority_bound
      generated_ready_raw_root_neq_delayed_a[OF priority_bound]
      generated_ready_raw_root_neq_delayed_b[OF priority_bound]
    by (cases "sa_current_role_a current") auto
  have family_at:
    "\<And>r. ?family r =
       (if r = ?target
        then ?insert (?old ?target)
        else if r = ?source
        then ?remove (?old ?source)
        else ?old r)"
    using source_target_ne
    by (simp add: one_due_reentry_snapshot_generic_at Let_def selector)

  have ready_target_iff:
    "\<And>p. p < 4 \<Longrightarrow> (?ready p = ?target) = (p = ?pri)"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    show "(?ready p = ?target) = (p = ?pri)"
    proof
      assume equal: "?ready p = ?target"
      have raw_equal: "?ready p = ?ready ?pri"
        using equal target by simp
      show "p = ?pri"
        by (rule generated_ready_raw_root_inj[
              OF bound priority_bound raw_equal])
    next
      assume "p = ?pri"
      then show "?ready p = ?target" using target by simp
    qed
  qed
  have ready_source_ne:
    "\<And>p. p < 4 \<Longrightarrow> ?ready p \<noteq> ?source"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    show "?ready p \<noteq> ?source"
      using source generated_ready_raw_root_neq_delayed_a[OF bound]
        generated_ready_raw_root_neq_delayed_b[OF bound]
      by (cases "sa_current_role_a current") auto
  qed
  have da_target_ne: "?da \<noteq> ?target"
  proof
    assume equal: "?da = ?target"
    have ready_equal: "?ready ?pri = ?da"
      using target equal by simp
    show False
      using generated_ready_raw_root_neq_delayed_a[OF priority_bound]
        ready_equal by contradiction
  qed
  have db_target_ne: "?db \<noteq> ?target"
  proof
    assume equal: "?db = ?target"
    have ready_equal: "?ready ?pri = ?db"
      using target equal by simp
    show False
      using generated_ready_raw_root_neq_delayed_b[OF priority_bound]
        ready_equal by contradiction
  qed
  have sus_target_ne: "?sus \<noteq> ?target"
  proof
    assume equal: "?sus = ?target"
    have ready_equal: "?ready ?pri = ?sus"
      using target equal by simp
    show False
      using generated_ready_raw_root_neq_suspended[OF priority_bound]
        ready_equal by contradiction
  qed
  have term_target_ne: "?term \<noteq> ?target"
  proof
    assume equal: "?term = ?target"
    have ready_equal: "?ready ?pri = ?term"
      using target equal by simp
    show False
      using generated_ready_raw_root_neq_termination[OF priority_bound]
        ready_equal by contradiction
  qed
  have da_db_ne: "?da \<noteq> ?db"
    and da_sus_ne: "?da \<noteq> ?sus"
    and db_sus_ne: "?db \<noteq> ?sus"
    and da_term_ne: "?da \<noteq> ?term"
    and db_term_ne: "?db \<noteq> ?term"
    using generated_nonready_raw_roots_distinct by blast+
  have sus_source_ne: "?sus \<noteq> ?source"
    using source da_sus_ne db_sus_ne
    by (cases "sa_current_role_a current") auto
  have term_source_ne: "?term \<noteq> ?source"
    using source da_term_ne db_term_ne
    by (cases "sa_current_role_a current") auto

  have ready_after:
    "\<And>p. p < 4 \<Longrightarrow> ?family (?ready p) = sa_ready ?after p"
  proof -
    fix p :: nat
    assume bound: "p < 4"
    show "?family (?ready p) = sa_ready ?after p"
    proof (cases "p = ?pri")
      case True
      have at_target: "?ready p = ?target"
        using ready_target_iff[OF bound] True by simp
      have old_target: "?old ?target = sa_ready current p"
        using ready_before[OF bound] at_target by simp
      have family_target:
        "?family (?ready p) =
         list_insert_end_abs (Generic task)
           (ods_generic_payload S task) (sa_ready current p)"
        using family_at[of "?ready p"] at_target old_target by simp
      have abstract_target:
        "sa_ready ?after p =
         list_insert_end_abs (Generic task)
           (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w)
           (sa_ready current p)"
        using due_prefix_result_step_ready_at[
          OF current, where p=p and task=task] True by simp
      show ?thesis using family_target abstract_target key by simp
    next
      case False
      have not_target: "?ready p \<noteq> ?target"
        using ready_target_iff[OF bound] False by simp
      have not_source: "?ready p \<noteq> ?source"
        by (rule ready_source_ne[OF bound])
      have family_frame: "?family (?ready p) = ?old (?ready p)"
        using family_at[of "?ready p"] not_target not_source by simp
      have abstract_frame: "sa_ready ?after p = sa_ready current p"
        using due_prefix_result_step_ready_at[
          OF current, where p=p and task=task] False by simp
      show ?thesis
        using family_frame abstract_frame ready_before[OF bound] by simp
    qed
  qed

  have da_after: "?family ?da = sa_delayed_a ?after"
  proof (cases "sa_current_role_a current")
    case True
    have source_da: "?source = ?da" using source True by simp
    have family_remove: "?family ?da = ?remove (?old ?da)"
      using family_at[of ?da] da_target_ne source_da by simp
    have abstract_remove:
      "sa_delayed_a ?after = ?remove (sa_delayed_a current)"
      using due_prefix_result_step_delayed_a[
        OF current, where task=task] True by simp
    show ?thesis using family_remove abstract_remove da_before by simp
  next
    case False
    have source_db: "?source = ?db" using source False by simp
    have source_da_ne: "?da \<noteq> ?source"
      using source_db da_db_ne by simp
    have family_frame: "?family ?da = ?old ?da"
      using family_at[of ?da] da_target_ne source_da_ne by simp
    have abstract_frame: "sa_delayed_a ?after = sa_delayed_a current"
      using due_prefix_result_step_delayed_a[
        OF current, where task=task] False by simp
    show ?thesis using family_frame abstract_frame da_before by simp
  qed
  have db_after: "?family ?db = sa_delayed_b ?after"
  proof (cases "sa_current_role_a current")
    case True
    have source_da: "?source = ?da" using source True by simp
    have source_db_ne: "?db \<noteq> ?source"
      using source_da da_db_ne by simp
    have family_frame: "?family ?db = ?old ?db"
      using family_at[of ?db] db_target_ne source_db_ne by simp
    have abstract_frame: "sa_delayed_b ?after = sa_delayed_b current"
      using due_prefix_result_step_delayed_b[
        OF current, where task=task] True by simp
    show ?thesis using family_frame abstract_frame db_before by simp
  next
    case False
    have source_db: "?source = ?db" using source False by simp
    have family_remove: "?family ?db = ?remove (?old ?db)"
      using family_at[of ?db] db_target_ne source_db by simp
    have abstract_remove:
      "sa_delayed_b ?after = ?remove (sa_delayed_b current)"
      using due_prefix_result_step_delayed_b[
        OF current, where task=task] False by simp
    show ?thesis using family_remove abstract_remove db_before by simp
  qed
  have sus_after: "?family ?sus = sa_suspended ?after"
  proof -
    have family_frame: "?family ?sus = ?old ?sus"
      using family_at[of ?sus] sus_target_ne sus_source_ne by simp
    have abstract_frame: "sa_suspended ?after = sa_suspended current"
      by (rule due_prefix_result_step_suspended[OF current])
    show ?thesis using family_frame abstract_frame sus_before by simp
  qed
  have term_after: "?family ?term = termination"
    using family_at[of ?term] term_target_ne term_source_ne term_before
    by simp

  show ?thesis
    unfolding strong_generic_role_projection_def
    using ready_after da_after db_after sus_after term_after by blast
qed

section \<open>Strong-head corollary with no post-state premise\<close>

theorem DueLoopStrongHeadRel_result_step_generic_role_projection:
  assumes strong:
      "DueLoopStrongHeadRel D c current managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S
         now entry processed (Generic task # remaining) future
         phase next pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed
         (Generic task # remaining) future current
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "strong_generic_role_projection
       (due_prefix_result_step_abs entry processed (Generic task))
       termination
       (ods_generic_family (one_due_reentry_snapshot C branch S))"
proof -
  have local:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    using gate by (simp add: due_prefix_gate_inv_def)
  have current:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have scheduler_role:
    "scheduler_role_rel generated_scheduler_roots c current"
    using strong
    by (simp add: DueLoopStrongHeadRel_def
        DueLoopSchedulerSnapshotRel_def Let_def)
  have task_local_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF local])
  have priority:
    "odc_priority C task = sa_priority current task"
    using local task_local_live selector
    by (simp add: one_due_gateH_entry_rel_def Let_def)
  have root_alignment:
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots)) \<and>
     one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots
           (sa_priority current task)) \<and>
     odc_delayed_root C \<noteq> one_due_target_root C \<and>
     odc_pending_root C = GeneratedPendingEventRoot"
  proof -
    note exact = one_due_gateH_exact_rootsD[OF local]
    have exact_delayed:
        "odc_delayed_root C =
         abi_list_ptr (Scheduler_V611_Parse.globals.pxDelayedTaskList_' c)"
      using exact by blast
    have exact_target:
        "one_due_target_root C =
         abi_list_ptr (sr_ready R (odc_priority C (odc_task C)))"
      using exact by blast
    have exact_distinct:
        "odc_delayed_root C \<noteq> one_due_target_root C"
      using exact by blast
    have exact_pending:
        "odc_pending_root C = abi_list_ptr (sr_pending R)"
      using exact by blast
    have role_delayed:
        "Scheduler_V611_Parse.globals.pxDelayedTaskList_' c =
         (if sa_current_role_a current
          then sr_delayed_a generated_scheduler_roots
          else sr_delayed_b generated_scheduler_roots)"
      using scheduler_role by (simp add: scheduler_role_rel_def)
    have aligned_delayed:
        "odc_delayed_root C =
         (if sa_current_role_a current
          then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
          else abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
      using exact_delayed role_delayed by simp
    have aligned_target:
        "one_due_target_root C =
         abi_list_ptr
           (sr_ready generated_scheduler_roots
             (sa_priority current task))"
      using exact_target priority selector roots by simp
    have aligned_pending:
        "odc_pending_root C = GeneratedPendingEventRoot"
      using exact_pending roots
      by (simp add: GeneratedPendingEventRoot_def)
    show ?thesis
      using aligned_delayed aligned_target exact_distinct aligned_pending
      by blast
  qed
  have source:
    "odc_delayed_root C =
       (if sa_current_role_a current
        then abi_list_ptr (sr_delayed_a generated_scheduler_roots)
        else abi_list_ptr (sr_delayed_b generated_scheduler_roots))"
    using root_alignment by simp
  have target:
    "one_due_target_root C =
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority current task))"
    using root_alignment by simp

  have core: "due_loop_core_wf current"
    using strong
    by (simp add: DueLoopStrongHeadRel_def
        DueLoopSchedulerSnapshotRel_def Let_def)
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # remaining @ future"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_current_member:
      "Generic task \<in> set (ring (current_delayed_ring current))"
    using current_ring by simp
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
             generic_task_set (sa_delayed_b current)"
    using task_current_member
    by (cases "sa_current_role_a current")
       (simp_all add: generic_task_set_def current_delayed_ring_def)
  have task_live: "task \<in> sa_live current"
    using core task_delayed
    by (auto simp: due_loop_core_wf_def membership_wf_def Let_def)
  have priority_bound: "sa_priority current task < 4"
    using core task_live by (simp add: due_loop_core_wf_def)

  have pre_role:
    "strong_generic_role_projection current termination generic_abs"
    and pre_wake: "strong_wake_payload_projection current K_G"
    and snapshot_generic: "ods_generic_family S = generic_abs"
    and snapshot_payload: "ods_generic_payload S = K_G"
    using strong
    by (simp_all add: DueLoopStrongHeadRel_def
        DueLoopSchedulerSnapshotRel_def
        strong_one_due_snapshot_projection_def Let_def)
  have role_S:
    "strong_generic_role_projection current termination
       (ods_generic_family S)"
    using pre_role snapshot_generic by simp
  have wake_task: "sa_wake current task = Some (K_G task)"
    using pre_wake task_live task_delayed
    by (simp add: strong_wake_payload_projection_def)
  have key:
    "ods_generic_payload S task =
       (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w)"
    using snapshot_payload wake_task by simp

  show ?thesis
    by (rule strong_generic_role_projection_one_due_reentry[
          OF current role_S priority_bound selector source target key])
qed

end

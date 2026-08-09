theory Scheduler_Due_Prefix_Strong_Snapshot_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage.Scheduler_Generic_Root_Universe_Coverage"
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Base.Scheduler_One_Due_Task_Phases_Base"
begin

text \<open>
  Strong whole-scheduler snapshot relation for the generated unlocked-tick
  due-prefix loop.  This layer deliberately separates two task domains:

    * @{term "sa_live a"} is the runnable scheduler domain represented by
      ready, delayed and suspended Generic roots;
    * \<open>managed\<close> is the finite allocated-and-observable TCB domain.
      It additionally contains tasks waiting for idle-task reclamation in
      xTasksWaitingTermination.

  The distinction is semantic, not cosmetic.  The frozen configuration has
  INCLUDE_vTaskDelete = 1, so a nonempty termination root is a legal state.
  Such a TCB must remain decoded, guarded, separated and physically observed,
  but it must not be reintroduced into \<open>sa_live\<close> merely to make a
  family theorem apply.

  The relation below covers every configured Generic root, the pending Event
  root, an arbitrary finite family of protected external Event roots, every
  raw ring/count/cursor/container/payload observation, and the scheduler
  role/scalar/current pins.  External Event-root topology is retained as
  ghost state because scheduler_abs records only the union
  \<open>sa_event_waiting\<close>.

  This is an explicit strengthening/refactor, not an alternative spelling of
  scheduler_unlocked_tick_rep_rel.  That older predicate only wraps
  scheduler_resume_rep_rel, whose scheduler_lists_rel omits the termination
  root and protected external Event roots and whose scheduler_scalar_rel
  equates uxCurrentNumberOfTasks with card sa_live.  Reusing it unchanged
  would lose precisely the legal states this theory is designed to retain.
\<close>

definition managed_scheduler_view ::
  "'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid scheduler_abs"
where
  "managed_scheduler_view a managed = a\<lparr>sa_live := managed\<rparr>"

definition scheduler_managed_scalar_rel ::
  "Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> bool"
where
  "scheduler_managed_scalar_rel c a managed \<longleftrightarrow>
     scheduler_scalar_rel c (managed_scheduler_view a managed)"

definition scheduler_managed_task_observation_rel ::
  "'tid scheduler_decode \<Rightarrow> heap_mem \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> bool"
where
  "scheduler_managed_task_observation_rel D h a managed \<longleftrightarrow>
     TaskObservationRel D h (managed_scheduler_view a managed)"

definition strong_managed_domain_rel ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring \<Rightarrow>
   'tid set \<Rightarrow> bool"
where
  "strong_managed_domain_rel a termination managed \<longleftrightarrow>
     finite managed \<and>
     sa_live a \<subseteq> managed \<and>
     xlist_wf termination \<and>
     generic_ring termination \<and>
     generic_task_set termination = managed - sa_live a"

definition strong_generic_role_projection ::
  "'tid scheduler_abs \<Rightarrow> 'tid node_ring \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow> bool"
where
  "strong_generic_role_projection a termination fam \<longleftrightarrow>
     (\<forall>p<4.
        fam (abi_list_ptr (sr_ready generated_scheduler_roots p)) =
          sa_ready a p) \<and>
     fam (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
       sa_delayed_a a \<and>
     fam (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
       sa_delayed_b a \<and>
     fam (abi_list_ptr (sr_suspended generated_scheduler_roots)) =
       sa_suspended a \<and>
     fam (abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_') =
       termination"

definition strong_event_role_projection ::
  "'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow> bool"
where
  "strong_event_role_projection a managed external fam \<longleftrightarrow>
     fam GeneratedPendingEventRoot = sa_pending a \<and>
     {t. \<exists>lp\<in>external. Event t \<in> set (ring (fam lp))} =
       sa_event_waiting a \<and>
     (\<forall>t\<in>managed - sa_live a.
        \<forall>lp\<in>EventRootUniverse external.
          Event t \<notin> set (ring (fam lp)))"

definition strong_wake_payload_projection ::
  "'tid scheduler_abs \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "strong_wake_payload_projection a K_G \<longleftrightarrow>
     (\<forall>t\<in>sa_live a.
        sa_wake a t =
          (if t \<in> generic_task_set (sa_delayed_a a) \<union>
                     generic_task_set (sa_delayed_b a)
           then Some (K_G t)
           else None))"

definition strong_one_due_snapshot_projection ::
  "'tid scheduler_abs \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "strong_one_due_snapshot_projection a generic_fam event_fam K_G K_E S
       \<longleftrightarrow>
     ods_generic_family S = generic_fam \<and>
     ods_event_family S = event_fam \<and>
     ods_generic_payload S = K_G \<and>
     ods_event_payload S = K_E \<and>
     ods_top S = sa_top_ready a \<and>
     ods_captured_generic_key S = None \<and>
     ods_checked_event S = None"

definition strong_due_next_ptr_rel ::
  "'tid scheduler_decode \<Rightarrow> 'tid node_kind option \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow> bool"
where
  "strong_due_next_ptr_rel D next p \<longleftrightarrow>
     (next = None \<and> p = NULL) \<or>
     (\<exists>t. next = Some (Generic t) \<and> p = sd_tcb_ptr D t)"

definition StrongSchedulerSnapshotRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     (let h = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)
      in core_wf a \<and>
         strong_managed_domain_rel a termination managed \<and>
         GenericRootFamilyCoverage D h GenericRootUniverse
           generic_raw generic_abs managed K_G \<and>
         EventRootFamilyCoverage external D h event_raw event_abs
           managed K_E \<and>
         strong_generic_role_projection a termination generic_abs \<and>
         strong_event_role_projection a managed external event_abs \<and>
         strong_wake_payload_projection a K_G \<and>
         scheduler_managed_task_observation_rel D h a managed \<and>
         strong_one_due_snapshot_projection a generic_abs event_abs
           K_G K_E S \<and>
         scheduler_role_rel generated_scheduler_roots c a \<and>
         scheduler_managed_scalar_rel c a managed \<and>
         scheduler_current_rel D c a \<and>
         scheduler_boundary_rel c \<and>
         (\<forall>g\<in>GenericRootUniverse.
          \<forall>e\<in>EventRootUniverse external.
            raw_xlist_storage g (generic_raw g) \<inter>
              raw_xlist_storage e (event_raw e) = {}))"

text \<open>Domain and compatibility facts.\<close>

lemma generic_ring_task_set_empty_iff:
  assumes generic: "generic_ring q"
  shows "generic_task_set q = {} \<longleftrightarrow> ring q = []"
proof (cases "ring q")
  case Nil
  then show ?thesis by (simp add: generic_task_set_def)
next
  case (Cons n ns)
  have n_member: "n \<in> set (ring q)"
    using Cons by simp
  obtain t where n_generic: "n = Generic t"
    using generic n_member
    by (auto simp: generic_ring_def)
  have t_member: "t \<in> generic_task_set q"
    using Cons n_generic
    by (simp add: generic_task_set_def)
  have task_set_nonempty: "generic_task_set q \<noteq> {}"
    using t_member by blast
  show ?thesis
    using Cons task_set_nonempty by simp
qed

lemma strong_managed_domain_no_retired_iff:
  assumes domain: "strong_managed_domain_rel a termination managed"
  shows "managed = sa_live a \<longleftrightarrow> ring termination = []"
proof
  assume managed_eq: "managed = sa_live a"
  have generic: "generic_ring termination"
    and retired:
      "generic_task_set termination = managed - sa_live a"
    using domain
    by (simp_all add: strong_managed_domain_rel_def)
  have task_set_empty: "generic_task_set termination = {}"
    using retired managed_eq by simp
  show "ring termination = []"
    by (rule iffD1[OF generic_ring_task_set_empty_iff[OF generic]
          task_set_empty])
next
  assume ring_empty: "ring termination = []"
  have subset: "sa_live a \<subseteq> managed"
    and generic: "generic_ring termination"
    and retired:
      "generic_task_set termination = managed - sa_live a"
    using domain
    by (simp_all add: strong_managed_domain_rel_def)
  have task_set_empty: "generic_task_set termination = {}"
    by (rule iffD2[OF generic_ring_task_set_empty_iff[OF generic]
          ring_empty])
  have difference_empty: "managed - sa_live a = {}"
    using retired task_set_empty by simp
  show "managed = sa_live a"
  proof (rule set_eqI)
    fix t
    show "t \<in> managed \<longleftrightarrow> t \<in> sa_live a"
    proof
      assume t_managed: "t \<in> managed"
      show "t \<in> sa_live a"
      proof (rule ccontr)
        assume "t \<notin> sa_live a"
        then have "t \<in> managed - sa_live a"
          using t_managed by simp
        then show False using difference_empty by simp
      qed
    next
      assume t_live: "t \<in> sa_live a"
      show "t \<in> managed"
        by (rule subsetD[OF subset t_live])
    qed
  qed
qed

lemma scheduler_managed_scalar_rel_no_retired:
  assumes no_retired: "managed = sa_live a"
  shows
    "scheduler_managed_scalar_rel c a managed \<longleftrightarrow>
     scheduler_scalar_rel c a"
  using no_retired
  by (simp add: scheduler_managed_scalar_rel_def
      managed_scheduler_view_def)

text \<open>Role projections are exact, including the configured termination
  root.\<close>

lemma strong_generic_role_readyD:
  assumes proj: "strong_generic_role_projection a termination fam"
    and priority: "p < 4"
  shows
    "fam (abi_list_ptr (sr_ready generated_scheduler_roots p)) =
       sa_ready a p"
  using proj priority
  by (simp add: strong_generic_role_projection_def)

lemma strong_generic_role_delayed_aD:
  assumes "strong_generic_role_projection a termination fam"
  shows
    "fam (abi_list_ptr (sr_delayed_a generated_scheduler_roots)) =
       sa_delayed_a a"
  using assms by (simp add: strong_generic_role_projection_def)

lemma strong_generic_role_delayed_bD:
  assumes "strong_generic_role_projection a termination fam"
  shows
    "fam (abi_list_ptr (sr_delayed_b generated_scheduler_roots)) =
       sa_delayed_b a"
  using assms by (simp add: strong_generic_role_projection_def)

lemma strong_generic_role_suspendedD:
  assumes "strong_generic_role_projection a termination fam"
  shows
    "fam (abi_list_ptr (sr_suspended generated_scheduler_roots)) =
       sa_suspended a"
  using assms by (simp add: strong_generic_role_projection_def)

lemma strong_generic_role_terminationD:
  assumes "strong_generic_role_projection a termination fam"
  shows
    "fam (abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_') =
       termination"
  using assms by (simp add: strong_generic_role_projection_def)

lemma strong_event_role_pendingD:
  assumes "strong_event_role_projection a managed external fam"
  shows "fam GeneratedPendingEventRoot = sa_pending a"
  using assms by (simp add: strong_event_role_projection_def)

lemma strong_event_role_external_unionD:
  assumes "strong_event_role_projection a managed external fam"
  shows
    "{t. \<exists>lp\<in>external. Event t \<in> set (ring (fam lp))} =
       sa_event_waiting a"
  using assms by (simp add: strong_event_role_projection_def)

lemma strong_event_role_retired_absentD:
  assumes rel: "strong_event_role_projection a managed external fam"
    and retired: "t \<in> managed - sa_live a"
    and root: "lp \<in> EventRootUniverse external"
  shows "Event t \<notin> set (ring (fam lp))"
  using rel retired root
  by (auto simp: strong_event_role_projection_def)

text \<open>
  raw_xlist_rel plus xlist_relabel really carries the concrete count and
  cursor; these are not merely inferred from membership sets.
\<close>

lemma raw_relabel_count_cursorD:
  assumes raw: "raw_xlist_rel h lp rx"
    and relabel: "xlist_relabel decode rx q"
  shows
    "unat (uxNumberOfItems_C (h_val h lp)) = length (ring q) \<and>
     rel_option (\<lambda>p n. decode p = Some n)
       (raw_cursor_at h lp) (cursor q)"
proof -
  have count_raw:
    "unat (uxNumberOfItems_C (h_val h lp)) = length (ring rx)"
    by (rule raw_xlist_rel_countD[OF raw])
  have lengths: "length (ring rx) = length (ring q)"
    by (rule xlist_relabel_ring_length[OF relabel])
  have cursor_raw: "cursor rx = raw_cursor_at h lp"
    by (rule raw_xlist_rel_cursorD[OF raw])
  have cursor_rel:
    "rel_option (\<lambda>p n. decode p = Some n)
       (cursor rx) (cursor q)"
    using relabel by (simp add: xlist_relabel_def)
  show ?thesis
    using count_raw lengths cursor_raw cursor_rel by simp
qed

lemma GenericRootFamilyCoverage_count_cursorD:
  assumes cov:
    "GenericRootFamilyCoverage D h roots raw_fam abs_fam managed K_G"
    and root: "lp \<in> roots"
  shows
    "unat (uxNumberOfItems_C (h_val h lp)) =
       length (ring (abs_fam lp)) \<and>
     rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (raw_cursor_at h lp) (cursor (abs_fam lp))"
  by (rule raw_relabel_count_cursorD[
        OF GenericRootFamilyCoverage_raw_rootD[OF cov root]
           GenericRootFamilyCoverage_relabelD[OF cov root]])

lemma EventRootFamilyCoverage_count_cursorD:
  assumes cov:
    "EventRootFamilyCoverage external D h raw_fam abs_fam managed K_E"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "unat (uxNumberOfItems_C (h_val h lp)) =
       length (ring (abs_fam lp)) \<and>
     rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (raw_cursor_at h lp) (cursor (abs_fam lp))"
proof -
  have family:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF cov])
  show ?thesis
    by (rule raw_relabel_count_cursorD[
          OF scheduler_event_root_family_raw_rootD[OF family root]
             scheduler_event_root_family_relabelD[OF family root]])
qed

end

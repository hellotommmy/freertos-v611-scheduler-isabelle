theory Scheduler_Resume_Managed_Phase_Adapter_Context
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Base.Scheduler_Resume_Managed_Phase_Adapter_Base"
begin

text \<open>
  The canonical pending context uses managed as its representation domain, but
  its task list remains the public-live pending work.  Priority bounds for
  retired managed tasks therefore come from the managed TaskObservationRel,
  not from the public core invariant.
\<close>

lemma CursorGeneralStrongResumePendingManagedGateRel_canonical_context_wf:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "resume_pending_context_wf
       (resume_pending_canonical_managed_context
          a managed external K_G K_E)"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0)"
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    and event_coverage:
      "EventRootFamilyCoverage external D ?h event_raw event_abs managed K_E"
    and observation:
      "TaskObservationRel D ?h (managed_scheduler_view a managed)"
    and canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using snapshot
    by (simp_all add: CursorGeneralStrongSchedulerSnapshotRel_def
        cursor_general_core_wf_def scheduler_managed_task_observation_rel_def
        Let_def)
  have finite_managed: "finite managed"
    and live_subset: "sa_live a \<subseteq> managed"
    using domain
    by (simp_all add: CursorGeneralStrongManagedDomainRel_def)
  have external_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
  have finite_event: "finite (EventRootUniverse external)"
    by (rule EventRootUniverse_finite[OF external_wf])
  have tasks_distinct: "distinct (resume_pending_managed_tasks a)"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_distinctD[
        OF gate])
  have tasks_public:
    "set (resume_pending_managed_tasks a) \<subseteq> sa_live a"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_liveD[
        OF gate])
  have tasks_managed:
    "set (resume_pending_managed_tasks a) \<subseteq> managed"
    using tasks_public live_subset by blast
  have managed_priority:
    "\<forall>t\<in>managed. sa_priority a t < 4"
  proof (intro ballI)
    fix t
    assume t: "t \<in> managed"
    have t_view: "t \<in> sa_live (managed_scheduler_view a managed)"
      using t by (simp add: managed_scheduler_view_def)
    have fields:
      "c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority (managed_scheduler_view a managed) t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val ?h (sd_tcb_ptr D t))) =
           sa_priority (managed_scheduler_view a managed) t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val ?h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val ?h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val ?h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t)"
      by (rule TaskObservationRel_liveD[OF observation t_view])
    show "sa_priority a t < 4"
      using fields by (simp add: managed_scheduler_view_def)
  qed
  have ready_roots:
    "\<forall>t\<in>managed.
       abi_list_ptr
         (sr_ready generated_scheduler_roots (sa_priority a t))
         \<in> GenericRootUniverse"
    using managed_priority
    by (blast intro: GenericRootUniverse_readyI)
  have top_bound: "sa_top_ready a < 4"
    using canonical_core
    by (simp add: core_wf_def ready_cache_wf_def)
  have current_bound: "resume_pending_managed_current_priority a < 4"
  proof (cases "sa_current a")
    case None
    show ?thesis
      by (simp add: resume_pending_managed_current_priority_def None)
  next
    case (Some t)
    have t_live_shadow:
      "t \<in> sa_live (canonicalize_scheduler_cursors a)"
      by (rule core_wf_current_is_live[OF canonical_core]) (simp add: Some)
    have t_live: "t \<in> sa_live a"
      using t_live_shadow by simp
    have t_managed: "t \<in> managed"
      by (rule subsetD[OF live_subset t_live])
    have priority: "sa_priority a t < 4"
      using managed_priority t_managed by blast
    show ?thesis
      using priority
      by (simp add: resume_pending_managed_current_priority_def Some)
  qed
  have owner_roots:
    "\<forall>t\<in>set (resume_pending_managed_tasks a).
       resume_pending_managed_owner a t \<in> GenericRootUniverse \<and>
       (\<forall>u\<in>managed.
          resume_pending_managed_owner a t \<noteq>
            abi_list_ptr
              (sr_ready generated_scheduler_roots (sa_priority a u)))"
  proof (intro ballI)
    fix t
    assume t: "t \<in> set (resume_pending_managed_tasks a)"
    have delayed_a_root:
      "abi_list_ptr (sr_delayed_a generated_scheduler_roots)
         \<in> GenericRootUniverse"
      by (rule GenericRootUniverse_delayed_aI)
    have delayed_b_root:
      "abi_list_ptr (sr_delayed_b generated_scheduler_roots)
         \<in> GenericRootUniverse"
      by (rule GenericRootUniverse_delayed_bI)
    have suspended_root:
      "abi_list_ptr (sr_suspended generated_scheduler_roots)
         \<in> GenericRootUniverse"
      by (rule GenericRootUniverse_suspendedI)
    have owner_root:
      "resume_pending_managed_owner a t \<in> GenericRootUniverse"
      using delayed_a_root delayed_b_root suspended_root
      by (simp add: resume_pending_managed_owner_def)
    have owner_ready:
      "\<And>u. u \<in> managed \<Longrightarrow>
         resume_pending_managed_owner a t \<noteq>
           abi_list_ptr
             (sr_ready generated_scheduler_roots (sa_priority a u))"
    proof -
      fix u
      assume u: "u \<in> managed"
      have bound: "sa_priority a u < 4"
        using managed_priority u by blast
      note neq = generated_ready_root_neq_roles[OF bound]
      show
        "resume_pending_managed_owner a t \<noteq>
           abi_list_ptr
             (sr_ready generated_scheduler_roots (sa_priority a u))"
        using neq
        by (auto simp: resume_pending_managed_owner_def)
    qed
    show
      "resume_pending_managed_owner a t \<in> GenericRootUniverse \<and>
       (\<forall>u\<in>managed.
          resume_pending_managed_owner a t \<noteq>
            abi_list_ptr
              (sr_ready generated_scheduler_roots (sa_priority a u)))"
      using owner_root owner_ready by blast
  qed
  show ?thesis
    unfolding resume_pending_context_wf_def
  using finite_managed finite_event tasks_distinct tasks_managed
    current_bound top_bound managed_priority ready_roots owner_roots
  by (simp add: resume_pending_canonical_managed_context_def)
qed

ML \<open>
  val th =
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_canonical_context_wf}
  val _ =
    if null (Thm.hyps_of th) then ()
    else error "canonical managed pending context has hidden hypotheses"
  val _ =
    if length (Thm.prems_of th) = 1 then ()
    else error "canonical managed pending context premise ledger changed"
\<close>

end

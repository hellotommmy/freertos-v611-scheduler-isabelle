theory Scheduler_Managed_Task_Observation_Cutpoints
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Projections.Scheduler_Due_Prefix_Strong_Snapshot_Projections"
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Insert_Frame.Scheduler_Task_Observation_Insert_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Family_Coverage_Remove_Preserved.Scheduler_Generic_Root_Family_Coverage_Remove_Preserved"
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Remove_Frames_Event_Coverage.Scheduler_Generic_Remove_Frames_Event_Coverage"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Remove_Frames_Generic_Coverage.Scheduler_Event_Remove_Frames_Generic_Coverage"
begin

text \<open>
  Exact heap cutpoints for one universally quantified due-task transaction.
  The transaction removes the task's Generic item from an arbitrary covered
  Generic source root, optionally removes its Event item according to the
  physical container field, and inserts the Generic item at the end of an
  arbitrary covered Generic target root.  No task, priority, key, root, ring,
  cursor, tick or Event owner is fixed.

  The abstract task observation is always indexed by
  @{term "managed_scheduler_view current managed"}.  In particular, this file
  never substitutes the runnable-only domain for the allocated-and-observable
  managed domain; tasks waiting for termination remain observed at every heap
  cutpoint.
\<close>

definition managed_due_generic_remove_heap ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  "managed_due_generic_remove_heap D t h =
     raw_remove_concrete_heap h (generic_item_raw_ptr D t)"

definition managed_due_generic_raw_after_remove ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs)"
where
  "managed_due_generic_raw_after_remove D t source raw_fam =
     scheduler_family_remove_raw raw_fam source
       (generic_item_raw_ptr D t)"

definition managed_due_generic_abs_after_remove ::
  "'tid \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "managed_due_generic_abs_after_remove t source abs_fam =
     scheduler_family_remove_abs abs_fam source (Generic t)"

definition managed_due_optional_event_remove_heap ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  "managed_due_optional_event_remove_heap D t h =
     (if pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL
      then h
      else raw_remove_concrete_heap h (event_item_raw_ptr D t))"

definition managed_due_ready_insert_heap ::
  "'tid scheduler_decode \<Rightarrow> 'tid \<Rightarrow> xLIST_C ptr \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   heap_mem \<Rightarrow> heap_mem"
where
  "managed_due_ready_insert_heap D t target raw_fam h =
     raw_insert_concrete_heap h target (raw_fam target)
       (generic_item_raw_ptr D t)"

lemma TaskObservationRel_managed_view_priority_cong:
  assumes obs:
    "TaskObservationRel D h (managed_scheduler_view before managed)"
    and priority: "sa_priority after = sa_priority before"
  shows "TaskObservationRel D h (managed_scheduler_view after managed)"
  using obs priority
  by (simp add: TaskObservationRel_def managed_scheduler_view_def)

text \<open>
  The complete Generic coverage and the managed-view observation imply the
  insertion geometry for every managed task.  Thus the later insertion does
  not need a caller-supplied freshness/geometry postcondition.  The proof uses
  the actual TCB field guard, exact root--TCB separation and pairwise managed
  item separation.
\<close>

lemma managed_cutpoint_item_list_disjoint_imp_not_end:
  assumes disjoint:
    "raw_item_region p \<inter> raw_list_region lp = {}"
  shows "p \<noteq> raw_end_item lp"
proof
  assume equal: "p = raw_end_item lp"
  have overlap:
      "ptr_val lp + of_nat 8 \<in>
         raw_item_region p \<inter> raw_list_region lp"
  proof (rule IntI)
    show "ptr_val lp + of_nat 8 \<in> raw_item_region p"
      unfolding raw_item_region_def equal raw_end_item_def
        raw_sentinel_ptr_def
      apply (simp add: field_lvalue_def xLIST_C_xListEnd_C_fl)
      apply (rule intvl_self)
      by (simp add: size_of_def)
    show "ptr_val lp + of_nat 8 \<in> raw_list_region lp"
      unfolding raw_list_region_def
      apply (rule intvlI)
      by (simp add: size_of_def)
  qed
  show False using disjoint overlap by blast
qed

lemma GenericRootFamilyCoverage_managed_view_insert_geometry:
  assumes coverage:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         raw_fam abs_fam managed K_G"
    and observation:
      "TaskObservationRel D h (managed_scheduler_view current managed)"
    and task: "t \<in> managed"
  shows
    "raw_family_insert_geometry GenericRootUniverse raw_fam
       (generic_item_raw_ptr D t)"
proof -
  let ?p = "generic_item_raw_ptr D t"
  have pre:
      "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have t_observed:
      "c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority (managed_scheduler_view current managed) t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t))) =
         sa_priority (managed_scheduler_view current managed) t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
           PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
             (sd_tcb_ptr D t)"
    by (rule TaskObservationRel_liveD[OF observation])
       (use task in \<open>simp add: managed_scheduler_view_def\<close>)
  have scheduler_guard:
      "c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t))"
    using t_observed by blast
  have raw_guard:
      "c_guard (abi_item_ptr
         (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    by (rule iffD2[OF abi_item_ptr_c_guard scheduler_guard])
  have p_guard: "c_guard ?p"
    using raw_guard by (simp add: generic_item_raw_ptr_def)
  have p_managed: "?p \<in> universal_managed_nodes managed D"
    using task
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have geometry: "universal_tcb_geometry managed D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  show ?thesis
    unfolding raw_family_insert_geometry_def
  proof (rule conjI)
    show "c_guard ?p" by (rule p_guard)
  next
    show
      "\<forall>lp\<in>GenericRootUniverse.
         ?p \<noteq> raw_end_item lp \<and>
         raw_item_region ?p \<inter> raw_list_region lp = {} \<and>
         (\<forall>q\<in>set (ring (raw_fam lp)).
            q \<noteq> ?p \<longrightarrow>
            raw_item_region ?p \<inter> raw_item_region q = {})"
    proof (intro ballI)
      fix lp
      assume root: "lp \<in> GenericRootUniverse"
    have list_item:
        "raw_list_region lp \<inter> raw_item_region ?p = {}"
      by (rule scheduler_family_root_managed_item_disjoint[
            OF pre root p_managed])
    have item_list:
        "raw_item_region ?p \<inter> raw_list_region lp = {}"
      using list_item by (simp add: Int_commute)
    have not_end: "?p \<noteq> raw_end_item lp"
      by (rule managed_cutpoint_item_list_disjoint_imp_not_end[
            OF item_list])
    have ring_managed:
        "set (ring (raw_fam lp)) \<subseteq>
           universal_managed_nodes managed D"
      using pre root by (auto simp: scheduler_family_pre_rel_def)
    have item_items:
        "\<forall>q\<in>set (ring (raw_fam lp)).
           q \<noteq> ?p \<longrightarrow>
           raw_item_region ?p \<inter> raw_item_region q = {}"
    proof (intro ballI impI)
      fix q
      assume member: "q \<in> set (ring (raw_fam lp))"
        and different: "q \<noteq> ?p"
      have q_managed: "q \<in> universal_managed_nodes managed D"
        by (rule subsetD[OF ring_managed member])
      have p_ne_q: "?p \<noteq> q" using different by blast
      show "raw_item_region ?p \<inter> raw_item_region q = {}"
        by (rule universal_distinct_managed_item_regions_disjoint[
              OF geometry p_managed q_managed p_ne_q])
    qed
    show
      "?p \<noteq> raw_end_item lp \<and>
       raw_item_region ?p \<inter> raw_list_region lp = {} \<and>
       (\<forall>q\<in>set (ring (raw_fam lp)).
          q \<noteq> ?p \<longrightarrow>
          raw_item_region ?p \<inter> raw_item_region q = {})"
    proof (intro conjI)
      show "?p \<noteq> raw_end_item lp" by (rule not_end)
      show "raw_item_region ?p \<inter> raw_list_region lp = {}"
        by (rule item_list)
      show
        "\<forall>q\<in>set (ring (raw_fam lp)).
           q \<noteq> ?p \<longrightarrow>
           raw_item_region ?p \<inter> raw_item_region q = {}"
        by (rule item_items)
    qed
  qed
qed
qed

text \<open>
  Core four-cutpoint composition.  The source membership premise is an
  abstract semantic fact (the selected due task is in the selected source
  ring), not a concrete pointer/member postcondition.  Coverage derives the
  concrete source member.  The optional Event owner is also absent from the
  theorem boundary: the physical container and Event coverage derive the
  arbitrary external owner in the linked branch.
\<close>

theorem managed_TaskObservationRel_exact_cutpoints:
  assumes observation:
      "TaskObservationRel D h0 (managed_scheduler_view current managed)"
    and generic_coverage:
      "GenericRootFamilyCoverage D h0 GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D h0
         event_raw event_abs managed K_E"
    and task: "t \<in> managed"
    and source: "source \<in> GenericRootUniverse"
    and source_member:
      "Generic t \<in> set (ring (generic_abs source))"
    and target: "target \<in> GenericRootUniverse"
    and pending_empty:
      "ring (event_abs GeneratedPendingEventRoot) = []"
  shows
    "let hg = managed_due_generic_remove_heap D t h0;
         generic_raw_g =
           managed_due_generic_raw_after_remove D t source generic_raw;
         generic_abs_g =
           managed_due_generic_abs_after_remove t source generic_abs;
         he = managed_due_optional_event_remove_heap D t hg;
         hi = managed_due_ready_insert_heap D t target generic_raw_g he;
         p = generic_item_raw_ptr D t;
         ep = event_item_raw_ptr D t
     in TaskObservationRel D h0
          (managed_scheduler_view current managed) \<and>
        TaskObservationRel D hg
          (managed_scheduler_view current managed) \<and>
        ((pvContainer_C (h_val hg ep) = NULL \<and>
            raw_family_members (EventRootUniverse external) event_raw ep = {})
         \<or>
         (\<exists>owner. owner \<in> external \<and>
            ep \<in> set (ring (event_raw owner)) \<and>
            pvContainer_C (h_val hg ep) =
              PTR_COERCE(xLIST_C \<rightarrow> unit) owner)) \<and>
        TaskObservationRel D he
          (managed_scheduler_view current managed) \<and>
        GenericRootFamilyCoverage D he GenericRootUniverse
          generic_raw_g generic_abs_g managed K_G \<and>
        raw_family_globally_unlinked he GenericRootUniverse
          generic_raw_g p \<and>
        raw_fresh_for_insert target (ring (generic_raw_g target)) p \<and>
        TaskObservationRel D hi
          (managed_scheduler_view current managed)"
proof -
  let ?p = "generic_item_raw_ptr D t"
  let ?ep = "event_item_raw_ptr D t"
  let ?hg = "managed_due_generic_remove_heap D t h0"
  let ?generic_raw_g =
    "managed_due_generic_raw_after_remove D t source generic_raw"
  let ?generic_abs_g =
    "managed_due_generic_abs_after_remove t source generic_abs"
  let ?he = "managed_due_optional_event_remove_heap D t ?hg"
  let ?hi =
    "managed_due_ready_insert_heap D t target ?generic_raw_g ?he"

  have raw_member:
      "?p \<in> set (ring (generic_raw source))"
    using GenericRootFamilyCoverage_member_iff[
      OF generic_coverage task source]
      source_member by blast
  have generic_pre0:
      "scheduler_family_pre_rel h0 GenericRootUniverse
         generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_coverage])
  have generic_pre0_observed:
      "scheduler_family_pre_rel h0 GenericRootUniverse generic_raw
         (sa_live (managed_scheduler_view current managed)) D"
    using generic_pre0 by (simp add: managed_scheduler_view_def)
  have observation_g:
      "TaskObservationRel D ?hg
         (managed_scheduler_view current managed)"
    unfolding managed_due_generic_remove_heap_def
    by (rule TaskObservationRel_remove_preserved[
          OF observation generic_pre0_observed source raw_member])
  have generic_coverage_g:
      "GenericRootFamilyCoverage D ?hg GenericRootUniverse
         ?generic_raw_g ?generic_abs_g managed K_G"
    unfolding managed_due_generic_remove_heap_def
      managed_due_generic_raw_after_remove_def
      managed_due_generic_abs_after_remove_def
    by (rule GenericRootFamilyCoverage_remove_preserved[
          OF generic_coverage source task raw_member])
  have event_coverage_g:
      "EventRootFamilyCoverage external D ?hg
         event_raw event_abs managed K_E"
    unfolding managed_due_generic_remove_heap_def
    by (rule Generic_remove_frames_Event_coverage[
          OF generic_coverage event_coverage source task raw_member])

  have branch_accounted:
      "(pvContainer_C (h_val ?hg ?ep) = NULL \<and>
          raw_family_members (EventRootUniverse external) event_raw ?ep = {})
       \<or>
       (\<exists>owner. owner \<in> external \<and>
          ?ep \<in> set (ring (event_raw owner)) \<and>
          pvContainer_C (h_val ?hg ?ep) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) owner)"
  proof (cases "pvContainer_C (h_val ?hg ?ep) = NULL")
    case True
    have absent:
        "raw_family_members (EventRootUniverse external) event_raw ?ep = {}"
      using EventRootFamilyCoverage_null_iff_global_absence[
        OF event_coverage_g task]
        True by blast
    show ?thesis using True absent by blast
  next
    case False
    have linked_owner:
        "\<exists>owner. owner \<in> external \<and>
           ?ep \<in> set (ring (event_raw owner)) \<and>
           pvContainer_C (h_val ?hg ?ep) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
      by (rule EventRootFamilyCoverage_linked_owner_externalD[
            OF event_coverage_g task pending_empty False])
    obtain owner where owner_external: "owner \<in> external"
      and member: "?ep \<in> set (ring (event_raw owner))"
      and container:
        "pvContainer_C (h_val ?hg ?ep) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
      using linked_owner by blast
    show ?thesis
      using owner_external member container by blast
  qed

  have observation_e:
      "TaskObservationRel D ?he
         (managed_scheduler_view current managed)"
  proof (cases "pvContainer_C (h_val ?hg ?ep) = NULL")
    case True
    show ?thesis
      using observation_g True
      by (simp add: managed_due_optional_event_remove_heap_def)
  next
    case False
    obtain owner where owner_external: "owner \<in> external"
      and member: "?ep \<in> set (ring (event_raw owner))"
      using EventRootFamilyCoverage_linked_owner_externalD[
        OF event_coverage_g task pending_empty False]
      by blast
    have owner_root: "owner \<in> EventRootUniverse external"
      by (rule EventRootUniverse_externalI[OF owner_external])
    have event_pre_g:
        "scheduler_family_pre_rel ?hg (EventRootUniverse external)
           event_raw managed D"
      by (rule scheduler_event_root_family_preD[
            OF EventRootFamilyCoverage_relD[OF event_coverage_g]])
    have event_pre_g_observed:
        "scheduler_family_pre_rel ?hg (EventRootUniverse external)
           event_raw (sa_live (managed_scheduler_view current managed)) D"
      using event_pre_g by (simp add: managed_scheduler_view_def)
    have removed_observation:
        "TaskObservationRel D
           (raw_remove_concrete_heap ?hg ?ep)
           (managed_scheduler_view current managed)"
      by (rule TaskObservationRel_remove_preserved[
            OF observation_g event_pre_g_observed owner_root member])
    show ?thesis
      using removed_observation False
      by (simp add: managed_due_optional_event_remove_heap_def)
  qed

  have generic_coverage_e:
      "GenericRootFamilyCoverage D ?he GenericRootUniverse
         ?generic_raw_g ?generic_abs_g managed K_G"
    unfolding managed_due_optional_event_remove_heap_def
    by (rule EventRootFamilyCoverage_optional_remove_Generic_heap_coverage[
          OF generic_coverage_g event_coverage_g task pending_empty])

  have remove_post:
      "scheduler_family_pre_rel
         (raw_remove_concrete_heap h0 ?p) GenericRootUniverse
         (scheduler_family_remove_raw generic_raw source ?p) managed D \<and>
       raw_family_globally_unlinked
         (raw_remove_concrete_heap h0 ?p) GenericRootUniverse
         (scheduler_family_remove_raw generic_raw source ?p) ?p"
    by (rule scheduler_family_remove_pre_rel_and_unlinked[
          OF generic_pre0 source raw_member])
  have unlinked_g:
      "raw_family_globally_unlinked ?hg GenericRootUniverse
         ?generic_raw_g ?p"
    using remove_post
    by (simp add: managed_due_generic_remove_heap_def
        managed_due_generic_raw_after_remove_def)
  have absent_e:
      "raw_family_members GenericRootUniverse ?generic_raw_g ?p = {}"
    using unlinked_g
    by (simp add: raw_family_globally_unlinked_def)
  have null_e:
      "pvContainer_C (h_val ?he ?p) = NULL"
    by (rule iffD2[OF
          GenericRootFamilyCoverage_null_iff_global_absence[
            OF generic_coverage_e task]
          absent_e])
  have unlinked_e:
      "raw_family_globally_unlinked ?he GenericRootUniverse
         ?generic_raw_g ?p"
    using absent_e null_e
    by (simp add: raw_family_globally_unlinked_def)
  have generic_pre_e:
      "scheduler_family_pre_rel ?he GenericRootUniverse
         ?generic_raw_g managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_coverage_e])
  have family_e:
      "raw_family_rel ?he GenericRootUniverse ?generic_raw_g"
    using generic_pre_e by (simp add: scheduler_family_pre_rel_def)
  have geometry_e:
      "raw_family_insert_geometry GenericRootUniverse ?generic_raw_g ?p"
    by (rule GenericRootFamilyCoverage_managed_view_insert_geometry[
          OF generic_coverage_e observation_e task])
  have fresh_e:
      "raw_fresh_for_insert target (ring (?generic_raw_g target)) ?p"
    by (rule raw_family_globally_unlinked_fresh_for_target[
          OF family_e unlinked_e target geometry_e])
  have p_managed:
      "?p \<in> universal_managed_nodes managed D"
    using task
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have generic_pre_e_observed:
      "scheduler_family_pre_rel ?he GenericRootUniverse ?generic_raw_g
         (sa_live (managed_scheduler_view current managed)) D"
    using generic_pre_e by (simp add: managed_scheduler_view_def)
  have p_managed_observed:
      "?p \<in> universal_managed_nodes
         (sa_live (managed_scheduler_view current managed)) D"
    using p_managed by (simp add: managed_scheduler_view_def)
  have observation_i:
      "TaskObservationRel D ?hi
         (managed_scheduler_view current managed)"
    unfolding managed_due_ready_insert_heap_def
    by (rule TaskObservationRel_insert_end_preserved[
          OF observation_e generic_pre_e_observed target fresh_e
             p_managed_observed])

  show ?thesis
    using observation observation_g branch_accounted observation_e
      generic_coverage_e unlinked_e fresh_e observation_i
    by (simp add: Let_def)
qed

text \<open>
  Strong-snapshot entry corollary.  The managed task premise is derived from
  the strong lifecycle domain; the managed observation and both family
  coverages are projected from the same snapshot.  The only remaining input
  facts are semantic control facts: the chosen runnable task, its abstract
  source membership, the chosen target root, and the stable empty-pending
  boundary.  These are precisely what the due-prefix loop/head connector must
  provide; no concrete owner, member, freshness or desired post-relation is a
  premise.
\<close>

corollary StrongSchedulerSnapshotRel_managed_observation_exact_cutpoints:
  assumes snapshot:
      "StrongSchedulerSnapshotRel D c current managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task_live: "t \<in> sa_live current"
    and source: "source \<in> GenericRootUniverse"
    and source_member:
      "Generic t \<in> set (ring (generic_abs source))"
    and target: "target \<in> GenericRootUniverse"
    and pending_empty: "ring (sa_pending current) = []"
  shows
    "let h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
         hg = managed_due_generic_remove_heap D t h0;
         generic_raw_g =
           managed_due_generic_raw_after_remove D t source generic_raw;
         generic_abs_g =
           managed_due_generic_abs_after_remove t source generic_abs;
         he = managed_due_optional_event_remove_heap D t hg;
         hi = managed_due_ready_insert_heap D t target generic_raw_g he;
         p = generic_item_raw_ptr D t;
         ep = event_item_raw_ptr D t
     in TaskObservationRel D h0
          (managed_scheduler_view current managed) \<and>
        TaskObservationRel D hg
          (managed_scheduler_view current managed) \<and>
        ((pvContainer_C (h_val hg ep) = NULL \<and>
            raw_family_members (EventRootUniverse external) event_raw ep = {})
         \<or>
         (\<exists>owner. owner \<in> external \<and>
            ep \<in> set (ring (event_raw owner)) \<and>
            pvContainer_C (h_val hg ep) =
              PTR_COERCE(xLIST_C \<rightarrow> unit) owner)) \<and>
        TaskObservationRel D he
          (managed_scheduler_view current managed) \<and>
        GenericRootFamilyCoverage D he GenericRootUniverse
          generic_raw_g generic_abs_g managed K_G \<and>
        raw_family_globally_unlinked he GenericRootUniverse
          generic_raw_g p \<and>
        raw_fresh_for_insert target (ring (generic_raw_g target)) p \<and>
        TaskObservationRel D hi
          (managed_scheduler_view current managed)"
proof -
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  have domain: "strong_managed_domain_rel current termination managed"
    by (rule StrongSchedulerSnapshotRel_domainD[OF snapshot])
  have live_subset: "sa_live current \<subseteq> managed"
    using domain by (simp add: strong_managed_domain_rel_def)
  have task_managed: "t \<in> managed"
    by (rule subsetD[OF live_subset task_live])
  have observation:
      "TaskObservationRel D ?h0
         (managed_scheduler_view current managed)"
    using StrongSchedulerSnapshotRel_managed_observationD[OF snapshot]
    by (simp add: scheduler_managed_task_observation_rel_def)
  have generic_coverage:
      "GenericRootFamilyCoverage D ?h0 GenericRootUniverse
         generic_raw generic_abs managed K_G"
    by (rule StrongSchedulerSnapshotRel_generic_coverageD[OF snapshot])
  have event_coverage:
      "EventRootFamilyCoverage external D ?h0
         event_raw event_abs managed K_E"
    by (rule StrongSchedulerSnapshotRel_event_coverageD[OF snapshot])
  have event_projection:
      "strong_event_role_projection current managed external event_abs"
    by (rule StrongSchedulerSnapshotRel_event_projectionD[OF snapshot])
  have pending_projection:
      "event_abs GeneratedPendingEventRoot = sa_pending current"
    by (rule strong_event_role_pendingD[OF event_projection])
  have pending_event_empty:
      "ring (event_abs GeneratedPendingEventRoot) = []"
    using pending_empty pending_projection by simp
  have composed:
      "let hg = managed_due_generic_remove_heap D t ?h0;
           generic_raw_g =
             managed_due_generic_raw_after_remove D t source generic_raw;
           generic_abs_g =
             managed_due_generic_abs_after_remove t source generic_abs;
           he = managed_due_optional_event_remove_heap D t hg;
           hi = managed_due_ready_insert_heap D t target generic_raw_g he;
           p = generic_item_raw_ptr D t;
           ep = event_item_raw_ptr D t
       in TaskObservationRel D ?h0
            (managed_scheduler_view current managed) \<and>
          TaskObservationRel D hg
            (managed_scheduler_view current managed) \<and>
          ((pvContainer_C (h_val hg ep) = NULL \<and>
              raw_family_members (EventRootUniverse external) event_raw ep = {})
           \<or>
           (\<exists>owner. owner \<in> external \<and>
              ep \<in> set (ring (event_raw owner)) \<and>
              pvContainer_C (h_val hg ep) =
                PTR_COERCE(xLIST_C \<rightarrow> unit) owner)) \<and>
          TaskObservationRel D he
            (managed_scheduler_view current managed) \<and>
          GenericRootFamilyCoverage D he GenericRootUniverse
            generic_raw_g generic_abs_g managed K_G \<and>
          raw_family_globally_unlinked he GenericRootUniverse
            generic_raw_g p \<and>
          raw_fresh_for_insert target (ring (generic_raw_g target)) p \<and>
          TaskObservationRel D hi
            (managed_scheduler_view current managed)"
    by (rule managed_TaskObservationRel_exact_cutpoints[
          OF observation generic_coverage event_coverage task_managed
             source source_member target pending_event_empty])
  show ?thesis
    using composed by (simp add: Let_def)
qed

end

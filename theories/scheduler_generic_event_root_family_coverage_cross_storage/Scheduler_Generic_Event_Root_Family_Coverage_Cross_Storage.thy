theory Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage.Scheduler_Generic_Root_Universe_Coverage"
begin

text \<open>
  Cross-kind storage separation at one whole-scheduler cutpoint.

  Both coverage relations below observe the same heap, decoder and finite
  allocated-and-observable TCB domain.  That domain is intentionally not
  narrowed to runnable tasks: callers use it for every managed TCB, including
  tasks still owned by xTasksWaitingTermination.  Roots, rings, task
  identities, payloads and the finite external Event-root family remain
  symbolic.

  No cross-family storage premise is assumed.  Generic/Event pointer-kind
  exclusion follows from the common decoder laws.  Item-region separation
  then follows from the TCB geometry already carried by Generic coverage.
  The remaining root-versus-root and root-versus-item cases follow from the
  two coverage relations themselves.
\<close>

lemma universal_decoder_laws_generic_event_ptr_distinct:
  assumes laws: "universal_decoder_laws managed D"
    and generic_task: "u \<in> managed"
    and event_task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
proof
  assume equal:
    "generic_item_raw_ptr D u = event_item_raw_ptr D t"
  have generic_decode:
    "sd_node_decode D (generic_item_raw_ptr D u) = Some (Generic u)"
    using universal_node_decode_Generic_iff[
        OF laws, where p="generic_item_raw_ptr D u" and t=u]
      generic_task
    by (simp add: generic_item_raw_ptr_def)
  have event_decode:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    using universal_node_decode_Event_iff[
        OF laws, where p="event_item_raw_ptr D t" and t=t]
      event_task
    by (simp add: event_item_raw_ptr_def)
  show False
    using generic_decode event_decode equal by simp
qed

lemma GenericRootFamilyCoverage_generic_event_ptr_distinct:
  assumes coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and generic_task: "u \<in> managed"
    and event_task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
  by (rule universal_decoder_laws_generic_event_ptr_distinct[
        OF GenericRootFamilyCoverage_decoder_lawsD[OF coverage]
           generic_task event_task])

lemma EventRootFamilyCoverage_generic_event_ptr_distinct:
  assumes coverage:
    "EventRootFamilyCoverage
       external D h event_raw event_abs managed K_E"
    and generic_task: "u \<in> managed"
    and event_task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
proof -
  have laws: "universal_decoder_laws managed D"
    by (rule scheduler_event_root_family_decoder_lawsD[
          OF EventRootFamilyCoverage_relD[OF coverage]])
  show ?thesis
    by (rule universal_decoder_laws_generic_event_ptr_distinct[
          OF laws generic_task event_task])
qed

lemma GenericRootFamilyCoverage_generic_event_item_regions_disjoint:
  assumes coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and generic_task: "u \<in> managed"
    and event_task: "t \<in> managed"
  shows
    "raw_item_region (generic_item_raw_ptr D u) \<inter>
       raw_item_region (event_item_raw_ptr D t) = {}"
proof -
  have pre:
    "scheduler_family_pre_rel h roots generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have geometry: "universal_tcb_geometry managed D"
    using pre by (simp add: scheduler_family_pre_rel_def)
  have generic_managed:
    "generic_item_raw_ptr D u \<in> universal_managed_nodes managed D"
    using generic_task
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have event_managed:
    "event_item_raw_ptr D t \<in> universal_managed_nodes managed D"
    using event_task
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have distinct:
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule GenericRootFamilyCoverage_generic_event_ptr_distinct[
          OF coverage generic_task event_task])
  show ?thesis
    by (rule universal_distinct_managed_item_regions_disjoint[
          OF geometry generic_managed event_managed distinct])
qed

lemma GenericRootFamilyCoverage_event_generic_item_regions_disjoint:
  assumes coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and event_task: "t \<in> managed"
    and generic_task: "u \<in> managed"
  shows
    "raw_item_region (event_item_raw_ptr D t) \<inter>
       raw_item_region (generic_item_raw_ptr D u) = {}"
  using GenericRootFamilyCoverage_generic_event_item_regions_disjoint[
      OF coverage generic_task event_task]
  by (simp add: Int_commute)

lemma GenericRootFamilyCoverage_event_notin_generic_root:
  assumes coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and event_task: "t \<in> managed"
    and root: "g \<in> roots"
  shows
    "event_item_raw_ptr D t \<notin> set (ring (generic_raw g))"
proof
  assume member:
    "event_item_raw_ptr D t \<in> set (ring (generic_raw g))"
  have subset:
    "set (ring (generic_raw g)) \<subseteq>
       generic_item_raw_set managed D"
    using GenericRootFamilyCoverage_root_repD[OF coverage root]
    by (simp add: generic_family_root_rep_def)
  obtain u where generic_task: "u \<in> managed"
    and equal:
      "event_item_raw_ptr D t = generic_item_raw_ptr D u"
    using subsetD[OF subset member]
    by (auto simp: generic_item_raw_set_def)
  have distinct:
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule GenericRootFamilyCoverage_generic_event_ptr_distinct[
          OF coverage generic_task event_task])
  show False using equal distinct by simp
qed

lemma EventRootFamilyCoverage_generic_notin_event_root:
  assumes coverage:
    "EventRootFamilyCoverage
       external D h event_raw event_abs managed K_E"
    and generic_task: "u \<in> managed"
    and root: "e \<in> EventRootUniverse external"
  shows
    "generic_item_raw_ptr D u \<notin> set (ring (event_raw e))"
proof
  assume member:
    "generic_item_raw_ptr D u \<in> set (ring (event_raw e))"
  have family:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF coverage])
  have subset:
    "set (ring (event_raw e)) \<subseteq>
       event_item_raw_set managed D"
    using scheduler_event_root_family_root_repD[OF family root]
    by (simp add: event_family_root_rep_def)
  obtain t where event_task: "t \<in> managed"
    and equal:
      "generic_item_raw_ptr D u = event_item_raw_ptr D t"
    using subsetD[OF subset member]
    by (auto simp: event_item_raw_set_def)
  have distinct:
    "generic_item_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule EventRootFamilyCoverage_generic_event_ptr_distinct[
          OF coverage generic_task event_task])
  show False using equal distinct by simp
qed

theorem GenericEventRootFamilyCoverage_cross_storage:
  assumes generic_coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and event_coverage:
    "EventRootFamilyCoverage
       external D h event_raw event_abs managed K_E"
    and generic_root: "g \<in> roots"
    and event_root: "e \<in> EventRootUniverse external"
  shows
    "raw_xlist_storage g (generic_raw g) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
proof -
  have universe: "roots = GenericRootUniverse"
    by (rule GenericRootFamilyCoverage_universeD[OF generic_coverage])
  have generic_pre:
    "scheduler_family_pre_rel h roots generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_coverage])
  have event_family:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF event_coverage])
  have event_pre:
    "scheduler_family_pre_rel h (EventRootUniverse external)
       event_raw managed D"
    by (rule scheduler_event_root_family_preD[OF event_family])
  have generic_subset:
    "set (ring (generic_raw g)) \<subseteq>
       generic_item_raw_set managed D"
    using GenericRootFamilyCoverage_root_repD[
        OF generic_coverage generic_root]
    by (simp add: generic_family_root_rep_def)
  have event_subset:
    "set (ring (event_raw e)) \<subseteq>
       event_item_raw_set managed D"
    using scheduler_event_root_family_root_repD[OF event_family event_root]
    by (simp add: event_family_root_rep_def)

  have root_regions:
    "raw_list_region g \<inter> raw_list_region e = {}"
  proof -
    have input_wf: "EventExternalRootInputWF external"
      by (rule EventRootFamilyCoverage_external_wfD[OF event_coverage])
    have reverse:
      "raw_list_region e \<inter> raw_list_region g = {}"
      using input_wf event_root generic_root universe
      by (auto simp: EventExternalRootInputWF_def)
    show ?thesis using reverse by (simp add: Int_commute)
  qed

  have generic_root_event_items:
    "raw_list_region g \<inter>
       (\<Union>q\<in>set (ring (event_raw e)). raw_item_region q) = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> raw_list_region g \<inter>
        (\<Union>q\<in>set (ring (event_raw e)). raw_item_region q)"
    then obtain q where
        q_ring: "q \<in> set (ring (event_raw e))"
      and x_root: "x \<in> raw_list_region g"
      and x_item: "x \<in> raw_item_region q"
      by blast
    have q_managed: "q \<in> universal_managed_nodes managed D"
      using subsetD[OF event_subset q_ring]
      by (auto simp: event_item_raw_set_def event_item_raw_ptr_def
          universal_managed_nodes_def)
    have disjoint:
      "raw_list_region g \<inter> raw_item_region q = {}"
      by (rule scheduler_family_root_managed_item_disjoint[
            OF generic_pre generic_root q_managed])
    show False using disjoint x_root x_item by blast
  qed

  have generic_items_event_root:
    "(\<Union>p\<in>set (ring (generic_raw g)). raw_item_region p) \<inter>
       raw_list_region e = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> (\<Union>p\<in>set (ring (generic_raw g)). raw_item_region p)
          \<inter> raw_list_region e"
    then obtain p where
        p_ring: "p \<in> set (ring (generic_raw g))"
      and x_item: "x \<in> raw_item_region p"
      and x_root: "x \<in> raw_list_region e"
      by blast
    have p_managed: "p \<in> universal_managed_nodes managed D"
      using subsetD[OF generic_subset p_ring]
      by (auto simp: generic_item_raw_set_def generic_item_raw_ptr_def
          universal_managed_nodes_def)
    have disjoint:
      "raw_list_region e \<inter> raw_item_region p = {}"
      by (rule scheduler_family_root_managed_item_disjoint[
            OF event_pre event_root p_managed])
    show False using disjoint x_root x_item by blast
  qed

  have item_regions:
    "(\<Union>p\<in>set (ring (generic_raw g)). raw_item_region p) \<inter>
       (\<Union>q\<in>set (ring (event_raw e)). raw_item_region q) = {}"
  proof (rule equals0I)
    fix x
    assume member:
      "x \<in> (\<Union>p\<in>set (ring (generic_raw g)). raw_item_region p)
          \<inter>
        (\<Union>q\<in>set (ring (event_raw e)). raw_item_region q)"
    then obtain p q where
        p_ring: "p \<in> set (ring (generic_raw g))"
      and q_ring: "q \<in> set (ring (event_raw e))"
      and x_p: "x \<in> raw_item_region p"
      and x_q: "x \<in> raw_item_region q"
      by blast
    obtain u where generic_task: "u \<in> managed"
      and p: "p = generic_item_raw_ptr D u"
      using subsetD[OF generic_subset p_ring]
      by (auto simp: generic_item_raw_set_def)
    obtain t where event_task: "t \<in> managed"
      and q: "q = event_item_raw_ptr D t"
      using subsetD[OF event_subset q_ring]
      by (auto simp: event_item_raw_set_def)
    have disjoint:
      "raw_item_region p \<inter> raw_item_region q = {}"
      using GenericRootFamilyCoverage_generic_event_item_regions_disjoint[
          OF generic_coverage generic_task event_task]
        p q
      by simp
    show False using disjoint x_p x_q by blast
  qed

  show ?thesis
    unfolding raw_xlist_storage_def
    using root_regions generic_root_event_items generic_items_event_root
      item_regions
    by blast
qed

corollary GenericEventRootFamilyCoverage_cross_storage_all:
  assumes generic_coverage:
    "GenericRootFamilyCoverage
       D h roots generic_raw generic_abs managed K_G"
    and event_coverage:
    "EventRootFamilyCoverage
       external D h event_raw event_abs managed K_E"
  shows
    "\<forall>g\<in>roots. \<forall>e\<in>EventRootUniverse external.
       raw_xlist_storage g (generic_raw g) \<inter>
         raw_xlist_storage e (event_raw e) = {}"
  using GenericEventRootFamilyCoverage_cross_storage[
      OF generic_coverage event_coverage]
  by blast

end

theory Scheduler_Generic_Insert_End_Frames_Event_Coverage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage.Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage"
    "EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Event_Heap_Frame.Scheduler_Global_Coverage_Event_Heap_Frame"
begin

text \<open>
  Insert-end into an arbitrary configured Generic root changes only the old
  target storage and the inserted Generic item.  The cross-family coverage
  theorem separates the old target storage from every Event root.  The Event
  family relation itself separates the inserted Generic item from each Event
  root, while the Generic family relation separates every observed Event item
  from the insert footprint.  Hence the complete Event coverage is a frame.

  No global-absence premise is needed: this theorem establishes only the
  unchanged Event projection.  Global Generic ownership is handled by the
  independent Generic insert-end coverage theorem.
\<close>

section \<open>Event root-storage frame\<close>

lemma GenericRootFamilyCoverage_insert_end_event_storage_frame:
  assumes generic:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and event:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and fresh:
      "raw_fresh_for_insert target (ring (generic_raw target))
         (generic_item_raw_ptr D t)"
    and event_root: "e \<in> EventRootUniverse external"
    and address: "address \<in> raw_xlist_storage e (event_raw e)"
  shows
    "raw_insert_concrete_heap h target (generic_raw target)
       (generic_item_raw_ptr D t) address = h address"
proof -
  let ?p = "generic_item_raw_ptr D t"
  have event_pre:
    "scheduler_family_pre_rel h (EventRootUniverse external)
       event_raw managed D"
    by (rule scheduler_event_root_family_preD[
          OF EventRootFamilyCoverage_relD[OF event]])
  have target_rel: "raw_xlist_rel h target (generic_raw target)"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF generic target])
  have footprint:
    "raw_insert_end_exact_write_footprint h target
       (generic_raw target) ?p
       \<subseteq> raw_xlist_storage target (generic_raw target) \<union>
         raw_item_region ?p"
    by (rule raw_insert_end_exact_footprint_subset_storage[OF target_rel])
  have target_event_disjoint:
    "raw_xlist_storage target (generic_raw target) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage[
          OF generic event target event_root])
  have p_managed: "?p \<in> universal_managed_nodes managed D"
    using task
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have p_nonmember:
    "?p \<notin> set (ring (event_raw e))"
    by (rule EventRootFamilyCoverage_generic_notin_event_root[
          OF event task event_root])
  have event_p_disjoint:
    "raw_xlist_storage e (event_raw e) \<inter> raw_item_region ?p = {}"
    by (rule scheduler_family_target_storage_disjoint_nonmember_item[
          OF event_pre event_root p_managed p_nonmember])
  have outside:
    "address \<notin> raw_insert_end_exact_write_footprint h target
       (generic_raw target) ?p"
    using footprint target_event_disjoint event_p_disjoint address by blast
  show ?thesis
    by (rule raw_insert_concrete_heap_exact_external_frame[
          OF target_rel fresh outside])
qed

section \<open>Managed Event-item frame\<close>

lemma GenericRootFamilyCoverage_insert_end_event_item_frame:
  assumes generic:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and fresh:
      "raw_fresh_for_insert target (ring (generic_raw target))
         (generic_item_raw_ptr D t)"
    and observed: "u \<in> managed"
  shows
    "h_val
       (raw_insert_concrete_heap h target (generic_raw target)
         (generic_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
     h_val h (event_item_raw_ptr D u)"
proof -
  let ?p = "generic_item_raw_ptr D t"
  let ?q = "event_item_raw_ptr D u"
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic])
  have p_managed: "?p \<in> universal_managed_nodes managed D"
    using task
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have q_managed: "?q \<in> universal_managed_nodes managed D"
    using observed
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have p_q: "?p \<noteq> ?q"
    by (rule GenericRootFamilyCoverage_generic_event_ptr_distinct[
          OF generic task observed])
  have q_nonmember: "?q \<notin> set (ring (generic_raw target))"
    by (rule GenericRootFamilyCoverage_event_notin_generic_root[
          OF generic observed target])
  have bytes:
    "\<forall>address\<in>raw_item_region ?q.
       raw_insert_concrete_heap h target (generic_raw target) ?p address =
         h address"
    using raw_insert_end_family_sibling_item_priority_byte_frame[
      OF pre target fresh p_managed q_managed p_q q_nonmember task]
    by blast
  show ?thesis
  proof (rule delay_h_val_region_cong)
    fix address
    assume
      "address \<in>
         {ptr_val ?q..+size_of TYPE(xLIST_ITEM_C)}"
    then show
      "raw_insert_concrete_heap h target (generic_raw target) ?p address =
       h address"
      using bytes by (simp add: raw_item_region_def)
  qed
qed

section \<open>Unchanged Event coverage\<close>

theorem Generic_insert_end_frames_Event_coverage:
  assumes generic:
      "GenericRootFamilyCoverage D h GenericRootUniverse
         generic_raw generic_abs managed K_G"
    and event:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and fresh:
      "raw_fresh_for_insert target (ring (generic_raw target))
         (generic_item_raw_ptr D t)"
  shows
    "EventRootFamilyCoverage external D
       (raw_insert_concrete_heap h target (generic_raw target)
         (generic_item_raw_ptr D t))
       event_raw event_abs managed K_E"
proof (rule EventRootFamilyCoverage_heap_frameI[OF event])
  fix e address
  assume event_root: "e \<in> EventRootUniverse external"
    and address: "address \<in> raw_xlist_storage e (event_raw e)"
  show
    "raw_insert_concrete_heap h target (generic_raw target)
       (generic_item_raw_ptr D t) address = h address"
    by (rule GenericRootFamilyCoverage_insert_end_event_storage_frame[
          OF generic event target task fresh event_root address])
next
  fix u
  assume observed: "u \<in> managed"
  show
    "h_val
       (raw_insert_concrete_heap h target (generic_raw target)
         (generic_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
     h_val h (event_item_raw_ptr D u)"
    by (rule GenericRootFamilyCoverage_insert_end_event_item_frame[
          OF generic target task fresh observed])
qed

end

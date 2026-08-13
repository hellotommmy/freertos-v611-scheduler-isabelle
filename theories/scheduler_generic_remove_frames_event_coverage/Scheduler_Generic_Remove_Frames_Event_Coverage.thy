theory Scheduler_Generic_Remove_Frames_Event_Coverage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage.Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage"
    "EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Event_Heap_Frame.Scheduler_Global_Coverage_Event_Heap_Frame"
begin

text \<open>
  Removing a represented Generic item changes the exact generated-list remove
  footprint of its arbitrary source root and no Event observation.  Both root
  families, every ring and cursor, the decoder, task domain, keys, source root
  and removed task remain symbolic.  In particular, the source may be the
  termination root and managed includes every allocated observable TCB,
  including TCBs waiting for termination.
\<close>

theorem Generic_remove_frames_Event_coverage:
  assumes generic_coverage:
      "GenericRootFamilyCoverage D h generic_roots
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and source: "source \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and member:
      "generic_item_raw_ptr D t \<in>
         set (ring (generic_raw source))"
  shows
    "EventRootFamilyCoverage external D
       (raw_remove_concrete_heap h (generic_item_raw_ptr D t))
       event_raw event_abs managed K_E"
proof (rule EventRootFamilyCoverage_heap_frameI[OF event_coverage])
  fix event_root address
  assume event_root:
      "event_root \<in> EventRootUniverse external"
    and address:
      "address \<in> raw_xlist_storage event_root (event_raw event_root)"
  have source_root: "source \<in> generic_roots"
    using source
      GenericRootFamilyCoverage_universeD[OF generic_coverage]
    by simp
  have source_rel:
      "raw_xlist_rel h source (generic_raw source)"
    by (rule GenericRootFamilyCoverage_raw_rootD[
          OF generic_coverage source_root])
  have footprint:
      "raw_remove_exact_write_footprint h source
         (generic_item_raw_ptr D t)
       \<subseteq> raw_xlist_storage source (generic_raw source)"
    by (rule raw_remove_exact_footprint_subset_storage[
          OF source_rel member])
  have storage_disjoint:
      "raw_xlist_storage source (generic_raw source) \<inter>
         raw_xlist_storage event_root (event_raw event_root) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage[
          OF generic_coverage event_coverage source_root event_root])
  have outside:
      "address \<notin> raw_remove_exact_write_footprint h source
         (generic_item_raw_ptr D t)"
    using footprint storage_disjoint address by blast
  show
    "raw_remove_concrete_heap h (generic_item_raw_ptr D t) address =
       h address"
    by (rule raw_remove_concrete_heap_exact_external_frame[
          OF source_rel member outside])
next
  fix u
  assume u_managed: "u \<in> managed"
  have source_root: "source \<in> generic_roots"
    using source
      GenericRootFamilyCoverage_universeD[OF generic_coverage]
    by simp
  have pre:
      "scheduler_family_pre_rel h generic_roots generic_raw managed D"
    by (rule GenericRootFamilyCoverage_preD[OF generic_coverage])
  have event_managed:
      "event_item_raw_ptr D u \<in> universal_managed_nodes managed D"
    using u_managed
    by (auto simp: event_item_raw_ptr_def universal_managed_nodes_def)
  have event_nonmember:
      "event_item_raw_ptr D u \<notin>
         set (ring (generic_raw source))"
    by (rule GenericRootFamilyCoverage_event_notin_generic_root[
          OF generic_coverage u_managed source_root])
  have byte_frame:
      "\<forall>address\<in>raw_item_region (event_item_raw_ptr D u).
         raw_remove_concrete_heap h (generic_item_raw_ptr D t) address =
           h address"
    by (rule scheduler_family_remove_nonmember_item_byte_frame[
          OF pre source_root member event_managed event_nonmember])
  show
    "h_val (raw_remove_concrete_heap h (generic_item_raw_ptr D t))
       (event_item_raw_ptr D u) =
     h_val h (event_item_raw_ptr D u)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume address:
      "address \<in>
         {ptr_val (event_item_raw_ptr D u)..+
          size_of TYPE(xLIST_ITEM_C)}"
    show
      "raw_remove_concrete_heap h (generic_item_raw_ptr D t) address =
       h address"
      using byte_frame address
      by (simp add: raw_item_region_def)
  qed
qed

end

theory Scheduler_Event_Remove_Frames_Generic_Coverage
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage.Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage"
    "EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Optional_Event_Remove.Scheduler_Global_Coverage_Optional_Event_Remove"
begin

text \<open>
  Removing an Event item from an arbitrary represented Event root changes no
  Generic observation.  The Event source root, both complete root families,
  every task identity and both total payload observations remain symbolic.
  Both coverage relations use the same heap, decoder and managed TCB domain;
  that domain includes every allocated observable TCB, including tasks owned
  by the termination list.

  The exact remove footprint is contained in the old Event-root storage.
  Whole-scheduler cross-kind separation frames every Generic root, while the
  same decoder and TCB geometry frame every Generic item, including the
  removed task's sibling Generic item.
\<close>

theorem Event_remove_frames_Generic_coverage:
  assumes generic_coverage:
      "GenericRootFamilyCoverage D h generic_roots
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and source: "source \<in> EventRootUniverse external"
    and task: "t \<in> managed"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (event_raw source))"
  shows
    "GenericRootFamilyCoverage D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       generic_roots generic_raw generic_abs managed K_G"
proof (rule GenericRootFamilyCoverage_heap_frameI[OF generic_coverage])
  fix generic_root address
  assume generic_root: "generic_root \<in> generic_roots"
    and address:
      "address \<in> raw_xlist_storage generic_root
         (generic_raw generic_root)"
  have source_rel: "raw_xlist_rel h source (event_raw source)"
    by (rule scheduler_event_root_family_raw_rootD[
          OF EventRootFamilyCoverage_relD[OF event_coverage] source])
  have footprint:
      "raw_remove_exact_write_footprint h source
         (event_item_raw_ptr D t)
       \<subseteq> raw_xlist_storage source (event_raw source)"
    by (rule raw_remove_exact_footprint_subset_storage[
          OF source_rel member])
  have storage_disjoint:
      "raw_xlist_storage generic_root (generic_raw generic_root) \<inter>
         raw_xlist_storage source (event_raw source) = {}"
    by (rule GenericEventRootFamilyCoverage_cross_storage[
          OF generic_coverage event_coverage generic_root source])
  have outside:
      "address \<notin> raw_remove_exact_write_footprint h source
         (event_item_raw_ptr D t)"
    using footprint storage_disjoint address by blast
  show
    "raw_remove_concrete_heap h (event_item_raw_ptr D t) address =
       h address"
    by (rule raw_remove_concrete_heap_exact_external_frame[
          OF source_rel member outside])
next
  fix u
  assume observed: "u \<in> managed"
  have event_pre:
      "scheduler_family_pre_rel h (EventRootUniverse external)
         event_raw managed D"
    by (rule scheduler_event_root_family_preD[
          OF EventRootFamilyCoverage_relD[OF event_coverage]])
  have generic_managed:
      "generic_item_raw_ptr D u \<in> universal_managed_nodes managed D"
    using observed
    by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
  have generic_nonmember:
      "generic_item_raw_ptr D u \<notin> set (ring (event_raw source))"
    by (rule EventRootFamilyCoverage_generic_notin_event_root[
          OF event_coverage observed source])
  have byte_frame:
      "\<forall>address\<in>raw_item_region (generic_item_raw_ptr D u).
         raw_remove_concrete_heap h (event_item_raw_ptr D t) address =
           h address"
    by (rule scheduler_family_remove_nonmember_item_byte_frame[
          OF event_pre source member generic_managed generic_nonmember])
  show
    "h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (generic_item_raw_ptr D u) =
     h_val h (generic_item_raw_ptr D u)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume address:
      "address \<in>
         {ptr_val (generic_item_raw_ptr D u)..+
          size_of TYPE(xLIST_ITEM_C)}"
    show
      "raw_remove_concrete_heap h (event_item_raw_ptr D t) address =
       h address"
      using byte_frame address
      by (simp add: raw_item_region_def)
  qed
qed

text \<open>
  The generated wake path does not supply an Event owner.  The physical
  container branch and complete Event coverage determine it instead.  This
  wrapper strengthens both branches of the existing optional-remove theorem
  with the unchanged Generic coverage: NULL is a genuine heap no-op, while a
  non-NULL container yields the arbitrary external owner and then applies the
  cross-kind frame theorem above.  No owner, externality or entry-membership
  premise is exposed to callers.
\<close>

theorem EventRootFamilyCoverage_optional_remove_frames_Generic_coverage:
  assumes generic_coverage:
      "GenericRootFamilyCoverage D h generic_roots
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and task: "t \<in> managed"
    and pending_empty:
      "ring (event_abs GeneratedPendingEventRoot) = []"
  shows
    "if pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL then
       raw_family_members (EventRootUniverse external) event_raw
         (event_item_raw_ptr D t) = {} \<and>
       EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E \<and>
       GenericRootFamilyCoverage D h generic_roots
         generic_raw generic_abs managed K_G
     else
       \<exists>owner. owner \<in> external \<and>
         event_item_raw_ptr D t \<in> set (ring (event_raw owner)) \<and>
         pvContainer_C (h_val h (event_item_raw_ptr D t)) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<and>
         EventRootFamilyCoverage external D
           (raw_remove_concrete_heap h (event_item_raw_ptr D t))
           (event_remove_raw_family event_raw owner
             (event_item_raw_ptr D t))
           (event_remove_abs_family event_abs owner t) managed K_E \<and>
         GenericRootFamilyCoverage D
           (raw_remove_concrete_heap h (event_item_raw_ptr D t))
           generic_roots generic_raw generic_abs managed K_G \<and>
         pvContainer_C
           (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
             (event_item_raw_ptr D t)) = NULL \<and>
         raw_family_members (EventRootUniverse external)
           (event_remove_raw_family event_raw owner
             (event_item_raw_ptr D t))
           (event_item_raw_ptr D t) = {}"
proof (cases
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL")
  case True
  have optional:
      "raw_family_members (EventRootUniverse external) event_raw
         (event_item_raw_ptr D t) = {} \<and>
       EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    using EventRootFamilyCoverage_optional_remove_from_container[
      OF event_coverage task pending_empty]
      True by simp
  show ?thesis
    using True optional generic_coverage by simp
next
  case False
  have optional:
      "\<exists>owner. owner \<in> external \<and>
        event_item_raw_ptr D t \<in> set (ring (event_raw owner)) \<and>
        pvContainer_C (h_val h (event_item_raw_ptr D t)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<and>
        EventRootFamilyCoverage external D
          (raw_remove_concrete_heap h (event_item_raw_ptr D t))
          (event_remove_raw_family event_raw owner
            (event_item_raw_ptr D t))
          (event_remove_abs_family event_abs owner t) managed K_E \<and>
        pvContainer_C
          (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
            (event_item_raw_ptr D t)) = NULL \<and>
        raw_family_members (EventRootUniverse external)
          (event_remove_raw_family event_raw owner
            (event_item_raw_ptr D t))
          (event_item_raw_ptr D t) = {}"
    using EventRootFamilyCoverage_optional_remove_from_container[
      OF event_coverage task pending_empty]
      False by simp
  then obtain owner where owner_external: "owner \<in> external"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (event_raw owner))"
    and container:
      "pvContainer_C (h_val h (event_item_raw_ptr D t)) =
        PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    and event_post:
      "EventRootFamilyCoverage external D
        (raw_remove_concrete_heap h (event_item_raw_ptr D t))
        (event_remove_raw_family event_raw owner
          (event_item_raw_ptr D t))
        (event_remove_abs_family event_abs owner t) managed K_E"
    and post_null:
      "pvContainer_C
        (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
          (event_item_raw_ptr D t)) = NULL"
    and post_absent:
      "raw_family_members (EventRootUniverse external)
        (event_remove_raw_family event_raw owner
          (event_item_raw_ptr D t))
        (event_item_raw_ptr D t) = {}"
    by blast
  have owner_root: "owner \<in> EventRootUniverse external"
    by (rule EventRootUniverse_externalI[OF owner_external])
  have generic_post:
      "GenericRootFamilyCoverage D
        (raw_remove_concrete_heap h (event_item_raw_ptr D t))
        generic_roots generic_raw generic_abs managed K_G"
    by (rule Event_remove_frames_Generic_coverage[
          OF generic_coverage event_coverage owner_root task member])
  have branch:
      "\<exists>owner. owner \<in> external \<and>
        event_item_raw_ptr D t \<in> set (ring (event_raw owner)) \<and>
        pvContainer_C (h_val h (event_item_raw_ptr D t)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<and>
        EventRootFamilyCoverage external D
          (raw_remove_concrete_heap h (event_item_raw_ptr D t))
          (event_remove_raw_family event_raw owner
            (event_item_raw_ptr D t))
          (event_remove_abs_family event_abs owner t) managed K_E \<and>
        GenericRootFamilyCoverage D
          (raw_remove_concrete_heap h (event_item_raw_ptr D t))
          generic_roots generic_raw generic_abs managed K_G \<and>
        pvContainer_C
          (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
            (event_item_raw_ptr D t)) = NULL \<and>
        raw_family_members (EventRootUniverse external)
          (event_remove_raw_family event_raw owner
            (event_item_raw_ptr D t))
          (event_item_raw_ptr D t) = {}"
    by (rule exI[where x=owner])
       (use owner_external member container event_post generic_post
          post_null post_absent in blast)
  show ?thesis
    using False branch by simp
qed

corollary EventRootFamilyCoverage_optional_remove_Generic_heap_coverage:
  assumes generic_coverage:
      "GenericRootFamilyCoverage D h generic_roots
         generic_raw generic_abs managed K_G"
    and event_coverage:
      "EventRootFamilyCoverage external D h
         event_raw event_abs managed K_E"
    and task: "t \<in> managed"
    and pending_empty:
      "ring (event_abs GeneratedPendingEventRoot) = []"
  shows
    "GenericRootFamilyCoverage D
       (if pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL
        then h
        else raw_remove_concrete_heap h (event_item_raw_ptr D t))
       generic_roots generic_raw generic_abs managed K_G"
proof (cases
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL")
  case True
  show ?thesis using True generic_coverage by simp
next
  case False
  obtain owner where owner_external: "owner \<in> external"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (event_raw owner))"
    using EventRootFamilyCoverage_linked_owner_externalD[
      OF event_coverage task pending_empty False]
    by blast
  have owner_root: "owner \<in> EventRootUniverse external"
    by (rule EventRootUniverse_externalI[OF owner_external])
  have post:
      "GenericRootFamilyCoverage D
        (raw_remove_concrete_heap h (event_item_raw_ptr D t))
        generic_roots generic_raw generic_abs managed K_G"
    by (rule Event_remove_frames_Generic_coverage[
          OF generic_coverage event_coverage owner_root task member])
  show ?thesis using False post by simp
qed

end

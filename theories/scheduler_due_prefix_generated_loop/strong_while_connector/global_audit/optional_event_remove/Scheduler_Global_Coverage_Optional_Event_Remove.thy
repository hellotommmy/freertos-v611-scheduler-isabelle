theory Scheduler_Global_Coverage_Optional_Event_Remove
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Event_Heap_Frame.Scheduler_Global_Coverage_Event_Heap_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Preservation.Scheduler_Event_Root_Family_Remove_Preservation"
begin

text \<open>
  The generated wake path branches on the physical Event-item container.  A
  non-null container is not supplied with a guessed owner: total coverage
  yields its unique represented root.  An empty pending ring excludes the
  distinguished pending root, leaving an arbitrary external owner.  A null
  container yields global absence directly from faithful coverage and is a
  genuine no-op branch.
\<close>

lemma EventRootFamilyCoverage_linked_owner_externalD:
  assumes coverage:
      "EventRootFamilyCoverage
         external D h raw_fam abs_fam managed K_E"
    and task: "t \<in> managed"
    and pending_empty:
      "ring (abs_fam GeneratedPendingEventRoot) = []"
    and linked:
      "pvContainer_C (h_val h (event_item_raw_ptr D t)) \<noteq> NULL"
  shows
    "\<exists>owner. owner \<in> external \<and>
       event_item_raw_ptr D t \<in> set (ring (raw_fam owner)) \<and>
       pvContainer_C (h_val h (event_item_raw_ptr D t)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
proof -
  have pending_root:
    "GeneratedPendingEventRoot \<in> EventRootUniverse external"
    by simp
  have not_pending:
    "event_item_raw_ptr D t \<notin>
       set (ring (raw_fam GeneratedPendingEventRoot))"
  proof
    assume member:
      "event_item_raw_ptr D t \<in>
        set (ring (raw_fam GeneratedPendingEventRoot))"
    have abstract_member:
      "Event t \<in> set (ring (abs_fam GeneratedPendingEventRoot))"
      using scheduler_event_root_family_member_iff[
        OF EventRootFamilyCoverage_relD[OF coverage]
           task pending_root]
        member by simp
    show False using abstract_member pending_empty by simp
  qed
  obtain owner where owner_root:
      "owner \<in> EventRootUniverse external"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
    using EventRootFamilyCoverage_nonnull_unique_root[
      OF coverage task linked]
    by blast
  have owner_not_pending: "owner \<noteq> GeneratedPendingEventRoot"
    using member not_pending by blast
  have owner_external: "owner \<in> external"
    using owner_root owner_not_pending
    by (auto simp: EventRootUniverse_def)
  have container:
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    using EventRootFamilyCoverage_container_iff[
      OF coverage task owner_root]
      member by simp
  show ?thesis
    using owner_external member container by blast
qed

theorem EventRootFamilyCoverage_optional_remove_from_container:
  assumes coverage:
      "EventRootFamilyCoverage
         external D h raw_fam abs_fam managed K_E"
    and task: "t \<in> managed"
    and pending_empty:
      "ring (abs_fam GeneratedPendingEventRoot) = []"
  shows
    "if pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL then
       raw_family_members (EventRootUniverse external) raw_fam
         (event_item_raw_ptr D t) = {} \<and>
       EventRootFamilyCoverage
         external D h raw_fam abs_fam managed K_E
     else
       \<exists>owner. owner \<in> external \<and>
         event_item_raw_ptr D t \<in> set (ring (raw_fam owner)) \<and>
         pvContainer_C (h_val h (event_item_raw_ptr D t)) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<and>
         EventRootFamilyCoverage external D
           (raw_remove_concrete_heap h (event_item_raw_ptr D t))
           (event_remove_raw_family raw_fam owner
             (event_item_raw_ptr D t))
           (event_remove_abs_family abs_fam owner t) managed K_E \<and>
         pvContainer_C
           (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
             (event_item_raw_ptr D t)) = NULL \<and>
         raw_family_members (EventRootUniverse external)
           (event_remove_raw_family raw_fam owner
             (event_item_raw_ptr D t))
           (event_item_raw_ptr D t) = {}"
proof (cases
    "pvContainer_C (h_val h (event_item_raw_ptr D t)) = NULL")
  case True
  have absent:
    "raw_family_members (EventRootUniverse external) raw_fam
       (event_item_raw_ptr D t) = {}"
    using EventRootFamilyCoverage_null_iff_global_absence[
      OF coverage task]
      True by simp
  show ?thesis using True absent coverage by simp
next
  case False
  obtain owner where owner_external: "owner \<in> external"
    and member:
      "event_item_raw_ptr D t \<in> set (ring (raw_fam owner))"
    and container:
      "pvContainer_C (h_val h (event_item_raw_ptr D t)) =
        PTR_COERCE(xLIST_C \<rightarrow> unit) owner"
    using EventRootFamilyCoverage_linked_owner_externalD[
      OF coverage task pending_empty False]
    by blast
  have owner_root: "owner \<in> EventRootUniverse external"
    by (rule EventRootUniverse_externalI[OF owner_external])
  have old_rel:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF coverage])
  have post_rel:
    "scheduler_event_root_family_rel D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (EventRootUniverse external) GeneratedPendingEventRoot
       (event_remove_raw_family raw_fam owner
         (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) managed K_E"
    by (rule scheduler_event_root_family_remove_preserved[
          OF old_rel owner_root task member])
  have post_coverage:
    "EventRootFamilyCoverage external D
       (raw_remove_concrete_heap h (event_item_raw_ptr D t))
       (event_remove_raw_family raw_fam owner
         (event_item_raw_ptr D t))
       (event_remove_abs_family abs_fam owner t) managed K_E"
    using EventRootFamilyCoverage_external_wfD[OF coverage] post_rel
    by (simp add: EventRootFamilyCoverage_def)
  have post_null:
    "pvContainer_C
       (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
         (event_item_raw_ptr D t)) = NULL"
    using scheduler_event_root_family_remove_item_effect[
      OF old_rel owner_root task member]
    by simp
  have post_absent:
    "raw_family_members (EventRootUniverse external)
       (event_remove_raw_family raw_fam owner
         (event_item_raw_ptr D t))
       (event_item_raw_ptr D t) = {}"
    by (rule scheduler_event_root_family_remove_members_empty[
          OF old_rel owner_root task member])
  have branch_post:
      "\<exists>owner. owner \<in> external \<and>
        event_item_raw_ptr D t \<in> set (ring (raw_fam owner)) \<and>
        pvContainer_C (h_val h (event_item_raw_ptr D t)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) owner \<and>
        EventRootFamilyCoverage external D
          (raw_remove_concrete_heap h (event_item_raw_ptr D t))
          (event_remove_raw_family raw_fam owner
            (event_item_raw_ptr D t))
          (event_remove_abs_family abs_fam owner t) managed K_E \<and>
        pvContainer_C
          (h_val (raw_remove_concrete_heap h (event_item_raw_ptr D t))
            (event_item_raw_ptr D t)) = NULL \<and>
        raw_family_members (EventRootUniverse external)
          (event_remove_raw_family raw_fam owner
            (event_item_raw_ptr D t))
          (event_item_raw_ptr D t) = {}"
    by (rule exI[where x=owner])
       (use owner_external member container post_coverage post_null
          post_absent in blast)
  show ?thesis
    using False branch_post by simp
qed

end

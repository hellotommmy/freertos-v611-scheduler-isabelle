theory Scheduler_Task_Observation_Insert_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Remove_Frame.Scheduler_Task_Observation_Remove_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Owner_Frame.Scheduler_Resume_Generated_Insert_Owner_Frame"
begin

text \<open>
  Insert-end changes the inserted item's links and container, the cursor and
  successor links, and root metadata.  The owner-field footprint theorem is
  valid both for the new item and every old managed item, including old ring
  members that alias the cursor or successor.  These two cases are exposed as
  separate proof rungs and joined into an all-managed projection theorem.
\<close>

lemma raw_insert_end_new_owner_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed: "p \<in> universal_managed_nodes live D"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p) p) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h p)"
proof (rule TaskObservationRel_raw_owner_bytes_projection)
  show
    "\<forall>a\<in>raw_owner_field_region p.
       raw_insert_concrete_heap h target (fam target) p a = h a"
    by (rule raw_insert_end_family_owner_byte_frame[
      OF pre target fresh managed managed])
qed

lemma raw_insert_end_old_owner_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and q_managed: "q \<in> universal_managed_nodes live D"
    and old: "q \<noteq> p"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p) q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof (rule TaskObservationRel_raw_owner_bytes_projection)
  show
    "\<forall>a\<in>raw_owner_field_region q.
       raw_insert_concrete_heap h target (fam target) p a = h a"
    by (rule raw_insert_end_family_owner_byte_frame[
      OF pre target fresh p_managed q_managed])
qed

theorem raw_insert_end_family_all_managed_owner_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and q_managed: "q \<in> universal_managed_nodes live D"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p) q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof (cases "q = p")
  case True
  show ?thesis
    using raw_insert_end_new_owner_projection[
      OF pre target fresh p_managed] True by simp
next
  case False
  show ?thesis
    by (rule raw_insert_end_old_owner_projection[
      OF pre target fresh p_managed q_managed False])
qed

lemma raw_insert_end_family_live_priority_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and p_managed: "p \<in> universal_managed_nodes live D"
    and live: "t \<in> live"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (sd_tcb_ptr D t)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))"
proof (rule TaskObservationRel_priority_bytes_projection)
  show
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_insert_concrete_heap h target (fam target) p a = h a"
    by (rule raw_insert_end_family_priority_byte_frame[
      OF pre target fresh p_managed live])
qed

text \<open>
  Universal insert-end capstone.  The inserted node, target root, old ring,
  cursor, all keys, and all live priorities remain symbolic.  Freshness and
  managed ownership are source/API preconditions; the expected post-relation
  is not assumed.
\<close>

theorem TaskObservationRel_insert_end_preserved:
  assumes observation: "TaskObservationRel D h a"
    and pre:
      "scheduler_family_pre_rel h roots fam (sa_live a) D"
    and target: "target \<in> roots"
    and fresh: "raw_fresh_for_insert target (ring (fam target)) p"
    and managed:
      "p \<in> universal_managed_nodes (sa_live a) D"
  shows
    "TaskObservationRel D
       (raw_insert_concrete_heap h target (fam target) p) a"
proof (rule TaskObservationRel_heap_frameI[OF observation])
  fix t
  assume live: "t \<in> sa_live a"
  show
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (sd_tcb_ptr D t)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))"
    by (rule raw_insert_end_family_live_priority_projection[
      OF pre target fresh managed live])
next
  fix t
  assume live: "t \<in> sa_live a"
  have observed:
    "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<in>
       universal_managed_nodes (sa_live a) D"
    using live by (auto simp: universal_managed_nodes_def)
  have raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (abi_generic_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_generic_list_item_ptr (sd_tcb_ptr D t)))"
    by (rule raw_insert_end_family_all_managed_owner_projection[
      OF pre target fresh managed observed])
  show
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    by (rule TaskObservationRel_generic_owner_raw_projection[OF raw])
next
  fix t
  assume live: "t \<in> sa_live a"
  have observed:
    "abi_event_list_item_ptr (sd_tcb_ptr D t) \<in>
       universal_managed_nodes (sa_live a) D"
    using live by (auto simp: universal_managed_nodes_def)
  have raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (abi_event_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_event_list_item_ptr (sd_tcb_ptr D t)))"
    by (rule raw_insert_end_family_all_managed_owner_projection[
      OF pre target fresh managed observed])
  show
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_insert_concrete_heap h target (fam target) p)
         (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t)))"
    by (rule TaskObservationRel_event_owner_raw_projection[OF raw])
qed

end

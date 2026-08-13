theory Scheduler_Task_Observation_Remove_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Heap_Frame.Scheduler_Task_Observation_Heap_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Owner_Frame.Scheduler_Resume_Generated_Owner_Frame"
begin

text \<open>
  Removal writes the next neighbour's previous link, the previous neighbour's
  next link, the selected root metadata, and the removed item's container.
  raw_remove_member_owner_byte_frame already performs the exact alias audit:
  q may be p, either neighbour, or any other member, and singleton rings are
  included.  The first rung below converts that byte theorem to the typed
  owner projection used by TaskObservationRel.
\<close>

lemma raw_remove_ring_member_owner_projection:
  assumes rel: "raw_xlist_rel h target xs"
    and removed: "p \<in> set (ring xs)"
    and observed: "q \<in> set (ring xs)"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p) q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof (rule TaskObservationRel_raw_owner_bytes_projection)
  show
    "\<forall>a\<in>raw_owner_field_region q.
       raw_remove_concrete_heap h p a = h a"
    by (rule raw_remove_member_owner_byte_frame[OF rel removed observed])
qed

text \<open>
  In particular the node that becomes unlinked retains its owner payload.
  Its stale next/previous links, and all head/middle/tail/singleton positions,
  remain covered; membership in the entry ring is the only positional fact.
\<close>

lemma raw_remove_unlinked_owner_projection:
  assumes rel: "raw_xlist_rel h target xs"
    and removed: "p \<in> set (ring xs)"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p) p) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h p)"
  by (rule raw_remove_ring_member_owner_projection[OF rel removed removed])

text \<open>
  A protected family contains only managed Generic/Event items.  A managed
  observation is either inside the selected entry ring, where the field-exact
  alias theorem applies, or outside it, where the scheduler family footprint
  theorem frames the whole owner region.  No sibling is exposed as a premise
  of the resulting all-managed theorem.
\<close>

theorem raw_remove_family_all_managed_owner_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and removed: "p \<in> set (ring (fam target))"
    and managed: "q \<in> universal_managed_nodes live D"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p) q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof (cases "q \<in> set (ring (fam target))")
  case True
  have source: "raw_xlist_rel h target (fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  show ?thesis
    by (rule raw_remove_ring_member_owner_projection[
          OF source removed True])
next
  case False
  obtain u where u_live: "u \<in> live"
    using managed by (auto simp: universal_managed_nodes_def)
  have bytes:
    "\<forall>a\<in>raw_owner_field_region q.
       raw_remove_concrete_heap h p a = h a"
    using raw_remove_family_sibling_owner_priority_byte_frame[
      OF pre target removed managed False u_live]
    by blast
  show ?thesis
    by (rule TaskObservationRel_raw_owner_bytes_projection[OF bytes])
qed

corollary raw_remove_family_unlinked_managed_owner_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and removed: "p \<in> set (ring (fam target))"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p) p) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h p)"
proof -
  have managed: "p \<in> universal_managed_nodes live D"
    using pre target removed
    by (auto simp: scheduler_family_pre_rel_def)
  show ?thesis
    by (rule raw_remove_family_all_managed_owner_projection[
      OF pre target removed managed])
qed

lemma raw_remove_family_live_priority_projection:
  assumes pre: "scheduler_family_pre_rel h roots fam live D"
    and target: "target \<in> roots"
    and removed: "p \<in> set (ring (fam target))"
    and live: "t \<in> live"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (raw_remove_concrete_heap h p) (sd_tcb_ptr D t)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))"
proof (rule TaskObservationRel_priority_bytes_projection)
  show
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       raw_remove_concrete_heap h p a = h a"
    by (rule scheduler_family_remove_priority_byte_frame[
      OF pre target removed live])
qed

text \<open>
  Universal remove capstone.  The quantified task in each proof subgoal is
  introduced only after applying TaskObservationRel_heap_frameI; no selected
  sibling or task is part of the theorem boundary.
\<close>

theorem TaskObservationRel_remove_preserved:
  assumes observation: "TaskObservationRel D h a"
    and pre:
      "scheduler_family_pre_rel h roots fam (sa_live a) D"
    and target: "target \<in> roots"
    and removed: "p \<in> set (ring (fam target))"
  shows
    "TaskObservationRel D (raw_remove_concrete_heap h p) a"
proof (rule TaskObservationRel_heap_frameI[OF observation])
  fix t
  assume live: "t \<in> sa_live a"
  show
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val (raw_remove_concrete_heap h p) (sd_tcb_ptr D t)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))"
    by (rule raw_remove_family_live_priority_projection[
      OF pre target removed live])
next
  fix t
  assume live: "t \<in> sa_live a"
  have managed:
    "abi_generic_list_item_ptr (sd_tcb_ptr D t) \<in>
       universal_managed_nodes (sa_live a) D"
    using live by (auto simp: universal_managed_nodes_def)
  have raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p)
         (abi_generic_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_generic_list_item_ptr (sd_tcb_ptr D t)))"
    by (rule raw_remove_family_all_managed_owner_projection[
      OF pre target removed managed])
  show
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p)
         (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    by (rule TaskObservationRel_generic_owner_raw_projection[OF raw])
next
  fix t
  assume live: "t \<in> sa_live a"
  have managed:
    "abi_event_list_item_ptr (sd_tcb_ptr D t) \<in>
       universal_managed_nodes (sa_live a) D"
    using live by (auto simp: universal_managed_nodes_def)
  have raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p)
         (abi_event_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_event_list_item_ptr (sd_tcb_ptr D t)))"
    by (rule raw_remove_family_all_managed_owner_projection[
      OF pre target removed managed])
  show
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val (raw_remove_concrete_heap h p)
         (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t)))"
    by (rule TaskObservationRel_event_owner_raw_projection[OF raw])
qed

end

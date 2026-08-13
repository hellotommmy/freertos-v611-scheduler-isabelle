theory Scheduler_Task_Observation_Heap_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel.Scheduler_Task_Observation_Rel"
    "EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone.Scheduler_List_Family_Frame_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
begin

text \<open>
  TaskObservationRel only observes three heap projections for each live task:
  the TCB priority, the Generic-item owner, and the Event-item owner.  This
  constructor isolates that exact obligation.  It deliberately does not ask
  for equality of whole TCBs or whole embedded list items, whose link and
  container fields are changed by the list primitives.
\<close>

theorem TaskObservationRel_heap_frameI:
  assumes observation: "TaskObservationRel D h a"
    and priority_frame:
      "\<And>t. t \<in> sa_live a \<Longrightarrow>
        Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val h' (sd_tcb_ptr D t)) =
        Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
          (h_val h (sd_tcb_ptr D t))"
    and generic_owner_frame:
      "\<And>t. t \<in> sa_live a \<Longrightarrow>
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
    and event_owner_frame:
      "\<And>t. t \<in> sa_live a \<Longrightarrow>
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
        Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
          (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t)))"
  shows "TaskObservationRel D h' a"
  unfolding TaskObservationRel_def
proof (rule conjI)
  show "finite (sa_live a)"
    using observation by (simp add: TaskObservationRel_def)
next
  show
    "\<forall>t\<in>sa_live a.
       c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority a t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h' (sd_tcb_ptr D t))) = sa_priority a t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h' (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t)"
  proof (intro ballI)
    fix t
    assume live: "t \<in> sa_live a"
    note old = TaskObservationRel_liveD[OF observation live]
    show
      "c_guard (sd_tcb_ptr D t) \<and>
       c_guard (scheduler_generic_item_ptr (sd_tcb_ptr D t)) \<and>
       c_guard (scheduler_event_item_ptr (sd_tcb_ptr D t)) \<and>
       sa_priority a t < 4 \<and>
       unat (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h' (sd_tcb_ptr D t))) = sa_priority a t \<and>
       Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
         (h_val h' (sd_tcb_ptr D t)) < 4 \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t) \<and>
       Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
         (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
         PTR_COERCE(Scheduler_V611_Parse.tskTaskControlBlock_C \<rightarrow> unit)
           (sd_tcb_ptr D t)"
      using old priority_frame[OF live] generic_owner_frame[OF live]
        event_owner_frame[OF live]
      by simp
  qed
qed

text \<open>
  Byte-level exact-footprint facts are converted to the three typed
  projections consumed by TaskObservationRel.  These are pure projection
  lemmas: no task, priority, root, ring, cursor, or key is fixed.
\<close>

lemma TaskObservationRel_raw_owner_bytes_projection:
  assumes bytes:
    "\<forall>a\<in>raw_owner_field_region q. h' a = h a"
  shows
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' q) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h q)"
proof -
  have field_same:
    "h_val h' (raw_owner_field_ptr q) =
     h_val h (raw_owner_field_ptr q)"
  proof (rule delay_h_val_region_cong)
    fix address
    assume address:
      "address \<in>
        {ptr_val (raw_owner_field_ptr q)..+size_of TYPE(unit ptr)}"
    show "h' address = h address"
      using bytes address by (simp add: raw_owner_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding raw_owner_field_ptr_def
    by (simp only:
      List_V611_Raw_Skip_Translation.xLIST_ITEM_C_h_val_fields(4))
qed

lemma TaskObservationRel_priority_bytes_projection:
  assumes bytes:
    "\<forall>a\<in>universal_priority_field_region (sd_tcb_ptr D t).
       h' a = h a"
  shows
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h' (sd_tcb_ptr D t)) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val h (sd_tcb_ptr D t))"
proof -
  have field_same:
    "h_val h' (universal_priority_field_ptr (sd_tcb_ptr D t)) =
     h_val h (universal_priority_field_ptr (sd_tcb_ptr D t))"
  proof (rule delay_h_val_region_cong)
    fix address
    assume address:
      "address \<in>
        {ptr_val (universal_priority_field_ptr (sd_tcb_ptr D t))..+
          size_of TYPE(32 word)}"
    show "h' address = h address"
      using bytes address
      by (simp add: universal_priority_field_region_def)
  qed
  show ?thesis
    using field_same
    unfolding universal_priority_field_ptr_def
    by (simp only:
      Scheduler_V611_Parse.tskTaskControlBlock_C_h_val_fields(4))
qed

lemma TaskObservationRel_generic_owner_raw_projection:
  assumes raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (abi_generic_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_generic_list_item_ptr (sd_tcb_ptr D t)))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_generic_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_generic_item_ptr (sd_tcb_ptr D t)))"
  using raw
  by (simp add: abi_generic_list_item_ptr_def
      scheduler_generic_item_ptr_def flip: abi_item_owner_h_val)

lemma TaskObservationRel_event_owner_raw_projection:
  assumes raw:
    "List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h' (abi_event_list_item_ptr (sd_tcb_ptr D t))) =
     List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
       (h_val h (abi_event_list_item_ptr (sd_tcb_ptr D t)))"
  shows
    "Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h' (scheduler_event_item_ptr (sd_tcb_ptr D t))) =
     Scheduler_V611_Parse.xLIST_ITEM_C.pvOwner_C
       (h_val h (scheduler_event_item_ptr (sd_tcb_ptr D t)))"
  using raw
  by (simp add: abi_event_list_item_ptr_def
      scheduler_event_item_ptr_def flip: abi_item_owner_h_val)

end

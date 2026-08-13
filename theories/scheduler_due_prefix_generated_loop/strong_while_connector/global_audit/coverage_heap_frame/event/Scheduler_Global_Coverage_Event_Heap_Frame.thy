theory Scheduler_Global_Coverage_Event_Heap_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Generic_Heap_Frame.Scheduler_Global_Coverage_Generic_Heap_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Heap_Frame.Scheduler_Resume_Generated_Event_Heap_Frame"
begin

text \<open>
  Event coverage has an additional arbitrary finite external-root parameter.
  Its input geometry is heap independent; the existing whole Event-family
  frame theorem transports the represented roots, containers and total Event
  payload observation.
\<close>

theorem EventRootFamilyCoverage_heap_frameI:
  assumes coverage:
      "EventRootFamilyCoverage
         external D h raw_fam abs_fam managed K_E"
    and root_frame:
      "\<And>lp address.
        lp \<in> EventRootUniverse external \<Longrightarrow>
        address \<in> raw_xlist_storage lp (raw_fam lp) \<Longrightarrow>
        h' address = h address"
    and item_frame:
      "\<And>t. t \<in> managed \<Longrightarrow>
        h_val h' (event_item_raw_ptr D t) =
          h_val h (event_item_raw_ptr D t)"
  shows
    "EventRootFamilyCoverage
       external D h' raw_fam abs_fam managed K_E"
proof -
  have input_wf: "EventExternalRootInputWF external"
    by (rule EventRootFamilyCoverage_external_wfD[OF coverage])
  have old_rel:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF coverage])
  have new_rel:
    "scheduler_event_root_family_rel D h'
       (EventRootUniverse external) GeneratedPendingEventRoot
       raw_fam abs_fam managed K_E"
    by (rule scheduler_event_root_family_heap_frameI[
          OF old_rel root_frame item_frame])
  show ?thesis
    using input_wf new_rel
    by (simp add: EventRootFamilyCoverage_def)
qed

end

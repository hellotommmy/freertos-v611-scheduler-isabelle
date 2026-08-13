theory Scheduler_Due_Prefix_Terminal_Future_Decode
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Ptr_Eq.Scheduler_Due_Prefix_Terminal_Head_Ptr_Eq"
begin

lemma due_prefix_gate_inv_last_due_future_decode:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
  shows
    "sd_node_decode D (one_due_generic_raw_ptr D f) = Some (Generic f)"
proof -
  note head_raw = due_prefix_gate_inv_last_due_head_raw[OF inv]
  have f_live: "f \<in> odc_live C"
    by (rule conjunct1[OF head_raw])
  show ?thesis
    by (rule due_prefix_gate_inv_generic_ptr_decode[OF inv f_live])
qed

end

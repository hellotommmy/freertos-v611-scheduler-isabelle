theory Scheduler_Due_Prefix_Terminal_Witness_Decode
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Decode.Scheduler_Due_Prefix_Terminal_Future_Decode"
begin

lemma due_prefix_gate_inv_last_due_witness_decode:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    and u_live: "u \<in> odc_live C"
  shows
    "sd_node_decode D (one_due_generic_raw_ptr D u) = Some (Generic u)"
  by (rule due_prefix_gate_inv_generic_ptr_decode[OF inv u_live])

end

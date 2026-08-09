theory Scheduler_Due_Prefix_Terminal_Gate_Decode
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner_Witness.Scheduler_Due_Prefix_Terminal_Head_Owner_Witness"
begin

lemma due_prefix_gate_inv_generic_ptr_decode:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
    and live: "u \<in> odc_live C"
  shows
    "sd_node_decode D (one_due_generic_raw_ptr D u) = Some (Generic u)"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  show ?thesis
    by (rule one_due_gateH_generic_ptr_decode[OF rel live])
qed

end

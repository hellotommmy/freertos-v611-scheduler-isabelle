theory Scheduler_Due_Prefix_Terminal_Head_Raw
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Removed_Relabel.Scheduler_Due_Prefix_Terminal_Removed_Relabel"
begin

lemma due_prefix_gate_inv_last_due_head_raw:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
  shows
    "f \<in> odc_live C \<and>
     ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> [] \<and>
     hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D f"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  have abstract:
    "ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) =
       Generic f # fs"
    by (rule due_prefix_gate_inv_last_due_abs_residual[OF inv])
  have head_shape:
    "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) =
       Generic f # rest"
    by (rule exI[where x = fs], rule abstract)
  show ?thesis
    by (rule one_due_gateH_removed_head_bridge[OF rel head_shape])
qed

end

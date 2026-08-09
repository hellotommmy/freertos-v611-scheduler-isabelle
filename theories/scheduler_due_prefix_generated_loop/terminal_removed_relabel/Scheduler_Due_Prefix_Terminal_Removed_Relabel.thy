theory Scheduler_Due_Prefix_Terminal_Removed_Relabel
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Last_Due_Ring.Scheduler_Due_Prefix_Terminal_Last_Due_Ring"
begin

lemma due_prefix_gate_inv_last_due_removed_relabel:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "xlist_relabel (sd_node_decode D)
       (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))
       (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C))) \<and>
     ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = future"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  show ?thesis
    using one_due_gateH_removed_relabel[OF rel]
      due_prefix_gate_inv_last_due_abs_residual[OF inv]
    by blast
qed

lemma due_prefix_gate_inv_last_due_raw_empty_iff:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) = [] \<longleftrightarrow>
     future = []"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  have abstract:
    "ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = future"
    by (rule due_prefix_gate_inv_last_due_abs_residual[OF inv])
  show ?thesis
    using one_due_gateH_removed_empty_iff[OF rel] abstract by simp
qed

end


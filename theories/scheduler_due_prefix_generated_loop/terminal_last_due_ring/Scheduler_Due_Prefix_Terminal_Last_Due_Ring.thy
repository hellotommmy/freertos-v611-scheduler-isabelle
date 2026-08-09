theory Scheduler_Due_Prefix_Terminal_Last_Due_Ring
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Projections.Scheduler_Due_Prefix_Terminal_Gate_Projections"
begin

lemma due_prefix_gate_inv_last_due_loopD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] future current"
  by (rule due_prefix_gate_inv_loopD[OF inv])

lemma due_prefix_gate_inv_last_due_delayedD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
  by (rule due_prefix_gate_inv_delayedD[OF inv])

lemma due_prefix_gate_inv_last_due_current_ring:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # future"
proof -
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] future current"
    by (rule due_prefix_gate_inv_last_due_loopD[OF inv])
  show ?thesis using due_prefix_loop_inv_ringD[OF prefix] by simp
qed

lemma due_prefix_gate_inv_last_due_abs_residual:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "ring (list_remove_abs (Generic (odc_task C))
       (ods_generic_family S (odc_delayed_root C))) = future"
proof -
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    by (rule due_prefix_gate_inv_last_due_delayedD[OF inv])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # future"
    by (rule due_prefix_gate_inv_last_due_current_ring[OF inv])
  show ?thesis
    using delayed current_ring by (simp add: list_remove_abs_def)
qed

end

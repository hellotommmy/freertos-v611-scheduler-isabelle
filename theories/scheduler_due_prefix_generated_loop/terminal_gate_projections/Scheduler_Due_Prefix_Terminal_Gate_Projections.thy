theory Scheduler_Due_Prefix_Terminal_Gate_Projections
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Ready.Scheduler_Due_Prefix_Terminal_Future_Ready"
begin

lemma due_prefix_gate_inv_factsD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw \<and>
     due_prefix_loop_inv now entry processed remaining future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"
  by (rule due_prefix_gate_inv_def[THEN iffD1, OF inv])

lemma due_prefix_gate_inv_gateD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
  by (rule conjunct1[OF due_prefix_gate_inv_factsD[OF inv]])

lemma due_prefix_gate_inv_loopD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "due_prefix_loop_inv now entry processed remaining future current"
  by (rule conjunct1[OF conjunct2[OF due_prefix_gate_inv_factsD[OF inv]]])

lemma due_prefix_gate_inv_context_tickD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "odc_tick C = now"
  by (rule conjunct1[OF conjunct2[OF conjunct2[OF
        due_prefix_gate_inv_factsD[OF inv]]]])

lemma due_prefix_gate_inv_abs_tickD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "sa_tick current = now"
  by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF
        due_prefix_gate_inv_factsD[OF inv]]]]])

lemma due_prefix_gate_inv_delayedD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
  by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF
        conjunct2[OF due_prefix_gate_inv_factsD[OF inv]]]]]])

lemma due_prefix_gate_inv_all_readyD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "one_due_all_ready_destinations C"
  by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF
        conjunct2[OF conjunct2[OF due_prefix_gate_inv_factsD[OF inv]]]]]]])

lemma due_prefix_gate_inv_pending_emptyD:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "ring (ods_event_family S (odc_pending_root C)) = []"
  by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
        conjunct2[OF conjunct2[OF due_prefix_gate_inv_factsD[OF inv]]]]]]])

end

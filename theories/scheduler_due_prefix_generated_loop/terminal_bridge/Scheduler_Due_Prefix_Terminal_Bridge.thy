theory Scheduler_Due_Prefix_Terminal_Bridge
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Exit.Scheduler_Due_Prefix_Terminal_Exit"
begin

lemma due_prefix_gate_inv_last_due_future_semantics:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
  shows
    "f \<in> odc_live C \<and>
     item_key (current_delayed_ring entry) (Generic f) =
       ods_generic_payload S f \<and>
     now < ods_generic_payload S f"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  have f_live: "f \<in> odc_live C"
    by (rule conjunct1[OF due_prefix_gate_inv_last_due_head_owner[OF inv]])
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] (Generic f # fs) current"
    by (rule due_prefix_gate_inv_loopD[OF inv])
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    by (rule due_prefix_gate_inv_delayedD[OF inv])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # Generic f # fs"
    using due_prefix_loop_inv_ringD[OF prefix] by simp
  have snapshot_ring:
    "ring (ods_generic_family S (odc_delayed_root C)) =
       Generic (odc_task C) # Generic f # fs"
    using delayed current_ring by simp
  have entry_rel: "one_due_entry_rel C branch S"
    by (rule one_due_gateH_pure_entryD[OF rel])
  have source_root: "odc_delayed_root C \<in> odc_generic_roots C"
    by (rule one_due_gateH_source_in_rootsD[OF rel])
  have shape: "one_due_family_shape C S"
  proof -
    note entry_facts = one_due_entry_rel_def[THEN iffD1, OF entry_rel]
    show ?thesis by (rule conjunct1[OF conjunct2[OF entry_facts]])
  qed
  have f_member:
    "Generic f \<in>
       set (ring (ods_generic_family S (odc_delayed_root C)))"
    using snapshot_ring by simp
  have payload:
    "item_key (ods_generic_family S (odc_delayed_root C))
       (Generic f) = ods_generic_payload S f"
  proof -
    note shape_facts = one_due_family_shape_def[THEN iffD1, OF shape]
    note generic_keys = conjunct1[OF conjunct2[OF conjunct2[OF
      conjunct2[OF conjunct2[OF shape_facts]]]]]
    note root_keys = bspec[OF generic_keys source_root]
    note task_keys = bspec[OF root_keys f_live]
    show ?thesis by (rule mp[OF task_keys f_member])
  qed
  have current_def: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF prefix])
  have entry_key:
    "item_key (current_delayed_ring entry) (Generic f) =
       ods_generic_payload S f"
    using delayed payload current_def by simp
  have post:
    "due_prefix_loop_inv now entry
       (processed @ [Generic (odc_task C)]) [] (Generic f # fs)
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
    by (rule due_prefix_result_step_preserves_inv[OF prefix])
  note terminal = due_prefix_future_head_exception_exit[OF post]
  have future_key:
    "now < item_key (current_delayed_ring entry) (Generic f)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF terminal]]])
  show ?thesis
    using f_live entry_key future_key by simp
qed

end

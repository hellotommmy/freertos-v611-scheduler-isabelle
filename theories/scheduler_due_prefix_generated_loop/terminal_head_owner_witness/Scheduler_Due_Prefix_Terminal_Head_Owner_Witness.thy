theory Scheduler_Due_Prefix_Terminal_Head_Owner_Witness
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Raw.Scheduler_Due_Prefix_Terminal_Head_Raw"
begin

lemma due_prefix_gate_inv_last_due_owner_witness:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
  shows
    "\<exists>u\<in>odc_live C.
       hd (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))) =
         one_due_generic_raw_ptr D u \<and>
       PTR_COERCE(unit \<rightarrow>
           Scheduler_V611_Parse.tskTaskControlBlock_C)
         (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
           (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
             (hd (ring (list_remove_abs
               (one_due_generic_raw_ptr D (odc_task C))
               (generic_raw (odc_delayed_root C))))))) =
         sd_tcb_ptr D u"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv])
  note head_raw = due_prefix_gate_inv_last_due_head_raw[OF inv]
  note head_tail = conjunct2[OF head_raw]
  have nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    by (rule conjunct1[OF head_tail])
  show ?thesis
    by (rule one_due_next_head_owner_decode[OF rel nonempty])
qed

end

theory Scheduler_Due_Prefix_Terminal_Head_Ptr_Eq
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Decode.Scheduler_Due_Prefix_Terminal_Gate_Decode"
begin

lemma due_prefix_gate_inv_last_due_head_ptr_eq:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    and hd_u:
      "hd (ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C)))) =
        one_due_generic_raw_ptr D u"
  shows
    "one_due_generic_raw_ptr D f = one_due_generic_raw_ptr D u"
proof -
  note head_raw = due_prefix_gate_inv_last_due_head_raw[OF inv]
  note head_tail = conjunct2[OF head_raw]
  have hd_f:
    "hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D f"
    by (rule conjunct2[OF head_tail])
  show ?thesis using hd_f hd_u by simp
qed

end

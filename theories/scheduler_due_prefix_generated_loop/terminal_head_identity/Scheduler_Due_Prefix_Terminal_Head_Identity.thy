theory Scheduler_Due_Prefix_Terminal_Head_Identity
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Witness_Decode.Scheduler_Due_Prefix_Terminal_Witness_Decode"
begin

lemma due_prefix_gate_inv_last_due_head_identity:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    and u_live: "u \<in> odc_live C"
    and hd_u:
      "hd (ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C)))) =
        one_due_generic_raw_ptr D u"
  shows "u = f"
proof -
  have ptr_eq:
    "one_due_generic_raw_ptr D f = one_due_generic_raw_ptr D u"
    by (rule due_prefix_gate_inv_last_due_head_ptr_eq[OF inv hd_u])
  have decode_f:
    "sd_node_decode D (one_due_generic_raw_ptr D f) = Some (Generic f)"
    by (rule due_prefix_gate_inv_last_due_future_decode[OF inv])
  have decode_u:
    "sd_node_decode D (one_due_generic_raw_ptr D u) = Some (Generic u)"
    by (rule due_prefix_gate_inv_last_due_witness_decode[OF inv u_live])
  have decode_eq:
    "sd_node_decode D (one_due_generic_raw_ptr D f) =
       sd_node_decode D (one_due_generic_raw_ptr D u)"
    by (rule arg_cong[OF ptr_eq])
  have left:
    "Some (Generic f) =
       sd_node_decode D (one_due_generic_raw_ptr D f)"
    by (rule sym[OF decode_f])
  have middle:
    "Some (Generic f) =
       sd_node_decode D (one_due_generic_raw_ptr D u)"
    by (rule trans[OF left decode_eq])
  have some_nodes: "Some (Generic f) = Some (Generic u)"
    by (rule trans[OF middle decode_u])
  have nodes: "Generic f = Generic u"
    using some_nodes by (simp only: option.inject)
  have f_eq_u: "f = u"
    using nodes by (simp only: node_kind.inject)
  show ?thesis by (rule sym[OF f_eq_u])
qed

end

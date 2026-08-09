theory Scheduler_Due_Prefix_Terminal_Head_Owner
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Identity.Scheduler_Due_Prefix_Terminal_Head_Identity"
begin

lemma due_prefix_gate_inv_last_due_head_owner:
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
       one_due_generic_raw_ptr D f \<and>
     PTR_COERCE(unit \<rightarrow> Scheduler_V611_Parse.tskTaskControlBlock_C)
       (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
         (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
           (hd (ring (list_remove_abs
             (one_due_generic_raw_ptr D (odc_task C))
             (generic_raw (odc_delayed_root C))))))) =
       sd_tcb_ptr D f"
proof -
  note head_raw = due_prefix_gate_inv_last_due_head_raw[OF inv]
  have f_live: "f \<in> odc_live C"
    by (rule conjunct1[OF head_raw])
  note head_tail = conjunct2[OF head_raw]
  have nonempty:
    "ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C))) \<noteq> []"
    by (rule conjunct1[OF head_tail])
  have hd_f:
    "hd (ring (list_remove_abs
       (one_due_generic_raw_ptr D (odc_task C))
       (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D f"
    by (rule conjunct2[OF head_tail])
  note witness = due_prefix_gate_inv_last_due_owner_witness[OF inv]
  obtain u where u_live: "u \<in> odc_live C"
    and hd_u:
      "hd (ring (list_remove_abs
        (one_due_generic_raw_ptr D (odc_task C))
        (generic_raw (odc_delayed_root C)))) =
        one_due_generic_raw_ptr D u"
    and owner_u:
      "PTR_COERCE(unit \<rightarrow>
          Scheduler_V611_Parse.tskTaskControlBlock_C)
        (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
          (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
            (hd (ring (list_remove_abs
              (one_due_generic_raw_ptr D (odc_task C))
              (generic_raw (odc_delayed_root C))))))) =
        sd_tcb_ptr D u"
    using witness by (elim bexE conjE)
  have u_eq_f: "u = f"
    by (rule due_prefix_gate_inv_last_due_head_identity[OF inv u_live hd_u])
  have owner_f:
    "PTR_COERCE(unit \<rightarrow>
        Scheduler_V611_Parse.tskTaskControlBlock_C)
      (List_V611_Raw_Skip_Translation.xLIST_ITEM_C.pvOwner_C
        (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
          (hd (ring (list_remove_abs
            (one_due_generic_raw_ptr D (odc_task C))
            (generic_raw (odc_delayed_root C))))))) =
      sd_tcb_ptr D f"
    using owner_u u_eq_f by simp
  show ?thesis
    apply (intro conjI)
    subgoal by (rule f_live)
    subgoal by (rule nonempty)
    subgoal by (rule hd_f)
    subgoal by (rule owner_f)
    done
qed

end

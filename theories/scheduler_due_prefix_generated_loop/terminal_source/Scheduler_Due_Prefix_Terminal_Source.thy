theory Scheduler_Due_Prefix_Terminal_Source
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Followup.Scheduler_Due_Prefix_Terminal_Followup"
begin

text \<open>
  Uniform last-due theorem for an arbitrary legal future suffix.  The family
  shape in Gate-H proves that every nonempty future head is Generic; no list
  length, task, priority, tick, cursor, address or branch is specialised.
\<close>

theorem due_prefix_generated_last_due_body_terminal:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
        \<exists>(v :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr) phase next.
        r = Result (v :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr) \<and>
        one_due_tick_body_post D C branch generic_raw c
          (Result (v :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr)) t \<and>
        due_prefix_exit_inv now entry
          (processed @ [Generic (odc_task C)]) [] future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) phase next \<and>
        due_prefix_terminal_source_rel D future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C))) phase next v\<rbrace>"
proof (cases future)
  case Nil
  have inv_empty:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] [] current C branch S
       generic_raw event_raw"
    using inv Nil by simp
  note empty = due_prefix_generated_last_due_empty_body[
    OF inv_empty roots]
  show ?thesis
    apply (rule runs_to_weaken[OF empty])
    apply (rule exI[where x =
      "NULL :: Scheduler_V611_Parse.tskTaskControlBlock_C ptr"])
    apply (rule exI[where x = EmptyExit])
    apply (rule exI[where x = None])
    apply (simp only: Nil)
    done
next
  case (Cons n fs)
  have inv_cons:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (n # fs) current C branch S
       generic_raw event_raw"
    using inv Cons by simp
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    by (rule due_prefix_gate_inv_gateD[OF inv_cons])
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] (n # fs) current"
    by (rule due_prefix_gate_inv_loopD[OF inv_cons])
  have delayed:
    "ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current"
    by (rule due_prefix_gate_inv_delayedD[OF inv_cons])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic (odc_task C) # n # fs"
    using due_prefix_loop_inv_ringD[OF prefix] by simp
  have snapshot_ring:
    "ring (ods_generic_family S (odc_delayed_root C)) =
       Generic (odc_task C) # n # fs"
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
  have n_member:
    "n \<in> set (ring (ods_generic_family S (odc_delayed_root C)))"
    using snapshot_ring by simp
  obtain f where n_generic: "n = Generic f"
  proof -
    note shape_facts = one_due_family_shape_def[THEN iffD1, OF shape]
    note generic_roots = conjunct1[OF shape_facts]
    note source_facts = bspec[OF generic_roots source_root]
    note source_tail = conjunct2[OF source_facts]
    have source_generic:
      "generic_ring (ods_generic_family S (odc_delayed_root C))"
      by (rule conjunct1[OF source_tail])
    note generic_all = generic_ring_def[THEN iffD1, OF source_generic]
    have n_exists: "\<exists>t. n = Generic t"
      by (rule bspec[OF generic_all n_member])
    show thesis using n_exists by (elim exE) (rule that)
  qed
  have inv_f:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] (Generic f # fs) current C branch S
       generic_raw event_raw"
    using inv Cons n_generic by simp
  note future_body = due_prefix_generated_last_due_future_body[
    OF inv_f roots]
  show ?thesis
    apply (rule runs_to_weaken[OF future_body])
    apply (rule exI[where x = "sd_tcb_ptr D f"])
    apply (rule exI[where x = FutureExit])
    apply (rule exI[where x = "Some (Generic f)"])
    apply (simp only: Cons n_generic)
    done
qed

end

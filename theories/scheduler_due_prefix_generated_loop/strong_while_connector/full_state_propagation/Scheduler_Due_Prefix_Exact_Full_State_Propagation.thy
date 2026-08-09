theory Scheduler_Due_Prefix_Exact_Full_State_Propagation
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Tick_Exact_Globals.Scheduler_One_Due_Tick_Exact_Globals"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Source_Step.Scheduler_Due_Prefix_Source_Step"
begin

text \<open>
  The exact tail theorem retains the complete generated globals record.  This
  file carries that equality through the enclosing generated body and then
  conjoins it with the already checked Gate-H and due-prefix source steps.
  No address, task, priority, key, root, list, cursor, tick, or branch is
  specialised.
\<close>

theorem one_due_tick_body_state_exact:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       t = one_due_tick_ready_inserted_state D C branch generic_raw c\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  let ?ready =
    "one_due_tick_ready_inserted_state D C branch generic_raw c"
  have task_live: "odc_task C \<in> odc_live C"
    by (rule one_due_gateH_task_liveD[OF rel])
  have task_abs: "odc_task C \<in> sa_live a"
    using task_live one_due_gateH_live_absD[OF rel] by simp
  have obs: "TaskObservationRel D ?h a"
    by (rule one_due_gateH_task_observationD[OF rel])
  note obs_task = TaskObservationRel_liveD[OF obs task_abs]
  have guard_item: "c_guard (scheduler_generic_item_ptr ?tp)"
    using obs_task by blast
  have guard_tcb: "c_guard ?tp"
    using obs_task by blast
  have key_read:
    "Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
       (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
         (h_val ?h ?tp)) =
     ods_generic_payload S (odc_task C)"
    using one_due_tcb_generic_key_read[of ?h ?tp]
      one_due_gateH_generic_keysD[OF rel task_live]
    by (simp add: one_due_generic_raw_ptr_def)
  have not_due_false:
    "\<not> Scheduler_V611_Parse.globals.xTickCount_' c <
       Scheduler_V611_Parse.xLIST_ITEM_C.xItemValue_C
         (Scheduler_V611_Parse.tskTaskControlBlock_C.xGenericListItem_C
           (h_val ?h ?tp))"
    using key_read one_due_gateH_head_dueD[OF rel]
      one_due_gateH_tick_wordD[OF rel]
    by (simp add: not_less)
  have ready_heap:
    "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' ?ready) =
       one_due_ready_insert_heap D C generic_raw
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C ?h))"
    by simp
  have ready_delayed:
    "Scheduler_V611_Parse.globals.pxDelayedTaskList_' ?ready =
       Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
    by (simp add: one_due_tick_ready_inserted_state_def Let_def
      scheduler_mem_state_def)
  have remainder:
    "one_due_tick_delayed_remainder \<bullet> ?ready
     \<lbrace>\<lambda>r t. t = ?ready\<rbrace>"
    apply (rule runs_to_weaken[OF
      one_due_tick_delayed_remainder_exact[
        OF rel ready_heap ready_delayed]])
    by simp
  have tail:
    "one_due_tick_top_ready_tail_source ?tp \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C ?h)) c)
     \<lbrace>\<lambda>r t. t = ?ready\<rbrace>"
    by (rule one_due_tick_tail_insert_composed_full_state[
      OF rel roots remainder])
  have inner:
    "bind
       (Scheduler_V611_Delay_Translation.vListRemove'
         (scheduler_generic_item_ptr ?tp))
       (\<lambda>_. one_due_tick_after_generic_source ?tp) \<bullet> c
     \<lbrace>\<lambda>r t. t = ?ready\<rbrace>"
    by (rule one_due_generated_generic_event_then_top_ready_cutpoint[
      OF rel tail])
  show ?thesis
    unfolding one_due_tick_loop_body_source_def
    apply runs_to_vcg
    subgoal by (rule guard_item)
    subgoal by (rule guard_tcb)
    subgoal using not_due_false by simp
    subgoal
      apply (rule runs_to_weaken[OF
        inner[unfolded runs_to_bind_iff]])
      apply clarsimp
      apply (rule runs_to_weaken)
       apply assumption
      apply clarsimp
      done
    done
qed

text \<open>
  Gate-H re-entry and exact globals are properties of the same source run.
  The conjunction law for runs-to therefore avoids reopening the checked
  family-preservation proof.
\<close>

theorem one_due_tick_gate_step_full_state:
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and u_live: "u \<in> odc_live C"
    and nonempty:
      "ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C))) \<noteq> []"
    and hd_link:
      "hd (ring (list_remove_abs
         (one_due_generic_raw_ptr D (odc_task C))
         (generic_raw (odc_delayed_root C)))) =
       one_due_generic_raw_ptr D u"
    and head_shape:
      "\<exists>rest. ring (list_remove_abs (Generic (odc_task C))
         (ods_generic_family S (odc_delayed_root C))) =
       Generic u # rest"
    and u_due: "ods_generic_payload S u \<le> odc_tick C"
    and target'_root:
      "odc_ready_root C (odc_priority C u) \<in> odc_generic_roots C"
    and target'_ne:
      "odc_delayed_root C \<noteq> odc_ready_root C (odc_priority C u)"
    and branch':
      "one_due_event_branch_at (one_due_reentry_context C u)
         (one_due_reentry_snapshot C branch S) branch'"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C))
       \<bullet> c
     \<lbrace>\<lambda>r t.
       (r = Result (sd_tcb_ptr D u) \<and>
        one_due_gateH_entry_rel D R t a
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c\<rbrace>"
proof -
  note gate = one_due_tick_gate_step[
    OF rel roots u_live nonempty hd_link head_shape u_due
       target'_root target'_ne branch']
  note state = one_due_tick_body_state_exact[OF rel roots]
  show ?thesis
    using gate state by (simp only: runs_to_conj)
qed

text \<open>
  The ledger-level theorem is strengthened without changing its invariant:
  the checked source step supplies the existential successor branch, while
  the exact body theorem supplies the complete generated globals equality.
\<close>

theorem due_prefix_generated_source_result_step_full_state:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       (Generic (odc_task C) # Generic u # remaining) future
       current C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw) \<and>
        t = one_due_tick_ready_inserted_state
          D C branch generic_raw c\<rbrace>"
proof -
  have rel:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using inv by (simp add: due_prefix_gate_inv_def)
  note source = due_prefix_generated_source_result_step[OF inv roots]
  note state = one_due_tick_body_state_exact[OF rel roots]
  have both:
    "one_due_tick_loop_body_source (sd_tcb_ptr D (odc_task C)) \<bullet> c
     \<lbrace>\<lambda>r t.
       (\<exists>branch'.
          r = Result (sd_tcb_ptr D u) \<and>
          due_prefix_gate_inv D R t now entry
            (processed @ [Generic (odc_task C)])
            (Generic u # remaining) future
            (due_prefix_result_step_abs entry processed
              (Generic (odc_task C)))
            (one_due_reentry_context C u) branch'
            (one_due_reentry_snapshot C branch S)
            (one_due_reentry_generic_raw D C
              (one_due_event_remove_heap D C branch
                (one_due_generic_remove_heap D C
                  (hrs_mem
                    (Scheduler_V611_Parse.globals.t_hrs_' c))))
              generic_raw)
            (one_due_event_raw_after_remove D C branch event_raw)) \<and>
        t = one_due_tick_ready_inserted_state
          D C branch generic_raw c\<rbrace>"
    using source state by (simp only: runs_to_conj)
  show ?thesis
  proof (rule runs_to_weaken[OF both])
    fix r t
    assume post:
      "(\<exists>branch'.
          r = Result (sd_tcb_ptr D u) \<and>
          due_prefix_gate_inv D R t now entry
            (processed @ [Generic (odc_task C)])
            (Generic u # remaining) future
            (due_prefix_result_step_abs entry processed
              (Generic (odc_task C)))
            (one_due_reentry_context C u) branch'
            (one_due_reentry_snapshot C branch S)
            (one_due_reentry_generic_raw D C
              (one_due_event_remove_heap D C branch
                (one_due_generic_remove_heap D C
                  (hrs_mem
                    (Scheduler_V611_Parse.globals.t_hrs_' c))))
              generic_raw)
            (one_due_event_raw_after_remove D C branch event_raw)) \<and>
       t = one_due_tick_ready_inserted_state D C branch generic_raw c"
    show
      "\<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw) \<and>
        t = one_due_tick_ready_inserted_state D C branch generic_raw c"
      using post by blast
  qed
qed

end

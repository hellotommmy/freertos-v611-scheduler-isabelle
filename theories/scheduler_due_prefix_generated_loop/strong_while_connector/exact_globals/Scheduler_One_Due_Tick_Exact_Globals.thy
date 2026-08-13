theory Scheduler_One_Due_Tick_Exact_Globals
  imports
    "EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tick_Loop.Scheduler_One_Due_Task_Phases_Tick_Loop"
begin

text \<open>
  Exact generated globals after the Generic removal, optional Event removal,
  top-ready update and ready-list insertion of one arbitrary due task.  The
  definition follows the generated source order.  In particular, the task
  priority is read from the heap after both removals; no frame rewrite back to
  the entry heap is built into the state definition.
\<close>

definition one_due_tick_ready_inserted_state ::
  "'tid scheduler_decode \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   Scheduler_V611_Parse.globals"
where
  "one_due_tick_ready_inserted_state D C branch generic_raw c =
     (let h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
          he = one_due_event_remove_heap D C branch
                 (one_due_generic_remove_heap D C h0);
          base = scheduler_mem_state he c;
          tp = sd_tcb_ptr D (odc_task C);
          pri =
            Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
              (h_val he tp);
          raised =
            (if Scheduler_V611_Parse.globals.uxTopReadyPriority_' base < pri
             then base\<lparr>
               Scheduler_V611_Parse.globals.uxTopReadyPriority_' := pri\<rparr>
             else base);
          hi = one_due_ready_insert_heap D C generic_raw he
      in scheduler_mem_state hi raised)"

lemma one_due_tick_ready_inserted_state_heap [simp]:
  "hrs_mem
      (Scheduler_V611_Parse.globals.t_hrs_'
        (one_due_tick_ready_inserted_state D C branch generic_raw c)) =
   one_due_ready_insert_heap D C generic_raw
     (one_due_event_remove_heap D C branch
       (one_due_generic_remove_heap D C
         (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))"
  by (simp add: one_due_tick_ready_inserted_state_def Let_def)

text \<open>
  The historical composed theorem passed only four projections of the state
  following vListInsertEnd to its continuation.  The exact insert theorem
  already returns the entire generated globals record.  This variant retains
  that record by starting the delayed-head continuation at the named exact
  state above.
\<close>

theorem one_due_tick_tail_insert_composed_full_state:
  fixes Q
  assumes rel:
    "one_due_gateH_entry_rel D R c a C branch S generic_raw event_raw"
    and roots: "R = generated_scheduler_roots"
    and cont:
      "one_due_tick_delayed_remainder \<bullet>
         (one_due_tick_ready_inserted_state D C branch generic_raw c)
       \<lbrace>Q\<rbrace>"
  shows
    "one_due_tick_top_ready_tail_source
       (sd_tcb_ptr D (odc_task C)) \<bullet>
       (scheduler_mem_state
         (one_due_event_remove_heap D C branch
           (one_due_generic_remove_heap D C
             (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)))) c)
     \<lbrace>Q\<rbrace>"
proof -
  let ?h = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?he = "one_due_event_remove_heap D C branch
    (one_due_generic_remove_heap D C ?h)"
  let ?tp = "sd_tcb_ptr D (odc_task C)"
  let ?target = "one_due_target_root C"
  let ?p = "one_due_generic_raw_ptr D (odc_task C)"
  have task_live: "odc_task C \<in> odc_live C"
    using one_due_gateH_pure_entryD[OF rel]
    by (auto simp: one_due_entry_rel_def one_due_context_wf_def)
  have live_abs: "odc_task C \<in> sa_live a"
    using task_live one_due_gateH_live_absD[OF rel] by simp
  have pri_he:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?he ?tp) =
     Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?h ?tp)"
    by (rule one_due_gateH_priority_after_eventD[OF rel task_live])
  have pri_lt:
    "Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
       (h_val ?h ?tp) < 4"
    using one_due_gateH_task_observationD[OF rel] live_abs
    by (simp add: TaskObservationRel_def)
  have target_sel:
    "?target =
       abi_list_ptr
         (array_ptr_index Scheduler_V611_Parse.pxReadyTasksLists_'
           False
           (unat
             (Scheduler_V611_Parse.tskTaskControlBlock_C.uxPriority_C
               (h_val ?h ?tp))))"
    by (rule one_due_gateH_source_ready_selectionD[OF rel roots])
  note after_event = one_due_gateH_after_event_obligations[OF rel]
  have rel_he_target:
    "raw_xlist_rel ?he ?target (generic_raw ?target)"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have fresh:
    "raw_fresh_for_insert ?target (ring (generic_raw ?target)) ?p"
    using after_event
    by (simp add: one_due_after_event_obligations_def Let_def)
  have hrs_reduce:
    "hrs_mem (hrs_mem_update (\<lambda>_. X) Y) = X" for X Y
    by (simp add: hrs_mem_update_def hrs_mem_def split: prod.splits)
  have item_abi:
    "abi_item_ptr (scheduler_generic_item_ptr ?tp) = ?p"
    by (simp add: one_due_generic_raw_ptr_def)
  show ?thesis
    apply (subst one_due_tail_source_split)
    apply runs_to_vcg
    subgoal by (simp add: pri_he pri_lt)
    subgoal by (rule one_due_ready_array_guard)
    subgoal
      apply (rule runs_to_weaken
          [OF scheduler_vListInsertEnd_general_exact_state])
        apply (insert rel_he_target)
        apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
          target_sel[symmetric])
       apply (insert fresh)
       apply (simp add: item_abi pri_he target_sel[symmetric]
         one_due_generic_raw_ptr_def)
      apply (clarsimp split: exception_or_result_splits)
      apply (insert cont)
      apply (simp add: one_due_tick_ready_inserted_state_def Let_def
        pri_he
        target_sel[symmetric] item_abi
        one_due_generic_raw_ptr_def one_due_ready_insert_heap_def)
      done
    subgoal by (simp add: pri_he pri_lt)
    subgoal by (rule one_due_ready_array_guard)
    subgoal
      apply (rule runs_to_weaken
          [OF scheduler_vListInsertEnd_general_exact_state])
        apply (insert rel_he_target)
        apply (simp add: scheduler_mem_state_def hrs_reduce pri_he
          target_sel[symmetric])
       apply (insert fresh)
       apply (simp add: item_abi pri_he target_sel[symmetric]
         one_due_generic_raw_ptr_def)
      apply (clarsimp split: exception_or_result_splits)
      apply (insert cont)
      apply (simp add: one_due_tick_ready_inserted_state_def Let_def
        pri_he
        target_sel[symmetric] item_abi
        one_due_generic_raw_ptr_def one_due_ready_insert_heap_def)
      done
    done
qed

end

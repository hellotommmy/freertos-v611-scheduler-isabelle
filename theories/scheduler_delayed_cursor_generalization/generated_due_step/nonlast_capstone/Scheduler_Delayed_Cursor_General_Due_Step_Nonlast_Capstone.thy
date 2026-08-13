theory Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core.Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core"
begin

definition CursorGeneralDueLoopManagedSharedResultPost ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid \<Rightarrow> 'tid \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "CursorGeneralDueLoopManagedSharedResultPost D R now entry processed task u
       remaining future current C branch S generic_raw event_raw K_G K_E
       managed termination external before r t \<longleftrightarrow>
     (let after =
          due_prefix_result_step_abs entry processed (Generic task);
          h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before);
          hg = one_due_generic_remove_heap D C h0;
          he = one_due_event_remove_heap D C branch hg;
          generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
          generic_abs' = one_due_generic_abs_after_insert C S;
          event_raw' =
            one_due_event_raw_after_remove D C branch event_raw;
          event_abs' = one_due_event_abs_after_remove C branch S;
          S' = one_due_reentry_snapshot C branch S
      in r = Result (sd_tcb_ptr D u) \<and>
         t = one_due_tick_ready_inserted_state
               D C branch generic_raw before \<and>
         (\<exists>branch'.
           due_prefix_managed_gate_inv D R t now entry
             (processed @ [Generic task])
             (Generic u # remaining) future after managed
             (one_due_reentry_context C u) branch'
             S' generic_raw' event_raw') \<and>
         CursorGeneralDueLoopStrongHeadRel D t after
           managed termination external
           generic_raw' generic_abs' event_raw' event_abs' K_G K_E S'
           now entry (processed @ [Generic task])
           (Generic u # remaining) future
           DueGate (Some (Generic u)) (sd_tcb_ptr D u))"

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_result_full:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed
       (Generic task # Generic u # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # Generic u # remaining) future current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>CursorGeneralDueLoopManagedSharedResultPost D R now entry
        processed task u remaining future current C branch S
        generic_raw event_raw K_G K_E managed termination external c\<rbrace>"
proof -
  have gate_C:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic (odc_task C) # Generic u # remaining) future
       current managed C branch S generic_raw event_raw"
    using gate selector by simp
  note source_C =
    due_prefix_managed_generated_nonlast_source_full_state[OF gate_C roots]
  have source:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_managed_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          managed (one_due_reentry_context C u) branch'
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
    using source_C selector by simp
  have strong_after:
    "let after =
         due_prefix_result_step_abs entry processed (Generic task);
         h0 = hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c);
         hg = one_due_generic_remove_heap D C h0;
         he = one_due_event_remove_heap D C branch hg;
         generic_raw' = one_due_reentry_generic_raw D C he generic_raw;
         event_raw' =
           one_due_event_raw_after_remove D C branch event_raw;
         S' = one_due_reentry_snapshot C branch S;
         post_c = one_due_tick_ready_inserted_state
           D C branch generic_raw c
     in CursorGeneralDueLoopStrongHeadRel D post_c after
          managed termination external
          generic_raw' (ods_generic_family S')
          event_raw' (ods_event_family S') K_G K_E S'
          now entry (processed @ [Generic task])
          (Generic u # remaining) future
          DueGate (Some (Generic u)) (sd_tcb_ptr D u)"
    by (rule CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_full_state[
          OF strong gate selector roots])
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "\<exists>branch'.
        r = Result (sd_tcb_ptr D u) \<and>
        due_prefix_managed_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          managed (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw) \<and>
        t = one_due_tick_ready_inserted_state
          D C branch generic_raw c"
    obtain branch' where result:
        "r = Result (sd_tcb_ptr D u)"
      and gate_after:
        "due_prefix_managed_gate_inv D R t now entry
          (processed @ [Generic (odc_task C)])
          (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed
            (Generic (odc_task C)))
          managed (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem
                  (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
      and state:
        "t = one_due_tick_ready_inserted_state
          D C branch generic_raw c"
      using post by blast
    show
      "CursorGeneralDueLoopManagedSharedResultPost D R now entry processed
        task u remaining future current C branch S generic_raw event_raw
        K_G K_E managed termination external c r t"
      unfolding CursorGeneralDueLoopManagedSharedResultPost_def Let_def
      apply (intro conjI)
      subgoal by (rule result)
      subgoal by (rule state)
      subgoal
        apply (rule exI[where x=branch'])
        using gate_after selector by simp
      subgoal
      proof -
        note strong0 = strong_after[unfolded Let_def]
        have generic_eq:
          "one_due_generic_abs_after_insert C S =
           ods_generic_family (one_due_reentry_snapshot C branch S)"
          by (rule one_due_generic_abs_after_insert_is_reentry)
        have event_eq:
          "one_due_event_abs_after_remove C branch S =
           ods_event_family (one_due_reentry_snapshot C branch S)"
          by (rule one_due_event_abs_after_remove_is_reentry)
        show ?thesis
        apply (subst state)
        apply (subst generic_eq)
        apply (subst event_eq)
        by (rule strong0)
      qed
      done
  qed
qed

text \<open>
  The public post names the exact raw transformers and the exact abstract
  family transformers.  It contains no canonical family, expected branch,
  successful-execution premise, or caller-supplied desired poststate.
\<close>

end

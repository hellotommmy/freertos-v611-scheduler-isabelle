theory Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State.Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State"
begin

text \<open>
  Reusable strong-state assembler for every symbolic successor tail.  The
  caller supplies only the concrete local corresponding to the mathematically
  determined next-node option.  Empty, future, and nonlast source rungs derive
  that local from their exact generated result; it is not a desired family,
  heap, or abstract-poststate premise.
\<close>

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_result_full_state_core:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
    and post_ptr:
      "strong_due_next_ptr_rel D
         (due_prefix_next_node_of remaining future) post_pxTCB"
  shows
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
          now entry (processed @ [Generic task]) remaining future
          (due_prefix_exit_phase_of remaining future)
          (due_prefix_next_node_of remaining future) post_pxTCB"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  let ?post_c =
    "one_due_tick_ready_inserted_state D C branch generic_raw c"

  have scheduler_snapshot_after:
    "CursorGeneralDueLoopSchedulerSnapshotRel D ?post_c ?after
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now remaining future"
    using CursorGeneralDueLoopStrongHeadRel_managed_gate_result_scheduler_snapshot[
      OF strong gate selector roots]
    by (simp add: Let_def)
  have exit_before:
    "due_prefix_exit_inv now entry processed
       (Generic task # remaining) future current phase next"
    using strong by (simp add: CursorGeneralDueLoopStrongHeadRel_def)
  have loop_before:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit_before])
  have current_eq: "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop_before])
  have frame: "due_prefix_abstract_control_frame current ?after"
    by (rule due_prefix_result_step_control_frame[OF current_eq])
  have loop_after:
    "due_prefix_loop_inv now entry (processed @ [Generic task])
       remaining future ?after"
    by (rule due_prefix_result_step_preserves_inv[OF loop_before])
  have exit_after:
    "due_prefix_exit_inv now entry (processed @ [Generic task])
       remaining future ?after
       (due_prefix_exit_phase_of remaining future)
       (due_prefix_next_node_of remaining future)"
    using loop_after by (simp add: due_prefix_exit_inv_def)
  have tick_before: "sa_tick current = now"
    and quiet_before: "sa_suspend_depth current = 0"
    and pending_before: "ring (sa_pending current) = []"
    using strong by (simp_all add: CursorGeneralDueLoopStrongHeadRel_def)
  have tick_after: "sa_tick ?after = now"
    and quiet_after: "sa_suspend_depth ?after = 0"
    and pending_after: "ring (sa_pending ?after) = []"
    using frame tick_before quiet_before pending_before
    by (simp_all add: due_prefix_abstract_control_frame_def)
  have strong_after:
    "CursorGeneralDueLoopStrongHeadRel D ?post_c ?after
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) remaining future
       (due_prefix_exit_phase_of remaining future)
       (due_prefix_next_node_of remaining future) post_pxTCB"
    unfolding CursorGeneralDueLoopStrongHeadRel_def
    apply (intro conjI)
    subgoal by (rule scheduler_snapshot_after)
    subgoal by (rule exit_after)
    subgoal by (rule tick_after)
    subgoal by (rule quiet_after)
    subgoal by (rule pending_after)
    subgoal by (rule post_ptr)
    done
  show ?thesis
    using strong_after by (simp add: Let_def)
qed

corollary CursorGeneralDueLoopStrongHeadRel_managed_gate_nonlast_full_state:
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
proof -
  have ptr:
    "strong_due_next_ptr_rel D
       (due_prefix_next_node_of (Generic u # remaining) future)
       (sd_tcb_ptr D u)"
    by (simp add: strong_due_next_ptr_rel_def)
  note core =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_result_full_state_core[
      OF strong gate selector roots ptr]
  show ?thesis
    using core by simp
qed

end

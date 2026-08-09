theory Scheduler_Due_Prefix_Terminal_Exit
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner.Scheduler_Due_Prefix_Terminal_Head_Owner"
begin

lemma due_prefix_gate_inv_last_due_exit:
  assumes inv:
    "due_prefix_gate_inv D R c now entry processed
       [Generic (odc_task C)] future current C branch S
       generic_raw event_raw"
  shows
    "due_prefix_exit_inv now entry
       (processed @ [Generic (odc_task C)]) [] future
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))
       (due_prefix_exit_phase_of [] future)
       (due_prefix_next_node_of [] future)"
proof -
  have prefix:
    "due_prefix_loop_inv now entry processed
       [Generic (odc_task C)] future current"
    by (rule due_prefix_gate_inv_loopD[OF inv])
  have post:
    "due_prefix_loop_inv now entry
       (processed @ [Generic (odc_task C)]) [] future
       (due_prefix_result_step_abs entry processed
         (Generic (odc_task C)))"
    by (rule due_prefix_result_step_preserves_inv[OF prefix])
  show ?thesis
    using post by (simp add: due_prefix_exit_inv_def)
qed

end


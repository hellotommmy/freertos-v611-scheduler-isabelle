theory Scheduler_Due_Prefix_Managed_Gate_Capstone
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Entry_Raw_Owner.Scheduler_Due_Prefix_Managed_Gate_Entry_Raw_Owner"
begin

theorem DueLoopStrongHeadRel_canonical_managed_gate:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current managed
       external K_E task"
    and
    "branch \<equiv> one_due_canonical_event_branch
       (due_prefix_canonical_managed_context R c current managed
         external K_E task) S"
  shows
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # remaining) future current managed C branch S
       generic_raw event_raw"
proof -
  have gateH:
    "one_due_gateH_entry_rel D R c
       (managed_scheduler_view current managed) C branch S
       generic_raw event_raw"
    unfolding C_def branch_def
    by (rule DueLoopStrongHeadRel_canonical_gateH_entry[
          OF strong roots])
  have ledger:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current \<and>
     odc_tick C = now \<and>
     sa_tick current = now \<and>
     ods_generic_family S (odc_delayed_root C) =
       current_delayed_ring current \<and>
     one_due_all_ready_destinations C \<and>
     ring (ods_event_family S (odc_pending_root C)) = []"
    unfolding C_def
    by (rule DueLoopStrongHeadRel_canonical_managed_cross_ledger[
          OF strong roots])
  show ?thesis
    using gateH ledger
    by (simp add: due_prefix_managed_gate_inv_def)
qed

corollary DueLoopStrongHeadRel_managed_gate_witness:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "\<exists>C branch.
       odc_task C = task \<and>
       due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed C branch S
         generic_raw event_raw"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current managed
       external K_E task"
  let ?branch = "one_due_canonical_event_branch ?C S"
  have gate:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # remaining) future current managed ?C ?branch S
       generic_raw event_raw"
    by (rule DueLoopStrongHeadRel_canonical_managed_gate[
          OF strong roots])
  show ?thesis
    apply (rule exI[where x=
      "due_prefix_canonical_managed_context R c current managed
         external K_E task"])
    apply (rule exI[where x=
      "one_due_canonical_event_branch
         (due_prefix_canonical_managed_context R c current managed
           external K_E task) S"])
    apply (rule conjI)
    subgoal by simp
    by (rule gate)
qed

text \<open>
  This is the non-vacuity boundary of the repair.  Conditional on the same
  legal strong head state, a nonempty termination ring makes the historical
  runnable-domain Gate-H impossible, while the managed-view Gate-H has the
  canonical task/branch witness constructed above.  No retired task is added
  to the loop state: the strict domain inequality is retained explicitly.
\<close>

corollary DueLoopStrongHeadRel_nonempty_termination_managed_gate_compatible:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
    and retired: "ring termination \<noteq> []"
  shows
    "managed \<noteq> sa_live current \<and>
     (\<not> (\<exists>C branch.
        due_prefix_gate_inv D R c now entry processed
          (Generic task # remaining) future current C branch S
          generic_raw event_raw)) \<and>
     (\<exists>C branch.
        odc_task C = task \<and>
        due_prefix_managed_gate_inv D R c now entry processed
          (Generic task # remaining) future current managed C branch S
          generic_raw event_raw)"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have domain:
    "strong_managed_domain_rel current termination managed"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have strict: "managed \<noteq> sa_live current"
  proof
    assume equal: "managed = sa_live current"
    have "ring termination = []"
      by (rule iffD1[OF strong_managed_domain_no_retired_iff[OF domain]
            equal])
    then show False using retired by contradiction
  qed
  have old_impossible:
    "\<not> (\<exists>C branch.
       due_prefix_gate_inv D R c now entry processed
         (Generic task # remaining) future current C branch S
         generic_raw event_raw)"
    by (rule DueLoopStrongHeadRel_retired_forbids_gateH[
          OF strong retired])
  have managed_witness:
    "\<exists>C branch.
       odc_task C = task \<and>
       due_prefix_managed_gate_inv D R c now entry processed
         (Generic task # remaining) future current managed C branch S
         generic_raw event_raw"
    by (rule DueLoopStrongHeadRel_managed_gate_witness[OF strong roots])
  show ?thesis using strict old_impossible managed_witness by blast
qed

end

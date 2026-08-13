theory Scheduler_Due_Prefix_ML_Public_Wrapper
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone.Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone"
begin

text \<open>
  Public managed/live interface for the generated due-prefix body.

  \<open>M\<close> is the finite managed decoder/geometry carrier.  It includes
  live TCBs and may additionally include retired TCBs in the termination
  root.  \<open>L\<close> is the runnable role domain and is fixed to the real
  abstract state's @{term sa_live}.  The managed scheduler view is used only
  inside the local Gate-H heap proof; it is not advertised as a well-formed
  scheduler state.
\<close>

lemma managed_scheduler_view_membership_wf_iff:
  assumes membership: "membership_wf a"
  shows
    "membership_wf (managed_scheduler_view a M) \<longleftrightarrow>
     M = sa_live a"
proof
  assume managed_membership:
    "membership_wf (managed_scheduler_view a M)"
  have old_owned:
    "ready_task_set a \<union>
       generic_task_set (sa_delayed_a a) \<union>
       generic_task_set (sa_delayed_b a) \<union>
       generic_task_set (sa_suspended a) = sa_live a"
    using membership
    by (auto simp: membership_wf_def Let_def)
  have managed_owned:
    "ready_task_set a \<union>
       generic_task_set (sa_delayed_a a) \<union>
       generic_task_set (sa_delayed_b a) \<union>
       generic_task_set (sa_suspended a) = M"
    using managed_membership
    by (auto simp: membership_wf_def managed_scheduler_view_def
        ready_task_set_def Let_def)
  show "M = sa_live a"
    using old_owned managed_owned by simp
next
  assume equal: "M = sa_live a"
  have view_equal: "managed_scheduler_view a M = a"
    using equal by (simp add: managed_scheduler_view_def)
  show "membership_wf (managed_scheduler_view a M)"
    using membership view_equal by simp
qed

corollary managed_scheduler_view_retired_not_membership_wf:
  assumes membership: "membership_wf a"
    and retired: "M \<noteq> sa_live a"
  shows "\<not> membership_wf (managed_scheduler_view a M)"
  using managed_scheduler_view_membership_wf_iff[OF membership, of M]
    retired by blast

corollary managed_scheduler_view_retired_not_core_wf:
  assumes membership: "membership_wf a"
    and retired: "M \<noteq> sa_live a"
  shows "\<not> core_wf (managed_scheduler_view a M)"
proof
  assume core: "core_wf (managed_scheduler_view a M)"
  have "membership_wf (managed_scheduler_view a M)"
    using core by (simp add: core_wf_def)
  then show False
    using managed_scheduler_view_retired_not_membership_wf[
        OF membership retired]
    by contradiction
qed

corollary managed_scheduler_view_retired_not_due_loop_core_wf:
  assumes membership: "membership_wf a"
    and retired: "M \<noteq> sa_live a"
  shows "\<not> due_loop_core_wf (managed_scheduler_view a M)"
proof
  assume core: "due_loop_core_wf (managed_scheduler_view a M)"
  have "membership_wf (managed_scheduler_view a M)"
    using core by (simp add: due_loop_core_wf_def)
  then show False
    using managed_scheduler_view_retired_not_membership_wf[
        OF membership retired]
    by contradiction
qed

lemma DueLoopStrongHeadRel_due_head_live:
  assumes strong:
    "DueLoopStrongHeadRel D c current M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
  shows "task \<in> sa_live current"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have loop:
    "due_prefix_loop_inv now entry processed
       (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have current_ring:
    "ring (current_delayed_ring current) =
       Generic task # (remaining @ future)"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_delayed:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current)"
    using current_ring
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def generic_task_set_def)
  have core: "due_loop_core_wf current"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  show ?thesis
    using core task_delayed
    by (auto simp: due_loop_core_wf_def membership_wf_def Let_def)
qed

lemma DueLoopStrongHeadRel_nonempty_termination_managed_view_not_wf:
  assumes strong:
    "DueLoopStrongHeadRel D c current M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase nxt pxTCB"
    and retired: "ring termination \<noteq> []"
  shows
    "\<not> membership_wf (managed_scheduler_view current M) \<and>
     \<not> core_wf (managed_scheduler_view current M) \<and>
     \<not> due_loop_core_wf (managed_scheduler_view current M)"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have core: "due_loop_core_wf current"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have membership: "membership_wf current"
    using core by (simp add: due_loop_core_wf_def)
  have domain: "strong_managed_domain_rel current termination M"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have strict: "M \<noteq> sa_live current"
  proof
    assume equal: "M = sa_live current"
    have "ring termination = []"
      by (rule iffD1[
          OF strong_managed_domain_no_retired_iff[OF domain] equal])
    then show False using retired by contradiction
  qed
  show ?thesis
    using managed_scheduler_view_retired_not_membership_wf[
        OF membership strict]
      managed_scheduler_view_retired_not_core_wf[
        OF membership strict]
      managed_scheduler_view_retired_not_due_loop_core_wf[
        OF membership strict]
    by blast
qed

definition due_prefix_ML_gate_inv ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid set \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   bool"
where
  "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw \<longleftrightarrow>
     L = sa_live current \<and>
     L \<subseteq> M \<and>
     odc_live C = M \<and>
     odc_task C \<in> L \<and>
     due_prefix_managed_gate_inv D R c now entry processed remaining future
       current M C branch S generic_raw event_raw"

lemma due_prefix_ML_gate_live_eqD:
  assumes gate:
    "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw"
  shows "L = sa_live current"
  using gate[unfolded due_prefix_ML_gate_inv_def] by blast

lemma due_prefix_ML_gate_domainD:
  assumes gate:
    "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw"
  shows "L \<subseteq> M"
  using gate[unfolded due_prefix_ML_gate_inv_def] by blast

lemma due_prefix_ML_gate_decoder_carrierD:
  assumes gate:
    "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw"
  shows "odc_live C = M"
  using gate[unfolded due_prefix_ML_gate_inv_def] by blast

lemma due_prefix_ML_gate_selected_liveD:
  assumes gate:
    "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw"
  shows "odc_task C \<in> L"
  using gate[unfolded due_prefix_ML_gate_inv_def] by blast

lemma due_prefix_ML_gate_managed_gateD:
  assumes gate:
    "due_prefix_ML_gate_inv D R c now entry processed remaining future
       current M L C branch S generic_raw event_raw"
  shows
    "due_prefix_managed_gate_inv D R c now entry processed remaining future
       current M C branch S generic_raw event_raw"
  using gate[unfolded due_prefix_ML_gate_inv_def] by blast

theorem DueLoopStrongHeadRel_canonical_ML_gate:
  assumes strong:
    "DueLoopStrongHeadRel D c current M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  defines
    "C \<equiv> due_prefix_canonical_managed_context R c current M
       external K_E task"
    and
    "branch \<equiv> one_due_canonical_event_branch
       (due_prefix_canonical_managed_context R c current M
         external K_E task) S"
  shows
    "due_prefix_ML_gate_inv D R c now entry processed
       (Generic task # remaining) future current M (sa_live current)
       C branch S generic_raw event_raw"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have domain: "strong_managed_domain_rel current termination M"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have live_subset: "sa_live current \<subseteq> M"
    using domain by (simp add: strong_managed_domain_rel_def)
  have task_live: "task \<in> sa_live current"
    by (rule DueLoopStrongHeadRel_due_head_live[OF strong])
  have managed_gate:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # remaining) future current M C branch S
       generic_raw event_raw"
    unfolding C_def branch_def
    by (rule DueLoopStrongHeadRel_canonical_managed_gate[
          OF strong roots])
  show ?thesis
    unfolding due_prefix_ML_gate_inv_def
    apply (intro conjI)
    subgoal by simp
    subgoal by (rule live_subset)
    subgoal unfolding C_def by simp
    subgoal unfolding C_def using task_live by simp
    by (rule managed_gate)
qed

corollary DueLoopStrongHeadRel_ML_gate_witness:
  assumes strong:
    "DueLoopStrongHeadRel D c current M termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase nxt pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "\<exists>C branch.
       odc_task C = task \<and>
       due_prefix_ML_gate_inv D R c now entry processed
         (Generic task # remaining) future current M (sa_live current)
         C branch S generic_raw event_raw"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current M
       external K_E task"
  let ?branch = "one_due_canonical_event_branch ?C S"
  have gate:
    "due_prefix_ML_gate_inv D R c now entry processed
       (Generic task # remaining) future current M (sa_live current)
       ?C ?branch S generic_raw event_raw"
    by (rule DueLoopStrongHeadRel_canonical_ML_gate[
          OF strong roots])
  show ?thesis
    apply (rule exI[where x = ?C])
    apply (rule exI[where x = ?branch])
    using gate by simp
qed

definition DueLoopMLStrongNonlastResultPost ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid \<Rightarrow> 'tid \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> 'tid set \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "DueLoopMLStrongNonlastResultPost D R now entry processed task u
       remaining future current M L S generic_raw event_raw K_G K_E
       termination external before r t \<longleftrightarrow>
     (\<exists>C branch.
        odc_task C = task \<and>
        due_prefix_ML_gate_inv D R before now entry processed
          (Generic task # Generic u # remaining) future current M L
          C branch S generic_raw event_raw \<and>
        DueLoopManagedSharedResultPost D R now entry processed task u
          remaining future current C branch S generic_raw event_raw
          K_G K_E M termination external before r t)"

theorem DueLoopStrongHeadRel_ML_nonlast_result_full:
  assumes strong:
    "DueLoopStrongHeadRel D c current M termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry processed
       (Generic task # Generic u # remaining) future
       phase next pxTCB"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>DueLoopMLStrongNonlastResultPost D R now entry processed task u
        remaining future current M (sa_live current) S generic_raw
        event_raw K_G K_E termination external c\<rbrace>"
proof -
  let ?C =
    "due_prefix_canonical_managed_context R c current M
       external K_E task"
  let ?branch = "one_due_canonical_event_branch ?C S"
  have ML_gate:
    "due_prefix_ML_gate_inv D R c now entry processed
       (Generic task # Generic u # remaining) future current M
       (sa_live current) ?C ?branch S generic_raw event_raw"
    by (rule DueLoopStrongHeadRel_canonical_ML_gate[
          OF strong roots])
  have managed_gate:
    "due_prefix_managed_gate_inv D R c now entry processed
       (Generic task # Generic u # remaining) future current M
       ?C ?branch S generic_raw event_raw"
    by (rule due_prefix_ML_gate_managed_gateD[OF ML_gate])
  have selector: "odc_task ?C = task"
    by simp
  note source =
    DueLoopStrongHeadRel_managed_gate_nonlast_result_full[
      OF strong managed_gate selector roots]
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "DueLoopManagedSharedResultPost D R now entry processed task u
        remaining future current ?C ?branch S generic_raw event_raw
        K_G K_E M termination external c r t"
    show
      "DueLoopMLStrongNonlastResultPost D R now entry processed task u
        remaining future current M (sa_live current) S generic_raw
        event_raw K_G K_E termination external c r t"
      unfolding DueLoopMLStrongNonlastResultPost_def
      apply (rule exI[where x = ?C])
      apply (rule exI[where x = ?branch])
      using selector ML_gate post by simp
  qed
qed

end

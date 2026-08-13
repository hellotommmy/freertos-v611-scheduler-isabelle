theory Scheduler_Resume_Managed_Gate_Base
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Control_Frame.Scheduler_Resume_Pending_Control_Frame"
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay.Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay"
begin

text \<open>
  A managed Resume gate must keep the public scheduler state separate from the
  total allocation/decoder domain.  The actual xTaskResumeAll cutpoint is
  protected at proof-port depth/mask 1/1, while the full cursor-general
  scheduler relation is retained on a public shadow.  No legacy pending gate
  is included: that relation equates its decoder domain with sa_live and would
  therefore exclude every legal task waiting for termination.
\<close>

definition CursorGeneralStrongProtectedSchedulerSnapshotRel ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D depth irq_mask c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     (\<exists>c0.
        c = scheduler_port_overlay depth irq_mask c0 \<and>
        CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
          external generic_raw generic_abs event_raw event_abs K_G K_E S)"

definition CursorGeneralStrongResumePendingManagedGateRel ::
  "'tid scheduler_decode \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> (raw_node_id, raw_key) xlist_abs) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow> bool"
where
  "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<longleftrightarrow>
     CursorGeneralStrongProtectedSchedulerSnapshotRel
       D (1 :: 32 word) (1 :: 32 word) c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
     sa_suspend_depth a = 0 \<and>
     (ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None)"

lemma CursorGeneralStrongProtectedSchedulerSnapshotRelI:
  assumes overlay: "c = scheduler_port_overlay depth irq_mask c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D depth irq_mask c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using overlay snapshot
  by (auto simp: CursorGeneralStrongProtectedSchedulerSnapshotRel_def)

lemma CursorGeneralStrongProtectedSchedulerSnapshotRelD:
  assumes protected:
    "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D depth irq_mask c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "\<exists>c0.
       c = scheduler_port_overlay depth irq_mask c0 \<and>
       CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
  using protected
  by (auto simp: CursorGeneralStrongProtectedSchedulerSnapshotRel_def)

lemma CursorGeneralStrongResumePendingManagedGateRelI:
  assumes protected:
    "CursorGeneralStrongProtectedSchedulerSnapshotRel
       D (1 :: 32 word) (1 :: 32 word) c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and quiet: "sa_suspend_depth a = 0"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
  shows
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  using protected quiet current_safe
  by (simp add: CursorGeneralStrongResumePendingManagedGateRel_def)

lemma CursorGeneralStrongResumePendingManagedGateRelD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "\<exists>c0.
       c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0 \<and>
       CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S \<and>
       sa_suspend_depth a = 0 \<and>
       (ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None)"
  using gate
  by (auto simp: CursorGeneralStrongResumePendingManagedGateRel_def
      CursorGeneralStrongProtectedSchedulerSnapshotRel_def)

lemma CursorGeneralStrongResumePendingManagedGateRel_managed_domainD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "CursorGeneralStrongManagedDomainRel a termination managed"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  show ?thesis
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_port_runningD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1 \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 1 \<and>
     Scheduler_V611_Parse.globals.xSchedulerRunning_' c = 1"
proof -
  obtain c0 where c:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have boundary: "scheduler_boundary_rel c0"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  show ?thesis
    using c boundary by (simp add: scheduler_boundary_rel_def)
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_current_liveD:
  assumes gate:
      "CursorGeneralStrongResumePendingManagedGateRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    and pending: "ring (sa_pending a) \<noteq> []"
  shows
    "\<exists>current.
       sa_current a = Some current \<and>
       current \<in> sa_live a"
proof -
  obtain c0 where snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    and current_safe:
      "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  obtain current where current: "sa_current a = Some current"
    using current_safe pending by (cases "sa_current a") auto
  have canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        cursor_general_core_wf_def Let_def)
  have live: "current \<in> sa_live a"
    using core_wf_current_is_live[OF canonical_core]
    by (simp add: current)
  show ?thesis using current live by blast
qed

lemma CursorGeneralStrongResumePendingManagedGateRel_pending_liveD:
  assumes gate:
    "CursorGeneralStrongResumePendingManagedGateRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "event_task_set (sa_pending a) \<subseteq> sa_live a"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate] by blast
  have canonical_core: "core_wf (canonicalize_scheduler_cursors a)"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def
        cursor_general_core_wf_def Let_def)
  have pending_subset:
    "event_task_set (sa_pending (canonicalize_scheduler_cursors a))
       \<subseteq> sa_live (canonicalize_scheduler_cursors a)"
    using canonical_core
    by (simp add: core_wf_def membership_wf_def Let_def)
  show ?thesis using pending_subset
    by (simp add: event_task_set_def)
qed

theorem CursorGeneralStrongResumePendingManagedGateRel_old_gate_forces_no_retired:
  assumes managed_gate:
      "CursorGeneralStrongResumePendingManagedGateRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    and old_gate:
      "resume_pending_gate_entry_rel D R c a C P
         old_generic_raw old_event_raw"
  shows "managed = sa_live a"
proof -
  obtain c0 where snapshot:
    "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
       external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF managed_gate]
    by blast
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c0))
       GenericRootUniverse generic_raw generic_abs managed K_G"
    using snapshot
    by (simp add: CursorGeneralStrongSchedulerSnapshotRel_def Let_def)
  have managed_laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  have old_laws: "universal_decoder_laws (rpc_live C) D"
    by (rule resume_pending_gate_decoder_lawsD[OF old_gate])
  have old_live: "rpc_live C = sa_live a"
    by (rule resume_pending_gate_live_absD[OF old_gate])
  have live_subset: "sa_live a \<subseteq> managed"
    using domain
    by (simp add: CursorGeneralStrongManagedDomainRel_def)
  have managed_subset: "managed \<subseteq> sa_live a"
  proof
    fix t
    assume t: "t \<in> managed"
    have decoded: "sd_tcb_decode D (sd_tcb_ptr D t) = Some t"
      using managed_laws t
      by (auto simp: universal_decoder_laws_def)
    have "t \<in> rpc_live C"
      using old_laws decoded
      by (auto simp: universal_decoder_laws_def)
    then show "t \<in> sa_live a" using old_live by simp
  qed
  show ?thesis using live_subset managed_subset by blast
qed

corollary CursorGeneralStrongResumePendingManagedGateRel_retired_forbids_old_gate:
  assumes managed_gate:
      "CursorGeneralStrongResumePendingManagedGateRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S"
    and retired: "ring termination \<noteq> []"
  shows
    "\<not> (\<exists>R C P old_generic_raw old_event_raw.
       resume_pending_gate_entry_rel D R c a C P
         old_generic_raw old_event_raw)"
proof
  assume old:
    "\<exists>R C P old_generic_raw old_event_raw.
       resume_pending_gate_entry_rel D R c a C P
         old_generic_raw old_event_raw"
  then obtain R C P old_generic_raw old_event_raw where old_gate:
    "resume_pending_gate_entry_rel D R c a C P
       old_generic_raw old_event_raw"
    by blast
  have no_retired: "managed = sa_live a"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_old_gate_forces_no_retired[
        OF managed_gate old_gate])
  have domain: "CursorGeneralStrongManagedDomainRel a termination managed"
    by (rule
      CursorGeneralStrongResumePendingManagedGateRel_managed_domainD[
        OF managed_gate])
  have generic: "generic_ring termination"
    and task_set:
      "generic_task_set termination = managed - sa_live a"
    using domain
    by (simp_all add: CursorGeneralStrongManagedDomainRel_def)
  have empty_tasks: "generic_task_set termination = {}"
    using task_set no_retired by simp
  have "ring termination = []"
    by (rule iffD1[OF generic_ring_task_set_empty_iff[OF generic] empty_tasks])
  then show False using retired by contradiction
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val hyps = Thm.hyps_of th
      val prems = Thm.prems_of th
      val _ =
        if null hyps then ()
        else error (label ^ " has hidden hypotheses")
      val _ =
        if length prems = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString (length prems))
    in () end

  val _ = audit_exact "protected scheduler snapshot constructor" 2
    @{thm CursorGeneralStrongProtectedSchedulerSnapshotRelI}
  val _ = audit_exact "protected scheduler snapshot destructor" 1
    @{thm CursorGeneralStrongProtectedSchedulerSnapshotRelD}
  val _ = audit_exact "managed Resume gate constructor" 3
    @{thm CursorGeneralStrongResumePendingManagedGateRelI}
  val _ = audit_exact "managed Resume gate destructor" 1
    @{thm CursorGeneralStrongResumePendingManagedGateRelD}
  val _ = audit_exact "managed Resume gate domain" 1
    @{thm CursorGeneralStrongResumePendingManagedGateRel_managed_domainD}
  val _ = audit_exact "managed Resume gate protected port/running" 1
    @{thm CursorGeneralStrongResumePendingManagedGateRel_port_runningD}
  val _ = audit_exact "managed Resume gate current-live" 2
    @{thm CursorGeneralStrongResumePendingManagedGateRel_current_liveD}
  val _ = audit_exact "managed Resume gate pending-live" 1
    @{thm CursorGeneralStrongResumePendingManagedGateRel_pending_liveD}
  val _ = audit_exact "old Resume gate domain collapse" 2
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_old_gate_forces_no_retired}
  val _ = audit_exact "retired task forbids old Resume gate" 2
    @{thm
      CursorGeneralStrongResumePendingManagedGateRel_retired_forbids_old_gate}
\<close>

end

theory Scheduler_Due_Prefix_Managed_Gate_Diagnostic
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone.Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone"
begin

text \<open>
  The historical Gate-H relation uses one field, odc_live, for two different
  domains: the currently runnable scheduler tasks and every allocated TCB that
  the total decoder can observe.  A task in xTasksWaitingTermination belongs
  only to the latter domain.  The diagnostic below records the resulting
  incompatibility before introducing the managed-view bridge.
\<close>

theorem DueLoopStrongHeadRel_gateH_forces_no_retired:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase nxt pxTCB"
    and gate:
    "due_prefix_gate_inv D R c now entry processed remaining future
       current C branch S generic_raw event_raw"
  shows "managed = sa_live current"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have domain:
    "strong_managed_domain_rel current termination managed"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have coverage:
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs managed K_G"
    using snapshot
    by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
  have managed_laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  have local:
    "one_due_gateH_entry_rel D R c current C branch S
       generic_raw event_raw"
    using gate by (simp add: due_prefix_gate_inv_def)
  have local_laws: "universal_decoder_laws (odc_live C) D"
    by (rule one_due_gateH_decoder_lawsD[OF local])
  have local_live: "odc_live C = sa_live current"
    using local[unfolded one_due_gateH_entry_rel_def Let_def]
    by blast
  have live_subset: "sa_live current \<subseteq> managed"
    using domain by (simp add: strong_managed_domain_rel_def)
  have managed_subset: "managed \<subseteq> sa_live current"
  proof
    fix t
    assume managed: "t \<in> managed"
    have decoded: "sd_tcb_decode D (sd_tcb_ptr D t) = Some t"
      using managed_laws managed
      by (auto simp: universal_decoder_laws_def)
    have "t \<in> odc_live C"
      using local_laws decoded
      by (auto simp: universal_decoder_laws_def)
    then show "t \<in> sa_live current"
      using local_live by simp
  qed
  show ?thesis using live_subset managed_subset by blast
qed

corollary DueLoopStrongHeadRel_retired_forbids_gateH:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed remaining future phase nxt pxTCB"
    and retired: "ring termination \<noteq> []"
  shows
    "\<not> (\<exists>C branch.
       due_prefix_gate_inv D R c now entry processed remaining future
         current C branch S generic_raw event_raw)"
proof (rule notI)
  assume exists:
    "\<exists>C branch.
       due_prefix_gate_inv D R c now entry processed remaining future
         current C branch S generic_raw event_raw"
  from exists show False
  proof (elim exE)
    fix C branch
    assume gate:
      "due_prefix_gate_inv D R c now entry processed remaining future
         current C branch S generic_raw event_raw"
    have no_retired: "managed = sa_live current"
      by (rule DueLoopStrongHeadRel_gateH_forces_no_retired[OF strong gate])
    note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
    have domain:
      "strong_managed_domain_rel current termination managed"
      using snapshot
      by (simp add: DueLoopSchedulerSnapshotRel_def Let_def)
    have "ring termination = []"
      by (rule iffD1[OF strong_managed_domain_no_retired_iff[OF domain]
            no_retired])
    then show False using retired by contradiction
  qed
qed

end

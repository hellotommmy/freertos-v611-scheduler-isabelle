theory Scheduler_Due_Prefix_Strong_Snapshot_Projections
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Core.Scheduler_Due_Prefix_Strong_Snapshot_Core"
begin

text \<open>
  Exact projections from the stable strong-snapshot core.  Each theorem
  exposes one semantic ledger entry without reopening the full conjunction in
  downstream generated-source proofs.
\<close>

lemma StrongSchedulerSnapshotRel_coreD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "core_wf a"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_domainD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "strong_managed_domain_rel a termination managed"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_generic_coverageD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "GenericRootFamilyCoverage D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       GenericRootUniverse generic_raw generic_abs managed K_G"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_event_coverageD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "EventRootFamilyCoverage external D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       event_raw event_abs managed K_E"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_generic_projectionD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "strong_generic_role_projection a termination generic_abs"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_event_projectionD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "strong_event_role_projection a managed external event_abs"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_snapshot_projectionD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "strong_one_due_snapshot_projection a generic_abs event_abs K_G K_E S"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_role_scalar_currentD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "scheduler_role_rel generated_scheduler_roots c a \<and>
     scheduler_managed_scalar_rel c a managed \<and>
     scheduler_current_rel D c a \<and>
     scheduler_boundary_rel c"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_scalar_pinsD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "Scheduler_V611_Parse.globals.xTickCount_' c = sa_tick a \<and>
     unat (Scheduler_V611_Parse.globals.uxSchedulerSuspended_' c) =
       sa_suspend_depth a \<and>
     unat (Scheduler_V611_Parse.globals.uxMissedTicks_' c) =
       sa_missed_ticks a \<and>
     Scheduler_V611_Parse.globals.xMissedYield_' c =
       (if sa_missed_yield a then 1 else 0) \<and>
     unat (Scheduler_V611_Parse.globals.uxTopReadyPriority_' c) =
       sa_top_ready a \<and>
     Scheduler_V611_Parse.globals.xNumOfOverflows_' c =
       of_nat (sa_overflows a) \<and>
     unat (Scheduler_V611_Parse.globals.uxCurrentNumberOfTasks_' c) =
       card managed \<and>
     unat (Scheduler_V611_Parse.globals.eal6_port_yield_count_' c) =
       sa_yield_count a"
proof -
  have scalar: "scheduler_managed_scalar_rel c a managed"
    using StrongSchedulerSnapshotRel_role_scalar_currentD[OF rel] by simp
  show ?thesis
    using scalar
    by (simp add: scheduler_managed_scalar_rel_def
        managed_scheduler_view_def scheduler_scalar_rel_def)
qed

lemma StrongSchedulerSnapshotRel_snapshot_pinsD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "ods_generic_family S = generic_abs \<and>
     ods_event_family S = event_abs \<and>
     ods_generic_payload S = K_G \<and>
     ods_event_payload S = K_E \<and>
     ods_top S = sa_top_ready a \<and>
     ods_captured_generic_key S = None \<and>
     ods_checked_event S = None"
  using StrongSchedulerSnapshotRel_snapshot_projectionD[OF rel]
  by (simp add: strong_one_due_snapshot_projection_def)

lemma StrongSchedulerSnapshotRel_managed_observationD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows
    "scheduler_managed_task_observation_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) a managed"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_wake_projectionD:
  assumes
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
  shows "strong_wake_payload_projection a K_G"
  using assms
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_wakeD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> sa_live a"
  shows
    "sa_wake a t =
       (if t \<in> generic_task_set (sa_delayed_a a) \<union>
                  generic_task_set (sa_delayed_b a)
        then Some (K_G t)
        else None)"
  using StrongSchedulerSnapshotRel_wake_projectionD[OF rel] task
  by (simp add: strong_wake_payload_projection_def)

lemma StrongSchedulerSnapshotRel_generic_count_cursorD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and root: "lp \<in> GenericRootUniverse"
  shows
    "unat (uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) lp)) =
       length (ring (generic_abs lp)) \<and>
     rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (raw_cursor_at
          (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) lp)
       (cursor (generic_abs lp))"
  by (rule GenericRootFamilyCoverage_count_cursorD[
        OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel] root])

lemma StrongSchedulerSnapshotRel_event_count_cursorD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "unat (uxNumberOfItems_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) lp)) =
       length (ring (event_abs lp)) \<and>
     rel_option (\<lambda>p n. sd_node_decode D p = Some n)
       (raw_cursor_at
          (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)) lp)
       (cursor (event_abs lp))"
  by (rule EventRootFamilyCoverage_count_cursorD[
        OF StrongSchedulerSnapshotRel_event_coverageD[OF rel] root])

lemma StrongSchedulerSnapshotRel_generic_container_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
    and root: "lp \<in> GenericRootUniverse"
  shows
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw lp))
       \<longleftrightarrow>
     pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (generic_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  by (rule GenericRootFamilyCoverage_container_iff[
        OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
           task root])

lemma StrongSchedulerSnapshotRel_event_container_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
    and root: "lp \<in> EventRootUniverse external"
  shows
    "event_item_raw_ptr D t \<in> set (ring (event_raw lp))
       \<longleftrightarrow>
     pvContainer_C
       (h_val (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
         (event_item_raw_ptr D t)) =
       PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
proof -
  have family:
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[
          OF StrongSchedulerSnapshotRel_event_coverageD[OF rel]])
  show ?thesis
    by (rule scheduler_event_root_family_container_iff[
          OF family task root])
qed

lemma StrongSchedulerSnapshotRel_cross_storageD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and generic_root: "g \<in> GenericRootUniverse"
    and event_root: "e \<in> EventRootUniverse external"
  shows
    "raw_xlist_storage g (generic_raw g) \<inter>
       raw_xlist_storage e (event_raw e) = {}"
  using rel generic_root event_root
  by (simp add: StrongSchedulerSnapshotRel_def Let_def)

lemma StrongSchedulerSnapshotRel_generic_payloadD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (generic_item_raw_ptr D t) = K_G t"
  by (rule GenericRootFamilyCoverage_physical_keyD[
        OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel] task])

lemma StrongSchedulerSnapshotRel_event_payloadD:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "raw_key_at (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (event_item_raw_ptr D t) = K_E t"
  by (rule EventRootFamilyCoverage_physical_keyD[
        OF StrongSchedulerSnapshotRel_event_coverageD[OF rel] task])

text \<open>Exact root-membership connectors to scheduler_abs.\<close>

lemma StrongSchedulerSnapshotRel_ready_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
    and priority: "p < 4"
  shows
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw
         (abi_list_ptr (sr_ready generated_scheduler_roots p))))
     \<longleftrightarrow>
     Generic t \<in> set (ring (sa_ready a p))"
proof -
  let ?lp = "abi_list_ptr (sr_ready generated_scheduler_roots p)"
  have root: "?lp \<in> GenericRootUniverse"
    by (rule GenericRootUniverse_readyI[OF priority])
  have member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?lp))
       \<longleftrightarrow>
     Generic t \<in> set (ring (generic_abs ?lp))"
    by (rule GenericRootFamilyCoverage_member_iff[
          OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
             task root])
  have projection: "generic_abs ?lp = sa_ready a p"
    by (rule strong_generic_role_readyD[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF rel]
             priority])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_delayed_a_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw
         (abi_list_ptr (sr_delayed_a generated_scheduler_roots))))
     \<longleftrightarrow>
     Generic t \<in> set (ring (sa_delayed_a a))"
proof -
  let ?lp = "abi_list_ptr (sr_delayed_a generated_scheduler_roots)"
  have member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?lp))
       \<longleftrightarrow>
     Generic t \<in> set (ring (generic_abs ?lp))"
    by (rule GenericRootFamilyCoverage_member_iff[
          OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
             task GenericRootUniverse_delayed_aI])
  have projection: "generic_abs ?lp = sa_delayed_a a"
    by (rule strong_generic_role_delayed_aD[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF rel]])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_delayed_b_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw
         (abi_list_ptr (sr_delayed_b generated_scheduler_roots))))
     \<longleftrightarrow>
     Generic t \<in> set (ring (sa_delayed_b a))"
proof -
  let ?lp = "abi_list_ptr (sr_delayed_b generated_scheduler_roots)"
  have member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?lp))
       \<longleftrightarrow>
     Generic t \<in> set (ring (generic_abs ?lp))"
    by (rule GenericRootFamilyCoverage_member_iff[
          OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
             task GenericRootUniverse_delayed_bI])
  have projection: "generic_abs ?lp = sa_delayed_b a"
    by (rule strong_generic_role_delayed_bD[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF rel]])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_suspended_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw
         (abi_list_ptr (sr_suspended generated_scheduler_roots))))
     \<longleftrightarrow>
     Generic t \<in> set (ring (sa_suspended a))"
proof -
  let ?lp = "abi_list_ptr (sr_suspended generated_scheduler_roots)"
  have member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?lp))
       \<longleftrightarrow>
     Generic t \<in> set (ring (generic_abs ?lp))"
    by (rule GenericRootFamilyCoverage_member_iff[
          OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
             task GenericRootUniverse_suspendedI])
  have projection: "generic_abs ?lp = sa_suspended a"
    by (rule strong_generic_role_suspendedD[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF rel]])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_termination_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D t \<in>
       set (ring (generic_raw
         (abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_')))
     \<longleftrightarrow>
     Generic t \<in> set (ring termination)"
proof -
  let ?lp =
    "abi_list_ptr Scheduler_V611_Parse.xTasksWaitingTermination_'"
  have member:
    "generic_item_raw_ptr D t \<in> set (ring (generic_raw ?lp))
       \<longleftrightarrow>
     Generic t \<in> set (ring (generic_abs ?lp))"
    by (rule GenericRootFamilyCoverage_member_iff[
          OF StrongSchedulerSnapshotRel_generic_coverageD[OF rel]
             task GenericRootUniverse_terminationI])
  have projection: "generic_abs ?lp = termination"
    by (rule strong_generic_role_terminationD[
          OF StrongSchedulerSnapshotRel_generic_projectionD[OF rel]])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_pending_event_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw GeneratedPendingEventRoot))
     \<longleftrightarrow>
     Event t \<in> set (ring (sa_pending a))"
proof -
  have family:
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[
          OF StrongSchedulerSnapshotRel_event_coverageD[OF rel]])
  have member:
    "event_item_raw_ptr D t \<in>
       set (ring (event_raw GeneratedPendingEventRoot))
       \<longleftrightarrow>
     Event t \<in> set (ring (event_abs GeneratedPendingEventRoot))"
    by (rule scheduler_event_root_family_member_iff[
          OF family task EventRootUniverse_pendingI])
  have projection:
    "event_abs GeneratedPendingEventRoot = sa_pending a"
    by (rule strong_event_role_pendingD[
          OF StrongSchedulerSnapshotRel_event_projectionD[OF rel]])
  show ?thesis using member projection by simp
qed

lemma StrongSchedulerSnapshotRel_external_event_member_iff:
  assumes rel:
    "StrongSchedulerSnapshotRel D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S"
    and task: "t \<in> managed"
  shows
    "(\<exists>lp\<in>external.
        event_item_raw_ptr D t \<in> set (ring (event_raw lp)))
     \<longleftrightarrow>
     t \<in> sa_event_waiting a"
proof -
  have family:
    "scheduler_event_root_family_rel D
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw event_abs managed K_E"
    by (rule EventRootFamilyCoverage_relD[
          OF StrongSchedulerSnapshotRel_event_coverageD[OF rel]])
  have each:
    "\<And>lp. lp \<in> external \<Longrightarrow>
       (event_item_raw_ptr D t \<in> set (ring (event_raw lp))
        \<longleftrightarrow>
        Event t \<in> set (ring (event_abs lp)))"
  proof -
    fix lp
    assume external_root: "lp \<in> external"
    have root: "lp \<in> EventRootUniverse external"
      by (rule EventRootUniverse_externalI[OF external_root])
    show
      "event_item_raw_ptr D t \<in> set (ring (event_raw lp))
       \<longleftrightarrow>
       Event t \<in> set (ring (event_abs lp))"
      by (rule scheduler_event_root_family_member_iff[
            OF family task root])
  qed
  have union:
    "{u. \<exists>lp\<in>external.
       Event u \<in> set (ring (event_abs lp))} = sa_event_waiting a"
    by (rule strong_event_role_external_unionD[
          OF StrongSchedulerSnapshotRel_event_projectionD[OF rel]])
  show ?thesis
  proof
    assume raw_owner:
      "\<exists>lp\<in>external.
         event_item_raw_ptr D t \<in> set (ring (event_raw lp))"
    then obtain lp where
        lp_external: "lp \<in> external"
      and raw_member:
        "event_item_raw_ptr D t \<in> set (ring (event_raw lp))"
      by clarify
    have abs_member: "Event t \<in> set (ring (event_abs lp))"
      by (rule iffD1[OF each[OF lp_external] raw_member])
    have abs_witness:
      "\<exists>root\<in>external.
         Event t \<in> set (ring (event_abs root))"
    proof (rule bexI[where x=lp])
      show "Event t \<in> set (ring (event_abs lp))"
        by (rule abs_member)
      show "lp \<in> external"
        by (rule lp_external)
    qed
    have
      "t \<in> {u. \<exists>root\<in>external.
         Event u \<in> set (ring (event_abs root))}"
      using abs_witness by simp
    then show "t \<in> sa_event_waiting a"
      using union by simp
  next
    assume waiting: "t \<in> sa_event_waiting a"
    have
      "t \<in> {u. \<exists>lp\<in>external.
         Event u \<in> set (ring (event_abs lp))}"
      using waiting union by simp
    then obtain lp where
        lp_external: "lp \<in> external"
      and abs_member: "Event t \<in> set (ring (event_abs lp))"
      by clarify
    have raw_member:
      "event_item_raw_ptr D t \<in> set (ring (event_raw lp))"
      by (rule iffD2[OF each[OF lp_external] abs_member])
    show
      "\<exists>lp\<in>external.
         event_item_raw_ptr D t \<in> set (ring (event_raw lp))"
    proof (rule bexI[where x=lp])
      show "event_item_raw_ptr D t \<in> set (ring (event_raw lp))"
        by (rule raw_member)
      show "lp \<in> external"
        by (rule lp_external)
    qed
  qed
qed

end

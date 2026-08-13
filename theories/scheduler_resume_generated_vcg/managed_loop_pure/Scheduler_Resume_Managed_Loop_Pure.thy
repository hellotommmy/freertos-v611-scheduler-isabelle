theory Scheduler_Resume_Managed_Loop_Pure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Loop_Induction.Scheduler_Resume_Managed_Loop_Induction"
begin

lemma CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows "ring (sa_pending a) = map Event (rpc_tasks C)"
proof -
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase]
  note ring =
    CursorGeneralStrongResumePendingManagedGateRel_managed_tasks_ringD[
      OF gate]
  note alignment =
    CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase]
  show ?thesis
    using ring alignment
    by (simp add: resume_pending_managed_phase_alignment_def)
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_drain_pending_absD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "drain_pending_nodes_abs (map Event (rpc_tasks C)) a =
       drain_pending_abs a"
  using
    CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD[OF phase]
  by (simp add: drain_pending_abs_def)

lemma CursorGeneralStrongResumePendingManagedPhaseRel_requires_yieldD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "resume_pending_requires_yield a \<longleftrightarrow>
       (\<exists>u\<in>set (rpc_tasks C).
          rpc_current_priority C \<le> rpc_priority C u)"
proof -
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase]
  note alignment =
    CursorGeneralStrongResumePendingManagedPhaseRel_alignmentD[OF phase]
  note pending =
    CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD[OF phase]
  have current_safe:
    "ring (sa_pending a) \<noteq> [] \<longrightarrow> sa_current a \<noteq> None"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  show ?thesis
  proof (cases "sa_current a")
    case None
    have pending_empty: "ring (sa_pending a) = []"
      using current_safe None by blast
    have tasks_empty: "rpc_tasks C = []"
      using pending pending_empty by simp
    show ?thesis
      using None tasks_empty
      by (simp add: resume_pending_requires_yield_def)
  next
    case (Some current)
    have priority: "rpc_priority C = sa_priority a"
      using alignment
      by (simp add: resume_pending_managed_phase_alignment_def)
    have current_priority:
      "rpc_current_priority C = sa_priority a current"
      using alignment Some
      by (simp add: resume_pending_managed_phase_alignment_def
          resume_pending_managed_current_priority_def)
    show ?thesis
      using pending Some priority current_priority
      by (auto simp: resume_pending_requires_yield_def)
  qed
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD:
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and empty: "rpc_tasks C = []"
  shows
    "ring (sa_pending a) = [] \<and>
     CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external \<and>
     Scheduler_V611_Parse.globals.eal6_port_critical_depth_' c = 1 \<and>
     Scheduler_V611_Parse.globals.eal6_port_interrupts_disabled_' c = 1 \<and>
     Scheduler_V611_Parse.globals.xSchedulerRunning_' c = 1"
proof -
  note gate =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase]
  have pending_empty: "ring (sa_pending a) = []"
    using
      CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD[OF phase]
      empty
    by simp
  have pending_wf: "tick_entry_pending_wf a"
    using pending_empty by (simp add: tick_entry_pending_wf_def)
  obtain c0 where overlay:
      "c = scheduler_port_overlay (1 :: 32 word) (1 :: 32 word) c0"
    and snapshot:
      "CursorGeneralStrongSchedulerSnapshotRel D c0 a managed termination
         external generic_raw generic_abs event_raw event_abs K_G K_E S"
    using CursorGeneralStrongResumePendingManagedGateRelD[OF gate]
    by blast
  have endpoint:
    "CursorGeneralStrongSchedulerEndpointRel
       D c0 a managed termination external"
    unfolding CursorGeneralStrongSchedulerEndpointRel_def
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x=generic_abs])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x=event_abs])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    using snapshot by blast
  have public:
    "CursorGeneralStrongVTaskIncrementTickPublicEntryRel
       D c0 a managed termination external"
    by (rule CursorGeneralStrongSchedulerEndpointRel_public_tick_entryI[
          OF endpoint pending_wf])
  have protected:
    "CursorGeneralStrongVTaskIncrementTickProtectedEntryRel
       D (1 :: 32 word) (1 :: 32 word) c a
       managed termination external"
    unfolding CursorGeneralStrongVTaskIncrementTickProtectedEntryRel_def
    apply (rule exI[where x=c0])
    using overlay public by blast
  note pins =
    CursorGeneralStrongResumePendingManagedGateRel_port_runningD[OF gate]
  show ?thesis
    using pending_empty protected pins by blast
qed

lemma CursorGeneralStrongResumePendingManagedPhaseRel_control_frame:
  assumes phase_before:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
    and phase_after:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D s b managed termination external
       generic_raw' generic_abs' event_raw' event_abs'
       K_G K_E S' C' P'"
  shows "resume_pending_control_frame c s"
proof -
  note gate_before =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase_before]
  note gate_after =
    CursorGeneralStrongResumePendingManagedPhaseRel_gateD[OF phase_after]
  note pins_before =
    CursorGeneralStrongResumePendingManagedGateRel_port_runningD[
      OF gate_before]
  note pins_after =
    CursorGeneralStrongResumePendingManagedGateRel_port_runningD[
      OF gate_after]
  show ?thesis
    using pins_before pins_after
    by (simp add: resume_pending_control_frame_def)
qed

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "managed pending ring" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_pending_ringD}
  val _ = audit_exact "managed drain pending abstract state" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_drain_pending_absD}
  val _ = audit_exact "managed resume requires yield" 1
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_requires_yieldD}
  val _ = audit_exact "managed empty protected tick entry" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_empty_tick_entryD}
  val _ = audit_exact "managed resume control frame" 2
    @{thm CursorGeneralStrongResumePendingManagedPhaseRel_control_frame}
\<close>

end
